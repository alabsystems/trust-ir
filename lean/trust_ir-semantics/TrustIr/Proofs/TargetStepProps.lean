-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0

import TrustIr.Proofs.TargetMemoryProps
import TrustIr.Proofs.MemorySafety
import TrustIr.Semantics.Eval
import TrustIr.Proofs.ConstantTypingEquations

namespace TrustIr

/-- Legacy layout and decoding selectors are unchanged. Encoding adds the
    physical-pointer observation check before the original encoder. -/
theorem legacy_model_selectors (ty : Ty) (mem : Memory) (value : Value)
    (bytes : List UInt8) :
    ty.bitWidthFor .le64 = ty.bitWidth ∧
    ty.byteSizeFor .le64 = ty.byteSize ∧
    ty.byteAlignFor .le64 = ty.byteAlign ∧
    encodeMemoryAt .le64 ty value = (do
      checkPointerImageWords .le64 value
      encodeValueAt ty value) ∧
    decodeMemoryAt .le64 mem ty bytes = decodeValueAt mem ty bytes := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The target check is an additional refusal before the same allocation,
    liveness, alignment and provenance checks. -/
theorem checkedAccess_model_factor (model : ByteModel) (op : String) (address : Addr)
    (id : AllocId) (size align : Nat) :
    Sem.checkedAccess op address id size align model = (do
      Sem.checkTargetRange model op address size
      Sem.checkedAccess op address id size align .le64) := by
  simp only [Sem.checkedAccess, Sem.checkTargetRange, pure_bind, bind_assoc]

theorem target_range32_ok (op : String) (address size : Nat) (s s' : MachineState)
    (h : Sem.run (Sem.checkTargetRange .le32 op address size) s = .ok ((), s')) :
    s' = s ∧ address < ByteModel.le32.addressLimit ∧
      address + size ≤ ByteModel.le32.addressLimit := by
  simp only [Sem.checkTargetRange, Bool.and_eq_true, decide_eq_true_eq] at h
  split at h
  · rename_i hb
    have hr : address < ByteModel.le32.addressLimit ∧
        address + size ≤ ByteModel.le32.addressLimit := hb
    have hs : s = s' := by simpa only [Sem.run, sr_pure, Except.ok.injEq, Prod.mk.injEq,
      true_and] using h
    exact ⟨hs.symm, hr⟩
  · simp only [Sem.run, sr_throwUB] at h <;> cases h

/-- Successful32-bit accesses satisfy both the new address-space bound and
    the unchanged full memory-access check. No target rule can replace it. -/
theorem checkedAccess32_retains_legacy (op : String) (address : Addr) (id : AllocId)
    (size align : Nat) (s s' : MachineState) (result : Addr)
    (h : Sem.run (Sem.checkedAccess op address id size align .le32) s = .ok (result, s')) :
    Sem.run (Sem.checkedAccess op address id size align .le64) s = .ok (result, s') ∧
    address < ByteModel.le32.addressLimit ∧ address + size ≤ ByteModel.le32.addressLimit := by
  rw [checkedAccess_model_factor, Sem.run_bind] at h
  cases hr : Sem.run (Sem.checkTargetRange .le32 op address size) s with
  | error e => simp only [hr, Except.bind] at h <;> cases h
  | ok pair =>
    rcases pair with ⟨unit, st⟩
    cases unit
    obtain ⟨hst, ha, he⟩ := target_range32_ok op address size s st hr
    subst st
    simp only [hr, Except.bind] at h
    exact ⟨h, ha, he⟩

theorem checkedAccess32_names_live_provenance (op : String) (address : Addr) (id : AllocId)
    (size align : Nat) (s s' : MachineState) (result : Addr)
    (h : Sem.run (Sem.checkedAccess op address id size align .le32) s = .ok (result, s')) :
    s' = s ∧ result = address ∧ ∃ alloc,
      s.memory.lookup id = some alloc ∧ alloc.alive = true ∧
      (align = 0 ∨ address % align = 0) ∧ alloc.base ≤ address ∧
      address - alloc.base + size ≤ alloc.size := by
  exact checkedAccess_ok_inv op address id size align s s' result
    (checkedAccess32_retains_legacy op address id size align s s' result h).1

private theorem memoryExcept_ok {α : Type} (value : α) :
    Sem.fromMemoryExcept (.ok value) = (pure value : Sem α) := rfl

/-- Memory exhaustion stays distinct from instruction fuel. A malformed
    overflowing allocation-id counter has its earlier UB branch; excluding
    that branch is necessary for the target-capacity classification. -/
theorem wordAllocation32_exhaustion_code (memory : Memory) (size alignment slack : Nat)
    (hId : memory.nextAllocId < word64Max)
    (hTarget : ByteModel.le32.addressLimit <
      alignUp memory.nextAddr alignment + max (size + slack) 1) :
    (checkWordAllocation .le32 memory size alignment slack).mapError SemError.code =
      .error "out_of_memory" := by
  unfold checkWordAllocation
  dsimp only
  split
  · rfl
  split
  · rfl
  split
  · rename_i hIdBad
    exact False.elim (Nat.not_lt_of_ge hIdBad hId)
  split
  · rfl
  split
  · rfl
  · rename_i hTargetBad
    exfalso
    omega

theorem allocation32_refuses_exhaustion (mem : Memory) (size align slack : Nat) (s : MachineState)
    (hId : mem.nextAllocId < word64Max)
    (h : ByteModel.le32.addressLimit < alignUp mem.nextAddr align + max (size + slack) 1) :
    Except.mapError SemError.code
      (Sem.run (Sem.checkTargetAllocation .le32 mem size align slack) s) =
      .error "out_of_memory" := by
  have checked := wordAllocation32_exhaustion_code mem size align slack hId h
  cases hc : checkWordAllocation .le32 mem size align slack with
  | error error =>
    simpa only [hc, Sem.checkTargetAllocation, Sem.fromMemoryExcept, Sem.run, sr_throw, Except.mapError, Except.error.injEq]
      using checked
  | ok unit => simp only [hc, Except.mapError] at checked <;> cases checked

set_option smartUnfolding false in
/-- A real32-bit Const step binds the residue at32 bits, not at the host's
    default width. Symbolic in the authored integer. -/
theorem step_usize32_residue (value : Int) :
    stepInst (.Const .Usize (.int value)) .le32 = (do
      let id ← Sem.bindFresh (Value.intAt 32 value)
      pure (.value (some id))) := by
  simp only [stepInst, Constant.hasSymbolAddr, Bool.false_eq_true, ↓reduceIte]
  rw [constValueAtChecked_eq]
  simp [constPointerFormsSupported, constValueAt, Ty.isInteger, exceptSem_pure, exceptSem_ok_bind,
    Ty.bitWidthFor, Ty.bitWidthAtModel, Ty.bitWidthAtPointerBits, ByteModel.pointerBits, ByteModel.pointerBytes]

theorem cast_address32_refuses_limit (s : MachineState) :
    Except.mapError SemError.code
      (Sem.run (Sem.addrOfInt "IntToPtr" 64 (Int.ofNat ByteModel.le32.addressLimit) .le32) s)
      = .error "ub" := rfl

theorem same_address_fits_legacy64 (s : MachineState) :
    Sem.run (Sem.addrOfInt "IntToPtr" 64 (Int.ofNat ByteModel.le32.addressLimit) .le64) s =
      .ok (ByteModel.le32.addressLimit, s) := rfl

/-- A real32-bit Alloca refuses before touching an exhausted allocator.
    The allocation-id counter retains its independent earlier UB condition. -/
theorem step_alloca32_refuses_exhaustion (s : MachineState)
    (hId : s.memory.nextAllocId < word64Max)
    (h : ByteModel.le32.addressLimit < alignUp s.memory.nextAddr 4 + 4) :
    Except.mapError SemError.code (Sem.run (stepInst (.Alloca .Ptr none none) .le32) s) =
      .error "out_of_memory" := by
  have hCheck := allocation32_refuses_exhaustion s.memory 4 4 0 s hId (by simpa using h)
  have hLayout : scalarMemoryLayout .le32 .Ptr = .ok ⟨4, 4⟩ := rfl
  have hMul : checkedWord64Mul "Alloca" 4 1 = .ok 4 := rfl
  have hAlign : checkedMemoryAlign "Alloca" 4 none = .ok 4 := rfl
  simp only [stepInst, semAlloca, semAllocaUsing, semAllocateUsing, hLayout,
    memoryExcept_ok, pure_bind, hMul, hAlign]
  change Except.mapError SemError.code
    (StateT.run (Sem.fromMemoryExcept (checkWordAllocation .le32 s.memory 4 4 0)) s) = _ at hCheck
  simp only [Sem.run, sr_bind, sr_get, Except.bind]
  cases hc : StateT.run (Sem.fromMemoryExcept (checkWordAllocation .le32 s.memory 4 4 0)) s with
  | error error => simpa only [hc, Except.bind, Except.mapError, Except.error.injEq] using hCheck
  | ok pair => simp only [hc, Except.mapError] at hCheck <;> cases hCheck

/-- Operand lookup and poison inspection precede the static metadata error,
    matching the reference constructor's error order. -/
theorem wrong_metadata32_refused_after_operand_inspection (data metadata : ValueId) :
    semPtrFromParts (.FatPtr .Str) .U64 data metadata .le32 = (do
      let dataValue ← Sem.lookupValue data
      let metadataValue ← Sem.lookupValue metadata
      Sem.rejectPartial dataValue "PtrFromParts data"
      Sem.rejectPartial metadataValue "PtrFromParts metadata"
      Sem.throwTypeError "PtrFromParts: declared metadata type does not match the fat-pointer kind") := rfl

-- Kernel controls for the separate conversion, arithmetic and allocator
-- guards. These do not allocate enormous images or use native_decide.
theorem wide_zst_index_refuses_before_multiplication (model : ByteModel) :
    gepOffsetUsing (scalarMemoryLayout model)
      (fun (_ : Unit) value => typedIntegerValue model .U128 value) .Unit
      [((), .int 128 18446744073709551616)] = .error
        (.ub "GEP: integer operand exceeds u64") := by
  cases model <;> rfl

theorem wide_zst_index_keeps_u64_on_target32 :
    gepOffsetUsing (scalarMemoryLayout .le32)
      (fun (_ : Unit) value => typedIntegerValue .le32 .U64 value) .Unit
      [((), .int 64 4294967296)] = .ok 0 := rfl

theorem unsigned_top_bit_keeps_magnitude :
    typedIntegerValue .le64 .U8 (.int 8 255) = .ok 255 := rfl

theorem signed_top_bit_keeps_signed_interpretation :
    typedIntegerValue .le64 .I8 (.int 8 255) = .ok (-1) := rfl

theorem allocation64_footprint_overflow_is_memory :
    checkWordAllocation .le64 Memory.empty word64Max 1 1 = .error
      (.outOfMemory "allocation footprint exceeds u64") := rfl

theorem allocation64_aligned_base_overflow_is_memory :
    checkWordAllocation .le64 { Memory.empty with nextAddr := word64Max } 1 8 0 = .error
      (.outOfMemory "aligned allocation base exceeds u64") := rfl

theorem allocation64_id_overflow_is_earlier_ub :
    checkWordAllocation .le64 { Memory.empty with nextAllocId := word64Max } 1 1 0 = .error
      (.ub "allocation identifier increment overflows u64") := rfl

theorem allocation64_next_address_must_fit_word :
    checkWordAllocation .le64 { Memory.empty with nextAddr := word64Max } 1 1 0 = .error
      (.outOfMemory "allocation next-address increment exceeds u64") := rfl

theorem allocation64_zst_still_needs_counter_bump :
    checkWordAllocation .le64 { Memory.empty with nextAddr := word64Max } 0 1 0 = .error
      (.outOfMemory "allocation next-address increment exceeds u64") := rfl

theorem allocation32_last_byte_is_available :
    checkWordAllocation .le32 { Memory.empty with nextAddr := 4294967295 } 1 1 0 = .ok () := rfl

theorem allocation32_beyond_last_byte_is_memory :
    checkWordAllocation .le32 { Memory.empty with nextAddr := 4294967295 } 2 1 0 = .error
      (.outOfMemory "allocation exceeds the target address space") := rfl

theorem allocation32_id_overflow_precedes_target_exhaustion :
    checkWordAllocation .le32
      { Memory.empty with nextAddr := 4294967295, nextAllocId := word64Max } 2 1 0 = .error
      (.ub "allocation identifier increment overflows u64") := rfl

end TrustIr
