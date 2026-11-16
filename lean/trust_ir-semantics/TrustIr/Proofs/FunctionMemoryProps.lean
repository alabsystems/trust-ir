-- Copyright 2026 Andrew Yates | Author: Andrew Yates | Apache-2.0
import TrustIr.Proofs.ByteMemory

namespace TrustIr

/-- A successful source-position lookup names that exact entry and lies
    within the full table. No executable-body or signature premise is used. -/
theorem functionAddressIndex_spec (target : FuncId) (ids : List FuncId) (index : Nat)
    (h : functionAddressIndex target ids = some index) :
    trustIrListGet? ids index = some target ∧ index < ids.length := by
  induction ids generalizing index with
  | nil => simp [functionAddressIndex] at h
  | cons head tail ih =>
    by_cases heq : head = target
    · subst head
      simp only [functionAddressIndex, if_pos rfl] at h
      have hn : index = 0 := (Option.some.inj h).symm
      subst index
      exact ⟨rfl, Nat.zero_lt_succ _⟩
    · simp only [functionAddressIndex, if_neg heq] at h
      cases ht : functionAddressIndex target tail with
      | none => simp [ht] at h
      | some n =>
        simp only [ht, Option.map] at h
        cases Option.some.inj h
        obtain ⟨hget, hlt⟩ := ih n ht
        exact ⟨hget, Nat.succ_lt_succ hlt⟩

theorem checkedFunctionAddress_ok (model : ByteModel) (index : Nat)
    (h : index + 1 < model.addressLimit) :
    checkedFunctionAddress model index = .ok (index + 1) := by
  simp [checkedFunctionAddress, h]

theorem checkedFunctionAddress_refuses_overflow (model : ByteModel) (index : Nat)
    (h : ¬ index + 1 < model.addressLimit) :
    checkedFunctionAddress model index =
      .error (.typeError "Store: function address exceeds target pointer width") := by
  simp [checkedFunctionAddress, h]

/-- Both pointer widths use the same exact byte arithmetic; no truncation is
    hidden in the address round trip. -/
theorem decode_encode_function_address (model : ByteModel) (address : Nat)
    (h : address < model.addressLimit) :
    decodeIntBytes (encodeIntBytes (Int.ofNat address) model.pointerBytes) = address := by
  change decodeIntBytes.go (encodeIntBytes.go model.pointerBytes address) 0 = address
  rw [decode_encode_go]
  simp only [Nat.pow_zero, Nat.one_mul]
  exact Nat.mod_eq_of_lt h

theorem functionTargetAt_index (model : ByteModel) (ids : List FuncId)
    (target : FuncId) (index : Nat)
    (h : functionAddressIndex target ids = some index)
    (hrange : index + 1 < model.addressLimit) :
    functionTargetAt model (some ids) (index + 1) = .ok target := by
  have hget := (functionAddressIndex_spec target ids index h).1
  simp [functionTargetAt, hrange, hget, bind, pure, Except.bind, Except.pure]

theorem encodeFunctionWord (model : ByteModel) (ids : List FuncId)
    (signature : FuncTyId) (target : FuncId) (index : Nat)
    (h : functionAddressIndex target ids = some index)
    (hrange : index + 1 < model.addressLimit) :
    encodeMemoryWithFunctions model (some ids) (.Func signature) (.fnDef signature target) =
      .ok (encodeIntBytes (Int.ofNat (index + 1)) model.pointerBytes) := by
  simp [encodeMemoryWithFunctions, functionAddressOf, h, checkedFunctionAddress, hrange,
    bind, pure, Except.bind, Except.pure]

/-- The load signature is retained independently of the target identity. The
    actual callee's contract remains an indirect-call obligation. -/
theorem decodeFunctionWord (model : ByteModel) (ids : List FuncId) (memory : Memory)
    (loadedSignature : FuncTyId) (target : FuncId) (index : Nat)
    (h : functionAddressIndex target ids = some index)
    (hrange : index + 1 < model.addressLimit) :
    decodeMemoryWithFunctions model (some ids) memory (.Func loadedSignature)
        (encodeIntBytes (Int.ofNat (index + 1)) model.pointerBytes) =
      .ok (.fnDef loadedSignature target) := by
  simp only [decodeMemoryWithFunctions, encodeIntBytes_length, if_pos rfl]
  rw [decode_encode_function_address model (index + 1) hrange]
  rw [if_neg (Nat.succ_ne_zero index)]
  rw [functionTargetAt_index model ids target index h hrange]
  rfl

theorem encodeFunctionNull (model : ByteModel) (order : FunctionAddressOrder)
    (signature : FuncTyId) :
    encodeMemoryWithFunctions model order (.Func signature) .nullPtr =
      .ok (List.replicate model.pointerBytes 0) := rfl

theorem decodeFunctionNull (model : ByteModel) (order : FunctionAddressOrder)
    (memory : Memory) (signature : FuncTyId) :
    decodeMemoryWithFunctions model order memory (.Func signature)
        (List.replicate model.pointerBytes 0) = .ok .nullPtr := by
  cases model <;> trustIrReduce

/-- Unknown nonzero words are errors at decode, without consulting data
    provenance or pretending that an unregistered address denotes a callee. -/
theorem functionTargetAt_unregistered (model : ByteModel) (ids : List FuncId) (address : Nat)
    (hzero : address ≠ 0) (hrange : address < model.addressLimit)
    (hunknown : trustIrListGet? ids (address - 1) = none) :
    functionTargetAt model (some ids) address =
      .error (.typeError "Load: unregistered function pointer address") := by
  simp [functionTargetAt, hzero, hrange, hunknown, bind, pure, Except.bind, Except.pure]

/-- The data cursor is initialized above the complete code namespace. Every
    in-range address above that namespace is rejected as a function word. -/
theorem functionTargetAt_above_table (model : ByteModel) (ids : List FuncId) (address : Nat)
    (habove : ids.length < address) (hrange : address < model.addressLimit) :
    functionTargetAt model (some ids) address =
      .error (.typeError "Load: unregistered function pointer address") := by
  have hzero : address ≠ 0 := by omega
  have hlen : ids.length ≤ address - 1 := by omega
  exact functionTargetAt_unregistered model ids address hzero hrange (CompilerCompat.listGet?_outside ids (address - 1) hlen)

/-- A function-address table contains no authenticated signature declarations,
    so it cannot by itself authorize a nominal zero-byte item image. -/
theorem encodeFnItemWithoutPlan (model : ByteModel) (order : FunctionAddressOrder)
    (target : FuncId) (value : Value) :
    encodeMemoryWithFunctions model order (.FnItem target) value =
      .error (.unsupported .layout "function item Store requires a prepared source plan") := rfl

theorem decodeFnItemWithoutPlan (model : ByteModel) (order : FunctionAddressOrder)
    (memory : Memory) (target : FuncId) (bytes : List UInt8) :
    decodeMemoryWithFunctions model order memory (.FnItem target) bytes =
      .error (.unsupported .layout "function item Load requires a prepared source plan") := rfl

end TrustIr
