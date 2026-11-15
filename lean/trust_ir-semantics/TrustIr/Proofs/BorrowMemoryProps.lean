-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0

import TrustIr.Semantics.Borrow
import TrustIr.Semantics.Step
import TrustIr.Proofs.MemorySafety

namespace TrustIr
namespace BorrowMemoryProps

-- Closed computations are checked by reduction in the Lean kernel. They do
-- not use native_decide or introduce assumptions about a native verifier.
private def outcome {α : Type} (program : Sem α)
    (initial : MachineState := MachineState.empty) : Except String α :=
  match Sem.run program initial with
  | .ok (value, _) => .ok value
  | .error error => .error error.code

private def sharedLoad : Sem Value := do
  let pointer ← semAlloca .I64 none
  let value ← Sem.bindFresh (.int 64 42)
  semStore .I64 pointer value
  let borrowed ← semBorrow pointer
  let loaded ← semLoad .I64 borrowed
  Sem.lookupValue loaded

/-- Allocation zero lives at address 1024 (the reference placement's first
    base); a borrow still reads its bytes. -/
theorem alloca_store_borrow_load : outcome sharedLoad = .ok (.int 64 42) := by rfl

private def mutableWrite : Sem Value := do
  let pointer ← semAlloca .I64 none
  let borrowed ← semBorrowMut pointer
  let value ← Sem.bindFresh (.int 64 57)
  semStore .I64 borrowed value
  let loaded ← semLoad .I64 borrowed
  Sem.lookupValue loaded

theorem alloca_borrow_mut_store_load : outcome mutableWrite = .ok (.int 64 57) := by rfl

private def sharedRoundtrip : Sem (Value × Permission × Permission × Permission) := do
  let pointer ← semAlloca .I64 none
  let first ← semBorrow pointer
  let second ← semBorrow first
  let two ← getPermission ⟨0⟩
  semEndBorrow first
  let one ← getPermission ⟨0⟩
  semEndBorrow second
  let owned ← getPermission ⟨0⟩
  let address ← Sem.lookupValue second
  pure (address, two, one, owned)

theorem shared_reborrow_and_end_preserve_address : outcome sharedRoundtrip =
    .ok (.ptr 1024 (some ⟨0⟩), .sharedBorrow 2, .sharedBorrow 1, .owned) := by rfl

private def mutableRoundtrip : Sem (Value × Permission) := do
  let pointer ← semAlloca .I64 none
  let borrowed ← semBorrowMut pointer
  semEndBorrow borrowed
  let permission ← getPermission ⟨0⟩
  let address ← Sem.lookupValue borrowed
  pure (address, permission)

theorem mutable_end_preserves_address : outcome mutableRoundtrip =
    .ok (.ptr 1024 (some ⟨0⟩), .owned) := by rfl

/-- An interior pointer of an `I64` slot (`gep i8 p [3]`, address 1027). -/
private def interiorOf (pointer : ValueId) : Sem ValueId := do
  let three ← Sem.bindFresh (.int 64 3)
  semGEPUsing (scalarMemoryLayout .le64) (fun _ => typedIntegerValue .le64 .I64)
    .I8 pointer [three]

private def interiorBorrow : Sem (Value × Option AllocId × Permission × Permission) := do
  let pointer ← semAlloca .I64 none
  let interior ← interiorOf pointer
  let borrowed ← semBorrow interior
  let address ← Sem.lookupValue borrowed
  let allocation ← borrowOperand "Borrow" address
  let permission ← getPermission ⟨0⟩
  semEndBorrow borrowed
  let restored ← getPermission ⟨0⟩
  pure (address, allocation, permission, restored)

/-- An interior pointer keeps its offset and its provenance, and borrows the
    allocation it was derived from. -/
theorem interior_borrow_keeps_offset : outcome interiorBorrow =
    .ok (.ptr 1027 (some ⟨0⟩), some ⟨0⟩, .sharedBorrow 1, .owned) := by rfl

private def interiorMutableBorrow : Sem (Value × Permission) := do
  let pointer ← semAlloca .I64 none
  let interior ← interiorOf pointer
  let borrowed ← semBorrowMut interior
  semEndBorrow borrowed
  let address ← Sem.lookupValue borrowed
  let permission ← getPermission ⟨0⟩
  pure (address, permission)

theorem interior_mutable_end_keeps_offset : outcome interiorMutableBorrow =
    .ok (.ptr 1027 (some ⟨0⟩), .owned) := by rfl

private def twoAllocations : Sem (Value × Permission × Permission) := do
  let _ ← semAlloca .I64 none
  let second ← semAlloca .I64 none
  let borrowed ← semBorrow second
  let address ← Sem.lookupValue borrowed
  let firstPermission ← getPermission ⟨0⟩
  let secondPermission ← getPermission ⟨1⟩
  pure (address, firstPermission, secondPermission)

theorem second_allocation_uses_its_own_permission : outcome twoAllocations =
    .ok (.ptr 1032 (some ⟨1⟩), .owned, .sharedBorrow 1) := by rfl

/-- A pointer one past the end of an `I64` slot (`gep i8 p [8]`) names that
    slot, its provenance, but lies outside the bytes it requested: the borrow
    passes the pointer through and moves no permission (SPEC "Freeing an
    allocation under a live borrow is undefined behaviour", clause 2). -/
private def onePastBorrow : Sem (Value × Permission) := do
  let pointer ← semAlloca .I64 none
  let eight ← Sem.bindFresh (.int 64 8)
  let past ← semGEPUsing (scalarMemoryLayout .le64) (fun _ => typedIntegerValue .le64 .I64) .I8 pointer [eight]
  let borrowed ← semBorrow past
  let address ← Sem.lookupValue borrowed
  let permission ← getPermission ⟨0⟩
  pure (address, permission)

theorem one_past_address_moves_no_permission : outcome onePastBorrow =
    .ok (.ptr 1032 (some ⟨0⟩), .owned) := by rfl

/-- An allocation id is not an address: a pointer value at address 0 — the
    number of allocation 0 — has no provenance and is null, and the borrow
    operand rule refuses it. -/
theorem allocation_id_is_not_an_address :
    outcome (do
      let _ ← semAlloca .I64 none
      borrowOperand "Borrow" (.ptr 0 none)) = .error "ub" := by rfl

/-- A borrow of a pointer derived from a FREED allocation moves no
    permission, whatever permission is still recorded for it: the
    allocation's liveness is part of `Memory.borrowTarget`. -/
private def deadBorrow : Sem Permission := do
  let pointer ← semAlloca .I64 none
  Sem.modifyState fun state => { state with memory := { state.memory with
    allocations := state.memory.allocations.map fun allocation => { allocation with alive := false } } }
  let _ ← semBorrow pointer
  getPermission ⟨0⟩

theorem dead_allocation_moves_no_permission : outcome deadBorrow = .ok .owned := by rfl

private def exclusiveReborrow : Sem ValueId := do
  let pointer ← semAlloca .I64 none
  let borrowed ← semBorrowMut pointer
  semBorrow borrowed

theorem shared_from_unique_still_refuses : outcome exclusiveReborrow = .error "ub" := by rfl

private def mutableFromShared : Sem ValueId := do
  let pointer ← semAlloca .I64 none
  let borrowed ← semBorrow pointer
  semBorrowMut borrowed

theorem mutable_from_shared_still_refuses : outcome mutableFromShared = .error "ub" := by rfl

theorem null_refuses : outcome (borrowOperand "Borrow" .nullPtr) = .error "ub" := by rfl
theorem nonpointer_refuses : outcome (borrowOperand "Borrow" (.int 64 1024)) =
    .error "type_error" := by rfl

-- =================================================================
-- A Rust reference carries no permission instruction
-- (`docs/SPEC_RATIFICATIONS.md`, the section of that name)
-- =================================================================
-- The two machine facts behind "no `EndBorrow` placement helps while the outer
-- `&mut` is live", stated for every state rather than computed on one: a
-- shared borrow of an allocation held by a `BorrowMut` faults, and so does a
-- `BorrowMut` of an allocation in any permission but `owned`. A Rust `&mut`
-- stays live across every reborrow of it, so a Rust program spelled with these
-- instructions faults here whatever ends a producer places. The third fact is
-- why the Rust producers' spelling cannot reach the machine: a `Copy` step
-- leaves memory and permissions exactly as they were.

/-- A shared `Borrow` of a thin pointer whose provenance names a live
    allocation it lies inside (`Memory.borrowTarget`, the operand rule) held
    by a `BorrowMut` (`uniqueBorrow`) is undefined behaviour, in every
    state. -/
theorem semBorrow_ub_of_uniqueBorrow (ptrId : ValueId) (s : MachineState)
    (addr : Addr) (id target : AllocId)
    (hp : s.lookupValue ptrId = some (.ptr addr (some id)))
    (hTarget : s.memory.borrowTarget addr id = some target)
    (hPerm : s.permissions.get target = some .uniqueBorrow) :
    ∃ msg, Sem.run (semBorrow ptrId) s = .error (.ub msg) := by
  unfold semBorrow borrowOperand getPermission
  simp only [Sem.run, sr_bind, sr_lookup, hp, Except.bind, sr_get, hTarget, sr_pure, hPerm,
    sr_throwUB]
  exact ⟨_, rfl⟩

/-- A `BorrowMut` of a thin pointer whose provenance names a live allocation
    it lies inside (`Memory.borrowTarget`) in any permission but `owned` (a
    live shared borrow, or a live `BorrowMut`) is undefined behaviour, in
    every state. -/
theorem semBorrowMut_ub_of_not_owned (ptrId : ValueId) (s : MachineState)
    (addr : Addr) (id target : AllocId) (perm : Permission)
    (hp : s.lookupValue ptrId = some (.ptr addr (some id)))
    (hTarget : s.memory.borrowTarget addr id = some target)
    (hPerm : s.permissions.get target = some perm)
    (hNotOwned : perm ≠ .owned) :
    ∃ msg, Sem.run (semBorrowMut ptrId) s = .error (.ub msg) := by
  cases perm <;>
    first
    | exact absurd rfl hNotOwned
    | (unfold semBorrowMut borrowOperand getPermission
       simp only [Sem.run, sr_bind, sr_lookup, hp, Except.bind, sr_get, hTarget, sr_pure, hPerm,
         sr_throwUB]
       exact ⟨_, rfl⟩)

/-- A `Copy` step that succeeds leaves memory and the permission map exactly as
    they were: the Rust producers' spelling of a reference never touches the
    permission machine, nor any byte. -/
theorem stepInst_copy_preserves_memory_and_permissions (ty : Ty) (operand : ValueId)
    (s s' : MachineState) (r : InstrResult)
    (h : Sem.run (stepInst (.Copy ty operand)) s = .ok (r, s')) :
    s'.memory = s.memory ∧ s'.permissions = s.permissions := by
  unfold stepInst at h
  simp only [Sem.run, sr_bind, sr_lookup] at h
  cases hv : s.lookupValue operand with
  | none =>
    rw [hv] at h
    cases h
  | some v =>
    rw [hv] at h
    simp only [Except.bind, Sem.bindFresh, sr_bind, sr_get, MachineState.bindValue,
      sr_set, sr_pure] at h
    cases h
    exact ⟨rfl, rfl⟩

end BorrowMemoryProps
end TrustIr

#trustIrAxiomsExact TrustIr.BorrowMemoryProps.shared_reborrow_and_end_preserve_address == []
#trustIrAxiomsExact TrustIr.BorrowMemoryProps.dead_allocation_moves_no_permission == []
