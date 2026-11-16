-- Copyright 2026 Andrew Yates
-- Licensed under the Apache License, Version 2.0

import SemRBoolAccess

/-! The actual canonical Bool Alloca computation, including its SSA pointer
and owned-permission update. Raw byte-allocation lemmas alone do not establish
that an executed Alloca produces those observations.

Fresh memory remains an explicit premise for poison initialization. Existing
SSA bindings are preserved only at a different result identifier. These facts
do not establish a global heap, SSA allocator invariant, borrow validity,
frame lifetime, finite-u64 addresses or a source/whole-execution refinement.
-/

namespace SemR.BoolMemory

open TrustIr

/-- The observable postcondition of the existing canonical instruction. -/
def boolAllocaResult (state : MachineState) : ValueId × MachineState :=
  let allocated := state.memory.alloc 1 1 0 .rustStack
  ({ state with
      memory := allocated.snd
      permissions := state.permissions.set ⟨state.memory.nextAllocId⟩ .owned }).bindValue
    (.ptr allocated.fst (some ⟨state.memory.nextAllocId⟩))

@[simp] private theorem run_set (before after : MachineState) :
    Sem.run (Sem.setState after) before = .ok ((), after) := rfl

/-- Exact behavior for every state, including exhausted address/identity counters. -/
theorem semAlloca_bool_checked_result (state : MachineState) :
    Sem.run (semAlloca .Bool none) state =
      match checkWordAllocation .le64 state.memory 1 1 0 with
      | .ok _ => .ok (boolAllocaResult state)
      | .error error => .error error := by
  cases checked : checkWordAllocation .le64 state.memory 1 1 0 <;>
    simp [semAlloca, semAllocaUsing, semAllocateUsing, scalarMemoryLayout,
      Ty.byteSizeFor, Ty.byteSize, Ty.byteAlignFor, Ty.byteAlign,
      checkedWord64Mul, checkedMemoryAlign, TrustIr.isPow2, TrustIr.isPow2Fuel,
      Except.bind, word64Max, word64Limit, word64Bits,
      Sem.fromMemoryExcept, Sem.run_bind, Sem.run_pure, checked, boolAllocaResult]

/-- Successful allocation requires the actual canonical capacity check. -/
def BoolAllocaCapacity (memory : Memory) : Prop :=
  checkWordAllocation .le64 memory 1 1 0 = .ok ()

theorem semAlloca_bool_result (state : MachineState)
    (capacity : BoolAllocaCapacity state.memory) :
    Sem.run (semAlloca .Bool none) state = .ok (boolAllocaResult state) := by
  rw [semAlloca_bool_checked_result, capacity]

private theorem empty_bool_capacity : BoolAllocaCapacity Memory.empty := rfl

private def exhaustedAddressState : MachineState :=
  { MachineState.empty with memory := { Memory.empty with nextAddr := word64Max } }

private def exhaustedIdentityState : MachineState :=
  { MachineState.empty with memory := { Memory.empty with nextAllocId := word64Max } }

theorem semAlloca_bool_address_exhaustion :
    Sem.run (semAlloca .Bool none) exhaustedAddressState =
      .error (.outOfMemory "allocation next-address increment exceeds u64") := rfl

theorem semAlloca_bool_identifier_exhaustion :
    Sem.run (semAlloca .Bool none) exhaustedIdentityState =
      .error (.ub "allocation identifier increment overflows u64") := rfl

theorem semAlloca_bool_exhaustion_is_not_success :
    Sem.run (semAlloca .Bool none) exhaustedAddressState ≠
      .ok (boolAllocaResult exhaustedAddressState) := by
  rw [semAlloca_bool_address_exhaustion]
  intro impossible
  cases impossible

theorem boolAlloca_result_id (state : MachineState) :
    (boolAllocaResult state).fst = ⟨state.nextValueId⟩ := rfl

theorem boolAlloca_result_memory (state : MachineState) :
    (boolAllocaResult state).snd.memory = (state.memory.alloc 1 1 0 .rustStack).snd := rfl

theorem boolAlloca_next_value (state : MachineState) :
    (boolAllocaResult state).snd.nextValueId = state.nextValueId + 1 := rfl

theorem boolAlloca_fresh (state : MachineState) (fresh : Fresh state.memory) :
    Fresh (boolAllocaResult state).snd.memory :=
  alloca_bool_fresh state.memory fresh

theorem boolAlloca_new_cell (state : MachineState) (fresh : Fresh state.memory) :
    CellAt (boolAllocaResult state).snd.memory state.memory.nextAddr
      { id := state.memory.nextAllocId, ty := .bool, value := .poison .bool } :=
  alloca_bool_cell state.memory fresh

theorem boolAlloca_new_pointer (state : MachineState) :
    PointerAt (boolAllocaResult state).snd (boolAllocaResult state).fst
      state.memory.nextAddr
      { id := state.memory.nextAllocId, ty := .bool, value := .poison .bool } := by
  simp [PointerAt, boolAllocaResult, MachineState.bindValue, MachineState.lookupValue,
    ValueMap.get, ValueMap.set, alloca_bool_base]

theorem boolAlloca_owned_permission (state : MachineState) :
    (boolAllocaResult state).snd.permissions.get ⟨state.memory.nextAllocId⟩ =
      some .owned := by
  simp [boolAllocaResult, MachineState.bindValue, PermissionMap.get, PermissionMap.set]

theorem boolAlloca_other_permission (state : MachineState) (id : AllocId)
    (different : id ≠ ⟨state.memory.nextAllocId⟩) :
    (boolAllocaResult state).snd.permissions.get id = state.permissions.get id := by
  simp [boolAllocaResult, MachineState.bindValue, PermissionMap.get, PermissionMap.set,
    different]

theorem boolAlloca_other_local (state : MachineState) (id : ValueId)
    (different : id ≠ ⟨state.nextValueId⟩) :
    (boolAllocaResult state).snd.lookupValue id = state.lookupValue id := by
  simp [boolAllocaResult, MachineState.bindValue, MachineState.lookupValue,
    ValueMap.get, ValueMap.set, different]

theorem boolAlloca_preserves_cell (state : MachineState) (base : Addr) (cell : Cell)
    (different : state.memory.nextAllocId ≠ cell.id)
    (related : CellAt state.memory base cell) :
    CellAt (boolAllocaResult state).snd.memory base cell :=
  alloca_bool_preserves_cell state.memory base cell different related

theorem boolAlloca_other_state (state : MachineState) :
    (boolAllocaResult state).snd.refCounts = state.refCounts ∧
    (boolAllocaResult state).snd.globals = state.globals ∧
    (boolAllocaResult state).snd.exceptions = state.exceptions ∧
    (boolAllocaResult state).snd.inHand = state.inHand := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- This composes the actual allocation and plain load monadic computations. -/
theorem semAlloca_bool_then_load_poison (state : MachineState)
    (fresh : Fresh state.memory) (capacity : BoolAllocaCapacity state.memory) :
    Sem.run (do let ptr ← semAlloca .Bool none; semLoad .Bool ptr) state =
      .ok ((boolAllocaResult state).snd.bindValue (.partial [none])) := by
  rw [Sem.run_bind, semAlloca_bool_result state capacity]
  exact semLoad_poison_cell (boolAllocaResult state).snd (boolAllocaResult state).fst
    state.memory.nextAddr
    { id := state.memory.nextAllocId, ty := .bool, value := .poison .bool }
    (boolAlloca_new_cell state fresh) (boolAlloca_new_pointer state) rfl

theorem semAlloca_bool_then_strict_load_refuses (state : MachineState)
    (fresh : Fresh state.memory) (capacity : BoolAllocaCapacity state.memory) :
    Sem.run (do let ptr ← semAlloca .Bool none; semLoad .Bool ptr true) state =
      .error (.ub "Load: reading uninitialized memory") := by
  rw [Sem.run_bind, semAlloca_bool_result state capacity]
  exact semLoad_strict_poison_refuses (boolAllocaResult state).snd
    (boolAllocaResult state).fst state.memory.nextAddr
    { id := state.memory.nextAllocId, ty := .bool, value := .poison .bool }
    (boolAlloca_new_cell state fresh) (boolAlloca_new_pointer state) rfl

/-- The closed initial computation also brings its Fresh proof into the
    dependency cone replayed by an independent checker. -/
theorem semAlloca_bool_empty_plain_poison :
    Sem.run (do let ptr ← semAlloca .Bool none; semLoad .Bool ptr) MachineState.empty =
      .ok ((boolAllocaResult MachineState.empty).snd.bindValue (.partial [none])) :=
  semAlloca_bool_then_load_poison MachineState.empty fresh_empty empty_bool_capacity

theorem semAlloca_bool_zero_alignment_refuses (state : MachineState) :
    Sem.run (semAlloca .Bool none (some 0)) state =
      .error (.typeError "Alloca: alignment must be a nonzero u64 power of two") := by
  rfl

/-- A malformed SSA allocator overwrites its result slot; no freshness theorem
    can preserve that slot without an additional allocator invariant. -/
def occupiedResultState : MachineState :=
  { MachineState.empty with locals := ValueMap.empty.set ⟨0⟩ (.bool true) }

theorem boolAlloca_reused_ssa_control :
    (boolAllocaResult occupiedResultState).snd.lookupValue ⟨0⟩ =
      some (.ptr Memory.empty.nextAddr (some ⟨Memory.empty.nextAllocId⟩)) := by
  rfl

theorem semAlloca_bool_exhausted_identity_refuses :
    Sem.run (semAlloca .Bool none) exhaustedIdentityState =
      .error (.ub "allocation identifier increment overflows u64") := rfl

theorem semAlloca_bool_exhausted_address_refuses :
    Sem.run (semAlloca .Bool none) exhaustedAddressState =
      .error (.outOfMemory "allocation next-address increment exceeds u64") := rfl

/-- False goals for an independent kernel's TypeMismatch controls. -/
def WrongAllocaPlainLoad : Prop :=
  Sem.run (do let ptr ← semAlloca .Bool none; semLoad .Bool ptr) MachineState.empty =
    .ok ((boolAllocaResult MachineState.empty).snd.bindValue (.bool false))

def WrongAllocaPreservesResultSlot : Prop :=
  (boolAllocaResult occupiedResultState).snd.lookupValue ⟨0⟩ = some (.bool true)

end SemR.BoolMemory
