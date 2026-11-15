-- Copyright 2026 Andrew Yates
-- Licensed under the Apache License, Version 2.0

import SemRBoolMemory

/-! Checked Bool accesses in the actual canonical semantic monad.

The pointer's SSA value carries the exact allocation identity recorded by
CellAt. Its live one-byte allocation supplies natural alignment and bounds.
These are statements about semLoad/semStore, not an alternate evaluator.
The existing wrappers do not read the permission map. This module makes no
claim about borrow permissions, frame lifetime, whole heaps or source rows.
The legacy le64 address domain remains unbounded Nat.
-/

namespace SemR.BoolMemory

open TrustIr

@[simp] private theorem run_get (state : MachineState) :
    Sem.run Sem.getState state = .ok (state, state) := rfl

@[simp] private theorem run_throw {α : Type} (state : MachineState) (error : SemError) :
    Sem.run (throw error : Sem α) state = .error error := rfl

@[simp] private theorem run_lookup (state : MachineState) (id : ValueId) :
    Sem.run (Sem.lookupValue id) state =
      match state.lookupValue id with
      | some value => .ok (value, state)
      | none => .error (.typeError s!"undefined SSA value: {repr id}") := by
  cases found : state.lookupValue id <;>
    simp [Sem.lookupValue, Sem.run_bind, Except.bind, found, Sem.run_pure,
      Sem.throwTypeError]

@[simp] private theorem run_bind_fresh (state : MachineState) (value : Value) :
    Sem.run (Sem.bindFresh value) state = .ok (state.bindValue value) := rfl

@[simp] private theorem run_modify (state : MachineState) (update : MachineState → MachineState) :
    Sem.run (Sem.modifyState update) state = .ok ((), update state) := rfl

@[simp] private theorem except_pure {α : Type} (value : α) :
    (pure value : Except SemError α) = .ok value := rfl

/-- The exact pointer operand for a related cell, including provenance. -/
def PointerAt (state : MachineState) (ptr : ValueId) (base : Addr) (cell : Cell) : Prop :=
  state.lookupValue ptr = some (.ptr base (some ⟨cell.id⟩))

theorem checked_access_cell (state : MachineState) (base : Addr) (cell : Cell)
    (related : CellAt state.memory base cell) (operation : String) :
    Sem.run (Sem.checkedAccess operation base ⟨cell.id⟩ 1 1) state =
      .ok (base, state) := by
  rcases related with ⟨_, found, _⟩
  simp [Sem.checkedAccess, Sem.checkTargetRange, Sem.run_bind, Sem.run_pure,
    Except.bind, found, allocation, Nat.mod_one]

private theorem read_bool (memory : Memory) (base : Addr) (cell : Cell) (value : Bool)
    (related : CellAt memory base cell) (defined : cell.value = .bool value) :
    memory.readBytes base 1 = some [if value then 1 else 0] := by
  have contents := related.2.2
  rw [defined] at contents
  have byte : memory.bytes base = some (if value then 1 else 0) := by
    simpa [image] using contents.symm
  simp [Memory.readBytes, Memory.readBytes.go, byte]

private theorem read_poison (memory : Memory) (base : Addr) (cell : Cell)
    (related : CellAt memory base cell) (poison : cell.value = .poison .bool) :
    memory.readBytes base 1 = none ∧ memory.readBytesMaybeUninit base 1 = [none] := by
  have contents := related.2.2
  rw [poison] at contents
  have byte : memory.bytes base = none := by simpa [image] using contents.symm
  simp [Memory.readBytes, Memory.readBytes.go, Memory.readBytesMaybeUninit,
    Memory.readBytesMaybeUninit.go, byte]

theorem semLoad_bool_cell (state : MachineState) (ptr : ValueId) (base : Addr)
    (cell : Cell) (value : Bool) (strict : Bool)
    (related : CellAt state.memory base cell) (operand : PointerAt state ptr base cell)
    (defined : cell.value = .bool value) :
    Sem.run (semLoad .Bool ptr strict) state = .ok (state.bindValue (.bool value)) := by
  have bytes := read_bool state.memory base cell value related defined
  have checked := checked_access_cell state base cell related "Load"
  unfold PointerAt at operand
  cases value <;>
    simp [semLoad, semLoadUsing, semLoadValueUsing, Sem.rejectPartial, Sem.run_bind,
      operand, Sem.expectPointer, Ty.byteSizeFor, Ty.byteSize,
      Sem.accessAlign, Sem.declaredOrNaturalAlign, Ty.byteAlignFor, Ty.byteAlign,
      TrustIr.isPow2, TrustIr.isPow2Fuel, checked, bytes, decodeMemoryAt, decodeValueAt,
      decodeImageAt, TrustIr.Ty.isFloat, decodeValue, Memory.resolveDecoded, Except.bind]

theorem semLoad_poison_cell (state : MachineState) (ptr : ValueId) (base : Addr)
    (cell : Cell) (related : CellAt state.memory base cell)
    (operand : PointerAt state ptr base cell) (poison : cell.value = .poison .bool) :
    Sem.run (semLoad .Bool ptr) state = .ok (state.bindValue (.partial [none])) := by
  have bytes := read_poison state.memory base cell related poison
  have checked := checked_access_cell state base cell related "Load"
  unfold PointerAt at operand
  simp [semLoad, semLoadUsing, semLoadValueUsing, Sem.rejectPartial, Sem.run_bind,
    operand, Sem.expectPointer, Ty.byteSizeFor, Ty.byteSize,
    Sem.accessAlign, Sem.declaredOrNaturalAlign, Ty.byteAlignFor, Ty.byteAlign,
    TrustIr.isPow2, TrustIr.isPow2Fuel, checked, bytes.1, bytes.2, isPartialLoadTyFor,
    isPartialLoadTy, Except.bind]

theorem semLoad_strict_poison_refuses (state : MachineState) (ptr : ValueId) (base : Addr)
    (cell : Cell) (related : CellAt state.memory base cell)
    (operand : PointerAt state ptr base cell) (poison : cell.value = .poison .bool) :
    Sem.run (semLoad .Bool ptr true) state =
      .error (.ub "Load: reading uninitialized memory") := by
  have bytes := read_poison state.memory base cell related poison
  have checked := checked_access_cell state base cell related "Load"
  unfold PointerAt at operand
  simp [semLoad, semLoadUsing, semLoadValueUsing, Sem.rejectPartial, Sem.run_bind,
    operand, Sem.expectPointer, Ty.byteSizeFor, Ty.byteSize,
    Sem.accessAlign, Sem.declaredOrNaturalAlign, Ty.byteAlignFor, Ty.byteAlign,
    TrustIr.isPow2, TrustIr.isPow2Fuel, checked, bytes.1, Sem.throwUB, Except.bind]

theorem semStore_bool_cell (state : MachineState) (ptr source : ValueId) (base : Addr)
    (cell : Cell) (value : Bool) (strict : Bool)
    (related : CellAt state.memory base cell) (operand : PointerAt state ptr base cell)
    (stored : state.lookupValue source = some (.bool value)) :
    Sem.run (semStore .Bool ptr source strict) state =
      .ok ((), { state with memory := state.memory.writeBytes base [if value then 1 else 0] }) := by
  have checked := checked_access_cell state base cell related "Store"
  unfold PointerAt at operand
  simp [semStore, semStoreUsing, semStoreValueUsing, Sem.rejectPartial, Sem.fromMemoryExcept,
    scalarMemoryLayout, checkedMemoryAlign, word64Max, word64Limit, word64Bits, Except.pure, checkPointerImageWords, Sem.run_pure, Sem.run_bind, Except.bind, operand, stored, Sem.expectPointer,
    Ty.byteSizeFor, Ty.byteSize, Sem.accessAlign, Sem.declaredOrNaturalAlign,
    Ty.byteAlignFor, Ty.byteAlign, TrustIr.isPow2, TrustIr.isPow2Fuel, checked, Value.isPoison,
    fatPtrStoreValueValidFor, fatPtrStoreValueValid, encodeMemoryAt, encodeValueAt,
    encodeValue]

theorem semStore_poison_cell (state : MachineState) (ptr source : ValueId) (base : Addr)
    (cell : Cell) (related : CellAt state.memory base cell)
    (operand : PointerAt state ptr base cell)
    (stored : state.lookupValue source = some (.partial [none])) :
    Sem.run (semStore .Bool ptr source) state =
      .ok ((), { state with memory := state.memory.writeBytesMaybeUninit base [none] }) := by
  have checked := checked_access_cell state base cell related "Store"
  unfold PointerAt at operand
  simp [semStore, semStoreUsing, semStoreValueUsing, Sem.rejectPartial, Sem.fromMemoryExcept,
    scalarMemoryLayout, checkedMemoryAlign, word64Max, word64Limit, word64Bits, Except.pure, checkPointerImageWords, Sem.run_pure, Sem.run_bind, Except.bind, operand, stored, Sem.expectPointer,
    Ty.byteSizeFor, Ty.byteSize, Sem.accessAlign, Sem.declaredOrNaturalAlign,
    Ty.byteAlignFor, Ty.byteAlign, TrustIr.isPow2, TrustIr.isPow2Fuel, checked, Value.isPoison]

theorem semStore_strict_poison_refuses (state : MachineState) (ptr source : ValueId) (base : Addr)
    (cell : Cell) (related : CellAt state.memory base cell)
    (operand : PointerAt state ptr base cell)
    (stored : state.lookupValue source = some (.partial [none])) :
    Sem.run (semStore .Bool ptr source true) state =
      .error (.ub "Store: strict (atomic/volatile) store of a partially-initialized value") := by
  have checked := checked_access_cell state base cell related "Store"
  unfold PointerAt at operand
  simp [semStore, semStoreUsing, semStoreValueUsing, Sem.rejectPartial, Sem.fromMemoryExcept,
    scalarMemoryLayout, checkedMemoryAlign, word64Max, word64Limit, word64Bits, Except.pure, checkPointerImageWords, Sem.run_pure, Sem.run_bind, Except.bind, operand, stored, Sem.expectPointer,
    Ty.byteSizeFor, Ty.byteSize, Sem.accessAlign, Sem.declaredOrNaturalAlign,
    Ty.byteAlignFor, Ty.byteAlign, TrustIr.isPow2, TrustIr.isPow2Fuel, checked, Value.isPoison,
    Sem.throwUB]

/-- This postcondition composes the actual monadic Store result with CellAt;
    it is not a claim only about an independently chosen raw write. -/
theorem semStore_bool_preserves_cell (state : MachineState) (ptr source : ValueId)
    (base : Addr) (cell : Cell) (value : Bool)
    (related : CellAt state.memory base cell) (operand : PointerAt state ptr base cell)
    (stored : state.lookupValue source = some (.bool value)) :
    ∃ result, Sem.run (semStore .Bool ptr source) state = .ok ((), result) ∧
      CellAt result.memory base { cell with value := .bool value } ∧
      PointerAt result ptr base cell ∧ result.locals = state.locals ∧
      result.permissions = state.permissions := by
  refine ⟨_, semStore_bool_cell state ptr source base cell value false related operand stored,
    store_bool_cell state.memory base cell value related, operand, rfl, rfl⟩

theorem semStore_poison_preserves_cell (state : MachineState) (ptr source : ValueId)
    (base : Addr) (cell : Cell) (related : CellAt state.memory base cell)
    (operand : PointerAt state ptr base cell)
    (stored : state.lookupValue source = some (.partial [none])) :
    ∃ result, Sem.run (semStore .Bool ptr source) state = .ok ((), result) ∧
      CellAt result.memory base { cell with value := .poison .bool } ∧
      PointerAt result ptr base cell ∧ result.locals = state.locals ∧
      result.permissions = state.permissions := by
  refine ⟨_, semStore_poison_cell state ptr source base cell related operand stored,
    store_poison_cell state.memory base cell related, operand, rfl, rfl⟩

/-- The same exact-typed, provenance-carrying pointer reloads the stored value
    through semLoad, including its SSA result binding. -/
theorem semStore_bool_then_load (state : MachineState) (ptr source : ValueId)
    (base : Addr) (cell : Cell) (value : Bool)
    (related : CellAt state.memory base cell) (operand : PointerAt state ptr base cell)
    (stored : state.lookupValue source = some (.bool value)) :
    Sem.run (do semStore .Bool ptr source; semLoad .Bool ptr) state =
      .ok (({ state with memory := state.memory.writeBytes base [if value then 1 else 0] }).bindValue
        (.bool value)) := by
  rw [Sem.run_bind, semStore_bool_cell state ptr source base cell value false related operand stored]
  simp only [Except.bind]
  exact semLoad_bool_cell _ ptr base { cell with value := .bool value } value false
    (store_bool_cell state.memory base cell value related) operand rfl

theorem semStore_poison_then_load (state : MachineState) (ptr source : ValueId)
    (base : Addr) (cell : Cell) (related : CellAt state.memory base cell)
    (operand : PointerAt state ptr base cell)
    (stored : state.lookupValue source = some (.partial [none])) :
    Sem.run (do semStore .Bool ptr source; semLoad .Bool ptr) state =
      .ok (({ state with memory := state.memory.writeBytesMaybeUninit base [none] }).bindValue
        (.partial [none])) := by
  rw [Sem.run_bind, semStore_poison_cell state ptr source base cell related operand stored]
  simp only [Except.bind]
  exact semLoad_poison_cell _ ptr base { cell with value := .poison .bool }
    (store_poison_cell state.memory base cell related) operand rfl

/-- Defined bytes at the numerical address do not license a pointer whose
    provenance names another allocation, even if both allocations are live. -/
private def wrongAllocation : MachineState :=
  { MachineState.empty with
    locals := fun _ => some (.ptr 1024 (some ⟨1⟩))
    memory := { (Memory.empty.writeBytes 1024 [1]).writeBytes 2048 [1] with
      allocations := [allocation 0 1024, allocation 1 2048] } }

theorem semLoad_wrong_allocation_refuses :
    Sem.run (semLoad .Bool ⟨0⟩) wrongAllocation =
      .error (.ub "Load: access is out of bounds") := rfl

theorem semStore_wrong_allocation_refuses :
    Sem.run (semStore .Bool ⟨0⟩ ⟨1⟩) wrongAllocation =
      .error (.ub "Store: access is out of bounds") := rfl

/-- Missing provenance cannot be recovered by this access from numerical
    address membership. Pointer recovery is a different explicit operation. -/
theorem semLoad_missing_provenance_refuses :
    Sem.run (semLoad .Bool ⟨0⟩)
      { wrongAllocation with locals := fun _ => some (.ptr 1024 none) } =
      .error (.ub "Load: pointer value 1024 has no allocation provenance") := rfl

theorem semLoad_dead_allocation_refuses :
    Sem.run (semLoad .Bool ⟨0⟩)
      { wrongAllocation with memory := { wrongAllocation.memory with
          allocations := [{ allocation 1 1024 with alive := false }] } } =
      .error (.ub "Load: use after dealloc") := rfl

theorem semLoad_unknown_allocation_refuses :
    Sem.run (semLoad .Bool ⟨0⟩)
      { wrongAllocation with memory := Memory.empty } =
      .error (.ub "Load: unknown allocation") := rfl

theorem semLoad_declared_alignment_refuses :
    Sem.run (semLoad .Bool ⟨0⟩ false (some 2))
      { wrongAllocation with
        locals := fun _ => some (.ptr 1025 (some ⟨1⟩))
        memory := { wrongAllocation.memory with allocations := [allocation 1 1025] } } =
      .error (.ub "Load: pointer address 1025 is not aligned to 2") := rfl

private def poisonState : MachineState :=
  { MachineState.empty with
    locals := fun _ => some (.ptr 1024 (some ⟨0⟩))
    memory := { Memory.empty with allocations := [allocation 0 1024] } }

theorem semLoad_plain_poison_control :
    Sem.run (semLoad .Bool ⟨0⟩) poisonState =
      .ok (poisonState.bindValue (.partial [none])) := rfl

theorem semLoad_strict_poison_control :
    Sem.run (semLoad .Bool ⟨0⟩ true) poisonState =
      .error (.ub "Load: reading uninitialized memory") := rfl

/-- False claims retained for independent ReferenceKernel TypeMismatch tests. -/
def WrongStrictPoisonAccess : Prop :=
  Sem.run (semLoad .Bool ⟨0⟩ true) poisonState =
    .ok (poisonState.bindValue (.partial [none]))

def WrongAllocationAccess : Prop :=
  Sem.run (semLoad .Bool ⟨0⟩) wrongAllocation =
    .ok (wrongAllocation.bindValue (.bool true))

end SemR.BoolMemory
