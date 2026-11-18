-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.AllocationLayout

/-! Observations of the existing contextual stack allocator. The successful
result is the actual Memory.alloc transition and canonical SSA publication. No
layout service, source allocation, runtime identity, caller rely, or physical
stack placement is constructed by these theorems. In particular, a nominal
zero-byte layout is not replaced by a scalar or an absent allocation.
-/

namespace TrustIr.ContextualAllocation

/-- Name the result of the existing allocation branch, not another allocator.
Its use as an execution result requires the checked operational equation below. -/
def result (before : MachineState) (size alignment : Nat) : ValueId × MachineState :=
  let id := AllocId.mk before.memory.nextAllocId
  let allocated := before.memory.alloc size alignment 0 .rustStack
  ({ before with
      memory := allocated.2
      permissions := before.permissions.set id .owned }).bindValue
    (.ptr allocated.1 (some id))

@[simp] private theorem run_get (state : MachineState) :
    Sem.run Sem.getState state = .ok (state, state) := rfl

@[simp] private theorem run_set (state replacement : MachineState) :
    Sem.run (Sem.setState replacement) state = .ok ((), replacement) := rfl

@[simp] private theorem run_fresh (state : MachineState) (value : Value) :
    Sem.run (Sem.bindFresh value) state = .ok (state.bindValue value) := rfl

@[simp] private theorem run_throw {α : Type} (state : MachineState) (error : SemError) :
    Sem.run (throw error : Sem α) state = .error error := rfl

/-- A contextual layout and its original arithmetic/alignment checks determine
the actual no-count Alloca result. The original capacity/identity/target failure
is retained verbatim, including for a zero-byte nominal layout. -/
theorem run_none_checked (query : MemoryLayoutQuery) (reader : IntegerOperandReader)
    (ty : Ty) (declared : Option Nat) (model : ByteModel) (before : MachineState)
    (layout : MemoryTypeLayout) (size alignment : Nat)
    (geometry : query ty = .ok layout)
    (sizeChecked : checkedWord64Mul "Alloca" layout.size 1 = .ok size)
    (alignmentChecked : checkedMemoryAlign "Alloca" layout.alignment declared = .ok alignment) :
    Sem.run (semAllocaUsing query reader ty none declared model) before =
      match checkWordAllocation model before.memory size alignment 0 with
      | .error error => .error error
      | .ok _ => .ok (result before size alignment) := by
  cases capacity : checkWordAllocation model before.memory size alignment 0 <;>
    simp [semAllocaUsing, semAllocateUsing, geometry, sizeChecked, alignmentChecked,
      capacity, Sem.fromMemoryExcept, Sem.run_bind, Sem.run_pure, Except.bind, result]

/-- Invert a real successful contextual allocation. A caller cannot replace
the source layout or any original check by an asserted size/alignment label. -/
theorem success_none (query : MemoryLayoutQuery) (reader : IntegerOperandReader)
    (ty : Ty) (declared : Option Nat) (model : ByteModel)
    (before after : MachineState) (pointer : ValueId)
    (executed : Sem.run (semAllocaUsing query reader ty none declared model) before =
      .ok (pointer, after)) :
    ∃ layout size alignment,
      query ty = .ok layout ∧
      checkedWord64Mul "Alloca" layout.size 1 = .ok size ∧
      checkedMemoryAlign "Alloca" layout.alignment declared = .ok alignment ∧
      checkWordAllocation model before.memory size alignment 0 = .ok () ∧
      (pointer, after) = result before size alignment := by
  cases geometry : query ty with
  | error error =>
    simp [semAllocaUsing, semAllocateUsing, geometry, Sem.fromMemoryExcept,
      Sem.run_bind, Except.bind] at executed
  | ok layout =>
    cases sizeChecked : checkedWord64Mul "Alloca" layout.size 1 with
    | error error =>
      simp [semAllocaUsing, semAllocateUsing, geometry, sizeChecked,
        Sem.fromMemoryExcept, Sem.run_bind, Except.bind] at executed
    | ok size =>
      cases alignmentChecked : checkedMemoryAlign "Alloca" layout.alignment declared with
      | error error =>
        simp [semAllocaUsing, semAllocateUsing, geometry, sizeChecked, alignmentChecked,
          Sem.fromMemoryExcept, Sem.run_bind, Except.bind] at executed
      | ok alignment =>
        rw [run_none_checked query reader ty declared model before layout size alignment
          geometry sizeChecked alignmentChecked] at executed
        cases capacity : checkWordAllocation model before.memory size alignment 0 with
        | error error => simp [capacity] at executed
        | ok unit =>
          cases unit
          simp only [capacity, Except.ok.injEq] at executed
          exact ⟨layout, size, alignment, rfl, sizeChecked, alignmentChecked,
            capacity, executed.symm⟩

theorem result_memory (before : MachineState) (size alignment : Nat) :
    (result before size alignment).2.memory =
      (before.memory.alloc size alignment 0 .rustStack).2 := rfl

/-- The published pointer keeps the actual allocation identity and base. -/
theorem result_pointer (before : MachineState) (size alignment : Nat) :
    (result before size alignment).2.lookupValue (result before size alignment).1 =
      some (.ptr (alignUp before.memory.nextAddr alignment)
        (some ⟨before.memory.nextAllocId⟩)) := by
  simp [result, MachineState.bindValue, MachineState.lookupValue, ValueMap.get,
    ValueMap.set, alloc_addr_is_aligned_nextAddr]

theorem result_record (before : MachineState) (size alignment : Nat) :
    (result before size alignment).2.memory.lookup ⟨before.memory.nextAllocId⟩ =
      some (before.memory.allocRecord size alignment 0 .rustStack) := by
  simp [result, MachineState.bindValue, Memory.alloc, Memory.lookup, Memory.allocRecord,
    List.find?]

theorem result_owned (before : MachineState) (size alignment : Nat) :
    (result before size alignment).2.permissions.get ⟨before.memory.nextAllocId⟩ =
      some .owned := by
  simp [result, MachineState.bindValue, PermissionMap.get, PermissionMap.set]

/-- Existing byte images are not changed by a slack-free stack allocation.
This does not assert that unused byte addresses were uninitialized. -/
theorem result_bytes (before : MachineState) (size alignment : Nat) :
    (result before size alignment).2.memory.bytes = before.memory.bytes := rfl

theorem result_other_permission (before : MachineState) (size alignment : Nat) (id : AllocId)
    (different : id ≠ ⟨before.memory.nextAllocId⟩) :
    (result before size alignment).2.permissions.get id = before.permissions.get id := by
  simp [result, MachineState.bindValue, PermissionMap.get, PermissionMap.set, different]

theorem result_other_local (before : MachineState) (size alignment : Nat) (id : ValueId)
    (different : id ≠ ⟨before.nextValueId⟩) :
    (result before size alignment).2.lookupValue id = before.lookupValue id := by
  simp [result, MachineState.bindValue, MachineState.lookupValue, ValueMap.get,
    ValueMap.set, different]

/-- The allocator's existing population invariant supplies runtime freshness;
the static source-allocation census supplies no such premise. -/
theorem result_layout (before : MachineState) (size alignment : Nat)
    (wellFormed : before.memory.layoutWF) :
    (result before size alignment).2.memory.layoutWF :=
  alloc_preserves_layoutWF before.memory size alignment 0 .rustStack wellFormed

theorem result_other_world (before : MachineState) (size alignment : Nat) :
    (result before size alignment).2.refCounts = before.refCounts ∧
    (result before size alignment).2.globals = before.globals ∧
    (result before size alignment).2.exceptions = before.exceptions ∧
    (result before size alignment).2.inHand = before.inHand ∧
    (result before size alignment).2.floatZeroChoices = before.floatZeroChoices ∧
    (result before size alignment).2.floatZeroChoiceCursor = before.floatZeroChoiceCursor ∧
    (result before size alignment).2.openFrameLineages = before.openFrameLineages ∧
    (result before size alignment).2.nextFrameLineage = before.nextFrameLineage := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end TrustIr.ContextualAllocation
