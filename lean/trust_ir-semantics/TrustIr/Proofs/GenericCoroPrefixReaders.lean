-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroPrefixMetadata

namespace TrustIr.GenericCoro.Prefix

/-- Allocation queries exactly its declared count. Changing a reader at other
    SSA names cannot affect lookup order, layout errors or placement effects. -/
theorem semAllocateUsing_reader_congr (layout : MemoryLayoutQuery)
    (source target : IntegerOperandReader) (ty : Ty) (count : Option ValueId)
    (align : Option Nat) (origin : AllocationOrigin) (refCounted : Bool)
    (slack : Nat) (model : ByteModel)
    (same : ∀ id, count = some id → ∀ value, source id value = target id value) :
    semAllocateUsing layout source ty count align origin refCounted slack model =
      semAllocateUsing layout target ty count align origin refCounted slack model := by
  cases count with
  | none => rfl
  | some id =>
    unfold semAllocateUsing
    simp only [bind_assoc, pure_bind]
    congr 1
    funext value
    simp only [pure_bind, same id rfl value]

theorem forIn_except_congr {α β : Type} (items : List α) (initial : β)
    (source target : α → β → Except SemError (ForInStep β))
    (same : ∀ item ∈ items, ∀ state, source item state = target item state) :
    forIn items initial source = forIn items initial target := by
  induction items generalizing initial with
  | nil => rfl
  | cons item rest ih =>
    rw [List.forIn_cons, List.forIn_cons, same item ((trustIrListMemConsSelf _ _)) initial]
    congr 1
    funext step
    cases step with
    | done value => rfl
    | yield value => exact ih value (fun item member => same item (List.mem_cons_of_mem _ member))

theorem gepOffsetUsing_reader_congr {key : Type} (layout : MemoryLayoutQuery)
    (source target : key → Value → Except SemError Int) (ty : Ty)
    (inputs : List (key × Value))
    (same : ∀ input ∈ inputs, source input.1 input.2 = target input.1 input.2) :
    gepOffsetUsing layout source ty inputs = gepOffsetUsing layout target ty inputs := by
  unfold gepOffsetUsing
  congr 1
  funext declaration
  apply forIn_except_congr
  intro input member state
  rw [same input member]

theorem lookupInput_key (id : ValueId) (state : MachineState)
    (result : (ValueId × Value) × MachineState)
    (run : Sem.run (do pure (id, ← Sem.lookupValue id)) state = .ok result) :
    result.1.1 = id := by
  simp only [Sem.run_bind] at run
  cases found : Sem.run (Sem.lookupValue id) state with
  | error error => simp only [found, Except.bind] at run <;> cases run
  | ok pair =>
    simp only [found, Except.bind, Sem.run_pure] at run
    exact congrArg (fun pair => pair.1.1) (Except.ok.inj run.symm)

theorem lookupInputs_keys (indices : List ValueId) (state : MachineState)
    (result : List (ValueId × Value) × MachineState)
    (run : Sem.run (indices.mapM (fun id => do pure (id, ← Sem.lookupValue id))) state = .ok result) :
    result.1.map Prod.fst = indices := by
  induction indices generalizing state result with
  | nil =>
    have equal := Except.ok.inj run
    exact congrArg (fun pair => pair.1.map Prod.fst) equal.symm
  | cons id rest ih =>
    rw [List.mapM_cons, Sem.run_bind] at run
    cases headRun : Sem.run (do pure (id, ← Sem.lookupValue id)) state with
    | error error => simp only [headRun, Except.bind] at run <;> cases run
    | ok head =>
      rw [headRun] at run
      simp only [Except.bind] at run
      rw [Sem.run_bind] at run
      cases tailRun : Sem.run (rest.mapM (fun id => do pure (id, ← Sem.lookupValue id))) head.2 with
      | error error => simp only [tailRun, Except.bind] at run <;> cases run
      | ok tail =>
        simp only [tailRun, Except.bind, Sem.run_pure] at run
        have equal := Except.ok.inj run
        rw [← equal]
        simp only [List.map_cons, lookupInput_key id state head headRun, ih head.2 tail tailRun]

theorem semGEPUsing_reader_congr (layout : MemoryLayoutQuery)
    (source target : IntegerOperandReader) (ty : Ty) (base : ValueId)
    (indices : List ValueId) (model : ByteModel)
    (same : ∀ id ∈ indices, ∀ value, source id value = target id value) :
    semGEPUsing layout source ty base indices model =
      semGEPUsing layout target ty base indices model := by
  unfold semGEPUsing
  funext state
  change Sem.run _ state = Sem.run _ state
  simp only [Sem.run_bind]
  cases baseRun : Sem.run (Sem.lookupValue base) state with
  | error error => rfl
  | ok pointer =>
    simp only [Except.bind, Sem.run_bind]
    cases inputsRun : Sem.run (indices.mapM (fun id => do pure (id, ← Sem.lookupValue id))) pointer.2 with
    | error error => rfl
    | ok inputs =>
      have keys := lookupInputs_keys indices pointer.2 inputs inputsRun
      have plan := gepOffsetUsing_reader_congr layout source target ty inputs.1 (fun input member =>
        same input.1 (by
          rw [← keys]
          exact List.mem_map.mpr ⟨input, member, rfl⟩) input.2)
      simp only [Except.bind, semGEPValuesUsing, plan]

end TrustIr.GenericCoro.Prefix
