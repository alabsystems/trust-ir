-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.StoreInstructionExecution

namespace TrustIr

/-- Successful held loads observe the whole state, without private SSA,
    allocation, permission, exception or choice-stream updates. -/
def LoadReadOnly {α : Type} (action : Sem α) : Prop :=
  ∀ before after value, Sem.run action before = .ok (value,after) → after = before

private theorem load_ro_pure {α : Type} (value : α) : LoadReadOnly (pure value : Sem α) := by
  intro before after result run
  cases run
  rfl

private theorem load_ro_throw {α : Type} (error : SemError) : LoadReadOnly (throw error : Sem α) := by
  intro before after result run
  cases run

private theorem load_ro_except {α : Type} (result : Except SemError α) :
    LoadReadOnly (Sem.fromMemoryExcept result) := by
  cases result with
  | ok value => exact load_ro_pure value
  | error error => exact load_ro_throw error

private theorem load_ro_get : LoadReadOnly Sem.getState := by
  intro before after result run
  cases run
  rfl

private theorem load_ro_bind {α β : Type} (first : Sem α) (next : α → Sem β)
    (head : LoadReadOnly first) (tail : ∀ value, LoadReadOnly (next value)) :
    LoadReadOnly (first >>= next) := by
  trustIrCompilerProof {
    intro before after result run
    rw [Sem.run_bind] at run
    cases accepted : Sem.run first before with
    | error error => simp only [accepted,Except.bind] at run
    | ok pair =>
      have rest : Sem.run (next pair.1) pair.2 = .ok (result,after) := by
        simpa only [accepted,Except.bind] using run
      exact (tail pair.1 pair.2 after result rest).trans (head before pair.2 pair.1 accepted)
  } {
    intro before after result run
    rw [Sem.run_bind] at run
    cases accepted : Sem.run first before with
    | error error => simp only [accepted,Except.bind] at run; cases run
    | ok pair =>
      have rest : Sem.run (next pair.1) pair.2 = .ok (result,after) := by
        simpa only [accepted,Except.bind] using run
      exact (tail pair.1 pair.2 after result rest).trans (head before pair.2 pair.1 accepted)
  }

private theorem load_ro_reject (pointer : Value) : LoadReadOnly (Sem.rejectPartial pointer "Load") := by
  intro before after value run
  exact rejectPartial_ok_state "Load" pointer before after value run

private theorem load_ro_pointer (pointer : Value) : LoadReadOnly (Sem.expectPointer "Load" pointer) := by
  intro before after value run
  exact (expectPointer_ok_inv "Load" pointer before after value run).1

private theorem load_ro_access (address : Nat) (allocation : AllocId) (size alignment : Nat) (model : ByteModel) :
    LoadReadOnly (Sem.checkedAccess "Load" address allocation size alignment model) := by
  intro before after value run
  cases model with
  | le64 => exact (checkedAccess_ok_inv "Load" address allocation size alignment before after value run).1
  | le32 => exact (checkedAccess32_names_live_provenance "Load" address allocation size alignment before after value run).1

local macro "load_observes" : tactic => `(tactic|
  repeat' first
    | exact load_ro_pure _
    | exact load_ro_throw _
    | exact load_ro_except _
    | exact load_ro_get
    | exact load_ro_reject _
    | exact load_ro_pointer _
    | exact load_ro_access _ _ _ _ _
    | (refine load_ro_bind _ _ ?_ (fun value => ?_) <;> dsimp only)
    | split
    | (dsimp only; split))

/-- Arbitrary scalar decoders may refuse, but a successful held load cannot
    modify state. No validity or successful-decode premise is assumed. -/
theorem scalarLoadValue_readOnly (decode : Memory → List UInt8 → Except SemError Value)
    (ty : Ty) (pointer : Value) (strict : Bool) (align : Option Nat) (model : ByteModel) :
    LoadReadOnly (semLoadValueUsing decode ty pointer strict align model) := by
  unfold semLoadValueUsing Sem.accessAlign Sem.declaredOrNaturalAlign
  load_observes

/-- Includes complete, partial, padding-only and unwritten-explained branches
    of the actual descriptor decoder, with its original target/check order. -/
theorem aggregateLoadValue_readOnly (service : AggregateMemory.Service) (order : FunctionAddressOrder)
    (ty : Ty) (pointer : Value) (strict : Bool) (align : Option Nat) (model : ByteModel) :
    LoadReadOnly (AggregateMemory.loadValue service order ty pointer strict align model) := by
  unfold AggregateMemory.loadValue
  load_observes

theorem originalClosureLoadValue_readOnly (service : OriginalClosureMemory.Service)
    (order : FunctionAddressOrder) (closure : ClosureTyId) (pointer : Value)
    (strict : Bool) (align : Option Nat) (model : ByteModel) :
    LoadReadOnly (OriginalClosureMemory.loadValue service order closure pointer strict align model) := by
  unfold OriginalClosureMemory.loadValue
  load_observes

def selectedLoadAction (ctx : EvalContext) (ty : Ty) (pointer : Value)
    (strict : Bool) (align : Option Nat) : Sem Value :=
  ctx.loadMemoryValueAligned ty pointer strict align

theorem selectedLoadAction_readOnly (ctx : EvalContext) (ty : Ty) (pointer : Value)
    (strict : Bool) (align : Option Nat) : LoadReadOnly (selectedLoadAction ctx ty pointer strict align) := by
  unfold selectedLoadAction EvalContext.loadMemoryValueAligned
  cases ctx.memoryRoute ty with
  | scalar => exact scalarLoadValue_readOnly _ _ _ _ _ _
  | descriptor service => exact aggregateLoadValue_readOnly _ _ _ _ _ _ _
  | original closure service => exact originalClosureLoadValue_readOnly _ _ _ _ _ _ _

theorem selectedLoadAction_default_align (ctx : EvalContext) (ty : Ty) (pointer : Value) (strict : Bool) :
    selectedLoadAction ctx ty pointer strict none = ctx.loadMemoryValue ty pointer strict := rfl

theorem stepLoad_lookup_action (ctx : EvalContext) (ty : Ty) (pointer : ValueId)
    (strict : Bool) (align : Option Nat) :
    stepInstWithContext ctx (.Load ty pointer strict align) = (do
      let heldPointer ← Sem.lookupValue pointer
      let value ← selectedLoadAction ctx ty heldPointer strict align
      let id ← Sem.bindFresh value
      pure (.value (some id))) := by
  rfl

/-- Every successful original Load node derives its operand from the original
    locals and its value from actual held execution. Its *only* state update
    is the single fresh SSA publication, at the original next id. -/
theorem stepLoad_success_publication (ctx : EvalContext) (ty : Ty) (pointer : ValueId)
    (strict : Bool) (align : Option Nat) (before after : MachineState) (result : InstrResult)
    (run : Sem.run (stepInstWithContext ctx (.Load ty pointer strict align)) before = .ok (result,after)) :
    ∃ heldPointer value, before.lookupValue pointer = some heldPointer ∧
      Sem.run (selectedLoadAction ctx ty heldPointer strict align) before = .ok (value,before) ∧
      result = .value (some ⟨before.nextValueId⟩) ∧
      after = { before with
        locals := before.locals.set ⟨before.nextValueId⟩ value
        nextValueId := before.nextValueId + 1 } := by
  trustIrCompilerProof {
    rw [stepLoad_lookup_action,Sem.run_bind,Sem.run_lookupValue] at run
    cases found : before.lookupValue pointer with
    | none => simp only [found,Except.bind] at run
    | some heldPointer =>
      simp only [found,Except.bind] at run
      rw [Sem.run_bind] at run
      cases loaded : Sem.run (selectedLoadAction ctx ty heldPointer strict align) before with
      | error error => simp only [loaded,Except.bind] at run
      | ok pair =>
        obtain ⟨value,middle⟩ := pair
        have same := selectedLoadAction_readOnly ctx ty heldPointer strict align before middle value loaded
        subst middle
        simp only [loaded,Except.bind,Sem.run_bind,Sem.run_bindFresh,Sem.run_pure] at run
        cases run
        exact ⟨heldPointer,value,rfl,loaded,rfl,rfl⟩
  } {
    rw [stepLoad_lookup_action,Sem.run_bind,Sem.run_lookupValue] at run
    cases found : before.lookupValue pointer with
    | none => simp only [found,Except.bind] at run; cases run
    | some heldPointer =>
      simp only [found,Except.bind] at run
      rw [Sem.run_bind] at run
      cases loaded : Sem.run (selectedLoadAction ctx ty heldPointer strict align) before with
      | error error => simp only [loaded,Except.bind] at run; cases run
      | ok pair =>
        obtain ⟨value,middle⟩ := pair
        have same := selectedLoadAction_readOnly ctx ty heldPointer strict align before middle value loaded
        subst middle
        simp only [loaded,Except.bind,Sem.run_bind,Sem.run_bindFresh,Sem.run_pure] at run
        cases run
        exact ⟨heldPointer,value,rfl,loaded,rfl,rfl⟩
  }

/-- A complete success characterization, retaining lookup, actual selected
    held execution and the precise one-binding update in both directions. -/
theorem stepLoad_success_iff (ctx : EvalContext) (ty : Ty) (pointer : ValueId)
    (strict : Bool) (align : Option Nat) (before after : MachineState) (result : InstrResult) :
    Sem.run (stepInstWithContext ctx (.Load ty pointer strict align)) before = .ok (result,after) ↔
    ∃ heldPointer value, before.lookupValue pointer = some heldPointer ∧
      Sem.run (selectedLoadAction ctx ty heldPointer strict align) before = .ok (value,before) ∧
      result = .value (some ⟨before.nextValueId⟩) ∧
      after = { before with
        locals := before.locals.set ⟨before.nextValueId⟩ value
        nextValueId := before.nextValueId + 1 } := by
  constructor
  · exact stepLoad_success_publication ctx ty pointer strict align before after result
  · rintro ⟨heldPointer,value,found,loaded,rfl,rfl⟩
    rw [stepLoad_lookup_action,Sem.run_bind,Sem.run_lookupValue]
    simp only [found,Except.bind,Sem.run_bind,loaded,Sem.run_bindFresh,Sem.run_pure]

/-- The original Load cannot modify any memory component, including allocation,
    provenance, permission and unwritten metadata. This requires no validity
    assumption and covers both byte models and all selected services. -/
theorem stepLoad_memory_unchanged (ctx : EvalContext) (ty : Ty) (pointer : ValueId)
    (strict : Bool) (align : Option Nat) (before after : MachineState) (result : InstrResult)
    (run : Sem.run (stepInstWithContext ctx (.Load ty pointer strict align)) before = .ok (result,after)) :
    after.memory = before.memory := by
  obtain ⟨heldPointer,value,_found,_loaded,_resultShape,rfl⟩ :=
    stepLoad_success_publication ctx ty pointer strict align before after result run
  rfl

theorem stepLoad_published_value (ctx : EvalContext) (ty : Ty) (pointer : ValueId)
    (strict : Bool) (align : Option Nat) (before after : MachineState) (result : InstrResult)
    (run : Sem.run (stepInstWithContext ctx (.Load ty pointer strict align)) before = .ok (result,after)) :
    ∃ heldPointer value, before.lookupValue pointer = some heldPointer ∧
      Sem.run (selectedLoadAction ctx ty heldPointer strict align) before = .ok (value,before) ∧
      after.lookupValue ⟨before.nextValueId⟩ = some value ∧ after.nextValueId = before.nextValueId + 1 := by
  obtain ⟨heldPointer,value,found,loaded,_resultShape,rfl⟩ :=
    stepLoad_success_publication ctx ty pointer strict align before after result run
  exact ⟨heldPointer,value,found,loaded,Sem.bindFresh_ok (Sem.run_bindFresh value before),rfl⟩

theorem stepLoad_descriptor_execution (ctx : EvalContext) (ty : Ty) (pointer : ValueId)
    (strict : Bool) (align : Option Nat) (service : AggregateMemory.Service)
    (selected : ctx.memoryRoute ty = .descriptor service) (before after : MachineState) (result : InstrResult)
    (run : Sem.run (stepInstWithContext ctx (.Load ty pointer strict align)) before = .ok (result,after)) :
    ∃ heldPointer value, before.lookupValue pointer = some heldPointer ∧
      Sem.run (AggregateMemory.loadValue service ctx.functionOrder ty heldPointer strict align ctx.byteModel)
        before = .ok (value,before) ∧ after.memory = before.memory ∧
      after.lookupValue ⟨before.nextValueId⟩ = some value ∧ after.nextValueId = before.nextValueId + 1 := by
  obtain ⟨heldPointer,value,found,loaded,published,next⟩ :=
    stepLoad_published_value ctx ty pointer strict align before after result run
  simp only [selectedLoadAction,EvalContext.loadMemoryValueAligned,selected] at loaded
  exact ⟨heldPointer,value,found,loaded,stepLoad_memory_unchanged ctx ty pointer strict align before after result run,published,next⟩

theorem stepLoad_canonical_execution (ctx : EvalContext) (ty : Ty) (pointer : ValueId)
    (strict : Bool) (align : Option Nat) (canonical : ty.hasCanonicalMemoryLayout = true)
    (before after : MachineState) (result : InstrResult)
    (run : Sem.run (stepInstWithContext ctx (.Load ty pointer strict align)) before = .ok (result,after)) :
    ∃ heldPointer value, before.lookupValue pointer = some heldPointer ∧
      Sem.run (semLoadValueUsing
        (fun memory bytes => decodeMemoryWithFunctions ctx.byteModel ctx.functionOrder memory ty bytes)
        ty heldPointer strict align ctx.byteModel) before = .ok (value,before) ∧
      after.memory = before.memory ∧ after.lookupValue ⟨before.nextValueId⟩ = some value ∧
      after.nextValueId = before.nextValueId + 1 := by
  obtain ⟨heldPointer,value,found,loaded,published,next⟩ :=
    stepLoad_published_value ctx ty pointer strict align before after result run
  simp only [selectedLoadAction,EvalContext.loadMemoryValueAligned,ctx.memoryRoute_canonical ty canonical] at loaded
  exact ⟨heldPointer,value,found,loaded,stepLoad_memory_unchanged ctx ty pointer strict align before after result run,published,next⟩

end TrustIr
