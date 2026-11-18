-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.AggregateStoreExecution
import TrustIr.Proofs.AggregateProps

namespace TrustIr

/-- The actual context selector, retaining both descriptor-backed and canonical
    scalar actions, including explicit instruction alignment. -/
def selectedStoreAction (ctx : EvalContext) (ty : Ty) (pointer value : Value)
    (strict : Bool) (align : Option Nat) : Sem Unit :=
  ctx.storeMemoryValueAligned ty pointer value strict align

theorem selectedStoreAction_default_align (ctx : EvalContext) (ty : Ty) (pointer value : Value) (strict : Bool) :
    selectedStoreAction ctx ty pointer value strict none = ctx.storeMemoryValue ty pointer value strict := rfl

/-- Exact operand order and memory dispatch of the original Store instruction.
    Both refusal branches and the result-free outcome are retained. -/
theorem stepStore_lookup_action (ctx : EvalContext) (ty : Ty) (pointer value : ValueId)
    (strict : Bool) (align : Option Nat) :
    stepInstWithContext ctx (.Store ty pointer value strict align) = (do
      let heldPointer ← Sem.lookupValue pointer
      let heldValue ← Sem.lookupValue value
      selectedStoreAction ctx ty heldPointer heldValue strict align
      pure (.value none)) := by
  rfl

private theorem lookup_pair_success {α : Type} (pointer value : ValueId) (action : Value → Value → Sem α)
    (before after : MachineState) (result : α)
    (run : Sem.run (do
      let heldPointer ← Sem.lookupValue pointer
      let heldValue ← Sem.lookupValue value
      action heldPointer heldValue) before = .ok (result,after)) :
    ∃ heldPointer heldValue, before.lookupValue pointer = some heldPointer ∧
      before.lookupValue value = some heldValue ∧ Sem.run (action heldPointer heldValue) before = .ok (result,after) := by
  trustIrCompilerProof {
    rw [Sem.run_bind,Sem.run_lookupValue] at run
    cases pointerFound : before.lookupValue pointer with
    | none => simp only [pointerFound,Except.bind] at run
    | some heldPointer =>
      simp only [pointerFound,Except.bind] at run
      rw [Sem.run_bind,Sem.run_lookupValue] at run
      cases valueFound : before.lookupValue value with
      | none => simp only [valueFound,Except.bind] at run
      | some heldValue =>
        simp only [valueFound,Except.bind] at run
        exact ⟨heldPointer,heldValue,rfl,rfl,run⟩
  } {
    rw [Sem.run_bind,Sem.run_lookupValue] at run
    cases pointerFound : before.lookupValue pointer with
    | none => simp only [pointerFound,Except.bind] at run; cases run
    | some heldPointer =>
      simp only [pointerFound,Except.bind] at run
      rw [Sem.run_bind,Sem.run_lookupValue] at run
      cases valueFound : before.lookupValue value with
      | none => simp only [valueFound,Except.bind] at run; cases run
      | some heldValue =>
        simp only [valueFound,Except.bind] at run
        exact ⟨heldPointer,heldValue,rfl,rfl,run⟩
  }

private theorem unit_then_success {α : Type} (action : Sem Unit) (constant result : α)
    (before after : MachineState)
    (run : Sem.run (do action; pure constant) before = .ok (result,after)) :
    result = constant ∧ Sem.run action before = .ok ((),after) := by
  trustIrCompilerProof {
    rw [Sem.run_bind] at run
    cases accepted : Sem.run action before with
    | error error => simp only [accepted,Except.bind] at run
    | ok pair =>
      obtain ⟨unit,middle⟩ := pair
      cases unit
      simp only [accepted,Except.bind,Sem.run_pure] at run
      cases run
      exact ⟨rfl,rfl⟩
  } {
    rw [Sem.run_bind] at run
    cases accepted : Sem.run action before with
    | error error => simp only [accepted,Except.bind] at run; cases run
    | ok pair =>
      obtain ⟨unit,middle⟩ := pair
      cases unit
      simp only [accepted,Except.bind,Sem.run_pure] at run
      cases run
      exact ⟨rfl,rfl⟩
  }

/-- Actual SSA Store success supplies both original-state operand lookups and
    the actual selected held execution, without publishing a fresh SSA result. -/
theorem stepStore_success_operands (ctx : EvalContext) (ty : Ty) (pointer value : ValueId)
    (strict : Bool) (align : Option Nat) (before after : MachineState) (result : InstrResult)
    (run : Sem.run (stepInstWithContext ctx (.Store ty pointer value strict align)) before = .ok (result,after)) :
    result = .value none ∧ ∃ heldPointer heldValue,
      before.lookupValue pointer = some heldPointer ∧ before.lookupValue value = some heldValue ∧
      Sem.run (selectedStoreAction ctx ty heldPointer heldValue strict align) before = .ok ((),after) := by
  rw [stepStore_lookup_action] at run
  obtain ⟨heldPointer,heldValue,pointerFound,valueFound,executed⟩ :=
    lookup_pair_success pointer value
      (fun heldPointer heldValue => do selectedStoreAction ctx ty heldPointer heldValue strict align; pure (.value none))
      before after result run
  obtain ⟨same,executed⟩ := unit_then_success (selectedStoreAction ctx ty heldPointer heldValue strict align)
    (.value none) result before after executed
  exact ⟨same,heldPointer,heldValue,pointerFound,valueFound,executed⟩

theorem aggregateStore_success_operands (service : AggregateMemory.Service) (order : FunctionAddressOrder)
    (ty : Ty) (pointer value : ValueId) (strict : Bool) (align : Option Nat) (model : ByteModel)
    (before after : MachineState)
    (run : Sem.run (AggregateMemory.store service order ty pointer value strict align model) before = .ok ((),after)) :
    ∃ heldPointer heldValue, before.lookupValue pointer = some heldPointer ∧ before.lookupValue value = some heldValue ∧
      Sem.run (AggregateMemory.storeValue service order ty heldPointer heldValue strict align model) before = .ok ((),after) :=
  lookup_pair_success pointer value (fun heldPointer heldValue =>
    AggregateMemory.storeValue service order ty heldPointer heldValue strict align model) before after () run

theorem stepStore_descriptor_execution (ctx : EvalContext) (ty : Ty) (pointer value : ValueId)
    (strict : Bool) (align : Option Nat) (service : AggregateMemory.Service)
    (selected : ctx.memoryRoute ty = .descriptor service) (before after : MachineState) (result : InstrResult)
    (run : Sem.run (stepInstWithContext ctx (.Store ty pointer value strict align)) before = .ok (result,after)) :
    result = .value none ∧ ∃ heldPointer heldValue,
      before.lookupValue pointer = some heldPointer ∧ before.lookupValue value = some heldValue ∧
      Sem.run (AggregateMemory.storeValue service ctx.functionOrder ty heldPointer heldValue strict align ctx.byteModel)
        before = .ok ((),after) := by
  obtain ⟨same,heldPointer,heldValue,pointerFound,valueFound,executed⟩ :=
    stepStore_success_operands ctx ty pointer value strict align before after result run
  simp only [selectedStoreAction,EvalContext.storeMemoryValueAligned,selected] at executed
  exact ⟨same,heldPointer,heldValue,pointerFound,valueFound,executed⟩

/-- Canonical types keep the actual scalar path even if the context contains
    an unrelated or malformed aggregate service. -/
theorem stepStore_canonical_execution (ctx : EvalContext) (ty : Ty) (pointer value : ValueId)
    (strict : Bool) (align : Option Nat) (canonical : ty.hasCanonicalMemoryLayout = true)
    (before after : MachineState) (result : InstrResult)
    (run : Sem.run (stepInstWithContext ctx (.Store ty pointer value strict align)) before = .ok (result,after)) :
    result = .value none ∧ ∃ heldPointer heldValue,
      before.lookupValue pointer = some heldPointer ∧ before.lookupValue value = some heldValue ∧
      Sem.run (semStoreValueUsing (scalarMemoryLayout ctx.byteModel)
        (encodeMemoryWithFunctions ctx.byteModel ctx.functionOrder ty) ty heldPointer heldValue strict align ctx.byteModel)
        before = .ok ((),after) := by
  obtain ⟨same,heldPointer,heldValue,pointerFound,valueFound,executed⟩ :=
    stepStore_success_operands ctx ty pointer value strict align before after result run
  simp only [selectedStoreAction,EvalContext.storeMemoryValueAligned,ctx.memoryRoute_canonical ty canonical] at executed
  exact ⟨same,heldPointer,heldValue,pointerFound,valueFound,executed⟩

theorem memoryServiceFor_descriptor_iff (ctx : EvalContext) (ty : Ty) (service : AggregateMemory.Service) :
    ctx.memoryServiceFor ty = some service ↔ ty.hasCanonicalMemoryLayout = false ∧ ctx.memoryService = some service := by
  cases canonical : ty.hasCanonicalMemoryLayout <;> simp [EvalContext.memoryServiceFor,canonical]

/-- The actual descriptor-backed Store node derives its original operands,
    selected checks, byte image and complete state update from node execution. -/
theorem stepStore_descriptor_success_steps (ctx : EvalContext) (ty : Ty) (pointer value : ValueId)
    (strict : Bool) (align : Option Nat) (service : AggregateMemory.Service)
    (selected : ctx.memoryRoute ty = .descriptor service) (before after : MachineState) (result : InstrResult)
    (run : Sem.run (stepInstWithContext ctx (.Store ty pointer value strict align)) before = .ok (result,after)) :
    result = .value none ∧ ∃ heldPointer heldValue plan alignment address allocation image,
      before.lookupValue pointer = some heldPointer ∧ before.lookupValue value = some heldValue ∧
      (strict && (heldValue.isPoison || AggregateMemory.carriesUnwritten heldValue)) = false ∧
      ctx.byteModel = service.model ∧ service.query ty = .ok plan ∧
      checkedMemoryAlign "Store" plan.layout.alignment align = .ok alignment ∧
      heldPointer = .ptr address (some allocation) ∧
      Sem.run (Sem.checkedAccess "Store" address allocation plan.layout.size alignment ctx.byteModel) before = .ok (address,before) ∧
      AggregateMemory.StoreImageAccepted ctx.byteModel ctx.functionOrder ty plan heldValue image ∧
      image.bytes.size = plan.layout.size ∧ after = { before with memory :=
        (before.memory.writeImage address image.bytes).recordUnwritten allocation address image.unwritten } := by
  obtain ⟨same,heldPointer,heldValue,pointerFound,valueFound,executed⟩ :=
    stepStore_descriptor_execution ctx ty pointer value strict align service selected before after result run
  obtain ⟨clean,plan,alignment,address,allocation,image,target,query,aligned,pointerShape,accessed,accepted,extent,state⟩ :=
    AggregateMemory.storeValue_success_steps service ctx.functionOrder ty heldPointer heldValue strict align ctx.byteModel before after executed
  exact ⟨same,heldPointer,heldValue,plan,alignment,address,allocation,image,pointerFound,valueFound,
    clean,target,query,aligned,pointerShape,accessed,accepted,extent,state⟩

/-- Actual SSA values without an explicit unwritten flag inherit the precise
    overwritten-window coverage law, including partial and poison transport. -/
theorem stepStore_descriptor_unwritten_coverage (ctx : EvalContext) (ty : Ty) (pointer value : ValueId)
    (strict : Bool) (align : Option Nat) (service : AggregateMemory.Service)
    (selected : ctx.memoryRoute ty = .descriptor service) (before after : MachineState) (result : InstrResult)
    (clear : ∀ heldValue, before.lookupValue value = some heldValue → AggregateMemory.carriesUnwritten heldValue = false)
    (run : Sem.run (stepInstWithContext ctx (.Store ty pointer value strict align)) before = .ok (result,after)) :
    result = .value none ∧ ∃ heldPointer heldValue plan address allocation,
      before.lookupValue pointer = some heldPointer ∧ before.lookupValue value = some heldValue ∧
      service.query ty = .ok plan ∧ heldPointer = .ptr address (some allocation) ∧
      ∀ queryAllocation query, after.memory.isUnwritten queryAllocation query =
        (before.memory.isUnwritten queryAllocation query && !(address ≤ query && query < address + plan.layout.size)) := by
  obtain ⟨same,heldPointer,heldValue,pointerFound,valueFound,executed⟩ :=
    stepStore_descriptor_execution ctx ty pointer value strict align service selected before after result run
  obtain ⟨plan,address,allocation,queried,pointerShape,coverage⟩ :=
    AggregateMemory.storeValue_success_unwritten_coverage service ctx.functionOrder ty heldPointer heldValue strict align
      ctx.byteModel before after (clear heldValue valueFound) executed
  exact ⟨same,heldPointer,heldValue,plan,address,allocation,pointerFound,valueFound,queried,pointerShape,coverage⟩

/-- Newly registered records of an actual descriptor-backed Store node are
    authenticated to its actual SSA carrier, selected image and complete state,
    then bounded inside the live allocation named by its pointer provenance. -/
theorem stepStore_descriptor_registered_bounds (ctx : EvalContext) (ty : Ty) (pointer value : ValueId)
    (strict : Bool) (align : Option Nat) (service : AggregateMemory.Service)
    (selected : ctx.memoryRoute ty = .descriptor service) (before after : MachineState) (result : InstrResult)
    (run : Sem.run (stepInstWithContext ctx (.Store ty pointer value strict align)) before = .ok (result,after)) :
    result = .value none ∧ ∃ (heldPointer heldValue : Value) (plan : AggregateMemory.Plan) (address : Nat)
      (allocation : AllocId) (image : AggregateMemory.Image) (live : Allocation),
      before.lookupValue pointer = some heldPointer ∧ before.lookupValue value = some heldValue ∧
      service.query ty = .ok plan ∧ heldPointer = .ptr address (some allocation) ∧
      before.memory.lookup allocation = some live ∧ live.alive = true ∧
      AggregateMemory.StoreImageAccepted ctx.byteModel ctx.functionOrder ty plan heldValue image ∧
      image.bytes.size = plan.layout.size ∧
      after = { before with memory := (before.memory.writeImage address image.bytes).recordUnwritten allocation address image.unwritten } ∧
      ∀ lane ∈ after.memory.unwritten,
        lane ∈ (before.memory.writeImage address image.bytes).unwritten ∨
          lane.allocation = allocation ∧ live.base ≤ lane.start ∧ lane.start < lane.stop ∧ lane.stop ≤ live.base + live.size := by
  obtain ⟨same,heldPointer,heldValue,pointerFound,valueFound,executed⟩ :=
    stepStore_descriptor_execution ctx ty pointer value strict align service selected before after result run
  obtain ⟨plan,address,allocation,image,live,queried,pointerShape,found,alive,accepted,extent,state,bounds⟩ :=
    AggregateMemory.storeValue_success_registered_bounds service ctx.functionOrder ty heldPointer heldValue strict align ctx.byteModel before after executed
  exact ⟨same,heldPointer,heldValue,plan,address,allocation,image,live,pointerFound,valueFound,
    queried,pointerShape,found,alive,accepted,extent,state,bounds⟩

end TrustIr
