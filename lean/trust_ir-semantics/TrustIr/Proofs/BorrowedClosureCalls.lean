-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.OriginalClosureMemoryReadback
import TrustIr.Proofs.CallProps
import TrustIr.DecodedContext

namespace TrustIr

/-- Stateful B5 transfer over the SAME actual call helper. Unlike a value-only
postcondition, this retains the callee's complete source Memory through caller
restoration. The callee obligation is still required; arbitrary machine memory,
SP, placement and callee-frame agreement are not supplied by this theorem. -/
theorem proof_context_memory_assume_sound (ctx : EvalContext) (fuel callDepth : Nat)
    (id : FuncId) (callee : EvalFunction) (args : List Value) (before : MachineState)
    (post : Memory → List Value → Prop) (found : ctx.functions id = some callee)
    (calleePost : ∀ values after,
      Sem.run (stepNWithContext (ctx.forFunction callee) fuel callDepth callee.cfg callee.entryBlock args)
        {before with locals := ValueMap.empty,nextValueId := 0} = .ok (values,after) →
      post after.memory values) :
    ∀ values after, Sem.run (runCallReq ctx fuel callDepth id args) before = .ok (values,after) →
      post after.memory values := by
  intro values after run
  obtain ⟨_arity,_argsClean,_returns,_returnsClean,calleeEnd,executed,restored⟩ :=
    runCallReq_ok_decomp ctx fuel callDepth id callee args before after values found run
  have result := calleePost values calleeEnd executed
  rw [restored,restoreFrame_preserves_memory]
  exact result

namespace OriginalClosureMemory

/-- An ordinary source body that returns the closure read through its borrowed
pointer. This is syntax, not a new evaluator, validator or execution license. -/
def borrowedLoadBlock (closure : ClosureTyId) (align : Option Nat) : BasicBlock :=
  {params := [(⟨0⟩,.Ptr)],body := [.Load (.Closure closure) ⟨0⟩ false align],
   bodyResultDests := [[⟨1⟩]],terminator := .Return [⟨1⟩]}

/-- Exact real evaluator spine for this source body, retaining original
parameter/result/return checks and fresh result publication. -/
theorem borrowed_load_body_spine (ctx : EvalContext) (fuel depth : Nat) (cfg : CFG)
    (pc : BlockId) (closure : ClosureTyId) (align : Option Nat) (pointer : Value)
    (selected : cfg pc = some (borrowedLoadBlock closure align)) :
    stepNWithContext ctx (fuel+1) depth cfg pc [pointer] = (do
      let _ ← Sem.fromMemoryExcept (checkFunctionItemValues ctx [.Ptr] [pointer])
      bindBlockParamsChecked [(⟨0⟩,.Ptr)] [pointer]
      let held ← Sem.lookupValue ⟨0⟩
      let value ← selectedLoadAction ctx (.Closure closure) held false align
      let fresh ← Sem.bindFresh value
      ctx.bindInstructionResults (.Load (.Closure closure) ⟨0⟩ false align) (.value (some fresh)) [⟨1⟩]
      let values ← [⟨1⟩].mapM Sem.lookupValue
      if let some expected := ctx.functionReturnTypes then
        let _ ← Sem.fromMemoryExcept (checkFunctionItemValues ctx expected values)
        pure values
      else pure values) := by
  unfold stepNWithContext
  rw [selected]
  simp only [borrowedLoadBlock,EvalContext.resolveBlock,EvalContext.resolveDrop,List.map_nil,List.map_cons,
    bodyInstsWithResultDests,List.forIn_cons,List.forIn_nil,stepLoad_lookup_action,
    stepTermWithContext,closureTermWithContext,stepInst,semReturn,pure_bind,bind_assoc]
  all_goals rfl


private theorem split_success {α β : Type} (first : Sem α) (next : α → Sem β)
    (before after : MachineState) (value : β)
    (run : Sem.run (first >>= next) before = .ok (value,after)) :
    ∃ actual middle, Sem.run first before = .ok (actual,middle) ∧
      Sem.run (next actual) middle = .ok (value,after) := by
  rw [Sem.run_bind] at run
  cases firstRun : Sem.run first before with
  | error error =>
    simp only [firstRun,Except.bind] at run
    all_goals cases run
  | ok pair => exact ⟨pair.1,pair.2,rfl,by simpa only [firstRun,Except.bind] using run⟩

private theorem except_success {α β : Type} (first : Except SemError α) (next : α → Sem β)
    (before after : MachineState) (value : β)
    (run : Sem.run (Sem.fromMemoryExcept first >>= next) before = .ok (value,after)) :
    ∃ actual, first = .ok actual ∧ Sem.run (next actual) before = .ok (value,after) := by
  cases first with
  | error error => cases run
  | ok actual => exact ⟨actual,rfl,run⟩

private theorem instruction_check_readonly (ctx : EvalContext) (inst : Inst)
    (dests : List ValueId) (values : List Value) (before after : MachineState)
    (run : Sem.run (ctx.checkInstructionResults inst dests values) before = .ok ((),after)) : after = before := by
  unfold EvalContext.checkInstructionResults at run
  cases queriedTypes : ctx.instructionResultTypes inst dests values.length with
  | error error => simp only [queriedTypes] at run; all_goals cases run
  | ok actualTypes =>
    simp only [queriedTypes,pure_bind] at run
    cases checked : checkSSACharValues actualTypes values with
    | error error => simp only [checked] at run; all_goals cases run
    | ok unit => cases unit; rw [checked] at run; cases run; rfl

/-- The actual successful publication check cannot alter memory or substitute
the produced value. Its declaration/Char refusals remain real premises. -/
private theorem one_result_publication (ctx : EvalContext) (inst : Inst) (value : Value)
    (before after : MachineState) (found : before.lookupValue ⟨1⟩ = some value)
    (run : Sem.run (ctx.bindInstructionResults inst (.value (some ⟨1⟩)) [⟨1⟩]) before = .ok ((),after)) :
    after.memory = before.memory ∧ after.lookupValue ⟨1⟩ = some value := by
  unfold EvalContext.bindInstructionResults at run
  rw [Sem.run_bind,Sem.run_lookupValue,found] at run
  simp only [Except.bind] at run
  obtain ⟨unit,middle,checked,run⟩ := split_success _ _ before after () run
  cases unit
  have unchanged := instruction_check_readonly ctx inst [⟨1⟩] [value] before middle checked
  subst middle
  have executed : Sem.run (bindInstrResultDests (.value (some ⟨1⟩)) [⟨1⟩]) before =
      .ok ((),{before with locals := before.locals.set ⟨1⟩ value,nextValueId := max before.nextValueId 2}) := by
    unfold bindInstrResultDests
    rw [Sem.run_bind,Sem.run_lookupValue,found]
    simp only [Except.bind]
    rfl
  rw [executed] at run
  cases run
  exact ⟨rfl,by rfl⟩

/-- The genuine callee's fresh SSA frame after its checked pointer parameter
binding. Full Memory, permissions and all nonlocal fields are retained. -/
def borrowedEntry (caller : MachineState) (pointer : Value) : MachineState :=
  {caller with locals := ValueMap.empty.set ⟨0⟩ pointer,nextValueId := 1}

/-- Invert the actual one-Load source body. It really reads its incoming
pointer and returns the loaded value; neither the load result nor its memory
preservation is supplied as a caller's decoder/model answer. -/
theorem borrowed_load_body_success (ctx : EvalContext) (fuel depth : Nat) (cfg : CFG)
    (pc : BlockId) (closure : ClosureTyId) (align : Option Nat) (pointer : Value)
    (caller after : MachineState) (values : List Value)
    (selected : cfg pc = some (borrowedLoadBlock closure align))
    (run : Sem.run (stepNWithContext ctx (fuel+1) depth cfg pc [pointer])
      {caller with locals := ValueMap.empty,nextValueId := 0} = .ok (values,after)) :
    ∃ output,
      Sem.run (selectedLoadAction ctx (.Closure closure) pointer false align)
        (borrowedEntry caller pointer) = .ok (output,borrowedEntry caller pointer) ∧
      values = [output] ∧ after.memory = caller.memory := by
  rw [borrowed_load_body_spine ctx fuel depth cfg pc closure align pointer selected] at run
  obtain ⟨checked,accepted,run⟩ := except_success _ _ _ _ _ run
  cases checked
  have bound : Sem.run (bindBlockParamsChecked [(⟨0⟩,.Ptr)] [pointer])
      {caller with locals := ValueMap.empty,nextValueId := 0} = .ok ((),borrowedEntry caller pointer) := by rfl
  rw [Sem.run_bind,bound] at run
  simp only [Except.bind] at run
  have pointerFound : (borrowedEntry caller pointer).lookupValue ⟨0⟩ = some pointer := by rfl
  rw [Sem.run_bind,Sem.run_lookupValue,pointerFound] at run
  simp only [Except.bind] at run
  obtain ⟨output,middle,loaded,run⟩ := split_success _ _ (borrowedEntry caller pointer) after values run
  have same := selectedLoadAction_readOnly ctx (.Closure closure) pointer false align
    (borrowedEntry caller pointer) middle output loaded
  subst middle
  rw [Sem.run_bind,Sem.run_bindFresh] at run
  simp only [Except.bind] at run
  obtain ⟨unit,published,publication,run⟩ := split_success _ _ _ after values run
  cases unit
  have loadedFound : ({borrowedEntry caller pointer with
      locals := (borrowedEntry caller pointer).locals.set ⟨1⟩ output,nextValueId := 2} : MachineState).lookupValue ⟨1⟩ = some output := by rfl
  obtain ⟨memory,present⟩ := one_result_publication ctx (.Load (.Closure closure) ⟨0⟩ false align)
    output _ published loadedFound publication
  have returned : Sem.run ([⟨1⟩].mapM Sem.lookupValue) published = .ok ([output],published) := by
    simp only [List.mapM_cons,List.mapM_nil,pure_bind,Sem.run_bind,Sem.run_lookupValue,present,Except.bind,Sem.run_pure]
  rw [Sem.run_bind,returned] at run
  simp only [Except.bind] at run
  have finalSame : values = [output] ∧ after = published := by
    cases expected : ctx.functionReturnTypes with
    | none => rw [expected] at run; cases run; exact ⟨rfl,rfl⟩
    | some types =>
      rw [expected] at run
      obtain ⟨unit,_checked,run⟩ := except_success _ _ published after values run
      cases unit
      cases run
      exact ⟨rfl,rfl⟩
  exact ⟨output,loaded,finalSame.1,finalSame.2 ▸ memory⟩


/-- The memory source comes from actual complete decoded-context assembly.
This is a projection of the maintained factory, not a parallel source scan. -/
theorem decoded_original_memory (source : TrustIrEval.Module) (depth : Nat) (ctx : EvalContext)
    (assembled : TrustIrEval.contextOf source depth = .ok ctx) :
    ctx.originalClosureMemory = some (TrustIrEval.originalMemoryServiceOf source ctx.byteModel) := by
  unfold TrustIrEval.contextOf at assembled
  simp only [bind,pure,Except.bind,Except.pure,TrustIrEval.unsupported,
    throw,throwThe,MonadExceptOf.throw] at assembled
  repeat' first
    | (solve | cases assembled)
    | split at assembled
  cases assembled
  rfl

/-- A checked source Store/readback input for the exact service actually
installed by the original context factory. The roots are not a guessed mirror
list; equality to that factory is required. This is a logical value admission,
not native allocation, SP, callee or byte-image authority. -/
def SourceReadbackInputs (source : TrustIrEval.Module) (ctx : EvalContext)
    (memory : Memory) (closure : ClosureTyId) (captures : List Value) : Prop :=
  ∃ roots, TrustIrEval.originalMemoryServiceOf source ctx.byteModel = prepare source ctx.byteModel roots ∧
    CaptureReadbackInputs source ctx.byteModel roots ctx.functionOrder memory closure captures ∧
    CaptureLeafQueries source ctx.byteModel roots closure

/-- A genuine source callee memory summary, consumed through the maintained B5
call helper. The actual original decoded body reads its argument and returns
the loaded closure. Its complete memory is preserved, including allocations,
provenance and unwritten metadata; Store/readback supplies the same original
code binding and the residue/provenance-aware value relation.

This theorem does NOT supply arbitrary callee memory rely or any actual
machine-array/SP/frame agreement. A body with a write or a changed return is
not this source body; original call/declaration/ABI/fuel/poison checks remain. -/
theorem source_borrowed_call_readback (source : TrustIrEval.Module) (maxDepth : Nat) (ctx : EvalContext)
    (assembled : TrustIrEval.contextOf source maxDepth = .ok ctx)
    (id : FuncId) (callee : EvalFunction) (fuel depth : Nat)
    (closure nominal : ClosureTyId) (target : FuncId) (captures : List Value) (pointer : Value)
    (strict : Bool) (align : Option Nat) (before stored after : MachineState) (values : List Value)
    (found : ctx.functions id = some callee)
    (body : callee.cfg callee.entryBlock = some (borrowedLoadBlock closure align))
    (admitted : SourceReadbackInputs source ctx stored.memory closure captures)
    (storeRun : Sem.run (storeValue (TrustIrEval.originalMemoryServiceOf source ctx.byteModel)
      ctx.functionOrder closure pointer (.typedClosure nominal target captures) strict align ctx.byteModel)
      before = .ok ((),stored))
    (callRun : Sem.run (runCallReq ctx (fuel+1) depth id [pointer]) stored = .ok (values,after)) :
    after.memory = stored.memory ∧
      ∃ (binding : TrustIrEval.ClosureStorage.Binding source closure) (output : Value),
        values = [output] ∧ ValueReadback source closure binding ctx.byteModel after.memory
          (.typedClosure nominal target captures) output := by
  have original := decoded_original_memory source maxDepth ctx assembled
  obtain ⟨roots,factory,inputs,leaves⟩ := admitted
  have route : (ctx.forFunction callee).memoryRoute (.Closure closure) =
      .original closure (prepare source ctx.byteModel roots) := by
    change ctx.memoryRoute (.Closure closure) = _
    simp only [EvalContext.memoryRoute,EvalContext.originalClosureFor,original,factory]
  rw [factory] at storeRun
  apply proof_context_memory_assume_sound ctx (fuel+1) depth id callee [pointer] stored
    (fun memory returned => memory = stored.memory ∧
      ∃ (binding : TrustIrEval.ClosureStorage.Binding source closure) (output : Value),
        returned = [output] ∧ ValueReadback source closure binding ctx.byteModel memory
          (.typedClosure nominal target captures) output) found ?_ values after callRun
  intro returned calleeEnd executed
  obtain ⟨output,loaded,returnedSame,memorySame⟩ := borrowed_load_body_success
    (ctx.forFunction callee) fuel depth callee.cfg callee.entryBlock closure align pointer stored calleeEnd returned body executed
  have observedMemory : (borrowedEntry stored pointer).memory = stored.memory := rfl
  obtain ⟨binding,expected,readback,related⟩ := prepared_store_load_observer source ctx.byteModel roots ctx.functionOrder
    closure nominal target captures pointer strict align before stored (borrowedEntry stored pointer)
    observedMemory inputs leaves storeRun
  simp only [selectedLoadAction,EvalContext.loadMemoryValueAligned,route] at loaded
  change Sem.run (loadValue (prepare source ctx.byteModel roots) ctx.functionOrder closure pointer false align ctx.byteModel)
    (borrowedEntry stored pointer) = .ok (output,borrowedEntry stored pointer) at loaded
  have sameStrict : loadValue (prepare source ctx.byteModel roots) ctx.functionOrder closure pointer strict align ctx.byteModel =
      loadValue (prepare source ctx.byteModel roots) ctx.functionOrder closure pointer false align ctx.byteModel := rfl
  rw [sameStrict,loaded] at readback
  cases readback
  refine ⟨memorySame,binding,output,returnedSame,?_⟩
  rw [memorySame]
  exact related

end OriginalClosureMemory
end TrustIr
