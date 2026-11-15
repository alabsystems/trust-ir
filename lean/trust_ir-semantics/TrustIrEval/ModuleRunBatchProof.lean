-- Copyright 2026 Andrew Yates | Apache-2.0
-- Logical runner correspondence only; no native renderer or wire-roundtrip claim.
import TrustIrEval.Run
import TrustIr.Proofs.GenericCoroModuleEntryEffects

namespace TrustIrEval.ModuleRunBatch
open TrustIr TrustIr.GenericCoro TrustIr.GenericCoroAllBlocksPlanner
open ModuleFactory

/-- The exact static-call accumulator used by the runner. -/
def calleeStep (glue : Ty → Option FuncId) (acc : List FuncId)
    (row : BlockId × BasicBlock) : List FuncId :=
  acc ++ row.2.body.foldl (fun found inst => found ++ calleesOfInst glue inst) [] ++
    calleesOfInst glue row.2.terminator

theorem expandedEntry_calleeStep (glue : Ty → Option FuncId) (names : Names)
    (id : BlockId) (block : BasicBlock) (acc : List FuncId) :
    calleeStep glue acc (id, expandedEntry names block) = calleeStep glue acc (id, block) := by
  cases term : block.terminator <;> first | rfl |
    simp only [calleeStep, expandedEntry, term, List.foldl_append, List.foldl_cons,
      List.foldl_nil, calleesOfInst, List.append_nil]

theorem list_any_append {α : Type} (test : α → Bool) (left right : List α) :
    (left ++ right).any test = (left.any test || right.any test) := by
  induction left with
  | nil => rfl
  | cons head rest ih =>
    simp only [List.cons_append, List.any_cons, ih, Bool.or_assoc]

trustIrDenseMatch
def blockDrops (block : BasicBlock) : Bool :=
  let isDrop : Inst → Bool
    | .Drop .. => true
    | .DropInvoke .. => true
    | _ => false
  block.body.any isDrop || isDrop block.terminator

theorem blocksDrop_cons (id : BlockId) (block : BasicBlock) (rest : Rows) :
    blocksDrop ((id, block) :: rest) = (blockDrops block || blocksDrop rest) := rfl

theorem expandedEntry_blocksDrop (names : Names) (id : BlockId) (block : BasicBlock) :
    blocksDrop [(id, expandedEntry names block)] = blocksDrop [(id, block)] := by
  cases term : block.terminator <;> simp only [expandedEntry, term] <;> first | rfl |
    simp only [blocksDrop, List.any_cons, List.any_nil, list_any_append, term, Bool.or_false]

theorem expandedEntry_blockDrops (names : Names) (block : BasicBlock) :
    blockDrops (expandedEntry names block) = blockDrops block := by
  have append_silent (test : Inst → Bool) (body suffix : List Inst)
      (silent : suffix.any test = false) :
      (body ++ suffix).any test = body.any test := by
    induction body with
    | nil => exact silent
    | cons instruction rest ih =>
      exact congrArg (fun value : Bool => test instruction || value) ih
  cases block with
  | mk parameters body destinations terminator terminatorDestinations =>
    cases terminator <;> first
    | rfl
    | change ((body ++ _).any _ || false) = (body.any _ || false)
      apply congrArg (fun value : Bool => value || false)
      exact append_silent _ body _ rfl

theorem plans_callees {domain : Nat} {used : List Nat}
    {before after : GenericCoroFreshCursor.Cursor domain used} {source target : Rows} {trace : Trace}
    (plans : Plans before after source target trace) (glue : Ty → Option FuncId) :
    calleesOf glue target = calleesOf glue source := by
  have fold (acc : List FuncId) : target.foldl (calleeStep glue) acc =
      source.foldl (calleeStep glue) acc := by
    induction plans generalizing acc with
    | nil => rfl
    | keep _ _ _ _ _ _ _ _ _ ih => exact ih _
    | expand _ _ _ id block _ names _ _ _ _ _ ih =>
      simpa only [List.foldl_cons, expandedEntry_calleeStep] using
        ih (calleeStep glue acc (id, block))
  exact fold []

theorem plans_blocksDrop {domain : Nat} {used : List Nat}
    {before after : GenericCoroFreshCursor.Cursor domain used} {source target : Rows} {trace : Trace}
    (plans : Plans before after source target trace) : blocksDrop target = blocksDrop source := by
  induction plans with
  | nil => rfl
  | keep _ _ _ _ _ _ _ _ _ ih => simp only [blocksDrop_cons, ih]
  | expand _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    simp only [blocksDrop_cons, expandedEntry_blockDrops, ih]

/-- Exactly the body information inspected by the eager wrapper walk. -/
def bodyObservation (glue : Ty → Option FuncId) (function : Function) :
    D (Bool × List FuncId) :=
  function.blocks.map (fun rows => (blocksDrop rows, calleesOf glue rows))

theorem lowerFunction_bodyObservation (signatures : Array FuncTyDef)
    (direct : FuncId → Option FuncTyDef) (source target : Function)
    (actual : lowerFunction signatures direct source = .ok target)
    (glue : Ty → Option FuncId) : bodyObservation glue target = bodyObservation glue source := by
  rcases lowerFunction_prepared signatures direct source target actual with
    unchanged | ⟨rows, expansion, _declaration, decoded, prepared, result⟩
  · rw [unchanged.2]
  · have valid := prepareRows_ready GenericCoroFreshIds.u32Domain direct
      (fun id => (trustIrArrayGet? signatures id.index)) rows expansion prepared
    cases expansion with
    | unchanged inferred => rw [result]
    | capacity inferred certificate => exact result.elim
    | expanded emitted inferred targetInferred =>
      have plan := lowerRows_ready GenericCoroFreshIds.u32Domain rows valid.2.2.1
      have calls := plans_callees plan glue
      have drops := plans_blocksDrop plan
      rw [← valid.2.1] at calls drops
      rw [result]
      simp only [bodyObservation, decoded, Except.map, calls, drops]

theorem produced_lookupObservation (signatures : Array FuncTyDef)
    (direct : FuncId → Option FuncTyDef) {source target : List Function}
    (produced : Produced signatures direct source target) (glue : Ty → Option FuncId)
    (requested : FuncId) :
    (target.find? (fun function => function.id == requested)).map (bodyObservation glue) =
      (source.find? (fun function => function.id == requested)).map (bodyObservation glue) := by
  induction produced with
  | nil => rfl
  | @cons source target sources targets actual rest ih =>
    have id := sameHeader_id (lowerFunction_law signatures direct source target actual).1
    have observation := lowerFunction_bodyObservation signatures direct source target actual glue
    cases found : source.id == requested with
    | false => simpa only [List.find?, id, found, Bool.false_eq_true, if_false] using ih
    | true => simp only [List.find?, id, found, if_true, Option.map, observation]

theorem reachableGo_step (module : Module) (lookup : FuncId → Option Function)
    (fuel : Nat) (seen : List FuncId) (fid : FuncId) (rest : List FuncId) :
    reachableDecodeFailure.go module lookup (fuel + 1) seen (fid :: rest) =
      if seen.contains fid then reachableDecodeFailure.go module lookup fuel seen rest
      else match (lookup fid).map (bodyObservation (dropGlueOf module)) with
        | none => reachableDecodeFailure.go module lookup fuel (fid :: seen) rest
        | some (Except.error error) => some error
        | some (Except.ok (drops, calls)) =>
          if drops && module.dropGlue.any (fun row => row.2.isNone) then
            some (.unsupported "drop_glue.key")
          else reachableDecodeFailure.go module lookup fuel (fid :: seen) (rest ++ calls) := by
  simp only [reachableDecodeFailure.go]
  split
  · rfl
  · cases found : lookup fid with
    | none => simp only [found, Option.map]
    | some function =>
      cases decoded : function.blocks <;>
        simp only [found, Option.map, bodyObservation, decoded, Except.map]

/-- Preserve the actual bounded walk, not merely its successful branch.
    The two lookups may contain duplicate keys and retained body errors. -/
theorem reachableGo_eq (source target : Module)
    (sourceLookup targetLookup : FuncId → Option Function)
    (views : ∀ id, (sourceLookup id).map (bodyObservation (dropGlueOf source)) =
      (targetLookup id).map (bodyObservation (dropGlueOf target)))
    (dropKeys : source.dropGlue.any (fun row => row.2.isNone) =
      target.dropGlue.any (fun row => row.2.isNone))
    (fuel : Nat) (seen work : List FuncId) :
    reachableDecodeFailure.go source sourceLookup fuel seen work =
      reachableDecodeFailure.go target targetLookup fuel seen work := by
  induction fuel generalizing seen work with
  | zero => cases work <;> rfl
  | succ fuel ih =>
    cases work with
    | nil => rfl
    | cons fid rest => simp only [reachableGo_step, views, dropKeys, ih]

/-- Eager decode/drop refusal is preserved at every fixed requested ID,
    including raw duplicates, absent IDs and partial drop tables. -/
theorem transform_ready_reachableDecodeFailure (source target : Module)
    (actual : ModuleFactory.transform source = .ready target) (requested : FuncId) :
    reachableDecodeFailure source requested = reachableDecodeFailure target requested := by
  have fields := (transform_ready source target actual).1
  have produced := transform_produced source target actual
  have glue : dropGlueOf source = dropGlueOf target :=
    (congrArg dropGlueOf fields).symm
  have dropKeys : source.dropGlue.any (fun row => row.2.isNone) =
      target.dropGlue.any (fun row => row.2.isNone) :=
    (congrArg (fun module : Module => module.dropGlue.any (fun row => row.2.isNone)) fields).symm
  have counts := congrArg List.length (transform_headers source target actual)
  simp only [List.length_map] at counts
  unfold reachableDecodeFailure
  rw [counts]
  apply reachableGo_eq source target _ _ ?_ dropKeys
  intro id
  rw [← glue]
  exact (produced_lookupObservation _ _ produced _ id).symm

/-- Updating executable tables does not alter the fields read by the runner
    before entering the evaluator. -/
theorem installFirst_runnerFields
    (choose : AllBlocksContext.FunctionUpdate → EvalFunction) (base : EvalContext)
    (updates : List AllBlocksContext.FunctionUpdate) :
    (AllBlocksContext.installFirst choose base updates).byteModel = base.byteModel ∧
      (AllBlocksContext.installFirst choose base updates).declared = base.declared := by
  induction updates with
  | nil => exact ⟨rfl, rfl⟩
  | cons update rest ih => exact ih

theorem transform_ready_runnerFields (source target : Module)
    (actual : ModuleFactory.transform source = .ready target) (maxDepth : Nat)
    (sourceContext targetContext : EvalContext)
    (sourceBuilt : contextOf source maxDepth = .ok sourceContext)
    (targetBuilt : contextOf target maxDepth = .ok targetContext) :
    sourceContext.byteModel = targetContext.byteModel ∧
      sourceContext.declared = targetContext.declared := by
  have fields := (transform_ready source target actual).1
  have targetEq : target = {source with functions := target.functions} := by
    exact congrArg (fun module : Module => {module with functions := target.functions}) fields
  rw [targetEq] at targetBuilt
  obtain ⟨base, updates, sourceEq, targetEq, _replacements⟩ :=
    ModuleContext.produced_context_updates source target.functions
      (transform_produced source target actual) maxDepth sourceContext targetContext sourceBuilt targetBuilt
  rw [sourceEq, targetEq]
  have first := installFirst_runnerFields AllBlocksContext.FunctionUpdate.source base updates
  have second := installFirst_runnerFields AllBlocksContext.FunctionUpdate.target base updates
  exact ⟨first.1.trans second.1.symm, first.2.trans second.2.symm⟩

/-- Every successful real batch initialization, including its choice tape,
    already has the cleared SSA fields required by the public entry theorem. -/
theorem initialState_cleared (model : ByteModel) (count : Nat) (choices : FloatZeroChoiceTape)
    (state : MachineState)
    (actual : (initialStateForFunctionCount model count).map
      (fun state => state.withFloatZeroChoices choices) = .ok state) :
    callerWorld state = state := by
  unfold initialStateForFunctionCount at actual
  split at actual
  · simp only [Except.map, Except.ok.injEq] at actual
    rw [← actual]
    rfl
  · contradiction

/-- The actual JSON verdict forgets successful machine state. Equal public
    entry observations therefore suffice; complete errors remain unchanged. -/
theorem verdict_eq_of_entry_observe_eq
    (source target : Except SemError (List Value × MachineState))
    (same : EntryObservation.observe source = EntryObservation.observe target) :
    (fun result : Except SemError (List Value × MachineState) => match result with
      | .ok (values, _) => obj [("ok", Observation.renderGraph values)]
      | .error error => renderError error) source =
    (fun result : Except SemError (List Value × MachineState) => match result with
      | .ok (values, _) => obj [("ok", Observation.renderGraph values)]
      | .error error => renderError error) target := by
  cases source with
  | error sourceError =>
    cases target with
    | error targetError =>
      simp only [EntryObservation.observe, Except.map, Except.error.injEq] at same
      change renderError sourceError = renderError targetError
      exact congrArg renderError same
    | ok result => cases same
  | ok sourceResult =>
    rcases sourceResult with ⟨sourceValues, sourceState⟩
    cases target with
    | error error => cases same
    | ok targetResult =>
      rcases targetResult with ⟨targetValues, targetState⟩
      simp only [EntryObservation.observe, Except.map, Except.ok.injEq, Prod.mk.injEq] at same
      change obj [("ok", Observation.renderGraph sourceValues)] =
        obj [("ok", Observation.renderGraph targetValues)]
      exact congrArg (fun values => obj [("ok", Observation.renderGraph values)]) same.1

/-- Actual per-request runner equality. No successful-entry, non-poison,
    positive-resource, unique-ID or well-formed-metadata premise is added. -/
theorem transform_ready_runOneWithInitialState (source target : Module)
    (actual : ModuleFactory.transform source = .ready target) (maxDepth : Nat)
    (sourceContext targetContext : EvalContext)
    (sourceBuilt : contextOf source maxDepth = .ok sourceContext)
    (targetBuilt : contextOf target maxDepth = .ok targetContext)
    (initial : Except SemError MachineState)
    (cleared : ∀ state, initial = .ok state → callerWorld state = state)
    (fuel : Nat) (strategy : PanicStrategy) (requested : FuncId) (arguments : List Value) :
    runOneWithInitialState source sourceContext initial fuel strategy requested arguments =
      runOneWithInitialState target targetContext initial fuel strategy requested arguments := by
  have related := ModuleEntryEffects.transform_ready_entryEffects source target actual maxDepth
    sourceContext targetContext sourceBuilt targetBuilt
  obtain ⟨models, declarations⟩ := transform_ready_runnerFields source target actual maxDepth
    sourceContext targetContext sourceBuilt targetBuilt
  simp only [runOneWithInitialState_eq_original]
  rw [transform_ready_reachableDecodeFailure source target actual requested]
  cases preflight : reachableDecodeFailure target requested with
  | some error => rfl
  | none =>
    simp only
    have headers := related.headers requested
    cases sourceFound : sourceContext.functions requested with
    | none =>
      cases targetFound : targetContext.functions requested with
      | none => simp only [declarations]
      | some function => rw [sourceFound, targetFound] at headers; cases headers
    | some sourceFunction =>
      cases targetFound : targetContext.functions requested with
      | none => rw [sourceFound, targetFound] at headers; cases headers
      | some targetFunction =>
        rw [sourceFound, targetFound] at headers
        cases headers with
        | present _ _ body _ =>
          cases initialized : initial with
          | error error => rfl
          | ok state =>
            simp only
            have argumentsEq : targetScalarArguments sourceContext sourceFunction.body.paramTys arguments =
                targetScalarArguments targetContext targetFunction.body.paramTys arguments := by
              simp only [targetScalarArguments, models, body]
            rw [argumentsEq]
            cases adapted : targetScalarArguments targetContext targetFunction.body.paramTys arguments with
            | error error => rfl
            | ok args =>
              simp only
              have observation := ModuleEntryEffects.transform_ready_entry_observe_eq source target actual maxDepth
                sourceContext targetContext sourceBuilt targetBuilt requested args fuel strategy state
              rw [cleared state initialized] at observation
              exact verdict_eq_of_entry_observe_eq _ _ observation

/-- Logical JSON equality for the ACTUAL decoded batch runner and ACTUAL
    module factory. Requests and per-request choice tapes remain identical.
    This does not assert correctness of compiled unsafe observation caching,
    parsing/serialization, native execution, or raw program_refines. -/
theorem transform_ready_runBatch (source target : Module)
    (actual : ModuleFactory.transform source = .ready target)
    (fuel callDepth : Nat) (strategy : PanicStrategy) (batch : Batch)
    (moduleEq : batch.module = source) :
    runBatch fuel callDepth strategy batch =
      runBatch fuel callDepth strategy {batch with module := target} := by
  have constructed := ModuleContext.transform_ready_context_calls source target actual callDepth
  cases sourceBuilt : contextOf source callDepth with
  | error sourceError =>
    cases targetBuilt : contextOf target callDepth with
    | error targetError =>
      rw [sourceBuilt, targetBuilt] at constructed
      change sourceError = targetError at constructed
      simp only [runBatch_eq_original, moduleEq, sourceBuilt, targetBuilt, constructed]
    | ok targetContext => rw [sourceBuilt, targetBuilt] at constructed; cases constructed
  | ok sourceContext =>
    cases targetBuilt : contextOf target callDepth with
    | error error => rw [sourceBuilt, targetBuilt] at constructed; cases constructed
    | ok targetContext =>
      have models := (transform_ready_runnerFields source target actual callDepth
        sourceContext targetContext sourceBuilt targetBuilt).1
      have counts := congrArg List.length (transform_headers source target actual)
      simp only [List.length_map] at counts
      simp only [runBatch_eq_original, moduleEq, sourceBuilt, targetBuilt]
      rw [← models, counts]
      apply congrArg Lean.Json.arr
      apply congrArg List.toArray
      apply congrArg (fun render : Nat × (FuncId × List Value) → Lean.Json => (trustIrEntryEnumFrom 0 batch.runs).map render)
      funext row
      rcases row with ⟨index, requested, arguments⟩
      exact transform_ready_runOneWithInitialState source target actual callDepth
        sourceContext targetContext sourceBuilt targetBuilt _
        (initialState_cleared sourceContext.byteModel source.functions.length
          (FloatZeroChoiceTape.ofList (batch.floatZeroChoices.getD index [])))
        fuel strategy requested arguments

end TrustIrEval.ModuleRunBatch

-- These representation bridges must be constructive on both pinned compilers.
#trustIrAxiomsExact TrustIrEval.ModuleRunBatch.blocksDrop_cons == []
#trustIrAxiomsExact TrustIrEval.ModuleRunBatch.expandedEntry_blockDrops == []
