-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Whole-program refinement with recursive calls and full outcomes.

import TrustIr.Proofs.TransformRefinementCtx
import TrustIr.Proofs.GenericCoroPrefixBody

namespace TrustIr

/-!
Rewriting every function body is related by induction on the actual
interprocedural evaluator, including recursive calls, SeqMap element calls,
tail calls and invoke continuations. The run relation keeps both resource
budgets and the complete result/state/error, except where the source is UB.
The entry theorem lifts that relation to all `BehavesFn` outcomes, including
divergence. These theorems use the ratified abort strategy.
-/

-- =================================================================
-- Whole function-table rewrite: UB-exploiting elimination of Unreachable
-- =================================================================

/-- Proof-only wrapper: the evaluator walk must not introduce the state
    quantifier inside `RunsLikeUnlessUB` before it reaches a leaf. -/
private structure ProgramRunRelation {α : Type} (target source : Sem α) : Prop where
  run : RunsLikeUnlessUB target source

private theorem ProgramRunRelation.refl {α : Type} (m : Sem α) : ProgramRunRelation m m :=
  ⟨RunsLikeUnlessUB.refl m⟩

private theorem ProgramRunRelation.seq {α β : Type} {target source : Sem α}
    {targetNext sourceNext : α → Sem β}
    (h : ProgramRunRelation target source)
    (hNext : ∀ x, ProgramRunRelation (targetNext x) (sourceNext x)) :
    ProgramRunRelation (target >>= targetNext) (source >>= sourceNext) :=
  ⟨RunsLikeUnlessUB.bind h.run (fun x => (hNext x).run)⟩

/-- Abstract a shared prefix before comparing its potentially large
    continuations. This includes prefix errors and the complete state. -/
private theorem ProgramRunRelation.samePrefix {α β : Type} (common : Sem α)
    {targetNext sourceNext : α → Sem β}
    (hNext : ∀ x, ProgramRunRelation (targetNext x) (sourceNext x)) :
    ProgramRunRelation (common >>= targetNext) (common >>= sourceNext) :=
  ProgramRunRelation.seq (ProgramRunRelation.refl _) hNext

private theorem ProgramRunRelation.lookupBind {α : Type} (id : ValueId)
    (targetNext sourceNext : Value → Sem α)
    (next : ∀ value, ProgramRunRelation (targetNext value) (sourceNext value)) :
    ProgramRunRelation (Sem.lookupValue id >>= targetNext) (Sem.lookupValue id >>= sourceNext) :=
  ProgramRunRelation.samePrefix _ next

private theorem ProgramRunRelation.of_ub {α : Type} {target source : Sem α}
    (h : ∀ s, ∃ message, Sem.run source s = .error (.ub message)) :
    ProgramRunRelation target source := ⟨RunsLikeUnlessUB.of_ub h⟩

/-- An identical complete error erases both continuations before their
    recursive evaluator contexts need to be compared. -/
private theorem ProgramRunRelation.errorBind {α β : Type} (error : SemError)
    (targetNext sourceNext : α → Sem β) :
    ProgramRunRelation ((throw error : Sem α) >>= targetNext)
      ((throw error : Sem α) >>= sourceNext) := ⟨fun _ => Or.inl rfl⟩

private theorem ProgramRunRelation.sameError {α : Type} (error : SemError) :
    ProgramRunRelation (throw error : Sem α) (throw error : Sem α) :=
  ProgramRunRelation.refl _

/-- An error stops before either continuation, including the hypothetical
    callee returned by a missing raw lookup. -/
private theorem ProgramRunRelation.typeErrorBind {α β : Type} (message : String)
    (targetNext sourceNext : α → Sem β) :
    ProgramRunRelation
      (Sem.throwTypeError message >>= targetNext)
      (Sem.throwTypeError message >>= sourceNext) := ⟨fun _ => Or.inl rfl⟩

private theorem ProgramRunRelation.loop {α β : Type} (values : List α) (initial : β)
    {targetBody sourceBody : α → β → Sem (ForInStep β)}
    (h : ∀ x acc, ProgramRunRelation (targetBody x acc) (sourceBody x acc)) :
    ProgramRunRelation (forIn values initial targetBody) (forIn values initial sourceBody) := by
  induction values generalizing initial with
  | nil =>
    simp only [List.forIn_nil]
    exact ProgramRunRelation.refl _
  | cons x rest ih =>
    simp only [List.forIn_cons]
    refine ProgramRunRelation.seq (h x initial) (fun result => ?_)
    cases result with
    | done final => exact ProgramRunRelation.refl _
    | yield next => exact ih next

/-- A direct lookup is a common source prefix. Its returned function is
    mapped only inside the target continuation, where the callee induction
    hypothesis can see the rewritten CFG. -/
private theorem ProgramRunRelation.directLookup {α : Type}
    (transform : CFG → CFG) (ctx : EvalContext) (id : FuncId)
    (declaredMessage missingMessage : String)
    {targetNext sourceNext : EvalFunction → Sem α}
    (hNext : ∀ function, ProgramRunRelation
      (targetNext { function with cfg := transform function.cfg }) (sourceNext function)) :
    ProgramRunRelation
      ((mapFunctionCFGs transform ctx).lookupDirectCallee id declaredMessage missingMessage >>= targetNext)
      (ctx.lookupDirectCallee id declaredMessage missingMessage >>= sourceNext) := by
  rw [lookupDirectCallee_mapFunctionCFGs]
  simp only [bind_assoc, pure_bind]
  exact ProgramRunRelation.seq (ProgramRunRelation.refl _) hNext

/-- Raw function-table lookups use the same source option discriminator;
    neither the lookup prefix nor a successful header check assumes that
    the rewritten callee's execution succeeds. -/
private theorem ProgramRunRelation.functionLookup {α : Type}
    (transform : CFG → CFG) (ctx : EvalContext) (id : FuncId) (missingMessage : String)
    {targetNext sourceNext : EvalFunction → Sem α}
    (hNext : ∀ function, ProgramRunRelation
      (targetNext { function with cfg := transform function.cfg }) (sourceNext function)) :
    ProgramRunRelation
      ((match (mapFunctionCFGs transform ctx).functions id with
        | some function => pure function | none => Sem.throwTypeError missingMessage) >>= targetNext)
      ((match ctx.functions id with
        | some function => pure function | none => Sem.throwTypeError missingMessage) >>= sourceNext) := by
  cases hFunction : ctx.functions id with
  | none =>
    simp only [mapFunctionCFGs, hFunction, Option.map]
    exact ⟨fun _ => Or.inl rfl⟩
  | some function =>
    simp only [mapFunctionCFGs, hFunction, Option.map, pure_bind]
    exact hNext function

/-- Lean's do elaborator also distributes a lookup match over its whole
    continuation. Relate those matches by splitting the source table once. -/
private theorem ProgramRunRelation.functionCases {α : Type}
    (transform : CFG → CFG) (ctx : EvalContext) (id : FuncId)
    {targetNone sourceNone : Sem α} {targetSome sourceSome : EvalFunction → Sem α}
    (hNone : ctx.functions id = none → ProgramRunRelation targetNone sourceNone)
    (hSome : ∀ function, ProgramRunRelation
      (targetSome { function with cfg := transform function.cfg }) (sourceSome function)) :
    ProgramRunRelation
      (match (mapFunctionCFGs transform ctx).functions id with
       | some function => targetSome function | none => targetNone)
      (match ctx.functions id with
       | some function => sourceSome function | none => sourceNone) := by
  cases hFunction : ctx.functions id with
  | none => simpa only [mapFunctionCFGs, hFunction, Option.map] using hNone hFunction
  | some function =>
    simpa only [mapFunctionCFGs, hFunction, Option.map] using hSome function

/-- Nominal resolution returns the genuinely mapped callee, while every
    undefined/bodyless/retained-error result is preserved exactly. -/
private theorem resolvedItem_map (transform : CFG → CFG) (ctx : EvalContext) (id : FuncId) :
    resolveFunctionItemBody (mapFunctionCFGs transform ctx) id =
      (resolveFunctionItemBody ctx id).map (fun function => {function with cfg := transform function.cfg}) := by
  cases present : ctx.functions id with
  | some function => simp only [resolveFunctionItemBody, mapFunctionCFGs, present, Option.map, Except.map]
  | none =>
    simp only [resolveFunctionItemBody, mapFunctionCFGs, present, Option.map]
    cases failed : ctx.functionErrors id with
    | some error => rfl
    | none =>
      dsimp only
      split <;> rfl

private theorem ProgramRunRelation.itemLookup {α : Type}
    (transform : CFG → CFG) (ctx : EvalContext) (id : FuncId)
    {targetNext sourceNext : EvalFunction → Sem α}
    (next : ∀ function, ProgramRunRelation
      (targetNext {function with cfg := transform function.cfg}) (sourceNext function)) :
    ProgramRunRelation
      (Sem.fromMemoryExcept (resolveFunctionItemBody (mapFunctionCFGs transform ctx) id) >>= targetNext)
      (Sem.fromMemoryExcept (resolveFunctionItemBody ctx id) >>= sourceNext) := by
  rw [resolvedItem_map]
  cases result : resolveFunctionItemBody ctx id with
  | error error => exact ProgramRunRelation.errorBind error _ _
  | ok function => simpa only [Except.map, Sem.fromMemoryExcept, pure_bind] using next function

private theorem missingItem_not_ok (ctx : EvalContext) (id : FuncId)
    (missing : ctx.functions id = none) :
    ∀ function, resolveFunctionItemBody ctx id ≠ .ok function := by
  intro function
  cases failed : ctx.functionErrors id with
  | some error =>
    simp only [resolveFunctionItemBody, missing, failed]
    intro impossible
    cases impossible
  | none =>
    simp only [resolveFunctionItemBody, missing, failed]
    split <;> intro impossible <;> cases impossible

/-- A real absent-row branch cannot invent a successful callee. Erase both
    continuations using that branch fact and retain the complete error. -/
private theorem ProgramRunRelation.missingItemLookup {α : Type}
    (ctx : EvalContext) (id : FuncId) (missing : ctx.functions id = none)
    (targetNext sourceNext : EvalFunction → Sem α) :
    ProgramRunRelation
      (Sem.fromMemoryExcept (resolveFunctionItemBody (mapFunctionCFGs unreachableToReturn ctx) id) >>= targetNext)
      (Sem.fromMemoryExcept (resolveFunctionItemBody ctx id) >>= sourceNext) := by
  rewrite [resolvedItem_map]
  cases result : resolveFunctionItemBody ctx id with
  | error error => exact ProgramRunRelation.sameError error
  | ok function => exact False.elim (missingItem_not_ok ctx id missing function result)

/-- Discharge the evaluator's instruction dispatch with abstract handlers.
    Constructor reduction keeps its large continuations out of generated
    matcher-equation declarations. -/
private theorem ProgramRunRelation.bodyDispatch (inst : Inst)
    (targetCall sourceCall : FuncId → List ValueId → Sem (ForInStep Unit))
    (targetIndirect sourceIndirect : ValueId → FuncTyId → List ValueId → CallingConv → Sem (ForInStep Unit))
    (targetAssert sourceAssert : Sem (ForInStep Unit))
    (targetPad sourcePad : Bool → List Nat → Sem (ForInStep Unit))
    (targetOther sourceOther : Sem (ForInStep Unit))
    (calls : ∀ callee args, inst = .Call callee args →
      ProgramRunRelation (targetCall callee args) (sourceCall callee args))
    (indirect : ∀ callee sig args conv, inst = .CallIndirect callee sig args conv →
      ProgramRunRelation (targetIndirect callee sig args conv) (sourceIndirect callee sig args conv))
    (assertion : ProgramRunRelation targetAssert sourceAssert)
    (pad : ∀ cleanup clauses, inst = .LandingPad cleanup clauses →
      ProgramRunRelation (targetPad cleanup clauses) (sourcePad cleanup clauses))
    (other : ProgramRunRelation targetOther sourceOther) :
    ProgramRunRelation
      (GenericCoro.Prefix.bodyDispatch targetCall targetIndirect targetAssert targetPad targetOther inst)
      (GenericCoro.Prefix.bodyDispatch sourceCall sourceIndirect sourceAssert sourcePad sourceOther inst) := by
  cases inst <;> first
    | exact calls _ _ rfl
    | exact indirect _ _ _ _ rfl
    | exact assertion
    | exact pad _ _ rfl
    | exact other

private theorem checkClosureValue_mapFunctionCFGs (transform : CFG → CFG)
    (ctx : EvalContext) (ty : Ty) (v : Value) :
    checkClosureValue (mapFunctionCFGs transform ctx) ty v = checkClosureValue ctx ty v :=
  checkClosureValue_withFunctions ctx _ ty v

private theorem abortTerm_mapFunctionCFGs (transform : CFG → CFG)
    (ctx : EvalContext) (depth : Nat) (source target : CFG) (term : Inst) :
    stepTermWithContext (mapFunctionCFGs transform ctx) depth target term .abort =
      stepTermWithContext ctx depth source term .abort := by
  rw [stepTermWithContext_mapFunctionCFGs]
  rfl

private theorem abortTerm_unreachable (ctx : EvalContext) (depth : Nat) (cfg : CFG) :
    stepTermWithContext ctx depth cfg .Unreachable .abort = pure (.terminator .Stuck) := rfl

private theorem ProgramRunRelation.abortTerm (transform : CFG → CFG)
    (ctx : EvalContext) (depth : Nat) (source target : CFG) (term : Inst) :
    ProgramRunRelation
      (stepTermWithContext (mapFunctionCFGs transform ctx) depth target term .abort)
      (stepTermWithContext ctx depth source term .abort) := by
  rw [abortTerm_mapFunctionCFGs transform ctx depth source target term]
  exact ProgramRunRelation.refl _

private theorem resolveBlock_map_def (transform : CFG → CFG) (ctx : EvalContext) (block : BasicBlock) :
    (mapFunctionCFGs transform ctx).resolveBlock block = ctx.resolveBlock block := rfl

private theorem resolveDrop_map_def (transform : CFG → CFG) (ctx : EvalContext) (inst : Inst) :
    (mapFunctionCFGs transform ctx).resolveDrop inst = ctx.resolveDrop inst := rfl

private theorem semPureBind {α β : Type} (value : α) (next : α → Sem β) :
    ((pure value : Sem α) >>= next) = next value := rfl

private theorem ProgramRunRelation.stepInst (transform : CFG → CFG) (ctx : EvalContext) (inst : Inst) :
    ProgramRunRelation (stepInstWithContext (mapFunctionCFGs transform ctx) inst)
      (stepInstWithContext ctx inst) := by
  rw [stepInstWithContext_mapFunctionCFGs]
  exact ProgramRunRelation.refl _

private theorem ProgramRunRelation.raiseStep (transform : CFG → CFG) (ctx : EvalContext) (inst : Inst) :
    ProgramRunRelation
      (raiseIfUnwind .abort (stepInstWithContext (mapFunctionCFGs transform ctx) inst)
        ctx.byteModel)
      (raiseIfUnwind .abort (stepInstWithContext ctx inst) ctx.byteModel) := by
  rw [stepInstWithContext_mapFunctionCFGs]
  exact ProgramRunRelation.refl _

private theorem ProgramRunRelation.pad (transform : CFG → CFG) (ctx : EvalContext)
    (inst : Inst) (dests : List ValueId) :
    ProgramRunRelation (semLandingPadWith .abort (mapFunctionCFGs transform ctx) inst dests)
      (semLandingPadWith .abort ctx inst dests) := by
  rw [semLandingPadWith_mapFunctionCFGs]
  exact ProgramRunRelation.refl _

/-- Preserve an opaque instruction action before considering its result
    continuation. No opcode, value or successful result is excluded. -/
private theorem ProgramRunRelation.stepInstBind {α : Type} (transform : CFG → CFG)
    (ctx : EvalContext) (inst : Inst) (targetNext sourceNext : InstrResult → Sem α)
    (next : ∀ result, ProgramRunRelation (targetNext result) (sourceNext result)) :
    ProgramRunRelation
      (stepInstWithContext (mapFunctionCFGs transform ctx) inst >>= targetNext)
      (stepInstWithContext ctx inst >>= sourceNext) :=
  ProgramRunRelation.seq (ProgramRunRelation.stepInst transform ctx inst) next

private theorem ProgramRunRelation.raiseStepBind {α : Type} (transform : CFG → CFG)
    (ctx : EvalContext) (inst : Inst) (targetNext sourceNext : InstrResult → Sem α)
    (next : ∀ result, ProgramRunRelation (targetNext result) (sourceNext result)) :
    ProgramRunRelation
      (raiseIfUnwind .abort (stepInstWithContext (mapFunctionCFGs transform ctx) inst)
        ctx.byteModel >>= targetNext)
      (raiseIfUnwind .abort (stepInstWithContext ctx inst) ctx.byteModel >>= sourceNext) :=
  ProgramRunRelation.seq (ProgramRunRelation.raiseStep transform ctx inst) next

private theorem ProgramRunRelation.invokeAbortBind {α : Type}
    {target source : Sem (List Value)}
    {targetNext sourceNext : (List Value ⊕ (Addr × MachineState)) → Sem α}
    (hCall : ProgramRunRelation target source)
    (hNext : ∀ values, ProgramRunRelation (targetNext (.inl values)) (sourceNext (.inl values))) :
    ProgramRunRelation (invokeCatch .abort target >>= targetNext)
      (invokeCatch .abort source >>= sourceNext) := by
  simp only [invokeCatch, bind_assoc, pure_bind]
  exact ProgramRunRelation.seq hCall hNext

private theorem mapFunctionCFGs_byteModel (transform : CFG → CFG) (ctx : EvalContext) :
    (mapFunctionCFGs transform ctx).byteModel = ctx.byteModel := rfl

private theorem mapFunctionCFGs_funcPtrs (transform : CFG → CFG) (ctx : EvalContext) :
    (mapFunctionCFGs transform ctx).funcPtrs = ctx.funcPtrs := rfl

private theorem mapFunctionCFGs_functionOrder (transform : CFG → CFG) (ctx : EvalContext) :
    (mapFunctionCFGs transform ctx).functionOrder = ctx.functionOrder := rfl

private theorem mapFunctionCFGs_funcTys (transform : CFG → CFG) (ctx : EvalContext) :
    (mapFunctionCFGs transform ctx).funcTys = ctx.funcTys := rfl

private theorem mapFunctionCFGs_maxCallDepth (transform : CFG → CFG) (ctx : EvalContext) :
    (mapFunctionCFGs transform ctx).maxCallDepth = ctx.maxCallDepth := rfl

private theorem mapFunctionCFGs_returnTypes (transform : CFG → CFG) (ctx : EvalContext) :
    (mapFunctionCFGs transform ctx).functionReturnTypes = ctx.functionReturnTypes := rfl

private theorem mapFunctionCFGs_currentFunction (transform : CFG → CFG) (ctx : EvalContext) :
    (mapFunctionCFGs transform ctx).currentFunction = ctx.currentFunction := rfl

/-- Nominal validation is a pure prefix; compare it while continuations
    remain abstract instead of searching inside the evaluator walk. -/
private theorem ProgramRunRelation.itemValuesBind {α : Type} (ctx : EvalContext)
    (types : List Ty) (values : List Value) (targetNext sourceNext : Unit → Sem α)
    (next : ∀ result, ProgramRunRelation (targetNext result) (sourceNext result)) :
    ProgramRunRelation
      (Sem.fromMemoryExcept (checkFunctionItemValues (mapFunctionCFGs unreachableToReturn ctx) types values) >>= targetNext)
      (Sem.fromMemoryExcept (checkFunctionItemValues ctx types values) >>= sourceNext) := by
  rewrite [checkFunctionItemValues_mapFunctionCFGs]
  exact ProgramRunRelation.samePrefix _ next

private theorem ProgramRunRelation.itemCalleeBind {α : Type} (ctx : EvalContext)
    (operand : ValueId) (value : Value) (targetNext sourceNext : Unit → Sem α)
    (next : ∀ result, ProgramRunRelation (targetNext result) (sourceNext result)) :
    ProgramRunRelation
      (Sem.fromMemoryExcept (checkFunctionItemCalleeType (mapFunctionCFGs unreachableToReturn ctx) operand value) >>= targetNext)
      (Sem.fromMemoryExcept (checkFunctionItemCalleeType ctx operand value) >>= sourceNext) := by
  rewrite [checkFunctionItemCalleeType_mapFunctionCFGs]
  exact ProgramRunRelation.samePrefix _ next

/-- Expose only the changed terminator, so the instruction loop is proved
    once before splitting on whether the block ends in Unreachable. -/
private def resolvedUnreachableToReturnTerm (ctx : EvalContext) : Inst → Inst
  | .Unreachable => .Return []
  | term => ctx.resolveDrop term

private theorem resolveBlock_unreachableToReturnBlock (ctx : EvalContext)
    (block : BasicBlock) :
    ctx.resolveBlock (unreachableToReturnBlock block) =
      { (ctx.resolveBlock block) with terminator :=
          resolvedUnreachableToReturnTerm ctx block.terminator } := by
  rcases block with ⟨params, body, bodyDests, term, termDests⟩
  unfold unreachableToReturnBlock resolvedUnreachableToReturnTerm EvalContext.resolveBlock
  cases term <;> rfl

private theorem ProgramRunRelation.stuck {α : Type} (target : Sem α) (message : String) :
    ProgramRunRelation target (Sem.throwUB message) :=
  ProgramRunRelation.of_ub (fun _ => ⟨message, rfl⟩)

/-- Walk already-outlined monadic handlers. The actual evaluator, source
    contexts and exact recursive hypothesis remain the only inputs. -/
macro "program_walk " ctx:term " using " ih:term : tactic =>
  `(tactic| repeat' (first
          | intro _
          | with_reducible exact ProgramRunRelation.sameError _
          | with_reducible exact ProgramRunRelation.typeErrorBind _ _ _
          | with_reducible refine ProgramRunRelation.missingItemLookup $ctx _ (by assumption) _ _
          | with_reducible exact ProgramRunRelation.errorBind _ _ _
          | with_reducible exact $ih _ _ _ _ _
          | with_reducible refine ProgramRunRelation.itemLookup unreachableToReturn $ctx _ ?_
          | with_reducible refine ProgramRunRelation.directLookup unreachableToReturn $ctx _ _ _ ?_
          | with_reducible refine ProgramRunRelation.functionLookup unreachableToReturn $ctx _ _ ?_
          | with_reducible refine ProgramRunRelation.functionCases unreachableToReturn $ctx _ ?_ ?_
          | with_reducible refine ProgramRunRelation.stepInstBind unreachableToReturn $ctx _ _ _ ?_
          | with_reducible refine ProgramRunRelation.raiseStepBind unreachableToReturn $ctx _ _ _ ?_
          | with_reducible refine ProgramRunRelation.itemValuesBind $ctx _ _ _ _ ?_
          | with_reducible refine ProgramRunRelation.itemCalleeBind $ctx _ _ _ _ ?_
          | rewrite [lookupFunctionHeader_mapFunctionCFGs]
          | rewrite [checkFunctionItemValues_mapFunctionCFGs]
          | rewrite [checkFunctionItemCalleeType_mapFunctionCFGs]
          | rewrite [functionItemCall_mapFunctionCFGs]
          | rewrite [checkSeqMapElement_mapFunctionCFGs]
          | rewrite [memoryLayout_mapFunctionCFGs]
          | rewrite [storeMemoryValue_mapFunctionCFGs]
          | rewrite [loadMemoryValue_mapFunctionCFGs]
          | rewrite [functionErrors_mapFunctionCFGs]
          | rewrite [functionHeader_matches_mapCFG]
          | rewrite [bindCallResults_mapFunctionCFGs]
          | rewrite [bindInstructionResults_mapFunctionCFGs]
          | with_reducible refine ProgramRunRelation.samePrefix _ ?_
          | with_reducible exact ProgramRunRelation.refl _
          | dsimp only [semPureBind, mapFunctionCFGs_byteModel, mapFunctionCFGs_funcPtrs,
              mapFunctionCFGs_functionOrder,
              mapFunctionCFGs_funcTys, mapFunctionCFGs_returnTypes,
              mapFunctionCFGs_currentFunction, resolveDrop_map_def]
          | (rw [forFunction_mapFunctionCFGs]; dsimp only [EvalContext.forFunction])
          | rewrite [functionCallWithConvention_mapFunctionCFGs]
          | rewrite [closureCall_mapFunctionCFGs]
          | (rw [forFunction_mapFunctionCFGs]; dsimp only [EvalContext.forFunction])
          | rewrite [checkClosureValue_mapFunctionCFGs]
          | with_reducible exact ProgramRunRelation.stepInst unreachableToReturn $ctx _
          | with_reducible exact ProgramRunRelation.raiseStep unreachableToReturn $ctx _
          | with_reducible exact ProgramRunRelation.pad unreachableToReturn $ctx _ _
          | simp only [bind_assoc]
          | refine ProgramRunRelation.directLookup unreachableToReturn $ctx _ _ _ ?_
          | refine ProgramRunRelation.functionCases unreachableToReturn $ctx _ ?_ ?_
          | refine ProgramRunRelation.functionLookup unreachableToReturn $ctx _ _ ?_
          | with_reducible refine ProgramRunRelation.seq ?_ ?_
          | with_reducible refine ProgramRunRelation.loop _ _ ?_
          | with_reducible refine ProgramRunRelation.loopAux ?_ _ _
          | intro _
          | dsimp only
          | refine ProgramRunRelation.functionCases unreachableToReturn $ctx _ ?_ ?_
          | refine ProgramRunRelation.functionLookup unreachableToReturn $ctx _ _ ?_
          | split))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- Rewriting every function body, including recursively called and SeqMap
    callees, preserves the complete abort run unless the original run is UB.
    Fuel and call depth are unchanged; no returning-only premise is used. -/
private theorem stepNWithContext_mapUnreachableToReturn_aux (ctx : EvalContext) :
    ∀ (fuel depth : Nat) (cfg : CFG) (pc : BlockId) (args : List Value),
      ProgramRunRelation
        (stepNWithContext (mapFunctionCFGs unreachableToReturn ctx) fuel depth
          (unreachableToReturn cfg) pc args .abort)
        (stepNWithContext ctx fuel depth cfg pc args .abort) := by
  intro fuel
  induction fuel generalizing ctx with
  | zero =>
    intro depth cfg pc args
    unfold stepNWithContext
    exact ProgramRunRelation.refl _
  | succ n ih =>
    intro depth cfg pc args
    have hTarget : (unreachableToReturn cfg) pc = (cfg pc).map unreachableToReturnBlock := rfl
    rewrite [GenericCoro.Prefix.stepNWithContext_succ_layer,
      GenericCoro.Prefix.stepNWithContext_succ_layer]
    unfold GenericCoro.Prefix.evalLayer
    rw [hTarget]
    cases _hBlock : cfg pc with
    | none => exact ProgramRunRelation.refl _
    | some block =>
      dsimp (config := { zeta := false }) only [Option.map, resolveBlock_map_def]
      rw [resolveBlock_unreachableToReturnBlock]
      dsimp only
      rw [checkFunctionItemValues_mapFunctionCFGs]
      refine ProgramRunRelation.samePrefix _ ?_
      intro _
      refine ProgramRunRelation.seq (ProgramRunRelation.refl _) ?_
      intro _
      refine ProgramRunRelation.seq ?_ ?_
      · -- Use the exact outlined handlers, with constructor identity kept
        -- in the dispatch premise instead of inferred from a huge match.
        unfold GenericCoro.Prefix.evalBody
        refine ProgramRunRelation.loop _ _ ?_
        intro bodyInst _acc
        rcases bodyInst with ⟨inst, resultDests⟩
        rewrite [GenericCoro.Prefix.evalBodyStep_dispatch,
          GenericCoro.Prefix.evalBodyStep_dispatch]
        apply ProgramRunRelation.bodyDispatch inst
        · intro callee callArgs constructor
          subst inst
          unfold GenericCoro.Prefix.bodyCall GenericCoro.callFrame GenericCoro.finishCall
          program_walk ctx using ih
        · intro callee signature callArgs convention constructor
          subst inst
          unfold GenericCoro.Prefix.bodyIndirect
          refine ProgramRunRelation.lookupBind _ _ _ ?_
          intro held
          refine ProgramRunRelation.itemCalleeBind ctx _ held _ _ ?_
          intro _
          cases held <;> dsimp only [GenericCoro.Prefix.indirectAddress,
            GenericCoro.Prefix.deferredIndirectArguments, GenericCoro.Prefix.indirectArguments,
            GenericCoro.Prefix.rawIndirectArguments]
          all_goals unfold GenericCoro.Prefix.callFrameWith GenericCoro.Prefix.finishCalleeWith GenericCoro.Prefix.checkReturns
          all_goals program_walk ctx using ih
        · program_walk ctx using ih
        · intro cleanup clauses constructor
          subst inst
          program_walk ctx using ih
        · unfold GenericCoro.Prefix.producedStep GenericCoro.Prefix.seqMapStep
          program_walk ctx using ih
      · intro _
        unfold resolvedUnreachableToReturnTerm
        split
        · rename_i hTerm
          simp only [resolveDrop_mapFunctionCFGs, EvalContext.resolveBlock, hTerm,
            EvalContext.resolveDrop, abortTerm_unreachable, pure_bind]
          exact ProgramRunRelation.stuck _ _
        · dsimp only [EvalContext.resolveBlock, resolveDrop_map_def]
          repeat' (first
            | intro _
            | with_reducible exact ProgramRunRelation.sameError _
            | with_reducible exact ProgramRunRelation.typeErrorBind _ _ _
            | with_reducible refine ProgramRunRelation.missingItemLookup ctx _ (by assumption) _ _
            | with_reducible exact ProgramRunRelation.errorBind _ _ _
            | with_reducible exact ih _ _ _ _ _
            | with_reducible exact ProgramRunRelation.abortTerm unreachableToReturn ctx _ _ _ _
            | with_reducible refine ProgramRunRelation.itemLookup unreachableToReturn ctx _ ?_
            | with_reducible refine ProgramRunRelation.directLookup unreachableToReturn ctx _ _ _ ?_
            | with_reducible refine ProgramRunRelation.functionLookup unreachableToReturn ctx _ _ ?_
            | with_reducible refine ProgramRunRelation.functionCases unreachableToReturn ctx _ ?_ ?_
            | with_reducible refine ProgramRunRelation.stepInstBind unreachableToReturn ctx _ _ _ ?_
            | with_reducible refine ProgramRunRelation.raiseStepBind unreachableToReturn ctx _ _ _ ?_
            | with_reducible refine ProgramRunRelation.itemValuesBind ctx _ _ _ _ ?_
            | with_reducible refine ProgramRunRelation.itemCalleeBind ctx _ _ _ _ ?_
            | rewrite [lookupFunctionHeader_mapFunctionCFGs]
            | rewrite [checkFunctionItemValues_mapFunctionCFGs]
            | rewrite [checkFunctionItemCalleeType_mapFunctionCFGs]
            | rewrite [functionItemCall_mapFunctionCFGs]
            | rewrite [checkSeqMapElement_mapFunctionCFGs]
            | rewrite [functionErrors_mapFunctionCFGs]
            | rewrite [functionHeader_matches_mapCFG]
            | rewrite [bindCallResults_mapFunctionCFGs]
            | rewrite [bindInstructionResults_mapFunctionCFGs]
            | with_reducible refine ProgramRunRelation.samePrefix _ ?_
            | with_reducible exact ProgramRunRelation.refl _
            | dsimp only [semPureBind, mapFunctionCFGs_byteModel, mapFunctionCFGs_funcPtrs,
                mapFunctionCFGs_functionOrder,
                mapFunctionCFGs_funcTys, mapFunctionCFGs_returnTypes,
              mapFunctionCFGs_currentFunction, resolveDrop_map_def]
            | (rw [forFunction_mapFunctionCFGs]; dsimp only [EvalContext.forFunction])
            | rewrite [checkClosureValue_mapFunctionCFGs]
            | with_reducible refine ProgramRunRelation.invokeAbortBind ?_ ?_
            | exact ProgramRunRelation.abortTerm unreachableToReturn ctx _ _ _ _
            | simp only [bind_assoc]
            | refine ProgramRunRelation.directLookup unreachableToReturn ctx _ _ _ ?_
            | refine ProgramRunRelation.functionCases unreachableToReturn ctx _ ?_ ?_
            | refine ProgramRunRelation.functionLookup unreachableToReturn ctx _ _ ?_
            | with_reducible refine ProgramRunRelation.seq ?_ ?_
            | with_reducible refine ProgramRunRelation.loop _ _ ?_
            | with_reducible refine ProgramRunRelation.loopAux ?_ _ _
            | intro _
            | dsimp only
            | refine ProgramRunRelation.functionCases unreachableToReturn ctx _ ?_ ?_
            | refine ProgramRunRelation.functionLookup unreachableToReturn ctx _ _ ?_
            | split)
/-- The full evaluator relation for the function-table rewrite. The target
    rewrites both the current CFG and every callee's CFG. -/
theorem stepNWithContext_mapUnreachableToReturn (ctx : EvalContext)
    (fuel depth : Nat) (cfg : CFG) (pc : BlockId) (args : List Value) :
    RunsLikeUnlessUB
      (stepNWithContext (mapFunctionCFGs unreachableToReturn ctx) fuel depth
        (unreachableToReturn cfg) pc args .abort)
      (stepNWithContext ctx fuel depth cfg pc args .abort) :=
  (stepNWithContext_mapUnreachableToReturn_aux ctx fuel depth cfg pc args).run

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- At a real entry the same relation preserves argument and return checks,
    caller state and the exact resource budgets, with rewritten callees. -/
theorem evalFunctionInContext_mapUnreachableToReturn (ctx : EvalContext)
    (entry : FuncId) (args : List Value) (fuel : Nat) :
    RunsLikeUnlessUB
      (evalFunctionInContext (mapFunctionCFGs unreachableToReturn ctx) entry args fuel .abort)
      (evalFunctionInContext ctx entry args fuel .abort) := by
  have h : ProgramRunRelation
      (evalFunctionInContext (mapFunctionCFGs unreachableToReturn ctx) entry args fuel .abort)
      (evalFunctionInContext ctx entry args fuel .abort) := by
    unfold evalFunctionInContext
    simp only [pure_bind]
    refine ProgramRunRelation.functionCases unreachableToReturn ctx entry ?_ ?_
    · intro _
      exact ProgramRunRelation.refl _
    intro function
    repeat' (first
      | rw [checkFunctionItemValues_mapFunctionCFGs]
      | with_reducible exact ProgramRunRelation.refl _
      | with_reducible exact ProgramRunRelation.errorBind _ _ _
      | with_reducible exact ProgramRunRelation.typeErrorBind _ _ _
      | with_reducible exact stepNWithContext_mapUnreachableToReturn_aux _ _ _ _ _ _
      | with_reducible refine ProgramRunRelation.functionLookup unreachableToReturn ctx _ _ ?_
      | with_reducible refine ProgramRunRelation.functionCases unreachableToReturn ctx _ ?_ ?_
      | simp only [mapFunctionCFGs_maxCallDepth, exitUnwinding,
          bind_assoc, pure_bind]
      | (rw [forFunction_mapFunctionCFGs]; dsimp only [EvalContext.forFunction])
      | with_reducible refine ProgramRunRelation.seq ?_ ?_
      | intro _
      | split
      | dsimp only)
  exact h.run

/-- Source UB-freedom at a real entry quantifies both block fuel and call
    depth, exactly as `BehavesFn`; no fixed resource policy is assumed. -/
theorem not_behavesFn_ub_iff (ctx : EvalContext) (strat : PanicStrategy) (entry : FuncId)
    (args : List Value) (s : MachineState) :
    ¬ BehavesFn ctx strat entry args s .ub ↔
      ∀ fuel depth message,
        Sem.run (evalFunctionInContext { ctx with maxCallDepth := depth }
          entry args fuel strat) s ≠ .error (.ub message) := by
  constructor
  · intro h fuel depth message hRun
    exact h (Or.inl ⟨fuel, depth, (Outcome.ofRun_eq_some_ub _).mpr ⟨message, hRun⟩⟩)
  · intro h hBehaviour
    rcases hBehaviour with ⟨fuel, depth, hOutcome⟩ | ⟨hOutcome, _⟩
    · obtain ⟨message, hRun⟩ := (Outcome.ofRun_eq_some_ub _).mp hOutcome
      exact h fuel depth message hRun
    · cases hOutcome

/-- **Whole-program UB-exploiting refinement, calls executed.** Replacing
    Unreachable in every function body preserves every behaviour of every
    UB-free source entry, including traps, errors and divergence. The
    companion run relation also preserves finite resource refusals pointwise.
    Every recursively called function and SeqMap element body is rewritten;
    the theorem does not assume their execution as a premise. -/
theorem unreachableToReturn_program_refines :
    program_refines .abort (mapFunctionCFGs unreachableToReturn) := by
  intro ctx entry args s hNoUB outcome hTarget
  have hNoUB' := (not_behavesFn_ub_iff ctx .abort entry args s).mp hNoUB
  have hEqual : ∀ fuel depth,
      Sem.run (evalFunctionInContext
        { mapFunctionCFGs unreachableToReturn ctx with maxCallDepth := depth }
        entry args fuel .abort) s =
      Sem.run (evalFunctionInContext { ctx with maxCallDepth := depth }
        entry args fuel .abort) s := by
    intro fuel depth
    rcases evalFunctionInContext_mapUnreachableToReturn
        { ctx with maxCallDepth := depth } entry args fuel s with h | ⟨message, h⟩
    · exact h
    · exact False.elim (hNoUB' fuel depth message h)
  rcases hTarget with ⟨fuel, depth, hOutcome⟩ | ⟨hOutcome, hDiverges⟩
  · exact Or.inl ⟨fuel, depth, by rw [← hEqual]; exact hOutcome⟩
  · exact Or.inr ⟨hOutcome, fun fuel depth => by rw [← hEqual]; exact hDiverges fuel depth⟩


end TrustIr
