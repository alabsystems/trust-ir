-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Whole-program refinement with recursive calls and full outcomes.

import TrustIr.Proofs.TransformRefinementCtx

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

private theorem ProgramRunRelation.of_ub {α : Type} {target source : Sem α}
    (h : ∀ s, ∃ message, Sem.run source s = .error (.ub message)) :
    ProgramRunRelation target source := ⟨RunsLikeUnlessUB.of_ub h⟩

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
    (hNone : ProgramRunRelation targetNone sourceNone)
    (hSome : ∀ function, ProgramRunRelation
      (targetSome { function with cfg := transform function.cfg }) (sourceSome function)) :
    ProgramRunRelation
      (match (mapFunctionCFGs transform ctx).functions id with
       | some function => targetSome function | none => targetNone)
      (match ctx.functions id with
       | some function => sourceSome function | none => sourceNone) := by
  cases hFunction : ctx.functions id with
  | none => simpa only [mapFunctionCFGs, hFunction, Option.map] using hNone
  | some function =>
    simpa only [mapFunctionCFGs, hFunction, Option.map] using hSome function

/-- Discharge the evaluator's instruction dispatch with abstract handlers.
    Constructor reduction keeps its large continuations out of generated
    matcher-equation declarations. -/
private theorem ProgramRunRelation.instCases {α : Type} (inst : Inst)
    {targetCall sourceCall : FuncId → List ValueId → Sem α}
    {targetIndirect sourceIndirect : ValueId → FuncTyId → List ValueId → CallingConv → Sem α}
    {targetAssert sourceAssert targetOther sourceOther : Sem α}
    {targetPad sourcePad : Bool → List Nat → Sem α}
    (hCall : ∀ callee args, ProgramRunRelation (targetCall callee args) (sourceCall callee args))
    (hIndirect : ∀ callee sig args conv,
      ProgramRunRelation (targetIndirect callee sig args conv) (sourceIndirect callee sig args conv))
    (hAssert : ProgramRunRelation targetAssert sourceAssert)
    (hPad : ∀ cleanup clauses, ProgramRunRelation (targetPad cleanup clauses) (sourcePad cleanup clauses))
    (hOther : ProgramRunRelation targetOther sourceOther) :
    ProgramRunRelation
      (match inst with
       | .Call callee args => targetCall callee args
       | .CallIndirect callee sig args conv => targetIndirect callee sig args conv
       | .Assert _ _ _ => targetAssert
       | .LandingPad cleanup clauses => targetPad cleanup clauses
       | _ => targetOther)
      (match inst with
       | .Call callee args => sourceCall callee args
       | .CallIndirect callee sig args conv => sourceIndirect callee sig args conv
       | .Assert _ _ _ => sourceAssert
       | .LandingPad cleanup clauses => sourcePad cleanup clauses
       | _ => sourceOther) := by
  cases inst <;> first
    | exact hCall _ _
    | exact hIndirect _ _ _ _
    | exact hAssert
    | exact hPad _ _
    | exact hOther

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
    unfold stepNWithContext
    rw [hTarget]
    cases _hBlock : cfg pc with
    | none => exact ProgramRunRelation.refl _
    | some block =>
      dsimp (config := { zeta := false }) only [Option.map, resolveBlock_map_def]
      rw [resolveBlock_unreachableToReturnBlock]
      dsimp only
      refine ProgramRunRelation.seq (ProgramRunRelation.refl _) ?_
      intro _
      refine ProgramRunRelation.seq ?_ ?_
      · -- Share the instruction handlers before walking their continuations.
        refine ProgramRunRelation.loop _ _ ?_
        intro bodyInst _acc
        rcases bodyInst with ⟨inst, resultDests⟩
        dsimp only
        refine ProgramRunRelation.instCases inst ?_ ?_ ?_ ?_ ?_
        all_goals repeat' (first
          | with_reducible exact ProgramRunRelation.typeErrorBind _ _ _
          | with_reducible exact ih _ _ _ _ _
          | with_reducible refine ProgramRunRelation.directLookup unreachableToReturn ctx _ _ _ ?_
          | with_reducible refine ProgramRunRelation.functionLookup unreachableToReturn ctx _ _ ?_
          | with_reducible refine ProgramRunRelation.functionCases unreachableToReturn ctx _ ?_ ?_
          | rw [lookupFunctionHeader_mapFunctionCFGs]
          | rw [checkSeqMapElement_mapFunctionCFGs]
          | rw [memoryLayout_mapFunctionCFGs]
          | rw [storeMemoryValue_mapFunctionCFGs]
          | rw [loadMemoryValue_mapFunctionCFGs]
          | rw [functionErrors_mapFunctionCFGs]
          | rw [functionHeader_matches_mapCFG]
          | rw [bindCallResults_mapFunctionCFGs]
          | rw [bindInstructionResults_mapFunctionCFGs]
          | with_reducible refine ProgramRunRelation.samePrefix _ ?_
          | with_reducible exact ProgramRunRelation.refl _
          | dsimp only [semPureBind, mapFunctionCFGs_byteModel, mapFunctionCFGs_funcPtrs,
              mapFunctionCFGs_functionOrder,
              mapFunctionCFGs_funcTys, resolveDrop_map_def]
          | (rw [forFunction_mapFunctionCFGs]; dsimp only [EvalContext.forFunction])
          | rw [functionCall_mapFunctionCFGs]
          | rw [closureCall_mapFunctionCFGs]
          | (rw [forFunction_mapFunctionCFGs]; dsimp only [EvalContext.forFunction])
            | rw [checkClosureValue_mapFunctionCFGs]
          | with_reducible exact ProgramRunRelation.stepInst unreachableToReturn ctx _
          | with_reducible exact ProgramRunRelation.raiseStep unreachableToReturn ctx _
          | with_reducible exact ProgramRunRelation.pad unreachableToReturn ctx _ _
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
      · intro _
        unfold resolvedUnreachableToReturnTerm
        split
        · rename_i hTerm
          simp only [resolveDrop_mapFunctionCFGs, EvalContext.resolveBlock, hTerm,
            EvalContext.resolveDrop, abortTerm_unreachable, pure_bind]
          exact ProgramRunRelation.stuck _ _
        · dsimp only [EvalContext.resolveBlock, resolveDrop_map_def]
          repeat' (first
            | with_reducible exact ProgramRunRelation.typeErrorBind _ _ _
            | with_reducible exact ih _ _ _ _ _
            | with_reducible exact ProgramRunRelation.abortTerm unreachableToReturn ctx _ _ _ _
            | with_reducible refine ProgramRunRelation.directLookup unreachableToReturn ctx _ _ _ ?_
            | with_reducible refine ProgramRunRelation.functionLookup unreachableToReturn ctx _ _ ?_
            | with_reducible refine ProgramRunRelation.functionCases unreachableToReturn ctx _ ?_ ?_
            | rw [lookupFunctionHeader_mapFunctionCFGs]
            | rw [checkSeqMapElement_mapFunctionCFGs]
            | rw [memoryLayout_mapFunctionCFGs]
            | rw [storeMemoryValue_mapFunctionCFGs]
            | rw [loadMemoryValue_mapFunctionCFGs]
            | rw [functionErrors_mapFunctionCFGs]
            | rw [functionHeader_matches_mapCFG]
            | rw [bindCallResults_mapFunctionCFGs]
            | rw [bindInstructionResults_mapFunctionCFGs]
            | with_reducible refine ProgramRunRelation.samePrefix _ ?_
            | with_reducible exact ProgramRunRelation.refl _
            | dsimp only [semPureBind, mapFunctionCFGs_byteModel, mapFunctionCFGs_funcPtrs,
                mapFunctionCFGs_functionOrder,
                mapFunctionCFGs_funcTys, resolveDrop_map_def]
            | (rw [forFunction_mapFunctionCFGs]; dsimp only [EvalContext.forFunction])
            | rw [checkClosureValue_mapFunctionCFGs]
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
    · exact ProgramRunRelation.refl _
    intro function
    repeat' (first
      | with_reducible exact ProgramRunRelation.refl _
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
