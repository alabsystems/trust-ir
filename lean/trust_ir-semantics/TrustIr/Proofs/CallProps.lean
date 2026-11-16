-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Call safety properties: stack depth bounded by fuel, frame
-- restore correctness, and switch exhaustiveness.
-- Phase 4 proofs from the formalization roadmap.
--
-- Reference: designs/2026-04-16-trust_ir-semantics-lean-architecture.md, Section 6 Phase 4

import TrustIr.Semantics.Call
import TrustIr.Semantics.Eval

namespace TrustIr

/-- A function value cannot change its signature identity by being forwarded.
    Rejection precedes any lookup of the target body. -/
theorem functionCall_signature_mismatch (ctx : EvalContext) (held sig : FuncTyId)
    (target : FuncId) (h : (held != sig) = true) :
    functionCall ctx held target sig =
      .error (.typeError "CallIndirect: function value signature id mismatch") := by
  unfold functionCall
  rw [if_pos h]
  rfl

/-- Const construction retains the signature independently of its code id. -/
theorem const_function_retains_identity (sig : FuncTyId) (target : FuncId) :
    constValueAt (.Func sig) (.fnDef target) = .fnDef sig target := by
  simp [constValueAt]

/-!
# Call Properties

These theorems establish key safety properties of TrustIr's function
call semantics.

## Proved properties

1. Call arity check passes when lengths match (call and return sides)
2. Empty call stack is top-level
3. Empty call stack is bounded by any number
4. Push increases stack depth by 1
5. matchSwitchCase on empty list returns none
6. B5 bridge: the evaluator's Call handling IS `runCallReq` (terminator
   `CallReq` branch verbatim; body `Call` branch composed with
   `bindResultDests`) — `stepNWithContext_callReq_eq_runCallReq`,
   `stepNWithContext_bodyCall_eq_runCallReq_bind`
7. B5 transfer: a callee postcondition on return values transfers to the
   caller across a call — `proof_context_assume_sound` (over `runCallReq`)
   and `proof_context_assume_sound_evaluator` (over `stepNWithContext`)
8. Call/inline decomposition: a successful `runCallReq` run is exactly a
   successful fresh-frame callee run plus `restoreFrame`
   (`runCallReq_ok_decomp` / `runCallReq_ok_of_inline`)
9. B5/EH Invoke bridge + transfer: the evaluator's `InvokeReq` branch IS
   `runInvokeCall` composed with the invoke node's result binding, the
   normal-edge argument evaluation, and the normal-edge continuation
   (`stepNWithContext_invokeReq_eq_runInvokeCall_bind`); a callee
   postcondition transfers to the caller on the normal edge
   (`proof_context_assume_sound_invoke`,
   `proof_context_assume_sound_invoke_evaluator`,
   `runInvokeCall_ok_decomp`)

## All theorems in this file are fully proved (no proof placeholders).

## Design note

These proofs operate on the pure helpers (checkCallArity, saveFrame,
restoreFrame, matchSwitchCase) rather than the monadic wrappers
(semCall, etc.).  This keeps the proofs clean and composable.
Lifting to the monadic level is mechanical.
-/

-- =================================================================
-- Call arity validation
-- =================================================================

/-- Arity check passes when lengths match. -/
theorem checkCallArity_ok (args : List Value) (paramTys : List Ty)
    (h : args.length = paramTys.length) :
    checkCallArity args paramTys = .ok () := by
  simp [checkCallArity]
  omega

/-- Return-arity check passes when lengths match (the return-side twin of
    `checkCallArity_ok`). -/
theorem checkReturnArity_ok (values : List Value) (returnTys : List Ty)
    (h : values.length = returnTys.length) :
    checkReturnArity values returnTys = .ok () := by
  simp [checkReturnArity]
  omega

-- =================================================================
-- Call stack predicates
-- =================================================================

/-- The empty call stack satisfies isTopLevel. -/
theorem empty_stack_is_top_level :
    isTopLevel CallStack.empty := by
  simp [isTopLevel, CallStack.empty]

/-- The empty call stack is bounded by any non-negative number. -/
theorem empty_stack_bounded (n : Nat) :
    callStackBounded CallStack.empty n := by
  simp [callStackBounded, CallStack.empty]

/-- Pushing a frame onto a stack bounded by n yields a stack
    bounded by (n + 1). -/
theorem push_bounded (stack : CallStack) (frame : StackFrame) (n : Nat)
    (h : callStackBounded stack n) :
    callStackBounded (frame :: stack) (n + 1) := by
  simp [callStackBounded] at *
  omega

-- =================================================================
-- Frame restore preserves non-local state
-- =================================================================

/-- Restoring a frame preserves the memory state.
    Memory is a global resource not affected by call frame manipulation. -/
theorem restoreFrame_preserves_memory (s : MachineState) (frame : StackFrame)
    (retVals : List Value) :
    (restoreFrame s frame retVals).memory = s.memory := by
  unfold restoreFrame
  -- restoreFrame only modifies locals and nextValueId via {s with ...}
  -- then optionally modifies locals again in the (some dest, [v]) branch.
  -- Memory is never touched in any branch.
  cases frame.returnDest <;> cases retVals <;> simp_all
  case some.cons hd tl => cases tl <;> simp_all

/-- Restoring a frame preserves the permission map. -/
theorem restoreFrame_preserves_permissions (s : MachineState)
    (frame : StackFrame) (retVals : List Value) :
    (restoreFrame s frame retVals).permissions = s.permissions := by
  unfold restoreFrame
  cases frame.returnDest <;> cases retVals <;> simp_all
  case some.cons hd tl => cases tl <;> simp_all

/-- Restoring a frame preserves the refcount map. -/
theorem restoreFrame_preserves_refCounts (s : MachineState)
    (frame : StackFrame) (retVals : List Value) :
    (restoreFrame s frame retVals).refCounts = s.refCounts := by
  unfold restoreFrame
  cases frame.returnDest <;> cases retVals <;> simp_all
  case some.cons hd tl => cases tl <;> simp_all

-- =================================================================
-- Switch properties
-- =================================================================

/-- If no case matches, matchSwitchCase returns none. -/
theorem matchSwitchCase_empty (v : Value) :
    matchSwitchCase v [] = none := by
  simp [matchSwitchCase, List.find?]

/-- matchSwitchCase on an integer value returns the first case
    whose constant equals the switch value. -/
theorem matchSwitchCase_found (w : Nat) (v : Int) (sc : SwitchCase)
    (rest : List SwitchCase) (hMatch : sc.value = .int v) :
    matchSwitchCase (.int w v) (sc :: rest) = some sc := by
  -- matchSwitchCase unfolds to List.find? with a predicate that matches
  -- (switchVal, sc.value). For (.int w v) and sc.value = .int v,
  -- the predicate matches .int _w v, .int cv with v == v = true.
  -- So List.find? returns some sc (first element matches).
  simp [matchSwitchCase, switchCaseMatches, Constant.hasSymbolAddr, List.find?, hMatch]

-- =================================================================
-- B5: the evaluator's Call handling, factored (runCallReq)
-- =================================================================

/-- The evaluator's Call handling, factored out as a standalone def: resolve
    the callee, check call arity, save the caller frame, reset to a fresh
    empty-locals frame, run the callee via `stepNWithContext`, check return
    arity, restore the caller frame, and return the callee's return values
    *unchanged*.

    This is NOT faithful by fiat: the bridge theorems below PROVE it is the
    evaluator's Call handling —

    * `stepNWithContext_callReq_eq_runCallReq`: the `CallReq` terminator
      branch of `stepNWithContext` (`TrustIr/Semantics/Eval.lean`) is exactly
      `runCallReq`;
    * `stepNWithContext_bodyCall_eq_runCallReq_bind`: the body-instruction
      `Call` branch is exactly `runCallReq` composed with
      `bindResultDests resultDests`.

    Any drift between this def and the evaluator's branches breaks those
    proofs, so the B5 theorems stated over `runCallReq` are anchored to the
    real evaluator.

    Kept as a standalone def — it calls the real `stepNWithContext`, so it is
    not mutually recursive and does not perturb the executable fixtures — so the
    B5 transfer theorem below can be stated and proved over it. -/
def runCallReq (ctx : EvalContext) (fuel callDepth : Nat)
    (calleeId : FuncId) (callArgs : List Value) (strat : PanicStrategy := .abort) :
    Sem (List Value) := do
  let callee ← match ctx.functions calleeId with
    | some f => pure f
    | none =>
      if ctx.declared calleeId then
        Sem.throwUnsupported .interproceduralCall
          "Call: callee is a bodyless declaration"
      else Sem.throwTypeError "Call: undefined function"
  requireUntypedAbi callee.body.abi
  match checkCallArity callArgs callee.body.paramTys with
  | .ok () => pure ()
  | .error msg => Sem.throwTypeError ("Call: " ++ msg)
  Sem.rejectPoisonValues callArgs "Call arguments"
  let callerState ← Sem.getState
  let frame := saveFrame callerState none
  Sem.setState { callerState with locals := ValueMap.empty, nextValueId := 0 }
  let retVals ← stepNWithContext (ctx.forFunction callee) fuel callDepth
    callee.cfg callee.entryBlock callArgs strat
  match checkReturnArity retVals callee.body.returnTys with
  | .ok () => pure ()
  | .error msg => Sem.throwTypeError ("Call: " ++ msg)
  Sem.rejectPoisonValues retVals "Call returns"
  let calleeState ← Sem.getState
  Sem.setState (restoreFrame calleeState frame [])
  pure retVals

-- =================================================================
-- B5 bridge: runCallReq IS the evaluator's Call handling
-- =================================================================

/-- Bind is congruent in its continuation.  Lets the bridge proofs walk
    under monadic binders (`>>=`-bound variables) via `funext`. -/
private theorem sem_bind_congr {α β : Type} (m : Sem α) {f g : α → Sem β}
    (h : ∀ a, f a = g a) : m >>= f = m >>= g :=
  congrArg (m >>= ·) (funext h)

/-- A typeError throw absorbs any continuation (definitional for
    `StateT _ (Except _)`). -/
private theorem throwTypeError_bind {α β : Type} (msg : String) (k : α → Sem β) :
    (Sem.throwTypeError msg >>= k) = Sem.throwTypeError msg := rfl

/-- An `unsupported` throw absorbs any continuation, exactly as a typeError
    throw does (both are `Except.error` in the same monad). Needed since
    WS2.19 gave the callee-lookup `none` arm a second refusal: a callee the
    module only DECLARES is `unsupported.interprocedural_call`, not a type
    error. -/
private theorem throwUnsupported_bind {α β : Type} (feat : UnsupportedFeature)
    (msg : String) (k : α → Sem β) :
    (Sem.throwUnsupported feat msg >>= k) = Sem.throwUnsupported feat msg := rfl

/-- The WS2.19 callee-lookup FAILURE expression absorbs any continuation: a
    callee the module only DECLARES throws `unsupported.interprocedural_call`
    and one absent from the module throws the `Call: undefined function` type
    error, so whichever side of the `if` is taken, the bind is the throw. -/
private theorem lookupFailure_bind {α β : Type} (c : Bool)
    (feat : UnsupportedFeature) (msg₁ msg₂ : String) (k : α → Sem β) :
    ((if c then Sem.throwUnsupported feat msg₁ else Sem.throwTypeError msg₂ :
        Sem α) >>= k)
      = (if c then Sem.throwUnsupported feat msg₁ else Sem.throwTypeError msg₂ :
          Sem β) := by
  cases c <;> rfl

/-- The pure declaration/Char checks add no state change to a successful
    destination binding. Keep the existing postcondition-transfer conclusion
    about the values actually published in the caller. -/
private theorem bindCallResults_ok_bare (ctx : EvalContext) (inst : Inst)
    (dests : List ValueId) (values : List Value) (s s' : MachineState)
    (h : Sem.run (ctx.bindCallResults inst dests values) s = .ok ((), s')) :
    Sem.run (bindResultDests dests values) s = .ok ((), s') := by
  unfold EvalContext.bindCallResults at h
  split at h
  · exact h
  · unfold EvalContext.checkInstructionResults at h
    cases types : ctx.instructionResultTypes inst dests values.length with
    | error error =>
      simp only [types, Sem.run_bind, Except.bind] at h
      cases h
    | ok tys =>
      simp only [types, pure_bind] at h
      cases valid : checkSSACharValues tys values with
      | error error =>
        simp only [valid, Sem.run_bind, Except.bind] at h
        cases h
      | ok unit =>
        cases unit
        simpa only [valid, pure_bind] using h

/-- **B5 bridge, terminator form.** For a block whose terminator is a `Call`
    (the canonical shape producing a `StepResult.CallReq`), the real
    evaluator `stepNWithContext` — by name, not a transcription — is exactly:
    bind the block parameters, resolve the argument values, then `runCallReq`.

    This PROVES the `CallReq` terminator branch of `stepNWithContext`
    (`TrustIr/Semantics/Eval.lean`) is `runCallReq`: the proof unfolds the
    evaluator once, normalizes both sides with the monad laws, and closes by
    `rfl` — it goes through only because the branch body and `runCallReq` are
    the same program.  The `callDepth + 1` instantiation selects the
    non-exhausted case; depth 0 is `stepNWithContext_callReq_zero_depth`.
    The block-shape hypothesis pins a concrete path INTO the branch (empty
    body, `Call` terminator); the branch handling itself does not depend on
    how it was reached. -/
theorem stepNWithContext_callReq_eq_runCallReq
    (ctx : EvalContext) (fuel callDepth : Nat) (cfg : CFG) (pc : BlockId)
    (params : List (ValueId × Ty)) (args : List Value)
    (calleeId : FuncId) (argIds : List ValueId)
    (hBlock : cfg pc = some
      { params := params, body := [], terminator := .Call calleeId argIds }) :
    stepNWithContext ctx (fuel + 1) (callDepth + 1) cfg pc args
      = (do
          let _ ← Sem.fromMemoryExcept (checkFunctionItemValues ctx (params.map (·.snd)) args)
          bindBlockParamsChecked params args
          let callArgs ← argIds.mapM Sem.lookupValue
          runCallReq ctx fuel callDepth calleeId callArgs) := by
  unfold stepNWithContext
  rw [hBlock]
  simp only [EvalContext.resolveBlock, EvalContext.resolveDrop, List.map_nil, List.map_cons,
    bodyInstsWithResultDests, List.forIn_nil, List.forIn_cons,
    stepTermWithContext, closureTermWithContext, stepInst, runCallReq, EvalContext.lookupDirectCallee, pure_bind, bind_assoc]
  refine sem_bind_congr _ fun _ => ?_
  refine sem_bind_congr _ fun _ => ?_
  refine sem_bind_congr _ fun _ => ?_
  cases _hfn : ctx.functions calleeId <;>
    simp only [pure_bind, throwTypeError_bind, throwUnsupported_bind, lookupFailure_bind] <;> rfl

/-- **B5 bridge, exhausted call depth.** At call depth 0 the evaluator's
    `CallReq` branch throws `outOfFuel` after the checked block-parameter
    and operand prefixes, before callee handling. Depth accounting belongs to
    the evaluator, not to `runCallReq` (which takes the decremented depth). -/
theorem stepNWithContext_callReq_zero_depth
    (ctx : EvalContext) (fuel : Nat) (cfg : CFG) (pc : BlockId)
    (params : List (ValueId × Ty)) (args : List Value)
    (calleeId : FuncId) (argIds : List ValueId)
    (hBlock : cfg pc = some
      { params := params, body := [], terminator := .Call calleeId argIds }) :
    stepNWithContext ctx (fuel + 1) 0 cfg pc args
      = (do
          let _ ← Sem.fromMemoryExcept (checkFunctionItemValues ctx (params.map (·.snd)) args)
          bindBlockParamsChecked params args
          let _ ← argIds.mapM Sem.lookupValue
          throw SemError.outOfFuel) := by
  unfold stepNWithContext
  rw [hBlock]
  simp only [EvalContext.resolveBlock, EvalContext.resolveDrop, List.map_nil, List.map_cons,
    bodyInstsWithResultDests, List.forIn_nil, List.forIn_cons,
    stepTermWithContext, closureTermWithContext, stepInst, pure_bind, bind_assoc]

/-- **B5 bridge, body-instruction form.** For a block whose body contains a
    `Call` with explicit result destinations (mirroring Rust
    `InstrNode.results`), the evaluator checks and binds the block parameters,
    resolves the argument values, runs `runCallReq`, then checks the actual
    source declarations and top-level Char results in `ctx.bindCallResults`
    before publishing the returned values.

    This anchors the complete body-`Call` branch of `stepNWithContext` to
    the call helper plus its actual checked publication step, including all
    refusals. No successful-run assumption removes those checks.  The `.Return retIds` terminator (its
    semantics is the trailing `retIds.mapM Sem.lookupValue`) closes the block
    so the statement stays finite; the body-`Call` handling itself does not
    depend on the terminator. -/
theorem stepNWithContext_bodyCall_eq_runCallReq_bind
    (ctx : EvalContext) (fuel callDepth : Nat) (cfg : CFG) (pc : BlockId)
    (params : List (ValueId × Ty)) (args : List Value)
    (calleeId : FuncId) (argIds resultDests retIds : List ValueId)
    (hBlock : cfg pc = some
      { params := params
        body := [.Call calleeId argIds]
        bodyResultDests := [resultDests]
        terminator := .Return retIds }) :
    stepNWithContext ctx (fuel + 1) (callDepth + 1) cfg pc args
      = (do
          let _ ← Sem.fromMemoryExcept (checkFunctionItemValues ctx (params.map (·.snd)) args)
          bindBlockParamsChecked params args
          let callArgs ← argIds.mapM Sem.lookupValue
          let retVals ← runCallReq ctx fuel callDepth calleeId callArgs
          ctx.bindCallResults (.Call calleeId argIds) resultDests retVals
          let values ← retIds.mapM Sem.lookupValue
          if let some expected := ctx.functionReturnTypes then
            let _ ← Sem.fromMemoryExcept (checkFunctionItemValues ctx expected values)
            pure values
          else pure values) := by
  unfold stepNWithContext
  rw [hBlock]
  simp only [EvalContext.resolveBlock, EvalContext.resolveDrop, List.map_nil, List.map_cons,
    bodyInstsWithResultDests, List.forIn_nil, List.forIn_cons,
    stepTermWithContext, closureTermWithContext, stepInst, semReturn, runCallReq, EvalContext.lookupDirectCallee, pure_bind, bind_assoc, bind_pure]
  -- Both sides are now the same monadic spine; the residual difference is
  -- WHERE the continuation sits relative to the pure `match`es (callee
  -- lookup, arity checks).  Walk under the binders and split those matches;
  -- every leaf either collapses into the same throw or normalizes to the
  -- same program.
  refine sem_bind_congr _ fun _ => ?_
  refine sem_bind_congr _ fun _ => ?_
  refine sem_bind_congr _ fun callArgs => ?_
  cases _hfn : ctx.functions calleeId with
  | none =>
    -- WS2.19: the lookup-failure arm is now two refusals (a callee the module
    -- only DECLARES is `unsupported.interprocedural_call`, not a type error).
    -- No case split is needed: BOTH absorb their continuation, so the two
    -- sides collapse to the same `if`.
    simp only [throwTypeError_bind, throwUnsupported_bind, lookupFailure_bind]
  | some callee =>
    dsimp only
    simp only [pure_bind, bind_assoc]
    refine sem_bind_congr _ fun _ => ?_
    cases _hca : checkCallArity callArgs callee.body.paramTys with
    | error msg => simp only [throwTypeError_bind]
    | ok u =>
      cases u
      dsimp only
      simp only [bind_assoc]
      -- The argument poison guard (`Sem.rejectPoisonValues`, WS2.10).
      refine sem_bind_congr _ fun _ => ?_
      refine sem_bind_congr _ fun callerState => ?_
      refine sem_bind_congr _ fun _ => ?_
      refine sem_bind_congr _ fun retVals => ?_
      cases _hret : checkReturnArity retVals callee.body.returnTys with
      | error msg => simp only [throwTypeError_bind]
      | ok u =>
        cases u
        simp only [bind_assoc, pure_bind, bind_pure]
        rfl

-- =================================================================
-- B5: per-call ProofContext postcondition transfer (soundness)
-- =================================================================

/-- **B5 soundness — postcondition transfer.**

    A callee postcondition `Q : List Value → Prop` (the denotation of an
    obligation listed in a call site's `ProofContext.assumes`) that the callee
    guarantees on its return values may be soundly relied on by the caller after
    the call returns, without re-checking it.

    If every terminating run of the callee from its entry (on a fresh
    empty-locals frame seeded with `callArgs`) yields return values satisfying
    `Q`, then whenever `runCallReq` (the call handling that runs the callee and
    restores the caller frame) succeeds, its returned values satisfy `Q`. The
    operational core is that the `CallReq` handling returns the callee's
    `retVals` *unchanged* after `restoreFrame`, so the callee's guarantee
    transfers verbatim to the caller.

    `Q` is kept abstract and quantified: connecting a serialized `ProofId` to a
    specific `Q` is the Rust validator's job, not the operational model's. No
    new axiom — the trust boundary stays the single `ay_sound_unsat`. -/
theorem proof_context_assume_sound
    (ctx : EvalContext) (fuel callDepth : Nat)
    (calleeId : FuncId) (callee : EvalFunction)
    (callArgs : List Value) (Q : List Value → Prop)
    (sCaller : MachineState)
    (hFn : ctx.functions calleeId = some callee)
    (hArity : callArgs.length = callee.body.paramTys.length)
    (hCalleePost :
      ∀ retVals sCalleeEnd,
        Sem.run
          (stepNWithContext (ctx.forFunction callee) fuel callDepth
             callee.cfg callee.entryBlock callArgs)
          { sCaller with locals := ValueMap.empty, nextValueId := 0 }
          = .ok (retVals, sCalleeEnd) →
        Q retVals) :
    ∀ retVals sEnd,
      Sem.run (runCallReq ctx fuel callDepth calleeId callArgs) sCaller
        = .ok (retVals, sEnd) →
      Q retVals := by
  intro retVals sEnd hrun
  have hget : ∀ s : MachineState, Sem.run Sem.getState s = .ok (s, s) := fun _ => rfl
  have hset : ∀ s s' : MachineState, Sem.run (Sem.setState s') s = .ok ((), s') :=
    fun _ _ => rfl
  have hthrow : ∀ {α β : Type} (e : SemError) (k : α → Sem β) (s : MachineState),
      Sem.run (throw e >>= k) s = .error e := fun _ _ _ => rfl
  have hAbi : callee.body.abi = none := by
    cases h : callee.body.abi with
    | none => rfl
    | some abi =>
      simp only [runCallReq, hFn, pure_bind, requireUntypedAbi, h, Sem.throwUnsupported, Option.isSome, if_true, bind_assoc, hthrow] at hrun <;> cases hrun
  unfold runCallReq at hrun
  simp only [hFn, pure_bind, hAbi, requireUntypedAbi_none] at hrun
  simp only [hFn, checkCallArity_ok callArgs callee.body.paramTys hArity,
    Sem.run_bind, Sem.run_pure, hget, hset, Except.bind] at hrun
  -- The argument poison guard (WS2.10): poison arguments throw.
  have hpa : callArgs.any Value.isPoison = false := by
    cases hp : callArgs.any Value.isPoison with
    | false => rfl
    | true =>
      obtain ⟨e, he⟩ := Sem.rejectPoisonValues_run_error callArgs "Call arguments" sCaller hp
      rw [he] at hrun; simp at hrun
  rw [Sem.rejectPoisonValues_run_ok callArgs "Call arguments" sCaller hpa] at hrun
  dsimp only at hrun
  -- Case on the callee run; `.error` contradicts the `.ok` hypothesis.
  cases hrec : Sem.run
      (stepNWithContext (ctx.forFunction callee) fuel callDepth callee.cfg callee.entryBlock callArgs)
      { sCaller with locals := ValueMap.empty, nextValueId := 0 } with
  | error e => rw [hrec] at hrun; simp at hrun
  | ok p =>
    obtain ⟨rv, se⟩ := p
    rw [hrec] at hrun
    -- The return-arity check; `.error` again contradicts `.ok`.
    cases hret : checkReturnArity rv callee.body.returnTys with
    | error msg =>
      simp only [hret, Sem.throwTypeError] at hrun
      rw [hthrow] at hrun
      exact absurd hrun (by simp)
    | ok u =>
      simp only [hret, Sem.run_bind, Sem.run_pure, hget, hset, Except.bind] at hrun
      -- The return poison guard (WS2.10): poison returns throw.
      have hpr : rv.any Value.isPoison = false := by
        cases hp : rv.any Value.isPoison with
        | false => rfl
        | true =>
          obtain ⟨e, he⟩ := Sem.rejectPoisonValues_run_error rv "Call returns" se hp
          rw [he] at hrun; simp at hrun
      rw [Sem.rejectPoisonValues_run_ok rv "Call returns" se hpr] at hrun
      dsimp only at hrun
      -- The tail is deterministic: it returns the callee's `rv` unchanged.
      simp only [Sem.run_bind, Sem.run_pure, hget, hset, Except.bind,
        Except.ok.injEq, Prod.mk.injEq] at hrun
      obtain ⟨hrv, _hse⟩ := hrun
      subst hrv
      exact hCalleePost rv se hrec

-- =================================================================
-- B5: call/inline decomposition of a successful runCallReq run
-- =================================================================

/-- **Forward decomposition.** A successful Call IS a successful inline run of
    the callee body: if `runCallReq` succeeds from caller state `s` with
    `(retVals, sEnd)`, then

    * both arity checks passed (the lengths match),
    * the callee body ran to success on the fresh empty-locals frame seeded
      from `s`, producing the SAME `retVals` and some callee end state, and
    * `sEnd` is exactly that callee end state with the caller frame restored
      (so `sEnd` agrees with it on memory/permissions/refCounts by
      `restoreFrame_preserves_*`).

    Together with `runCallReq_ok_of_inline` this characterizes the call as
    inline execution of the callee body under the frame discipline; the
    inlining-correctness theorem `inlining_preserving`
    (`TrustIr/Proofs/TransformCorrectness.lean`) packages the two directions. -/
theorem runCallReq_ok_decomp
    (ctx : EvalContext) (fuel callDepth : Nat)
    (calleeId : FuncId) (callee : EvalFunction) (callArgs : List Value)
    (s sEnd : MachineState) (retVals : List Value)
    (hFn : ctx.functions calleeId = some callee)
    (hCall : Sem.run (runCallReq ctx fuel callDepth calleeId callArgs) s
      = .ok (retVals, sEnd)) :
    callArgs.length = callee.body.paramTys.length ∧
    callArgs.any Value.isPoison = false ∧
    retVals.length = callee.body.returnTys.length ∧
    retVals.any Value.isPoison = false ∧
    ∃ sCalleeEnd,
      Sem.run (stepNWithContext (ctx.forFunction callee) fuel callDepth
          callee.cfg callee.entryBlock callArgs)
        { s with locals := ValueMap.empty, nextValueId := 0 }
        = .ok (retVals, sCalleeEnd) ∧
      sEnd = restoreFrame sCalleeEnd (saveFrame s none) [] := by
  have hget : ∀ st : MachineState, Sem.run Sem.getState st = .ok (st, st) :=
    fun _ => rfl
  have hset : ∀ st st' : MachineState, Sem.run (Sem.setState st') st = .ok ((), st') :=
    fun _ _ => rfl
  have hthrow : ∀ {α β : Type} (e : SemError) (k : α → Sem β) (st : MachineState),
      Sem.run (throw e >>= k) st = .error e := fun _ _ _ => rfl
  have hAbi : callee.body.abi = none := by
    cases h : callee.body.abi with
    | none => rfl
    | some abi =>
      simp only [runCallReq, hFn, pure_bind, requireUntypedAbi, h, Sem.throwUnsupported, Option.isSome, if_true, bind_assoc, hthrow] at hCall <;> cases hCall
  unfold runCallReq at hCall
  simp only [hFn, pure_bind, hAbi, requireUntypedAbi_none] at hCall
  try simp only [hFn, Sem.run_bind, Sem.run_pure, hget, hset, Except.bind] at hCall
  -- The call-arity check: `.error` contradicts the `.ok` hypothesis, and
  -- `.ok` forces the lengths to match.
  cases hca : checkCallArity callArgs callee.body.paramTys with
  | error msg =>
    rw [hca] at hCall
    simp only [Sem.throwTypeError] at hCall
    rw [hthrow] at hCall
    exact absurd hCall (by simp)
  | ok u =>
    cases u
    rw [hca] at hCall
    have hArity : callArgs.length = callee.body.paramTys.length := by
      unfold checkCallArity at hca
      split at hca
      next h => exact eq_of_beq h
      next h => exact absurd hca (by simp)
    simp only [Sem.run_bind, Sem.run_pure, hget, hset, Except.bind] at hCall
    -- The argument poison guard (WS2.10): poison arguments throw.
    have hpa : callArgs.any Value.isPoison = false := by
      cases hp : callArgs.any Value.isPoison with
      | false => rfl
      | true =>
        obtain ⟨e, he⟩ := Sem.rejectPoisonValues_run_error callArgs "Call arguments" s hp
        rw [he] at hCall; simp at hCall
    rw [Sem.rejectPoisonValues_run_ok callArgs "Call arguments" s hpa] at hCall
    dsimp only at hCall
    -- The callee run: `.error` contradicts `.ok`.
    cases hrec : Sem.run
        (stepNWithContext (ctx.forFunction callee) fuel callDepth callee.cfg callee.entryBlock callArgs)
        { s with locals := ValueMap.empty, nextValueId := 0 } with
    | error e => rw [hrec] at hCall; simp at hCall
    | ok p =>
      obtain ⟨rv, se⟩ := p
      rw [hrec] at hCall
      -- The return-arity check, same treatment as the call-arity check.
      cases hret : checkReturnArity rv callee.body.returnTys with
      | error msg =>
        simp only [hret, Sem.throwTypeError] at hCall
        rw [hthrow] at hCall
        exact absurd hCall (by simp)
      | ok u =>
        cases u
        have hRet : rv.length = callee.body.returnTys.length := by
          unfold checkReturnArity at hret
          split at hret
          next h => exact eq_of_beq h
          next h => exact absurd hret (by simp)
        -- The deterministic tail forces retVals = rv and pins sEnd.
        simp only [hret, Sem.run_bind, Sem.run_pure, hget, hset, Except.bind] at hCall
        -- The return poison guard (WS2.10): poison returns throw.
        have hpr : rv.any Value.isPoison = false := by
          cases hp : rv.any Value.isPoison with
          | false => rfl
          | true =>
            obtain ⟨e, he⟩ := Sem.rejectPoisonValues_run_error rv "Call returns" se hp
            rw [he] at hCall; simp at hCall
        rw [Sem.rejectPoisonValues_run_ok rv "Call returns" se hpr] at hCall
        dsimp only at hCall
        simp only [Sem.run_bind, Sem.run_pure, hget, hset, Except.bind,
          Except.ok.injEq, Prod.mk.injEq] at hCall
        obtain ⟨hrv, hse⟩ := hCall
        subst hrv
        subst hse
        exact ⟨hArity, hpa, hRet, hpr, se, rfl, rfl⟩

/-- **Converse composition.** A successful inline run of the callee body on
    the fresh frame (with matching arities) yields the successful Call: the
    same return values, and the caller end state is the callee end state with
    the caller frame restored.  The converse direction of
    `runCallReq_ok_decomp`. -/
theorem runCallReq_ok_of_inline
    (ctx : EvalContext) (fuel callDepth : Nat)
    (calleeId : FuncId) (callee : EvalFunction) (callArgs : List Value)
    (s sCalleeEnd : MachineState) (retVals : List Value)
    (hFn : ctx.functions calleeId = some callee)
    (hAbi : callee.body.abi = none)
    (hArity : callArgs.length = callee.body.paramTys.length)
    (hRet : retVals.length = callee.body.returnTys.length)
    (hArgsClean : callArgs.any Value.isPoison = false)
    (hRetClean : retVals.any Value.isPoison = false)
    (hInline : Sem.run (stepNWithContext (ctx.forFunction callee) fuel callDepth
          callee.cfg callee.entryBlock callArgs)
        { s with locals := ValueMap.empty, nextValueId := 0 }
        = .ok (retVals, sCalleeEnd)) :
    Sem.run (runCallReq ctx fuel callDepth calleeId callArgs) s
      = .ok (retVals, restoreFrame sCalleeEnd (saveFrame s none) []) := by
  have hget : ∀ st : MachineState, Sem.run Sem.getState st = .ok (st, st) :=
    fun _ => rfl
  have hset : ∀ st st' : MachineState, Sem.run (Sem.setState st') st = .ok ((), st') :=
    fun _ _ => rfl
  unfold runCallReq
  simp only [hFn, hAbi, requireUntypedAbi_none, checkCallArity_ok callArgs callee.body.paramTys hArity,
    Sem.run_bind, Sem.run_pure, hget, hset, Except.bind,
    Sem.rejectPoisonValues_run_ok callArgs _ s hArgsClean, hInline,
    checkReturnArity_ok retVals callee.body.returnTys hRet,
    Sem.rejectPoisonValues_run_ok retVals _ sCalleeEnd hRetClean]

-- =================================================================
-- B5: postcondition transfer over the REAL evaluator
-- =================================================================

/-- A successful validation-prefixed run preserves the original continuation's
    state and result. Failed validation cannot satisfy the success premise. -/
private theorem checked_prefix_ok_bare {α : Type} (checked : Except SemError Unit)
    (next : Sem α) (s s' : MachineState) (result : α)
    (success : Sem.run (do let _ ← Sem.fromMemoryExcept checked; next) s = .ok (result, s')) :
    Sem.run next s = .ok (result, s') := by
  cases checked with
  | error error => cases success
  | ok unit => cases unit; exact success

/-- **B5 soundness over `stepNWithContext` itself.**  The postcondition
    transfer of `proof_context_assume_sound`, restated for the real evaluator
    via the bridge lemma: for a caller block whose terminator is a `Call`, if
    the callee guarantees `Q` on the return values of every terminating run
    (from any fresh frame and any resolved arguments), then a successful run
    of `stepNWithContext` through that block returns values satisfying `Q`.

    `hCalleePost` quantifies over the resolved `callArgs` and the pre-call
    state because both are produced by the caller's own execution (parameter
    binding and argument lookup) rather than being statically known — this is
    the honest per-call-site form of "the callee's `ProofContext.assumes`
    postcondition holds on return". -/
theorem proof_context_assume_sound_evaluator
    (ctx : EvalContext) (fuel callDepth : Nat) (cfg : CFG) (pc : BlockId)
    (params : List (ValueId × Ty)) (args : List Value)
    (calleeId : FuncId) (callee : EvalFunction) (argIds : List ValueId)
    (Q : List Value → Prop) (s : MachineState)
    (hBlock : cfg pc = some
      { params := params, body := [], terminator := .Call calleeId argIds })
    (hFn : ctx.functions calleeId = some callee)
    (hCalleePost :
      ∀ (callArgs retVals : List Value) (sCall sCalleeEnd : MachineState),
        Sem.run (stepNWithContext (ctx.forFunction callee) fuel callDepth
            callee.cfg callee.entryBlock callArgs)
          { sCall with locals := ValueMap.empty, nextValueId := 0 }
          = .ok (retVals, sCalleeEnd) →
        Q retVals) :
    ∀ retVals sEnd,
      Sem.run (stepNWithContext ctx (fuel + 1) (callDepth + 1) cfg pc args) s
        = .ok (retVals, sEnd) →
      Q retVals := by
  intro retVals sEnd hrun
  rw [stepNWithContext_callReq_eq_runCallReq ctx fuel callDepth cfg pc params args
    calleeId argIds hBlock] at hrun
  have hrun := checked_prefix_ok_bare _ _ s sEnd retVals hrun
  -- Peel the parameter-binding and argument-lookup prefix.
  rw [Sem.run_bind] at hrun
  cases h1 : Sem.run (bindBlockParamsChecked params args) s with
  | error e => rw [h1] at hrun; exact absurd hrun (by simp [Except.bind])
  | ok p1 =>
    obtain ⟨u1, s1⟩ := p1
    rw [h1] at hrun
    simp only [Except.bind] at hrun
    rw [Sem.run_bind] at hrun
    cases h2 : Sem.run (argIds.mapM Sem.lookupValue) s1 with
    | error e => rw [h2] at hrun; exact absurd hrun (by simp [Except.bind])
    | ok p2 =>
      obtain ⟨callArgs, s2⟩ := p2
      rw [h2] at hrun
      simp only [Except.bind] at hrun
      -- hrun is now a successful runCallReq run; decompose and transfer.
      obtain ⟨-, -, -, -, sCalleeEnd, hInline, -⟩ :=
        runCallReq_ok_decomp ctx fuel callDepth calleeId callee callArgs s2 sEnd
          retVals hFn hrun
      exact hCalleePost callArgs retVals s2 sCalleeEnd hInline

-- =================================================================
-- B5/EH: the evaluator's Invoke handling, factored (runInvokeCall)
-- =================================================================

/-- The CALL portion of the evaluator's `InvokeReq` branch
    (`stepNWithContext`, TrustIr/Semantics/Eval.lean), factored out as a
    standalone def: resolve the callee, check call arity, save the caller
    frame, run the callee with its own declarations on a fresh empty-locals frame, check return arity,
    restore the caller frame, and return the callee's return values
    *unchanged*.  The same program as `runCallReq` up to the `"Invoke: "`
    diagnostic prefixes on the throws — which is why it is transcribed
    separately rather than reused (the throw payloads differ, so the branch
    is not literally `runCallReq`).

    NOT faithful by fiat: `stepNWithContext_invokeReq_eq_runInvokeCall_bind`
    below PROVES the evaluator's `InvokeReq` branch is exactly this def
    composed with the invoke node's checked result binding
    (`ctx.bindCallResults`), the normal-edge argument
    evaluation, and the normal-edge continuation — the same anchoring
    pattern as `stepNWithContext_callReq_eq_runCallReq` /
    `stepNWithContext_bodyCall_eq_runCallReq_bind`.  Any drift between this
    def and the branch breaks that proof. -/
def runInvokeCall (ctx : EvalContext) (fuel innerDepth : Nat)
    (calleeId : FuncId) (callArgs : List Value) : Sem (List Value) := do
  let callee ← match ctx.functions calleeId with
    | some f => pure f
    | none =>
      if ctx.declared calleeId then
        Sem.throwUnsupported .interproceduralCall
          "Invoke: callee is a bodyless declaration"
      else Sem.throwTypeError "Invoke: undefined function"
  requireUntypedAbi callee.body.abi
  match checkCallArity callArgs callee.body.paramTys with
  | .ok () => pure ()
  | .error msg => Sem.throwTypeError ("Invoke: " ++ msg)
  Sem.rejectPoisonValues callArgs "Call arguments"
  let callerState ← Sem.getState
  let frame := saveFrame callerState none
  Sem.setState { callerState with locals := ValueMap.empty, nextValueId := 0 }
  let retVals ← stepNWithContext (ctx.forFunction callee) fuel innerDepth
    callee.cfg callee.entryBlock callArgs
  match checkReturnArity retVals callee.body.returnTys with
  | .ok () => pure ()
  | .error msg => Sem.throwTypeError ("Invoke: " ++ msg)
  Sem.rejectPoisonValues retVals "Call returns"
  let calleeState ← Sem.getState
  Sem.setState (restoreFrame calleeState frame [])
  pure retVals

/-- **Invoke bridge.** For a block whose terminator is an `Invoke` (the
    canonical shape producing a `StepResult.InvokeReq`), the real evaluator
    `stepNWithContext` — by name, not a transcription — is exactly: bind the
    block parameters, resolve the argument values, `runInvokeCall`, bind the
    callee's returns to the invoke node's result destinations
    (`terminatorResultDests`), THEN evaluate the normal-edge arguments (they
    may reference those results), and continue in the CALLER at the normal
    destination.  The unwind destination appears in the block but is never
    taken — the executable model is non-throwing (`panic=abort`), mirroring
    the reference interpreter.

    Depth accounting, per the branch: instantiated at `callDepth =
    innerDepth + 1`, the CALLEE runs at `innerDepth` (nesting consumes one
    level) while the normal-edge continuation resumes at the UNdecremented
    `innerDepth + 1` — an Invoke must not permanently burn depth budget. -/
theorem stepNWithContext_invokeReq_eq_runInvokeCall_bind
    (ctx : EvalContext) (fuel innerDepth : Nat) (cfg : CFG) (pc : BlockId)
    (params : List (ValueId × Ty)) (args : List Value)
    (calleeId : FuncId) (argIds normalArgIds : List ValueId)
    (normalDest unwindDest : BlockId) (termDests : List ValueId)
    (hBlock : cfg pc = some
      { params := params
        body := []
        terminator := .Invoke calleeId argIds normalDest normalArgIds unwindDest
        terminatorResultDests := termDests }) :
    stepNWithContext ctx (fuel + 1) (innerDepth + 1) cfg pc args
      = (do
          let _ ← Sem.fromMemoryExcept (checkFunctionItemValues ctx (params.map (·.snd)) args)
          bindBlockParamsChecked params args
          let callArgs ← argIds.mapM Sem.lookupValue
          let retVals ← runInvokeCall ctx fuel innerDepth calleeId callArgs
          ctx.bindCallResults (.Invoke calleeId argIds normalDest normalArgIds unwindDest) termDests retVals
          let edgeArgs ← normalArgIds.mapM Sem.lookupValue
          stepNWithContext ctx fuel (innerDepth + 1) cfg normalDest edgeArgs) := by
  -- Unfold ONLY the left-hand evaluator call: the right-hand side carries the
  -- normal-edge continuation as a bare `stepNWithContext` application under a
  -- binder, which a goal-wide (simp-based) unfold would desynchronize from the
  -- (not further unfolded) continuation inside the evaluator's branch body.
  -- `rw` does not rewrite under binders, so it hits exactly the outer call.
  rw [stepNWithContext]
  rw [hBlock]
  simp only [EvalContext.resolveBlock, EvalContext.resolveDrop, List.map_nil, List.map_cons,
    bodyInstsWithResultDests, List.forIn_nil, List.forIn_cons,
    stepTermWithContext, closureTermWithContext, stepInst, runInvokeCall, EvalContext.lookupDirectCallee, invokeCatch, pure_bind, bind_assoc]
  -- Both sides are the same monadic spine; the residual difference is WHERE
  -- the continuation (result binding + edge args + normal-edge recursion)
  -- sits relative to the pure `match`es.  Walk under the binders and split.
  refine sem_bind_congr _ fun _ => ?_
  refine sem_bind_congr _ fun _ => ?_
  refine sem_bind_congr _ fun callArgs => ?_
  cases _hfn : ctx.functions calleeId with
  | none =>
    -- WS2.19: the lookup-failure arm is now two refusals (a callee the module
    -- only DECLARES is `unsupported.interprocedural_call`, not a type error).
    -- No case split is needed: BOTH absorb their continuation, so the two
    -- sides collapse to the same `if`.
    simp only [throwTypeError_bind, throwUnsupported_bind, lookupFailure_bind]
  | some callee =>
    dsimp only
    simp only [pure_bind, bind_assoc]
    refine sem_bind_congr _ fun _ => ?_
    cases _hca : checkCallArity callArgs callee.body.paramTys with
    | error msg => simp only [throwTypeError_bind]
    | ok u =>
      cases u
      dsimp only
      simp only [bind_assoc]
      -- The argument poison guard (`Sem.rejectPoisonValues`, WS2.10).
      refine sem_bind_congr _ fun _ => ?_
      refine sem_bind_congr _ fun callerState => ?_
      refine sem_bind_congr _ fun _ => ?_
      refine sem_bind_congr _ fun retVals => ?_
      cases _hret : checkReturnArity retVals callee.body.returnTys with
      | error msg => simp only [throwTypeError_bind]
      | ok u =>
        cases u
        simp only [bind_assoc, pure_bind, bind_pure]

/-- **Invoke bridge, exhausted call depth.** At call depth 0 the evaluator's
    `InvokeReq` branch throws `outOfFuel` after the checked block-parameter
    and operand prefixes, before callee handling. Depth accounting belongs to
    the evaluator, not to `runInvokeCall` (which takes decremented depth). -/
theorem stepNWithContext_invokeReq_zero_depth
    (ctx : EvalContext) (fuel : Nat) (cfg : CFG) (pc : BlockId)
    (params : List (ValueId × Ty)) (args : List Value)
    (calleeId : FuncId) (argIds normalArgIds : List ValueId)
    (normalDest unwindDest : BlockId) (termDests : List ValueId)
    (hBlock : cfg pc = some
      { params := params
        body := []
        terminator := .Invoke calleeId argIds normalDest normalArgIds unwindDest
        terminatorResultDests := termDests }) :
    stepNWithContext ctx (fuel + 1) 0 cfg pc args
      = (do
          let _ ← Sem.fromMemoryExcept (checkFunctionItemValues ctx (params.map (·.snd)) args)
          bindBlockParamsChecked params args
          let _ ← argIds.mapM Sem.lookupValue
          throw SemError.outOfFuel) := by
  unfold stepNWithContext
  rw [hBlock]
  simp only [EvalContext.resolveBlock, EvalContext.resolveDrop, List.map_nil, List.map_cons,
    bodyInstsWithResultDests, List.forIn_nil, List.forIn_cons,
    stepTermWithContext, closureTermWithContext, stepInst, pure_bind, bind_assoc]

-- =================================================================
-- B5/EH: per-invoke ProofContext postcondition transfer (soundness)
-- =================================================================

/-- **Invoke postcondition transfer (over `runInvokeCall`).**  The `Invoke`
    analogue of `proof_context_assume_sound`: a callee postcondition
    `Q : List Value → Prop` (the denotation of an obligation in the invoke
    site's `ProofContext.assumes`) that the callee guarantees on its return
    values transfers to the caller whenever the invoke's call completes —
    i.e. on the NORMAL edge, the only edge the non-throwing executable model
    can take.  The operational core is identical to the `Call` case: the
    handling returns the callee's `retVals` *unchanged* after
    `restoreFrame`. -/
theorem proof_context_assume_sound_invoke
    (ctx : EvalContext) (fuel innerDepth : Nat)
    (calleeId : FuncId) (callee : EvalFunction)
    (callArgs : List Value) (Q : List Value → Prop)
    (sCaller : MachineState)
    (hFn : ctx.functions calleeId = some callee)
    (hArity : callArgs.length = callee.body.paramTys.length)
    (hCalleePost :
      ∀ retVals sCalleeEnd,
        Sem.run
          (stepNWithContext (ctx.forFunction callee) fuel innerDepth
             callee.cfg callee.entryBlock callArgs)
          { sCaller with locals := ValueMap.empty, nextValueId := 0 }
          = .ok (retVals, sCalleeEnd) →
        Q retVals) :
    ∀ retVals sEnd,
      Sem.run (runInvokeCall ctx fuel innerDepth calleeId callArgs) sCaller
        = .ok (retVals, sEnd) →
      Q retVals := by
  intro retVals sEnd hrun
  have hget : ∀ s : MachineState, Sem.run Sem.getState s = .ok (s, s) := fun _ => rfl
  have hset : ∀ s s' : MachineState, Sem.run (Sem.setState s') s = .ok ((), s') :=
    fun _ _ => rfl
  have hthrow : ∀ {α β : Type} (e : SemError) (k : α → Sem β) (s : MachineState),
      Sem.run (throw e >>= k) s = .error e := fun _ _ _ => rfl
  have hAbi : callee.body.abi = none := by
    cases h : callee.body.abi with
    | none => rfl
    | some abi =>
      simp only [runInvokeCall, hFn, pure_bind, requireUntypedAbi, h, Sem.throwUnsupported, Option.isSome, if_true, bind_assoc, hthrow] at hrun <;> cases hrun
  unfold runInvokeCall at hrun
  simp only [hFn, pure_bind, hAbi, requireUntypedAbi_none] at hrun
  simp only [hFn, checkCallArity_ok callArgs callee.body.paramTys hArity,
    Sem.run_bind, Sem.run_pure, hget, hset, Except.bind] at hrun
  -- The argument poison guard (WS2.10): poison arguments throw.
  have hpa : callArgs.any Value.isPoison = false := by
    cases hp : callArgs.any Value.isPoison with
    | false => rfl
    | true =>
      obtain ⟨e, he⟩ := Sem.rejectPoisonValues_run_error callArgs "Call arguments" sCaller hp
      rw [he] at hrun; simp at hrun
  rw [Sem.rejectPoisonValues_run_ok callArgs "Call arguments" sCaller hpa] at hrun
  dsimp only at hrun
  cases hrec : Sem.run
      (stepNWithContext (ctx.forFunction callee) fuel innerDepth callee.cfg callee.entryBlock callArgs)
      { sCaller with locals := ValueMap.empty, nextValueId := 0 } with
  | error e => rw [hrec] at hrun; simp at hrun
  | ok p =>
    obtain ⟨rv, se⟩ := p
    rw [hrec] at hrun
    cases hret : checkReturnArity rv callee.body.returnTys with
    | error msg =>
      simp only [hret, Sem.throwTypeError] at hrun
      rw [hthrow] at hrun
      exact absurd hrun (by simp)
    | ok u =>
      simp only [hret, Sem.run_bind, Sem.run_pure, hget, hset, Except.bind] at hrun
      -- The return poison guard (WS2.10): poison returns throw.
      have hpr : rv.any Value.isPoison = false := by
        cases hp : rv.any Value.isPoison with
        | false => rfl
        | true =>
          obtain ⟨e, he⟩ := Sem.rejectPoisonValues_run_error rv "Call returns" se hp
          rw [he] at hrun; simp at hrun
      rw [Sem.rejectPoisonValues_run_ok rv "Call returns" se hpr] at hrun
      dsimp only at hrun
      simp only [Sem.run_bind, Sem.run_pure, hget, hset, Except.bind,
        Except.ok.injEq, Prod.mk.injEq] at hrun
      obtain ⟨hrv, _hse⟩ := hrun
      subst hrv
      exact hCalleePost rv se hrec

/-- **Forward decomposition of a successful `runInvokeCall` run** — the
    `Invoke` twin of `runCallReq_ok_decomp`: both arity checks passed, the
    callee body ran to success on the fresh empty-locals frame seeded from
    the caller state producing the SAME `retVals`, and the end state is that
    callee end state with the caller frame restored. -/
theorem runInvokeCall_ok_decomp
    (ctx : EvalContext) (fuel innerDepth : Nat)
    (calleeId : FuncId) (callee : EvalFunction) (callArgs : List Value)
    (s sEnd : MachineState) (retVals : List Value)
    (hFn : ctx.functions calleeId = some callee)
    (hCall : Sem.run (runInvokeCall ctx fuel innerDepth calleeId callArgs) s
      = .ok (retVals, sEnd)) :
    callArgs.length = callee.body.paramTys.length ∧
    callArgs.any Value.isPoison = false ∧
    retVals.length = callee.body.returnTys.length ∧
    retVals.any Value.isPoison = false ∧
    ∃ sCalleeEnd,
      Sem.run (stepNWithContext (ctx.forFunction callee) fuel innerDepth
          callee.cfg callee.entryBlock callArgs)
        { s with locals := ValueMap.empty, nextValueId := 0 }
        = .ok (retVals, sCalleeEnd) ∧
      sEnd = restoreFrame sCalleeEnd (saveFrame s none) [] := by
  have hget : ∀ st : MachineState, Sem.run Sem.getState st = .ok (st, st) :=
    fun _ => rfl
  have hset : ∀ st st' : MachineState, Sem.run (Sem.setState st') st = .ok ((), st') :=
    fun _ _ => rfl
  have hthrow : ∀ {α β : Type} (e : SemError) (k : α → Sem β) (st : MachineState),
      Sem.run (throw e >>= k) st = .error e := fun _ _ _ => rfl
  have hAbi : callee.body.abi = none := by
    cases h : callee.body.abi with
    | none => rfl
    | some abi =>
      simp only [runInvokeCall, hFn, pure_bind, requireUntypedAbi, h, Sem.throwUnsupported, Option.isSome, if_true, bind_assoc, hthrow] at hCall <;> cases hCall
  unfold runInvokeCall at hCall
  simp only [hFn, pure_bind, hAbi, requireUntypedAbi_none] at hCall
  try simp only [hFn, Sem.run_bind, Sem.run_pure, hget, hset, Except.bind] at hCall
  cases hca : checkCallArity callArgs callee.body.paramTys with
  | error msg =>
    rw [hca] at hCall
    simp only [Sem.throwTypeError] at hCall
    rw [hthrow] at hCall
    exact absurd hCall (by simp)
  | ok u =>
    cases u
    rw [hca] at hCall
    have hArity : callArgs.length = callee.body.paramTys.length := by
      unfold checkCallArity at hca
      split at hca
      next h => exact eq_of_beq h
      next h => exact absurd hca (by simp)
    simp only [Sem.run_bind, Sem.run_pure, hget, hset, Except.bind] at hCall
    -- The argument poison guard (WS2.10): poison arguments throw.
    have hpa : callArgs.any Value.isPoison = false := by
      cases hp : callArgs.any Value.isPoison with
      | false => rfl
      | true =>
        obtain ⟨e, he⟩ := Sem.rejectPoisonValues_run_error callArgs "Call arguments" s hp
        rw [he] at hCall; simp at hCall
    rw [Sem.rejectPoisonValues_run_ok callArgs "Call arguments" s hpa] at hCall
    dsimp only at hCall
    cases hrec : Sem.run
        (stepNWithContext (ctx.forFunction callee) fuel innerDepth callee.cfg callee.entryBlock callArgs)
        { s with locals := ValueMap.empty, nextValueId := 0 } with
    | error e => rw [hrec] at hCall; simp at hCall
    | ok p =>
      obtain ⟨rv, se⟩ := p
      rw [hrec] at hCall
      cases hret : checkReturnArity rv callee.body.returnTys with
      | error msg =>
        simp only [hret, Sem.throwTypeError] at hCall
        rw [hthrow] at hCall
        exact absurd hCall (by simp)
      | ok u =>
        cases u
        have hRet : rv.length = callee.body.returnTys.length := by
          unfold checkReturnArity at hret
          split at hret
          next h => exact eq_of_beq h
          next h => exact absurd hret (by simp)
        simp only [hret, Sem.run_bind, Sem.run_pure, hget, hset, Except.bind] at hCall
        -- The return poison guard (WS2.10): poison returns throw.
        have hpr : rv.any Value.isPoison = false := by
          cases hp : rv.any Value.isPoison with
          | false => rfl
          | true =>
            obtain ⟨e, he⟩ := Sem.rejectPoisonValues_run_error rv "Call returns" se hp
            rw [he] at hCall; simp at hCall
        rw [Sem.rejectPoisonValues_run_ok rv "Call returns" se hpr] at hCall
        dsimp only at hCall
        simp only [Sem.run_bind, Sem.run_pure, hget, hset, Except.bind,
          Except.ok.injEq, Prod.mk.injEq] at hCall
        obtain ⟨hrv, hse⟩ := hCall
        subst hrv
        subst hse
        exact ⟨hArity, hpa, hRet, hpr, se, rfl, rfl⟩

/-- **Invoke postcondition transfer over `stepNWithContext` itself.**  The
    `Invoke` analogue of `proof_context_assume_sound_evaluator`, stated
    honestly against everything the `InvokeReq` branch does after the call:
    for a caller block whose terminator is an `Invoke`, if the callee
    guarantees `Q` on the return values of every terminating run, then a
    successful run of the evaluator through that block DECOMPOSES as

    * a call whose return values `retVals` satisfy `Q`,
    * `bindResultDests termDests retVals` — the invoke node's result
      destinations are bound to exactly those `Q`-satisfying values in the
      caller frame (state `sCall` → `sBound`),
    * the normal-edge argument evaluation (which may read those results;
      `sBound` → `sMid`, a pure read), and
    * the normal-edge continuation from `sMid`, which produces the overall
      result — at the UNdecremented depth `innerDepth + 1`.

    So the caller may rely on `Q` for the invoke's results from the moment
    the normal edge is entered — the ProofContext-transfer statement for the
    `Invoke` path.  The unwind edge is never taken (non-throwing executable
    model, `panic=abort`); a future unwinding model must revisit what `Q`
    means on the unwind edge (the callee did NOT return values there). -/
theorem proof_context_assume_sound_invoke_evaluator
    (ctx : EvalContext) (fuel innerDepth : Nat) (cfg : CFG) (pc : BlockId)
    (params : List (ValueId × Ty)) (args : List Value)
    (calleeId : FuncId) (callee : EvalFunction)
    (argIds normalArgIds : List ValueId) (normalDest unwindDest : BlockId)
    (termDests : List ValueId)
    (Q : List Value → Prop) (s : MachineState)
    (hBlock : cfg pc = some
      { params := params
        body := []
        terminator := .Invoke calleeId argIds normalDest normalArgIds unwindDest
        terminatorResultDests := termDests })
    (hFn : ctx.functions calleeId = some callee)
    (hCalleePost :
      ∀ (callArgs retVals : List Value) (sCall sCalleeEnd : MachineState),
        Sem.run (stepNWithContext (ctx.forFunction callee) fuel innerDepth
            callee.cfg callee.entryBlock callArgs)
          { sCall with locals := ValueMap.empty, nextValueId := 0 }
          = .ok (retVals, sCalleeEnd) →
        Q retVals) :
    ∀ out sEnd,
      Sem.run (stepNWithContext ctx (fuel + 1) (innerDepth + 1) cfg pc args) s
        = .ok (out, sEnd) →
      ∃ (retVals edgeArgs : List Value) (sCall sBound sMid : MachineState),
        Q retVals ∧
        Sem.run (bindResultDests termDests retVals) sCall = .ok ((), sBound) ∧
        Sem.run (normalArgIds.mapM Sem.lookupValue) sBound = .ok (edgeArgs, sMid) ∧
        Sem.run (stepNWithContext ctx fuel (innerDepth + 1) cfg normalDest edgeArgs)
            sMid
          = .ok (out, sEnd) := by
  intro out sEnd hrun
  rw [stepNWithContext_invokeReq_eq_runInvokeCall_bind ctx fuel innerDepth cfg pc
    params args calleeId argIds normalArgIds normalDest unwindDest termDests
    hBlock] at hrun
  have hrun := checked_prefix_ok_bare _ _ s sEnd out hrun
  -- Peel the prefix one effect at a time; each `.error` contradicts `.ok`.
  rw [Sem.run_bind] at hrun
  cases h1 : Sem.run (bindBlockParamsChecked params args) s with
  | error e => rw [h1] at hrun; exact absurd hrun (by simp [Except.bind])
  | ok p1 =>
    obtain ⟨_u1, s1⟩ := p1
    rw [h1] at hrun
    simp only [Except.bind] at hrun
    rw [Sem.run_bind] at hrun
    cases h2 : Sem.run (argIds.mapM Sem.lookupValue) s1 with
    | error e => rw [h2] at hrun; exact absurd hrun (by simp [Except.bind])
    | ok p2 =>
      obtain ⟨callArgs, s2⟩ := p2
      rw [h2] at hrun
      simp only [Except.bind] at hrun
      rw [Sem.run_bind] at hrun
      cases h3 : Sem.run (runInvokeCall ctx fuel innerDepth calleeId callArgs) s2 with
      | error e => rw [h3] at hrun; exact absurd hrun (by simp [Except.bind])
      | ok p3 =>
        obtain ⟨retVals, sCall⟩ := p3
        rw [h3] at hrun
        simp only [Except.bind] at hrun
        rw [Sem.run_bind] at hrun
        cases h4 : Sem.run (ctx.bindCallResults
            (.Invoke calleeId argIds normalDest normalArgIds unwindDest) termDests retVals) sCall with
        | error e => rw [h4] at hrun; exact absurd hrun (by simp [Except.bind])
        | ok p4 =>
          obtain ⟨u4, sBound⟩ := p4
          cases u4
          rw [h4] at hrun
          simp only [Except.bind] at hrun
          rw [Sem.run_bind] at hrun
          cases h5 : Sem.run (normalArgIds.mapM Sem.lookupValue) sBound with
          | error e => rw [h5] at hrun; exact absurd hrun (by simp [Except.bind])
          | ok p5 =>
            obtain ⟨edgeArgs, sMid⟩ := p5
            rw [h5] at hrun
            simp only [Except.bind] at hrun
            -- Q on retVals via the decomposition of the successful call.
            obtain ⟨-, -, -, -, sCalleeEnd, hInline, -⟩ :=
              runInvokeCall_ok_decomp ctx fuel innerDepth calleeId callee callArgs
                s2 sCall retVals hFn h3
            exact ⟨retVals, edgeArgs, sCall, sBound, sMid,
              hCalleePost callArgs retVals s2 sCalleeEnd hInline,
              bindCallResults_ok_bare ctx _ _ _ _ _ h4, h5, hrun⟩

-- =================================================================
-- Future work stubs (Phase 4 completeness claims)
-- =================================================================

/-
## Theorems to prove in subsequent iterations

1. **Call stack depth bounded by fuel:**
   For any execution via stepN with fuel n, the implicit call stack
   depth never exceeds n.  This requires extending stepN with
   explicit call stack tracking.

2. **Return restores caller frame:**
   After semReturn + restoreFrame, the machine state locals equal
   the saved frame's locals (with return value bound).

3. **CallIndirect is Call after resolution:**
   semCallIndirect with a valid function pointer produces the same
   result as semCall with the resolved FuncId.

4. **Switch completeness:**
   For an integer value and a complete case list covering all possible
   values, matchSwitchCase always returns Some.
-/

end TrustIr
