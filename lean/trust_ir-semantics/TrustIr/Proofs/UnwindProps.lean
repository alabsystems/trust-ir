-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Amendment D, Part 2 (`docs/SPEC_RATIFICATIONS.md` §21): unwinding as an
-- exit, and the abort projection.
--
-- The contextual evaluator runs under a named `PanicStrategy`. Under
-- `.unwind` a failed check raises, an invoke-family terminator catches the
-- unwinding into its landing pad and `Resume` re-raises it; under `.abort`
-- (the ratified panic=abort projection) none of that happens. This file
-- proves that the abort run is a PREFIX of the unwind run of the same program
-- from the same state:
--
--   * `stepNWithContext_abort_prefix`: for every fuel, depth, CFG, block and
--     arguments, the abort run either IS the unwind run (same values, same
--     final state, same error) or it stopped at an `AbortStop` outcome — a
--     panic (its first raise), a refused landing pad or `Resume`
--     (`unsupported.host_unwind`), or an unwinding — where the unwind run may
--     go on;
--   * `abort_projection_normal_exit`, `abort_projection_ub`,
--     `abort_projection_out_of_fuel`: lifted to the entry
--     (`evalFunctionInContext`), a normal return, undefined behaviour and
--     running out of fuel of the abort run are outcomes of the unwind run
--     too, verbatim. So a verdict computed under `.unwind` — no UB on any
--     executed instruction, a postcondition on every normal return — covers
--     the abort build as well;
--   * `plain_call_propagates_unwinding`: a plain call propagates an
--     unwinding out of its callee unchanged;
--   * `resume_reraises_in_hand_exception`: `Resume` of a recorded exception
--     object re-raises it.
--
-- `SemPrefix` is a one-field structure rather than a bare `∀ s, ...`, so the
-- walk below cannot `intro` through it by accident.

import TrustIr.Semantics.Eval
import TrustIr.Proofs.CallProps

namespace TrustIr

/-- An error at which an `.abort` run may stop while the `.unwind` run of
    the same program goes on: the first raise (a panic under `.abort`), a
    landing pad or `Resume` the projection refuses (`unsupported.host_unwind`),
    or an unwinding. -/
def AbortStopError : SemError → Prop
  | .panic _ _ => True
  | .unsupported .hostUnwind _ => True
  | .unwinding _ _ => True
  | _ => False

/-- `AbortStopError` lifted to a run's outcome (a normal return is never
    one). -/
def AbortStop {α : Type} : Except SemError α → Prop
  | .error e => AbortStopError e
  | .ok _ => False

/-- `a` is an abort prefix of `u`: from every state, `a`'s run IS `u`'s run,
    or `a` stopped at an `AbortStop` outcome. -/
structure SemPrefix {α : Type} (a u : Sem α) : Prop where
  run : ∀ s, Sem.run a s = Sem.run u s ∨ AbortStop (Sem.run a s)

namespace SemPrefix

theorem refl {α : Type} (m : Sem α) : SemPrefix m m := ⟨fun _ => Or.inl rfl⟩

theorem of_stop {α : Type} {a u : Sem α} (h : ∀ s, AbortStop (Sem.run a s)) :
    SemPrefix a u := ⟨fun s => Or.inr (h s)⟩

theorem seq {α β : Type} {mA mU : Sem α} {fA fU : α → Sem β}
    (hm : SemPrefix mA mU) (hf : ∀ x, SemPrefix (fA x) (fU x)) :
    SemPrefix (mA >>= fA) (mU >>= fU) := by
  constructor
  intro s
  rw [Sem.run_bind, Sem.run_bind]
  rcases hm.run s with h | h
  · rw [← h]
    cases Sem.run mA s with
    | error e => exact Or.inl rfl
    | ok p =>
      obtain ⟨x, s'⟩ := p
      exact (hf x).run s'
  · cases hr : Sem.run mA s with
    | error e =>
      rw [hr] at h
      exact Or.inr h
    | ok p =>
      rw [hr] at h
      exact False.elim h

/-- The loop `forIn` runs is a prefix when its body is. -/
theorem loopAux {β γ : Type} {fA fU : β → γ → Sem (ForInStep γ)}
    (h : ∀ x c, SemPrefix (fA x c) (fU x c)) :
    ∀ (xs : List β) (b : γ), SemPrefix (forIn xs b fA) (forIn xs b fU) := by
  intro xs
  induction xs with
  | nil => intro b; exact SemPrefix.refl _
  | cons x xs ih =>
    intro b
    rw [List.forIn_cons, List.forIn_cons]
    refine SemPrefix.seq (h x b) (fun r => ?_)
    cases r with
    | done c => exact SemPrefix.refl _
    | yield c => exact ih c

theorem loop {β γ : Type} (xs : List β) (b : γ) {fA fU : β → γ → Sem (ForInStep γ)}
    (h : ∀ x c, SemPrefix (fA x c) (fU x c)) :
    SemPrefix (forIn xs b fA) (forIn xs b fU) :=
  loopAux h xs b

/-- An abort prefix's normal return is the unwind run's. -/
theorem ok_eq {α : Type} {a u : Sem α} (h : SemPrefix a u) {s : MachineState}
    {r : α × MachineState} (ha : Sem.run a s = .ok r) : Sem.run u s = .ok r := by
  rcases h.run s with h | h
  · rw [← h, ha]
  · rw [ha] at h; exact False.elim h

/-- An abort prefix's undefined behaviour is the unwind run's. -/
theorem ub_eq {α : Type} {a u : Sem α} (h : SemPrefix a u) {s : MachineState}
    {m : String} (ha : Sem.run a s = .error (.ub m)) : Sem.run u s = .error (.ub m) := by
  rcases h.run s with h | h
  · rw [← h, ha]
  · rw [ha] at h; exact False.elim h

/-- An abort prefix's running out of fuel is the unwind run's. -/
theorem outOfFuel_eq {α : Type} {a u : Sem α} (h : SemPrefix a u) {s : MachineState}
    (ha : Sem.run a s = .error .outOfFuel) : Sem.run u s = .error .outOfFuel := by
  rcases h.run s with h | h
  · rw [← h, ha]
  · rw [ha] at h; exact False.elim h

end SemPrefix

/-- `tryCatch` in `Sem`: the handler runs from the state the protected
    computation started in. -/
theorem Sem.run_tryCatch {α : Type} (m : Sem α) (h : SemError → Sem α) (s : MachineState) :
    Sem.run (tryCatch m h) s = Except.tryCatch (Sem.run m s) (fun e => Sem.run (h e) s) := rfl

-- -----------------------------------------------------------------
-- The strategy-dependent steps, one lemma each
-- -----------------------------------------------------------------

/-- R1: a body `Assert` under `.abort` is a prefix of the same `Assert`
    under `.unwind` (equal, unless the abort run panicked: its first raise). -/
theorem SemPrefix.raiseIfUnwind (m : Sem InstrResult) (model : ByteModel := .le64) :
    SemPrefix (raiseIfUnwind .abort m model) (raiseIfUnwind .unwind m model) := by
  constructor
  intro s
  simp only [TrustIr.raiseIfUnwind]
  rw [Sem.run_tryCatch]
  cases Sem.run m s with
  | ok p => exact Or.inl rfl
  | error e => cases e <;> first | exact Or.inr trivial | exact Or.inl rfl

/-- R5: a landing pad under `.abort` is the projection's refusal
    (`unsupported.host_unwind`), an `AbortStop`. -/
theorem SemPrefix.landingPad (ctx : EvalContext) (isCleanup : Bool) (clauses : List Nat)
    (dests : List ValueId) :
    SemPrefix (semLandingPadWith .abort ctx (.LandingPad isCleanup clauses) dests)
      (semLandingPadWith .unwind ctx (.LandingPad isCleanup clauses) dests) := by
  exact SemPrefix.of_stop (fun _ => trivial)

/-- The terminator step under `.abort` (the bare step) is a prefix of the
    terminator step under `.unwind`: a failing `AssertInvoke` panics where the
    unwind run enters its pad, and `Resume` is refused where the unwind run
    re-raises; every other terminator steps identically. -/
theorem SemPrefix.stepTerm (cfg : CFG) (t : Inst) (model : ByteModel := .le64) :
    SemPrefix (stepInst t model) (stepTermUnwind cfg t model) := by
  constructor
  intro s
  cases t with
  | AssertInvoke cond kind site nd na ud =>
    simp only [stepTermUnwind]
    rw [Sem.run_tryCatch]
    cases Sem.run (stepInst (.AssertInvoke cond kind site nd na ud) model) s with
    | ok p => exact Or.inl rfl
    | error e => cases e <;> first | exact Or.inr trivial | exact Or.inl rfl
  | Resume exnId => exact Or.inr trivial
  | _ => exact Or.inl rfl

/-- Typed closure resolution is the same computation under either panic
    strategy; its fallback inherits the existing prefix relationship. -/
theorem SemPrefix.closureTermWithContext (ctx : EvalContext) (depth : Nat)
    (term : Inst) {abort unwind : Sem InstrResult} (h : SemPrefix abort unwind) :
    SemPrefix (TrustIr.closureTermWithContext ctx depth term abort)
      (TrustIr.closureTermWithContext ctx depth term unwind) := by
  cases term with
  | CallIndirect valueId sig argIds conv =>
    simp only [TrustIr.closureTermWithContext]
    refine SemPrefix.seq (SemPrefix.refl _) (fun value => ?_)
    cases value <;> first | exact h | exact SemPrefix.refl _
  | InvokeIndirect valueId sig argIds conv normalDest normalArgs unwindDest =>
    simp only [TrustIr.closureTermWithContext]
    refine SemPrefix.seq (SemPrefix.refl _) (fun value => ?_)
    cases value <;> first | exact h | exact SemPrefix.refl _
  | _ => exact h

/-- Contextual termination preserves the same abort/unwind prefix theorem. -/
theorem SemPrefix.stepTermWithContext (ctx : EvalContext) (depth : Nat)
    (cfg : CFG) (term : Inst) :
    SemPrefix (TrustIr.stepTermWithContext ctx depth cfg term .abort)
      (TrustIr.stepTermWithContext ctx depth cfg term .unwind) := by
  exact SemPrefix.closureTermWithContext ctx depth term
    (SemPrefix.stepTerm cfg term ctx.byteModel)

/-- R3: the invoke-family catch. The abort run never catches; where the
    unwind run catches an unwinding, the abort run stopped at it. -/
theorem SemPrefix.invokeCatch {mA mU : Sem (List Value)} (h : SemPrefix mA mU) :
    SemPrefix (invokeCatch .abort mA) (invokeCatch .unwind mU) := by
  constructor
  intro s
  simp only [TrustIr.invokeCatch]
  rw [Sem.run_tryCatch, Sem.run_bind, Sem.run_bind]
  rcases h.run s with h | h
  · rw [← h]
    cases Sem.run mA s with
    | ok p =>
      obtain ⟨x, s'⟩ := p
      exact Or.inl rfl
    | error e => cases e <;> first | exact Or.inr trivial | exact Or.inl rfl
  · cases hr : Sem.run mA s with
    | error e =>
      rw [hr] at h
      exact Or.inr h
    | ok p =>
      rw [hr] at h
      exact False.elim h

/-- R7: the entry's report of an escaping unwinding. -/
theorem SemPrefix.exitUnwinding {mA mU : Sem (List Value)} (h : SemPrefix mA mU) :
    SemPrefix (exitUnwinding .abort mA) (exitUnwinding .unwind mU) := by
  constructor
  intro s
  simp only [TrustIr.exitUnwinding]
  rw [Sem.run_tryCatch]
  rcases h.run s with h | h
  · rw [← h]
    cases Sem.run mA s with
    | ok p =>
      obtain ⟨x, s'⟩ := p
      exact Or.inl rfl
    | error e => cases e <;> first | exact Or.inr trivial | exact Or.inl rfl
  · cases hr : Sem.run mA s with
    | error e =>
      rw [hr] at h
      exact Or.inr h
    | ok p =>
      rw [hr] at h
      exact False.elim h

-- -----------------------------------------------------------------
-- The prefix theorem
-- -----------------------------------------------------------------

set_option maxHeartbeats 40000000 in
/-- **The abort run is a prefix of the unwind run.** For every fuel, call
    depth, CFG, block and arguments, the `.abort` run of the contextual
    evaluator either IS the `.unwind` run from the same state (same values,
    same final state, same error), or it stopped at an `AbortStop` outcome.
    By fuel induction: one block step is the same program under both
    strategies except at the strategy-dependent steps (each related by its
    lemma above) and at the recursive calls (the induction hypothesis). -/
theorem stepNWithContext_abort_prefix (ctx : EvalContext) :
    ∀ (fuel depth : Nat) (cfg : CFG) (pc : BlockId) (args : List Value),
      SemPrefix (stepNWithContext ctx fuel depth cfg pc args .abort)
        (stepNWithContext ctx fuel depth cfg pc args .unwind) := by
  intro fuel
  induction fuel generalizing ctx with
  | zero =>
    intro depth cfg pc args
    simp only [stepNWithContext]
    exact SemPrefix.refl _
  | succ n ih =>
    intro depth cfg pc args
    simp only [stepNWithContext]
    repeat' (first
      | with_reducible exact SemPrefix.refl _
      | with_reducible exact ih _ _ _ _ _
      | with_reducible exact SemPrefix.raiseIfUnwind _ ctx.byteModel
      | with_reducible exact SemPrefix.landingPad _ _ _ _
      | with_reducible exact SemPrefix.stepTermWithContext ctx _ _ _
      | with_reducible exact SemPrefix.stepTerm _ _ ctx.byteModel
      | (with_reducible apply SemPrefix.invokeCatch; with_reducible exact ih _ _ _ _ _)
      | refine SemPrefix.seq ?_ ?_
      | refine SemPrefix.loop _ _ ?_
      | intro _
      | split
      | dsimp only)

set_option maxHeartbeats 4000000 in
/-- The prefix theorem at the entry (`evalFunctionInContext`). -/
theorem evalFunctionInContext_abort_prefix (ctx : EvalContext) (entry : FuncId)
    (args : List Value) (fuel : Nat) :
    SemPrefix (evalFunctionInContext ctx entry args fuel .abort)
      (evalFunctionInContext ctx entry args fuel .unwind) := by
  unfold evalFunctionInContext
  repeat' (first
    | with_reducible exact SemPrefix.refl _
    | (apply SemPrefix.exitUnwinding; exact stepNWithContext_abort_prefix _ _ _ _ _ _)
    | refine SemPrefix.seq ?_ ?_
    | intro _
    | split
    | dsimp only)

/-- **Abort projection, normal exit.** An abort run that returns normally is
    an unwind run that returns the same values in the same final state: a
    postcondition proved of every normal return of the unwind build binds the
    abort build too. -/
theorem abort_projection_normal_exit (ctx : EvalContext) (entry : FuncId)
    (args : List Value) (fuel : Nat) (s : MachineState) (vs : List Value)
    (s' : MachineState)
    (h : Sem.run (evalFunctionInContext ctx entry args fuel .abort) s = .ok (vs, s')) :
    Sem.run (evalFunctionInContext ctx entry args fuel .unwind) s = .ok (vs, s') :=
  (evalFunctionInContext_abort_prefix ctx entry args fuel).ok_eq h

/-- **Abort projection, undefined behaviour.** UB in the abort run is UB in
    the unwind run, with the same diagnostic: a NoUB verdict for the unwind
    build (every executed instruction, cleanup paths included) covers the
    abort build. -/
theorem abort_projection_ub (ctx : EvalContext) (entry : FuncId)
    (args : List Value) (fuel : Nat) (s : MachineState) (m : String)
    (h : Sem.run (evalFunctionInContext ctx entry args fuel .abort) s = .error (.ub m)) :
    Sem.run (evalFunctionInContext ctx entry args fuel .unwind) s = .error (.ub m) :=
  (evalFunctionInContext_abort_prefix ctx entry args fuel).ub_eq h

/-- **Abort projection, out of fuel.** An abort run that runs out of fuel is
    an unwind run that runs out of fuel. -/
theorem abort_projection_out_of_fuel (ctx : EvalContext) (entry : FuncId)
    (args : List Value) (fuel : Nat) (s : MachineState)
    (h : Sem.run (evalFunctionInContext ctx entry args fuel .abort) s = .error .outOfFuel) :
    Sem.run (evalFunctionInContext ctx entry args fuel .unwind) s = .error .outOfFuel :=
  (evalFunctionInContext_abort_prefix ctx entry args fuel).outOfFuel_eq h

-- -----------------------------------------------------------------
-- Propagation and re-raise
-- -----------------------------------------------------------------

/-- **A plain call propagates an unwinding.** Under `.unwind`, a callee run
    that ends in an unwinding makes the plain call (`runCallReq`, which IS
    the evaluator's Call handling: `stepNWithContext_callReq_eq_runCallReq`,
    `stepNWithContext_bodyCall_eq_runCallReq_bind`) end in the SAME
    unwinding, exception and state included: a plain call has no landing pad. -/
theorem plain_call_propagates_unwinding
    (ctx : EvalContext) (fuel callDepth : Nat)
    (calleeId : FuncId) (callee : EvalFunction) (callArgs : List Value)
    (s : MachineState) (exn : Addr) (st : MachineState)
    (hFn : ctx.functions calleeId = some callee)
    (hAbi : callee.body.abi = none)
    (hArity : callArgs.length = callee.body.paramTys.length)
    (hArgsClean : callArgs.any Value.isPoison = false)
    (hCallee : Sem.run (stepNWithContext (ctx.forFunction callee) fuel callDepth
          callee.cfg callee.entryBlock callArgs .unwind)
        { s with locals := ValueMap.empty, nextValueId := 0 } = .error (.unwinding exn st)) :
    Sem.run (runCallReq ctx fuel callDepth calleeId callArgs .unwind) s
      = .error (.unwinding exn st) := by
  have hget : ∀ st : MachineState, Sem.run Sem.getState st = .ok (st, st) :=
    fun _ => rfl
  have hset : ∀ st st' : MachineState, Sem.run (Sem.setState st') st = .ok ((), st') :=
    fun _ _ => rfl
  unfold runCallReq
  simp only [hFn, hAbi, requireUntypedAbi_none, checkCallArity_ok callArgs callee.body.paramTys hArity,
    Sem.run_bind, Sem.run_pure, hget, hset, Except.bind,
    Sem.rejectPoisonValues_run_ok callArgs _ s hArgsClean, hCallee]

/-- **`Resume` re-raises the exception in hand.** Under `.unwind`, `Resume`
    of a pointer whose address is a recorded exception object re-raises that
    exception, from the current state, whatever the pointer's provenance. -/
theorem resume_reraises_in_hand_exception (cfg : CFG) (exnId : ValueId) (exn : Addr)
    (prov : Option AllocId) (s : MachineState)
    (hv : s.lookupValue exnId = some (.ptr exn prov))
    (hrec : s.exceptions.any (fun row => row.1 == exn) = true) :
    Sem.run (stepTermUnwind cfg (.Resume exnId)) s = .error (.unwinding exn s) := by
  have hget : ∀ st : MachineState, Sem.run Sem.getState st = .ok (st, st) := fun _ => rfl
  simp only [stepTermUnwind, semResumeUnwind, Sem.lookupValue, Sem.run_bind, hget,
    Except.bind, hv, Sem.run_pure, hrec, ↓reduceIte]
  try rfl

end TrustIr
