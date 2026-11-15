-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameRecursiveExits

namespace TrustIr.FrameLifetime
open GenericCoro GenericCoro.Prefix NoUnwindEffects

private theorem panic_no_unwind {α : Type} (message : String) (site : Option PanicOutcomeSite) :
    CallCheckNoUnwind (Sem.throwPanic message site : Sem α) := by
  intro state exception after run
  cases run

local macro "assert_leaves" : tactic => `(tactic|
  repeat' first
    | exact pure_safe _
    | exact type_safe _
    | exact ub_safe _
    | exact lookup_safe _
    | exact reject_safe _ _
    | exact get_safe
    | exact panic_no_unwind _ _
    | (refine CallCheckNoUnwind.bind _ _ ?_ (fun value => ?_) <;> try dsimp only)
    | (split <;> try dsimp only))

theorem assert_operand_no_unwind (id : ValueId) (role : String) : CallCheckNoUnwind (assertOperandNat id role) := by
  unfold assertOperandNat
  assert_leaves

theorem assert_message_no_unwind (kind : AssertKind) : CallCheckNoUnwind (assertFailMessage kind) := by
  unfold assertFailMessage
  repeat' first
    | exact assert_operand_no_unwind _ _
    | (solve | assert_leaves)
    | (refine CallCheckNoUnwind.bind _ _ ?_ (fun value => ?_) <;> try dsimp only)
    | (split <;> try dsimp only)

theorem panic_location_no_unwind (location : PanicLocation) : CallCheckNoUnwind (resolvePanicLocation location) := by
  unfold resolvePanicLocation
  assert_leaves

theorem assert_failure_no_unwind {α : Type} (kind : AssertKind) (site : Option PanicSite) :
    CallCheckNoUnwind (semAssertFail kind site : Sem α) := by
  unfold semAssertFail
  apply CallCheckNoUnwind.bind _ _ (assert_message_no_unwind kind)
  intro message
  cases site with
  | none => exact panic_no_unwind _ _
  | some site => exact CallCheckNoUnwind.bind _ _ (panic_location_no_unwind site.location) (fun _ => panic_no_unwind _ _)

theorem assert_step_no_unwind (ctx : EvalContext) (condition : ValueId) (kind : AssertKind) (site : Option PanicSite) :
    CallCheckNoUnwind (stepInstWithContext ctx (.Assert condition kind site)) := by
  change CallCheckNoUnwind (stepInst (.Assert condition kind site) ctx.byteModel)
  unfold stepInst
  repeat' first
    | exact assert_failure_no_unwind _ _
    | (solve | assert_leaves)
    | (refine CallCheckNoUnwind.bind _ _ ?_ (fun value => ?_) <;> try dsimp only)
    | (split <;> try dsimp only)

/-- Normal assertion success is the original no-op; all diagnostics/refusals
are consumed from the actual original action. -/
theorem assert_step_frame_exit (ctx : EvalContext) (condition : ValueId) (kind : AssertKind) (site : Option PanicSite) :
    FrameActionValid (fun _ result => result = .value none) (stepInstWithContext ctx (.Assert condition kind site)) := by
  apply frame_action_of_success_no_unwind _ _ (assert_step_no_unwind ctx condition kind site)
  intro state after result valid run
  have anchored : Sem.run (stepInst (.Assert condition kind site)) state = .ok (result,after) := run
  obtain ⟨same,_⟩ := stepInst_assert_ok condition kind site state (result,after) anchored
  cases same
  exact ⟨valid,rfl,.refl _⟩

private theorem run_catch {α : Type} (action : Sem α) (handler : SemError → Sem α) (state : MachineState) :
    Sem.run (tryCatch action handler) state =
      match Sem.run action state with
      | .ok result => .ok result
      | .error error => Sem.run (handler error) state := by
  rw [Sem.run_tryCatch]
  cases Sem.run action state <;> rfl

/-- Panic conversion raises from the original catch state; an existing unwind
retains its own embedded throw state. The StateT rollback is not mistaken for
that throw state, and no successful-only premise is used. -/
theorem raise_if_unwind_frame_exit (post : Nat → InstrResult → Prop) (strategy : PanicStrategy)
    (action : Sem InstrResult) (model : ByteModel) (state : MachineState) (valid : WellMintedState state)
    (executedValid : FrameActionExit post state (Sem.run action state)) :
    FrameActionExit post state (Sem.run (raiseIfUnwind strategy action model) state) := by
  cases strategy with
  | abort => exact executedValid
  | unwind =>
    unfold raiseIfUnwind
    rw [run_catch]
    cases executed : Sem.run action state with
    | ok pair => rw [executed] at executedValid; exact executedValid
    | error error =>
      rw [executed] at executedValid
      cases error
      case panic message site => exact raise_frame_action post message site model state valid
      case unwinding exception after => exact executedValid
      all_goals exact True.intro

theorem assert_body_frame_exit (recurse : Recurse) (ctx : EvalContext) (depth : Nat) (strategy : PanicStrategy)
    (condition : ValueId) (kind : AssertKind) (site : Option PanicSite) (dests : List ValueId) :
    FrameActionValid (fun _ _ => True) (evalBodyStep recurse ctx depth strategy (.Assert condition kind site,dests)) := by
  intro state valid
  apply FrameActionExit.bind (fun _ result => result = .value none) (fun _ _ => True) _ _ state
    (raise_if_unwind_frame_exit _ strategy _ ctx.byteModel state valid (assert_step_frame_exit ctx condition kind site state valid))
  intro result before beforeValid _
  apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ before
    (instruction_results_frame_action ctx (.Assert condition kind site) result dests before beforeValid)
  intro unit published publishedValid _
  cases unit
  exact ⟨publishedValid,True.intro,.refl _⟩

/-- Actual pad body entry consumes the hand and publishes its pointer/selector.
Abort or absent hand keeps the original unsupported refusal. -/
theorem landing_pad_frame_exit (ctx : EvalContext) (strategy : PanicStrategy) (cleanup : Bool)
    (clauses : List Nat) (dests : List ValueId) :
    FrameActionValid (fun _ _ => True) (semLandingPadWith strategy ctx (.LandingPad cleanup clauses) dests) := by
  intro state valid
  cases strategy with
  | abort => exact True.intro
  | unwind =>
    cases hand : state.inHand with
    | none =>
      simp [semLandingPadWith,hand,stepInstWithContext,stepInst,Sem.run,Sem.getState,StateT.run,StateT.bind,StateT.get,
        StateT.lift,bind,pure,Except.bind,Except.pure,Sem.throwUnsupported,throw,throwThe,MonadExceptOf.throw,FrameActionExit]
    | some held =>
      rcases held with ⟨exception,allocation,selector⟩
      have anchored : Sem.run (semLandingPadWith .unwind ctx (.LandingPad cleanup clauses) dests) state =
          Sem.run (ctx.bindCallResults (.LandingPad cleanup clauses) dests [.ptr exception (some allocation),.int 32 (selector : Int)])
            {state with inHand := none} := by
        simp [semLandingPadWith,hand,Sem.run,Sem.getState,Sem.setState,StateT.run,StateT.bind,
          StateT.get,StateT.set,StateT.pure,bind,pure,Except.bind,Except.pure]
      rw [anchored]
      apply FrameActionExit.history (fun _ _ => True) state {state with inHand := none} _
        ⟨Nat.le_refl _,fun _ _ closed => closed⟩
      apply call_results_frame_exit ctx (.LandingPad cleanup clauses) dests
        [.ptr exception (some allocation),.int 32 (selector : Int)] {state with inHand := none} ⟨valid.table,valid.values⟩
      intro value member
      simp at member
      rcases member with rfl | rfl <;> intro lineage occurrence <;> cases occurrence

theorem landing_pad_body_frame_exit (recurse : Recurse) (ctx : EvalContext) (depth : Nat) (strategy : PanicStrategy)
    (cleanup : Bool) (clauses : List Nat) (dests : List ValueId) :
    FrameActionValid (fun _ _ => True) (evalBodyStep recurse ctx depth strategy (.LandingPad cleanup clauses,dests)) := by
  apply FrameActionValid.bind (fun _ _ => True) (fun _ _ => True) _ _ (landing_pad_frame_exit ctx strategy cleanup clauses dests)
  intro unit before beforeValid _
  cases unit
  exact ⟨beforeValid,True.intro,.refl _⟩

private theorem resume_no_success (id : ValueId) (state : MachineState) (result : InstrResult × MachineState) :
    Sem.run (semResumeUnwind id) state ≠ .ok result := by
  intro run
  cases found : state.lookupValue id with
  | none =>
    simp [semResumeUnwind,Sem.lookupValue,found,Sem.run,Sem.getState,Sem.throwTypeError,
      StateT.run,StateT.bind,StateT.get,StateT.pure,StateT.lift,bind,pure,Except.bind,Except.pure,
      throw,throwThe,MonadExceptOf.throw] at run
  | some held =>
    cases held
    case ptr address provenance =>
      by_cases recorded : state.exceptions.any (fun row => row.1 == address) = true <;>
        simp [semResumeUnwind,Sem.lookupValue,found,recorded,Sem.run,Sem.getState,Sem.throwUB,
          StateT.run,StateT.bind,StateT.get,StateT.pure,StateT.lift,bind,pure,Except.bind,Except.pure,
          throw,throwThe,MonadExceptOf.throw] at run
    all_goals simp [semResumeUnwind,Sem.lookupValue,found,Sem.run,Sem.getState,Sem.throwUB,
      StateT.run,StateT.bind,StateT.get,StateT.pure,StateT.lift,bind,pure,Except.bind,Except.pure,
      throw,throwThe,MonadExceptOf.throw] at run

/-- Resume never returns normally; its original embedded throw state is the
current caller state, including existing exception records and SSA values. -/
theorem resume_term_frame_exit (ctx : EvalContext) (depth : Nat) (cfg : CFG) (strategy : PanicStrategy) (id : ValueId) :
    FrameActionValid (fun _ _ => False) (stepTermWithContext ctx depth cfg (.Resume id) strategy) := by
  intro state valid
  cases strategy with
  | abort => exact True.intro
  | unwind =>
    change FrameActionExit (fun _ _ => False) state (Sem.run (semResumeUnwind id) state)
    cases executed : Sem.run (semResumeUnwind id) state with
    | ok pair => exact False.elim (resume_no_success id state pair executed)
    | error error =>
      cases error <;> first
        | exact True.intro
        | (have same := resume_unwind_state id state _ _ executed; subst_vars; exact ⟨valid,.refl _⟩)

end TrustIr.FrameLifetime
