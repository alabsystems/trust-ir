-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroPrefixCalls
import TrustIr.Proofs.SSAFreshStep

namespace TrustIr.GenericCoro.Prefix

theorem callFrameWith_run (check : List Value → Sem Unit) (callee : Sem (List Value))
    (state : MachineState) :
    Sem.run (callFrameWith check callee) state = (do
      let (values, after) ← Sem.run callee (callerWorld state)
      let (_, afterCheck) ← Sem.run (check values) after
      pure (values, restoreFrame afterCheck (saveFrame state none) [])) := rfl

/-- The callback and checker may have arbitrary effects and errors. They run
    on the same cleared callee state after any caller SSA replacement; only
    the actual saved caller frame is restored on return. -/
theorem callFrameWith_equivariant (check : List Value → Sem Unit)
    (callee : Sem (List Value)) : HeldMemoryFrames.Equivariant (callFrameWith check callee) := by
  intro state locals next
  simp only [callFrameWith_run,
    show callerWorld (HeldMemoryFrames.replaceSSA state locals next) = callerWorld state from rfl]
  cases called : Sem.run callee (callerWorld state) with
  | error error => rfl
  | ok result =>
    cases checked : Sem.run (check result.1) result.2 with
    | error error => simp only [Bind.bind, Pure.pure, Except.bind, Except.pure, checked]; rfl
    | ok result => simp only [Bind.bind, Pure.pure, Except.bind, Except.pure, checked]; rfl

theorem callFrameWith_fresh (check : List Value → Sem Unit) (callee : Sem (List Value)) :
    SSAFreshStep.KeepsFresh (callFrameWith check callee) :=
  SSAFreshStep.equivariant_fresh _ (callFrameWith_equivariant check callee)

theorem callFrame_with_checkReturns (ctx : EvalContext) (returnTys : List Ty)
    (callee : Sem (List Value)) :
    callFrame returnTys callee = callFrameWith (checkReturns ctx returnTys true false "Call: ") callee := by
  simp only [callFrame, finishCall, callFrameWith, finishCalleeWith, checkReturns,
    Bool.true_eq, Bool.false_eq_true, if_true, if_false, bind_assoc, pure_bind,
    bind_match_unit]
  apply bind_same
  intro caller
  apply bind_same
  intro unit
  apply bind_same
  intro values
  cases arity : checkReturnArity values returnTys with
  | error error => simp only [arity, bind_assoc]
  | ok unit => cases unit; simp only [arity, pure_bind]

theorem callFrame_equivariant (returnTys : List Ty) (callee : Sem (List Value)) :
    HeldMemoryFrames.Equivariant (callFrame returnTys callee) := by
  rw [callFrame_with_checkReturns EvalContext.empty]
  exact callFrameWith_equivariant _ _

theorem callFrame_fresh (returnTys : List Ty) (callee : Sem (List Value)) :
    SSAFreshStep.KeepsFresh (callFrame returnTys callee) :=
  SSAFreshStep.equivariant_fresh _ (callFrame_equivariant returnTys callee)

end TrustIr.GenericCoro.Prefix
