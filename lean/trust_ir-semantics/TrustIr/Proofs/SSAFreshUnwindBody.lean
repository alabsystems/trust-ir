-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SSAFreshContext
import TrustIr.Proofs.GenericCoroInvoke

namespace TrustIr.SSAFreshUnwindBody
open SSAFreshFrames SSAFreshStep SSAFreshInstructions SSAFreshMemory SSAFreshContext

/-- A StateT error carries no outer state; its handler starts from the actual
    original state, whose freshness is available independently of the error. -/
theorem tryCatch_fresh {α : Type} (action : Sem α) (handler : SemError → Sem α)
    (actionFresh : KeepsFresh action) (handlerFresh : ∀ error, KeepsFresh (handler error)) :
    KeepsFresh (tryCatch action handler) := by
  intro state result fresh run
  rw [Sem.run_tryCatch] at run
  cases found : Sem.run action state with
  | error error =>
    rw [found] at run
    exact handlerFresh error state result fresh run
  | ok returned =>
    rw [found] at run
    exact actionFresh state result fresh (found.trans run)

theorem semAllocException_fresh (message : String) (site : Option PanicOutcomeSite) (model : ByteModel) :
    KeepsFresh (semAllocException message site model) := by
  unfold semAllocException
  refine getState_bind_fresh _ (fun before fresh => ?_)
  refine bind_fresh _ _ (fromMemoryExcept_fresh _) (fun _ => ?_)
  dsimp only
  exact bind_fresh _ _ (setState_fresh _ (sameSSA_fresh before _ fresh rfl rfl)) (fun _ => pure_fresh _)

theorem semRaise_fresh {α : Type} (message : String) (site : Option PanicOutcomeSite) (model : ByteModel) :
    KeepsFresh (semRaise message site model : Sem α) := by
  unfold semRaise
  exact bind_fresh _ _ (semAllocException_fresh message site model) (fun _ =>
    bind_fresh _ _ get_fresh (fun _ => throw_fresh _))

/-- Raising a failed body assertion preserves the successful-run invariant
    under both strategies, without changing any callee/error assumption. -/
theorem raiseIfUnwind_fresh (strategy : PanicStrategy) (action : Sem InstrResult) (model : ByteModel)
    (actionFresh : KeepsFresh action) : KeepsFresh (raiseIfUnwind strategy action model) := by
  cases strategy with
  | abort => exact actionFresh
  | unwind =>
    unfold raiseIfUnwind
    apply tryCatch_fresh _ _ actionFresh
    intro error
    cases error <;> first | exact semRaise_fresh _ _ _ | exact throw_fresh _

/-- A landing pad clears only the actual exception hand and publishes its
    checked destinations; arbitrary fallback instructions retain their errors. -/
theorem semLandingPadWith_fresh (strategy : PanicStrategy) (ctx : EvalContext)
    (pad : Inst) (dests : List ValueId) : KeepsFresh (semLandingPadWith strategy ctx pad dests) := by
  cases strategy with
  | abort =>
    unfold semLandingPadWith
    exact bind_fresh _ _ (stepInstWithContext_fresh ctx pad)
      (fun result => bindInstructionResults_fresh ctx pad result dests)
  | unwind =>
    unfold semLandingPadWith
    refine getState_bind_fresh _ (fun before fresh => ?_)
    cases held : before.inHand with
    | none =>
      simp only [held]
      exact bind_fresh _ _ (stepInstWithContext_fresh ctx pad)
        (fun result => bindInstructionResults_fresh ctx pad result dests)
    | some hand =>
      rcases hand with ⟨exception, allocation, selector⟩
      simp only [held]
      exact bind_fresh _ _ (setState_fresh _ (sameSSA_fresh before _ fresh rfl rfl))
        (fun _ => bindCallResults_fresh ctx pad dests _)

end TrustIr.SSAFreshUnwindBody
