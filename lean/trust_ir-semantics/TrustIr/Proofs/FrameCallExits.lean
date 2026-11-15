-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameActionExits

namespace TrustIr.FrameLifetime
open GenericCoro GenericCoro.Prefix

/-- Plain calls use the same checked normal-return protocol as Invoke under
abort, with no catch of callee errors. This is equality of original helpers. -/
theorem call_frame_with_eq_invoke_abort (check : List Value → Sem Unit) (callee : Sem (List Value)) :
    callFrameWith check callee = invokeFrameWith .abort check callee
      (fun values => pure values) (fun _ => pure []) := by
  simp only [callFrameWith,invokeFrameWith,finishCalleeWith,finishInvokeWith,invokeCatch,
    finishInvokeReturnWith,bind_assoc,pure_bind]

/-- A plain call propagates the exact callee error, including its embedded
throw state. Caller restoration occurs only after successful checked returns. -/
theorem call_frame_with_error (check : List Value → Sem Unit) (callee : Sem (List Value))
    (s : MachineState) (error : SemError)
    (run : Sem.run callee (callerWorld s) = .error error) :
    Sem.run (callFrameWith check callee) s = .error error := by
  change Sem.run (finishCalleeWith check (saveFrame s none) callee) (callerWorld s) = .error error
  unfold finishCalleeWith
  rw [Sem.run_bind,run]
  rfl

/-- Full plain-call exit preservation, with checker safety and the actual
callee exit contract explicit. Unwinds propagate without restoring old SSA. -/
theorem call_frame_with_exit (check : List Value → Sem Unit) (callee : Sem (List Value))
    (s : MachineState) (valid : WellMintedState s)
    (readonly : ∀ returned, CallCheckReadOnly (check returned))
    (safe : ∀ returned, CallCheckNoUnwind (check returned))
    (execution : FrameCalleeExit (callerWorld s) (Sem.run callee (callerWorld s))) :
    FrameCalleeExit s (Sem.run (callFrameWith check callee) s) := by
  rw [call_frame_with_eq_invoke_abort]
  apply invoke_frame_exit .abort check callee _ _ s valid readonly safe execution
  · intro returned before beforeValid incoming
    exact ⟨beforeValid,incoming,.refl _⟩
  · intro _ before beforeValid
    exact ⟨beforeValid,(fun _ member => nomatch member),.refl _⟩

/-- Normalize original direct-call returns to the actual arity/poison checker. -/
theorem direct_call_frame_eq_checked (ctx : EvalContext) (returns : List Ty) (callee : Sem (List Value)) :
    callFrame returns callee = callFrameWith (checkReturns ctx returns true false "Call: ") callee := by
  have normalized := callFrameWith_checkReturns_bind ctx returns true false "Call: " callee pure
  simp only [bind_pure,Bool.true_eq,Bool.false_eq_true,if_true,if_false,pure_bind] at normalized
  simpa only [callFrame,finishCall,bind_assoc] using normalized.symm

/-- Original direct callFrame preserves normal and actual unwinding exits.
Both checker premises are discharged for its unchanged return checks. -/
theorem direct_call_frame_exit (returns : List Ty) (callee : Sem (List Value))
    (s : MachineState) (valid : WellMintedState s)
    (execution : FrameCalleeExit (callerWorld s) (Sem.run callee (callerWorld s))) :
    FrameCalleeExit s (Sem.run (callFrame returns callee) s) := by
  rw [direct_call_frame_eq_checked EvalContext.empty]
  exact call_frame_with_exit _ callee s valid
    (fun returned => check_returns_readonly EvalContext.empty returns true false "Call: " returned)
    (fun returned => invoke_returns_no_unwind EvalContext.empty returns "Call: " returned) execution

theorem direct_call_frame_error (returns : List Ty) (callee : Sem (List Value))
    (s : MachineState) (error : SemError)
    (run : Sem.run callee (callerWorld s) = .error error) :
    Sem.run (callFrame returns callee) s = .error error := by
  rw [direct_call_frame_eq_checked EvalContext.empty]
  exact call_frame_with_error _ callee s error run

/-- The plain-call result fits the composable action contract. The callee
contract remains an induction premise, not a success-only substitute. -/
theorem direct_call_frame_action (returns : List Ty) (callee : Sem (List Value))
    (execution : ∀ state, WellMintedState state →
      FrameCalleeExit (callerWorld state) (Sem.run callee (callerWorld state))) :
    FrameActionValid MintedArgs (callFrame returns callee) := by
  intro state valid
  exact (FrameActionExit.callee state _).2 (direct_call_frame_exit returns callee state valid (execution state valid))

end TrustIr.FrameLifetime
