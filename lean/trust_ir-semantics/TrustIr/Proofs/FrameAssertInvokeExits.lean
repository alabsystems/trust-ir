-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameExceptionalExits

namespace TrustIr.FrameLifetime
open GenericCoro GenericCoro.Prefix

theorem FrameActionExit.weaken {α : Type} (post nextPost : Nat → α → Prop) (before : MachineState)
    (result : Except SemError (α × MachineState)) (valid : FrameActionExit post before result)
    (implies : ∀ bound value, post bound value → nextPost bound value) : FrameActionExit nextPost before result := by
  cases result with
  | ok pair => exact ⟨valid.1,implies _ _ valid.2.1,valid.2.2⟩
  | error error => cases error <;> exact valid

/-- The original abort projection is a sited assertion followed by its normal
edge. Source lookup and diagnostic refusal order are retained. -/
theorem assert_invoke_bare_frame_exit (model : ByteModel) (condition : ValueId) (kind : AssertKind)
    (site : PanicSite) (normal : BlockId) (ids : List ValueId) (unwind : BlockId) :
    FrameActionValid OrdinaryTermValues (stepInst (.AssertInvoke condition kind site normal ids unwind) model) := by
  intro state valid
  have anchored : Sem.run (stepInst (.AssertInvoke condition kind site normal ids unwind) model) state =
      Sem.run (stepInst (.Assert condition kind (some site)) >>= fun _ => stepInst (.Br normal ids)) state :=
    assertInvoke_is_sited_assert_then_br condition kind site normal ids unwind state
  rw [anchored]
  apply FrameActionExit.bind (fun _ result => result = .value none) OrdinaryTermValues _ _ state
    (assert_step_frame_exit EvalContext.empty condition kind (some site) state valid)
  intro result before beforeValid _
  exact (FrameControl.br normal ids).term_frame_exit EvalContext.empty 0 (fun _ => none) .abort before beforeValid

private theorem run_catch {α : Type} (action : Sem α) (handler : SemError → Sem α) (state : MachineState) :
    Sem.run (tryCatch action handler) state =
      match Sem.run action state with
      | .ok result => .ok result
      | .error error => Sem.run (handler error) state := by
  rw [Sem.run_tryCatch]
  cases Sem.run action state <;> rfl

/-- Original self-catching assertion transfer. Its unwind handler allocates the
real exception, enters the selected pad and emits an empty-argument edge;
no-action pads may rethrow their actual state. -/
theorem assert_invoke_term_frame_exit (ctx : EvalContext) (depth : Nat) (cfg : CFG) (strategy : PanicStrategy)
    (condition : ValueId) (kind : AssertKind) (site : PanicSite)
    (normal : BlockId) (ids : List ValueId) (unwind : BlockId) :
    FrameActionValid OrdinaryTermValues
      (stepTermWithContext ctx depth cfg (.AssertInvoke condition kind site normal ids unwind) strategy) := by
  intro state valid
  cases strategy with
  | abort => exact assert_invoke_bare_frame_exit ctx.byteModel condition kind site normal ids unwind state valid
  | unwind =>
    change FrameActionExit OrdinaryTermValues state (Sem.run
      (tryCatch (stepInst (.AssertInvoke condition kind site normal ids unwind) ctx.byteModel)
        (fun error => match error with
          | .panic message outcome => do
            let exception ← semAllocException message outcome ctx.byteModel
            semEnterPad cfg exception unwind
            pure (.terminator (.Continue unwind []))
          | other => throw other)) state)
    rw [run_catch]
    have first := assert_invoke_bare_frame_exit ctx.byteModel condition kind site normal ids unwind state valid
    cases executed : Sem.run (stepInst (.AssertInvoke condition kind site normal ids unwind) ctx.byteModel) state with
    | ok pair => rw [executed] at first; exact first
    | error error =>
      rw [executed] at first
      cases error
      case panic message outcome =>
        apply FrameActionExit.bind (fun _ _ => True) OrdinaryTermValues _ _ state
          (exception_allocation_frame_action message outcome ctx.byteModel state valid)
        intro exception allocated allocatedValid _
        apply FrameActionExit.bind (fun _ _ => True) OrdinaryTermValues _ _ allocated
          (enter_pad_frame_action cfg exception unwind allocated allocatedValid)
        intro unit before beforeValid _
        cases unit
        exact ⟨beforeValid,(fun _ member => nomatch member),.refl _⟩
      case unwinding exception after => exact first
      all_goals exact True.intro

/-- Generic final-transfer composition for terms producing only ordinary edge
or return values, including exceptional preparations such as AssertInvoke. -/
theorem ordinary_dispatch_of_term_exit (inst : Inst) (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (cfg : CFG) (block : BasicBlock) (strategy : PanicStrategy)
    (termValid : FrameActionValid OrdinaryTermValues (stepTermWithContext ctx depth cfg inst strategy))
    (state : MachineState) (valid : WellMintedState state)
    (continuation : ∀ next args before, WellMintedState before → MintedArgs before.nextFrameLineage args →
      FrameCalleeExit before (Sem.run (recurse ctx depth cfg next args strategy) before)) :
    FrameActionExit MintedArgs state (Sem.run (do
      let termResult ← stepTermWithContext ctx depth cfg inst strategy
      let result ← match termResult with
        | .terminator step => pure step
        | .value _ => Sem.throwTypeError "basic block does not end with a terminator"
        | .values _ => Sem.throwTypeError "basic block does not end with a terminator"
      evalTransfer recurse ctx depth cfg block strategy result) state) := by
  apply FrameActionExit.bind OrdinaryTermValues MintedArgs _ _ state (termValid state valid)
  intro result before beforeValid transported
  cases result with
  | terminator step =>
    exact (FrameActionExit.callee before _).2 (ordinary_transfer_frame_exit recurse ctx depth cfg block strategy step before beforeValid transported continuation)
  | value _ => cases transported
  | values _ => cases transported

theorem resume_dispatch_frame_exit (recurse : Recurse) (ctx : EvalContext) (depth : Nat) (cfg : CFG)
    (block : BasicBlock) (strategy : PanicStrategy) (id : ValueId) (state : MachineState) (valid : WellMintedState state)
    (continuation : ∀ next args before, WellMintedState before → MintedArgs before.nextFrameLineage args →
      FrameCalleeExit before (Sem.run (recurse ctx depth cfg next args strategy) before)) :
    FrameActionExit MintedArgs state (Sem.run (do
      let termResult ← stepTermWithContext ctx depth cfg (.Resume id) strategy
      let result ← match termResult with
        | .terminator step => pure step
        | .value _ => Sem.throwTypeError "basic block does not end with a terminator"
        | .values _ => Sem.throwTypeError "basic block does not end with a terminator"
      evalTransfer recurse ctx depth cfg block strategy result) state) := by
  apply ordinary_dispatch_of_term_exit _ recurse ctx depth cfg block strategy _ state valid continuation
  intro before beforeValid
  exact FrameActionExit.weaken (fun _ _ => False) OrdinaryTermValues before _
    (resume_term_frame_exit ctx depth cfg strategy id before beforeValid) (fun _ _ impossible => False.elim impossible)

end TrustIr.FrameLifetime
