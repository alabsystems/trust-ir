-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameGEPExits
import TrustIr.Proofs.FrameControlExits

namespace TrustIr.FrameLifetime
open GenericCoro GenericCoro.Prefix

/-- The intrinsic's actual held-value GEP and Store precede the original
return lookup. No private SSA aliases are introduced by this proof. -/
theorem coro_suspend_frame_exit (frame : ValueId) (slot : Nat) (next : Int) (value : ValueId) (model : ByteModel) :
    FrameActionValid TransferValues (semCoroSuspend frame slot next value model) := by
  intro state valid
  unfold semCoroSuspend
  apply FrameActionExit.bind MintedValue TransferValues _ _ state (lookup_value_frame_action frame state valid)
  intro pointer state valid _
  apply FrameActionExit.bind MintedValue TransferValues _ _ state
    (gep_values_frame_exit (scalarMemoryLayout model) (fun (_ : Unit) held => typedIntegerValue model .I64 held)
      (scalar_layout_no_unwind model) (fun _ held => typed_integer_no_unwind model .I64 held)
      .I64 pointer [((),Value.intAt 64 slot)] model state valid)
  intro pointer state valid _
  apply FrameActionExit.bind (fun _ _ => True) TransferValues _ _ state
    (scalar_store_value_frame_exit {EvalContext.empty with byteModel := model} .I64 pointer (Value.intAt 64 next) false none state valid)
  intro unit state valid _
  cases unit
  exact (FrameControl.ret [value]).action_frame_exit state valid

theorem coro_suspend_term_frame_exit (ctx : EvalContext) (depth : Nat) (cfg : CFG) (strategy : PanicStrategy)
    (frame : ValueId) (slot : Nat) (next : Int) (value : ValueId) :
    FrameActionValid OrdinaryTermValues (stepTermWithContext ctx depth cfg (.CoroSuspend frame slot next value) strategy) := by
  have normalize : stepTermWithContext ctx depth cfg (.CoroSuspend frame slot next value) strategy =
      (semCoroSuspend frame slot next value ctx.byteModel >>= fun result => pure (.terminator result)) := by
    cases strategy <;> rfl
  rw [normalize]
  intro state valid
  apply FrameActionExit.bind TransferValues OrdinaryTermValues _ _ state
    (coro_suspend_frame_exit frame slot next value ctx.byteModel state valid)
  intro result state valid transported
  exact ⟨valid,transported,.refl _⟩

theorem coro_suspend_dispatch_frame_exit (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (cfg : CFG) (block : BasicBlock) (strategy : PanicStrategy)
    (frame : ValueId) (slot : Nat) (next : Int) (value : ValueId)
    (state : MachineState) (valid : WellMintedState state)
    (continuation : ∀ pc args before, WellMintedState before → MintedArgs before.nextFrameLineage args →
      FrameCalleeExit before (Sem.run (recurse ctx depth cfg pc args strategy) before)) :
    FrameActionExit MintedArgs state (Sem.run (do
      let termResult ← stepTermWithContext ctx depth cfg (.CoroSuspend frame slot next value) strategy
      let result ← match termResult with
        | .terminator step => pure step
        | .value _ => Sem.throwTypeError "basic block does not end with a terminator"
        | .values _ => Sem.throwTypeError "basic block does not end with a terminator"
      evalTransfer recurse ctx depth cfg block strategy result) state) := by
  apply FrameActionExit.bind OrdinaryTermValues MintedArgs _ _ state
    (coro_suspend_term_frame_exit ctx depth cfg strategy frame slot next value state valid)
  intro result before beforeValid transported
  cases result with
  | terminator step =>
    exact (FrameActionExit.callee before _).2
      (ordinary_transfer_frame_exit recurse ctx depth cfg block strategy step before beforeValid transported continuation)
  | value _ => cases transported
  | values _ => cases transported

end TrustIr.FrameLifetime
