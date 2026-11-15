-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameMemoryLoads

namespace TrustIr.FrameLifetime
open GenericCoro GenericCoro.Prefix

/-- Existing no-op and structured refusals, without adding execution support
for host-unwind boundaries, unresolved destructors or unlowered dialects. -/
inductive StaticFrameInstruction : Inst → Prop where
  | assume (condition : ValueId) : StaticFrameInstruction (.Assume condition)
  | cannotUnwind (id : FuncId) (args : List ValueId) : StaticFrameInstruction (.CallCannotUnwind id args)
  | indirectCannotUnwind (callee : ValueId) (sig : FuncTyId) (args : List ValueId) (conv : CallingConv) :
      StaticFrameInstruction (.CallIndirectCannotUnwind callee sig args conv)
  | drop (ty : Ty) (pointer : ValueId) : StaticFrameInstruction (.Drop ty pointer)
  | dialect (op : DialectInst) : StaticFrameInstruction (.DialectOp op)

theorem static_step_frame_exit (ctx : EvalContext) (inst : Inst) (site : StaticFrameInstruction inst) :
    FrameActionValid (fun _ result => BodyValueResult result) (stepInstWithContext ctx inst) := by
  cases site <;> intro state valid <;> first
    | exact ⟨valid,True.intro,.refl _⟩
    | exact True.intro

theorem static_body_frame_exit (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strategy : PanicStrategy) (inst : Inst) (site : StaticFrameInstruction inst) (dests : List ValueId) :
    FrameActionValid (fun _ _ => True) (evalBodyStep recurse ctx depth strategy (inst,dests)) := by
  intro state valid
  have safe := static_step_frame_exit ctx inst site state valid
  cases site <;> apply FrameActionExit.bind (fun _ result => BodyValueResult result) (fun _ _ => True) _ _ state safe
  all_goals
    intro result state valid shape
    cases result with
    | terminator step => cases shape
    | value id =>
      apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state
        (instruction_results_frame_action ctx _ (.value id) dests state valid)
      intro unit state valid _
      cases unit
      exact ⟨valid,True.intro,.refl _⟩
    | values ids =>
      apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state
        (instruction_results_frame_action ctx _ (.values ids) dests state valid)
      intro unit state valid _
      cases unit
      exact ⟨valid,True.intro,.refl _⟩

theorem unresolved_drop_invoke_dispatch_exit (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (cfg : CFG) (block : BasicBlock) (strategy : PanicStrategy) (ty : Ty) (pointer : ValueId)
    (normal : BlockId) (args : List ValueId) (unwind : BlockId) (state : MachineState) :
    FrameActionExit MintedArgs state (Sem.run (do
      let termResult ← stepTermWithContext ctx depth cfg (.DropInvoke ty pointer normal args unwind) strategy
      let result ← match termResult with
        | .terminator step => pure step
        | .value _ => Sem.throwTypeError "basic block does not end with a terminator"
        | .values _ => Sem.throwTypeError "basic block does not end with a terminator"
      evalTransfer recurse ctx depth cfg block strategy result) state) := by
  cases strategy <;> exact True.intro

end TrustIr.FrameLifetime
