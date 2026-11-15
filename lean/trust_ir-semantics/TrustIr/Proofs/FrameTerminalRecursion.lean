-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameTerminalExits
import TrustIr.Proofs.FrameCoroExits
import TrustIr.Proofs.FrameStaticExits

namespace TrustIr.FrameLifetime
open GenericCoro GenericCoro.Prefix

/-- Existing exception controls and both original terminal call forms. -/
inductive TerminalFrameControl : Inst → Type where
  | suspend (frame : ValueId) (slot : Nat) (next : Int) (value : ValueId) :
      TerminalFrameControl (.CoroSuspend frame slot next value)
  | dropInvoke (ty : Ty) (pointer : ValueId) (normal : BlockId) (args : List ValueId) (unwind : BlockId) :
      TerminalFrameControl (.DropInvoke ty pointer normal args unwind)
  | unwind {inst : Inst} (control : UnwindFrameControl inst) : TerminalFrameControl inst
  | call (id : FuncId) (args : List ValueId) : TerminalFrameControl (.Call id args)
  | indirect (callee : ValueId) (sig : FuncTyId) (args : List ValueId) (conv : CallingConv) :
      TerminalFrameControl (.CallIndirect callee sig args conv)

def TerminalFrameCFG (ctx : EvalContext) (cfg : CFG) : Prop :=
  ∀ pc block, cfg pc = some block →
    (∀ row ∈ bodyInstsWithResultDests (ctx.resolveBlock block).body (ctx.resolveBlock block).bodyResultDests,
      UnwindFrameInstruction row.1) ∧ Nonempty (TerminalFrameControl (ctx.resolveBlock block).terminator)

def TerminalFrameProgram (ctx : EvalContext) : Prop :=
  ∀ id function, ctx.functions id = some function → TerminalFrameCFG ctx function.cfg

theorem TerminalFrameCFG.forFunction (ctx : EvalContext) (function : EvalFunction) (cfg : CFG)
    (grammar : TerminalFrameCFG ctx cfg) : TerminalFrameCFG (ctx.forFunction function) cfg := grammar

theorem TerminalFrameProgram.forFunction (ctx : EvalContext) (function : EvalFunction)
    (program : TerminalFrameProgram ctx) : TerminalFrameProgram (ctx.forFunction function) := program

theorem UnwindFrameCFG.toTerminalCFG (ctx : EvalContext) (cfg : CFG) (grammar : UnwindFrameCFG ctx cfg) :
    TerminalFrameCFG ctx cfg := by
  intro pc block found
  obtain ⟨sites,⟨control⟩⟩ := grammar pc block found
  exact ⟨sites,⟨.unwind control⟩⟩

theorem AllTailFrameCFG.toTerminalCFG (ctx : EvalContext) (cfg : CFG) (grammar : AllTailFrameCFG ctx cfg) :
    TerminalFrameCFG ctx cfg := by
  intro pc block found
  obtain ⟨sites,⟨control⟩⟩ := grammar pc block found
  refine ⟨fun row member => .call (sites row member),?_⟩
  generalize termEq : (ctx.resolveBlock block).terminator = inst at control
  cases control with
  | ordinary site => exact ⟨.unwind (.ordinary site)⟩
  | call id args => exact ⟨.call id args⟩
  | indirect callee sig args conv => exact ⟨.indirect callee sig args conv⟩

theorem UnwindFrameProgram.toTerminalProgram (ctx : EvalContext) (program : UnwindFrameProgram ctx) :
    TerminalFrameProgram ctx := fun id fn found => (program id fn found).toTerminalCFG ctx fn.cfg

theorem AllTailFrameProgram.toTerminalProgram (ctx : EvalContext) (program : AllTailFrameProgram ctx) :
    TerminalFrameProgram ctx := fun id fn found => (program id fn found).toTerminalCFG ctx fn.cfg

theorem TerminalFrameControl.dispatch_frame_exit {inst : Inst} (site : TerminalFrameControl inst)
    (recurse : Recurse) (ctx : EvalContext) (safe : StaticFunctionErrors ctx) (depth : Nat)
    (cfg : CFG) (block : BasicBlock) (strategy : PanicStrategy) (state : MachineState) (valid : WellMintedState state)
    (callees : FrameCalleeExitContract recurse ctx strategy)
    (continuation : ∀ next args before, WellMintedState before → MintedArgs before.nextFrameLineage args →
      FrameCalleeExit before (Sem.run (recurse ctx depth cfg next args strategy) before)) :
    FrameActionExit MintedArgs state (Sem.run (do
      let termResult ← stepTermWithContext ctx depth cfg inst strategy
      let result ← match termResult with
        | .terminator step => pure step
        | .value _ => Sem.throwTypeError "basic block does not end with a terminator"
        | .values _ => Sem.throwTypeError "basic block does not end with a terminator"
      evalTransfer recurse ctx depth cfg block strategy result) state) := by
  cases site with
  | suspend frame slot next value => exact coro_suspend_dispatch_frame_exit recurse ctx depth cfg block strategy frame slot next value state valid continuation
  | dropInvoke ty pointer normal args unwind => exact unresolved_drop_invoke_dispatch_exit recurse ctx depth cfg block strategy ty pointer normal args unwind state
  | unwind site => exact site.dispatch_frame_exit recurse ctx safe depth cfg block strategy state valid callees continuation
  | call id args => exact terminal_direct_dispatch_exit recurse ctx depth cfg block strategy id args state valid callees
  | indirect callee sig args conv => exact terminal_indirect_dispatch_exit recurse ctx safe depth cfg block strategy callee sig args conv state valid callees

theorem terminal_frame_layer_exit (recurse : Recurse) (ctx : EvalContext) (safe : StaticFunctionErrors ctx)
    (depth : Nat) (cfg : CFG) (pc : BlockId) (args : List Value) (strategy : PanicStrategy)
    (state : MachineState) (valid : WellMintedState state) (incoming : MintedArgs state.nextFrameLineage args)
    (grammar : TerminalFrameCFG ctx cfg) (callees : FrameCalleeExitContract recurse ctx strategy)
    (continuation : ∀ next args before, WellMintedState before → MintedArgs before.nextFrameLineage args →
      FrameCalleeExit before (Sem.run (recurse ctx depth cfg next args strategy) before)) :
    FrameCalleeExit state (Sem.run (evalLayer recurse ctx depth cfg pc args strategy) state) := by
  rw [evalLayer_eq_transfer]
  apply (FrameActionExit.callee state _).1
  cases found : cfg pc with
  | none => simp only [found]; exact True.intro
  | some block =>
    obtain ⟨sites,⟨control⟩⟩ := grammar pc block found
    simp only [found]
    apply FrameActionExit.bind (fun _ _ => True) MintedArgs _ _ state
      (checked_params_frame_exit (ctx.resolveBlock block).params args state valid incoming)
    intro unit bound boundValid _
    cases unit
    apply FrameActionExit.bind (fun _ _ => True) MintedArgs _ _ bound
      (unwind_frame_body_list_exit recurse ctx safe depth strategy _ sites callees bound boundValid)
    intro unit afterBody bodyValid _
    cases unit
    exact control.dispatch_frame_exit recurse ctx safe depth cfg (ctx.resolveBlock block) strategy afterBody bodyValid callees continuation

/-- Full original bounded CFG exits with real raising, catching and rethrowing.
The callee and caller continuation contracts are both discharged by fuel
induction, across the actual forFunction contexts and their original scopes. -/
theorem terminal_frame_cfg_exit (ctx : EvalContext) (cfg : CFG) (grammar : TerminalFrameCFG ctx cfg)
    (program : TerminalFrameProgram ctx) (safe : StaticFunctionErrors ctx) (fuel depth : Nat)
    (pc : BlockId) (args : List Value) (strategy : PanicStrategy)
    (state : MachineState) (valid : WellMintedState state) (incoming : MintedArgs state.nextFrameLineage args) :
    FrameCalleeExit state (Sem.run (stepNWithContext ctx fuel depth cfg pc args strategy) state) := by
  induction fuel generalizing ctx cfg depth pc args state with
  | zero => exact True.intro
  | succ fuel ih =>
    rw [stepNWithContext_succ_layer]
    apply terminal_frame_layer_exit _ ctx safe depth cfg pc args strategy state valid incoming grammar
    · intro id callee found childDepth values before beforeValid transported
      exact ih (ctx.forFunction callee) callee.cfg
        (TerminalFrameCFG.forFunction ctx callee callee.cfg (program id callee found))
        (TerminalFrameProgram.forFunction ctx callee program)
        (StaticFunctionErrors.forFunction ctx callee safe) childDepth callee.entryBlock values before beforeValid transported
    · intro next values before beforeValid transported
      exact ih ctx cfg grammar program safe depth next values before beforeValid transported

theorem terminal_frame_entry_exit (ctx : EvalContext) (cfg : CFG) (grammar : TerminalFrameCFG ctx cfg)
    (program : TerminalFrameProgram ctx) (safe : StaticFunctionErrors ctx) (fuel depth : Nat)
    (pc : BlockId) (args : List Value) (strategy : PanicStrategy)
    (state : MachineState) (valid : WellMintedState state) (incoming : MintedArgs state.nextFrameLineage args) :
    FrameCalleeExit state (Sem.run (exitUnwinding strategy (stepNWithContext ctx fuel depth cfg pc args strategy)) state) :=
  exit_unwinding_frame_exit strategy _ state (terminal_frame_cfg_exit ctx cfg grammar program safe fuel depth pc args strategy state valid incoming)

end TrustIr.FrameLifetime
