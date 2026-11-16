-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameAssertInvokeExits

namespace TrustIr.FrameLifetime
open GenericCoro GenericCoro.Prefix

/-- Existing ordinary/call bodies plus real exception production and pads. -/
inductive UnwindFrameInstruction : Inst → Prop where
  | call {inst : Inst} (site : CallFrameInstruction inst) : UnwindFrameInstruction inst
  | assert (condition : ValueId) (kind : AssertKind) (site : Option PanicSite) :
      UnwindFrameInstruction (.Assert condition kind site)
  | pad (cleanup : Bool) (clauses : List Nat) : UnwindFrameInstruction (.LandingPad cleanup clauses)

/-- Ordinary edges plus the original direct/raw/FnDef Invoke protocols,
self-catching assertions and exact Resume rethrows. Tail calls stay separate. -/
inductive UnwindFrameControl : Inst → Type where
  | ordinary {inst : Inst} (site : FrameControl inst) : UnwindFrameControl inst
  | invoke (id : FuncId) (args : List ValueId) (normal : BlockId) (ids : List ValueId) (unwind : BlockId) :
      UnwindFrameControl (.Invoke id args normal ids unwind)
  | indirect (callee : ValueId) (sig : FuncTyId) (args : List ValueId) (conv : CallingConv)
      (normal : BlockId) (ids : List ValueId) (unwind : BlockId) :
      UnwindFrameControl (.InvokeIndirect callee sig args conv normal ids unwind)
  | assert (condition : ValueId) (kind : AssertKind) (site : PanicSite)
      (normal : BlockId) (ids : List ValueId) (unwind : BlockId) :
      UnwindFrameControl (.AssertInvoke condition kind site normal ids unwind)
  | resume (id : ValueId) : UnwindFrameControl (.Resume id)

def UnwindFrameCFG (ctx : EvalContext) (cfg : CFG) : Prop :=
  ∀ pc block, cfg pc = some block →
    (∀ row ∈ bodyInstsWithResultDests (ctx.resolveBlock block).body (ctx.resolveBlock block).bodyResultDests,
      UnwindFrameInstruction row.1) ∧ Nonempty (UnwindFrameControl (ctx.resolveBlock block).terminator)

def UnwindFrameProgram (ctx : EvalContext) : Prop :=
  ∀ id function, ctx.functions id = some function → UnwindFrameCFG ctx function.cfg

theorem UnwindFrameCFG.forFunction (ctx : EvalContext) (function : EvalFunction) (cfg : CFG)
    (grammar : UnwindFrameCFG ctx cfg) : UnwindFrameCFG (ctx.forFunction function) cfg := grammar

theorem UnwindFrameProgram.forFunction (ctx : EvalContext) (function : EvalFunction)
    (program : UnwindFrameProgram ctx) : UnwindFrameProgram (ctx.forFunction function) := program

theorem CallFrameCFG.toUnwindCFG (ctx : EvalContext) (cfg : CFG) (grammar : CallFrameCFG ctx cfg) : UnwindFrameCFG ctx cfg := by
  intro pc block found
  obtain ⟨sites,⟨control⟩⟩ := grammar pc block found
  exact ⟨fun row member => .call (sites row member),⟨.ordinary control⟩⟩

theorem UnwindFrameInstruction.body_frame_exit {inst : Inst} (site : UnwindFrameInstruction inst)
    (recurse : Recurse) (ctx : EvalContext) (safe : StaticFunctionErrors ctx) (depth : Nat)
    (strategy : PanicStrategy) (dests : List ValueId) (callees : FrameCalleeExitContract recurse ctx strategy) :
    FrameActionValid (fun _ _ => True) (evalBodyStep recurse ctx depth strategy (inst,dests)) := by
  cases site with
  | call site => exact site.body_frame_exit recurse ctx safe depth strategy dests callees
  | assert condition kind site => exact assert_body_frame_exit recurse ctx depth strategy condition kind site dests
  | pad cleanup clauses => exact landing_pad_body_frame_exit recurse ctx depth strategy cleanup clauses dests

theorem unwind_frame_body_list_exit (recurse : Recurse) (ctx : EvalContext) (safe : StaticFunctionErrors ctx)
    (depth : Nat) (strategy : PanicStrategy) (rows : List (Inst × List ValueId))
    (sites : ∀ row ∈ rows, UnwindFrameInstruction row.1) (callees : FrameCalleeExitContract recurse ctx strategy) :
    FrameActionValid (fun _ _ => True) (evalBody recurse ctx depth strategy rows) :=
  frame_body_list_exit recurse ctx depth strategy rows
    (fun row member => (sites row member).body_frame_exit recurse ctx safe depth strategy row.2 callees)

theorem UnwindFrameControl.dispatch_frame_exit {inst : Inst} (site : UnwindFrameControl inst)
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
  | ordinary site => exact site.dispatch_frame_exit recurse ctx depth cfg block strategy state valid continuation
  | invoke id args normal ids unwind =>
    exact direct_invoke_dispatch_exit recurse ctx depth cfg block strategy id args normal ids unwind state valid (callees id) continuation
  | indirect callee sig args conv normal ids unwind =>
    exact indirect_invoke_dispatch_exit recurse ctx safe depth cfg block strategy callee sig args conv normal ids unwind state valid callees continuation
  | assert condition kind site normal ids unwind =>
    exact ordinary_dispatch_of_term_exit _ recurse ctx depth cfg block strategy
      (assert_invoke_term_frame_exit ctx depth cfg strategy condition kind site normal ids unwind) state valid continuation
  | resume id => exact resume_dispatch_frame_exit recurse ctx depth cfg block strategy id state valid continuation

theorem unwind_frame_layer_exit (recurse : Recurse) (ctx : EvalContext) (safe : StaticFunctionErrors ctx)
    (depth : Nat) (cfg : CFG) (pc : BlockId) (args : List Value) (strategy : PanicStrategy)
    (state : MachineState) (valid : WellMintedState state) (incoming : MintedArgs state.nextFrameLineage args)
    (grammar : UnwindFrameCFG ctx cfg) (callees : FrameCalleeExitContract recurse ctx strategy)
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
    apply FrameActionExit.bind (fun bound _ => MintedArgs bound args) MintedArgs _ _ state
      (function_item_checks_frame_exit ctx ((ctx.resolveBlock block).params.map (·.snd)) args state valid incoming)
    intro unit state valid incoming
    cases unit
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
theorem unwind_frame_cfg_exit (ctx : EvalContext) (cfg : CFG) (grammar : UnwindFrameCFG ctx cfg)
    (program : UnwindFrameProgram ctx) (safe : StaticFunctionErrors ctx) (fuel depth : Nat)
    (pc : BlockId) (args : List Value) (strategy : PanicStrategy)
    (state : MachineState) (valid : WellMintedState state) (incoming : MintedArgs state.nextFrameLineage args) :
    FrameCalleeExit state (Sem.run (stepNWithContext ctx fuel depth cfg pc args strategy) state) := by
  induction fuel generalizing ctx cfg depth pc args state with
  | zero => exact True.intro
  | succ fuel ih =>
    rw [stepNWithContext_succ_layer]
    apply unwind_frame_layer_exit _ ctx safe depth cfg pc args strategy state valid incoming grammar
    · intro id callee found childDepth values before beforeValid transported
      exact ih (ctx.forFunction callee) callee.cfg
        (UnwindFrameCFG.forFunction ctx callee callee.cfg (program id callee found))
        (UnwindFrameProgram.forFunction ctx callee program)
        (StaticFunctionErrors.forFunction ctx callee safe) childDepth callee.entryBlock values before beforeValid transported
    · intro next values before beforeValid transported
      exact ih ctx cfg grammar program safe depth next values before beforeValid transported

/-- Original entry conversion retains normal exits and maps escaping unwinds
to their recorded panic (or its original missing-record refusal). -/
theorem exit_unwinding_frame_exit (strategy : PanicStrategy) (action : Sem (List Value)) (state : MachineState)
    (executedValid : FrameCalleeExit state (Sem.run action state)) :
    FrameCalleeExit state (Sem.run (exitUnwinding strategy action) state) := by
  cases strategy with
  | abort => exact executedValid
  | unwind =>
    unfold exitUnwinding
    rw [Sem.run_tryCatch]
    cases executed : Sem.run action state with
    | ok pair => rw [executed] at executedValid; exact executedValid
    | error error =>
      rw [executed] at executedValid
      cases error
      case unwinding exception after =>
        cases recorded : after.exceptions.find? (fun row => row.1 == exception) with
        | none => simp only [Except.tryCatch,recorded]; exact True.intro
        | some held =>
          rcases held with ⟨address,allocation,message,site⟩
          simp only [Except.tryCatch,recorded]
          exact True.intro
      all_goals exact executedValid

theorem unwind_frame_entry_exit (ctx : EvalContext) (cfg : CFG) (grammar : UnwindFrameCFG ctx cfg)
    (program : UnwindFrameProgram ctx) (safe : StaticFunctionErrors ctx) (fuel depth : Nat)
    (pc : BlockId) (args : List Value) (strategy : PanicStrategy)
    (state : MachineState) (valid : WellMintedState state) (incoming : MintedArgs state.nextFrameLineage args) :
    FrameCalleeExit state (Sem.run (exitUnwinding strategy (stepNWithContext ctx fuel depth cfg pc args strategy)) state) :=
  exit_unwinding_frame_exit strategy _ state (unwind_frame_cfg_exit ctx cfg grammar program safe fuel depth pc args strategy state valid incoming)

end TrustIr.FrameLifetime
