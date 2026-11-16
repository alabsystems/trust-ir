-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameGrammarExits

namespace TrustIr.FrameLifetime
open GenericCoro GenericCoro.Prefix

/-- Original block layer with ordinary control and full ordinary/direct/indirect
body exits. Both smaller-fuel callee and successor contracts are explicit. -/
theorem call_frame_layer_exit (recurse : Recurse) (ctx : EvalContext) (safe : StaticFunctionErrors ctx)
    (depth : Nat) (cfg : CFG) (pc : BlockId) (args : List Value) (strategy : PanicStrategy)
    (state : MachineState) (valid : WellMintedState state) (incoming : MintedArgs state.nextFrameLineage args)
    (grammar : CallFrameCFG ctx cfg) (callees : FrameCalleeExitContract recurse ctx strategy)
    (continuation : ∀ next values before, WellMintedState before → MintedArgs before.nextFrameLineage values →
      FrameCalleeExit before (Sem.run (recurse ctx depth cfg next values strategy) before)) :
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
      (frame_call_body_list_exit recurse ctx safe depth strategy _ sites callees bound boundValid)
    intro unit afterBody bodyValid _
    cases unit
    exact control.dispatch_frame_exit recurse ctx depth cfg (ctx.resolveBlock block) strategy afterBody bodyValid continuation

/-- Full exit preservation for the original bounded evaluator, discharging
both recursive contracts by fuel induction for the existing CallFrameCFG /
CallFrameProgram grammar. No sufficient fuel or successful-run premise is used.
Invoke-family and exceptional-body grammar extensions remain separate. -/
theorem call_frame_cfg_exit (ctx : EvalContext) (cfg : CFG) (grammar : CallFrameCFG ctx cfg)
    (program : CallFrameProgram ctx) (safe : StaticFunctionErrors ctx) (fuel depth : Nat)
    (pc : BlockId) (args : List Value) (strategy : PanicStrategy)
    (state : MachineState) (valid : WellMintedState state) (incoming : MintedArgs state.nextFrameLineage args) :
    FrameCalleeExit state (Sem.run (stepNWithContext ctx fuel depth cfg pc args strategy) state) := by
  induction fuel generalizing ctx cfg depth pc args state with
  | zero => exact True.intro
  | succ fuel ih =>
    rw [stepNWithContext_succ_layer]
    apply call_frame_layer_exit _ ctx safe depth cfg pc args strategy state valid incoming grammar
    · intro id callee found childDepth values before beforeValid transported
      exact ih (ctx.forFunction callee) callee.cfg
        (CallFrameCFG.forFunction ctx callee callee.cfg (program id callee found))
        (CallFrameProgram.forFunction ctx callee program)
        (StaticFunctionErrors.forFunction ctx callee safe) childDepth callee.entryBlock values before beforeValid transported
    · intro next values before beforeValid transported
      exact ih ctx cfg grammar program safe depth next values before beforeValid transported

/-- Ordinary CFGs need no program-wide callee grammar or static error-table
premise because their original steps never inspect either field. -/
theorem ordinary_frame_layer_exit (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (cfg : CFG) (pc : BlockId) (args : List Value) (strategy : PanicStrategy)
    (state : MachineState) (valid : WellMintedState state) (incoming : MintedArgs state.nextFrameLineage args)
    (grammar : FrameCFG ctx cfg)
    (continuation : ∀ next values before, WellMintedState before → MintedArgs before.nextFrameLineage values →
      FrameCalleeExit before (Sem.run (recurse ctx depth cfg next values strategy) before)) :
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
      (frame_ordinary_body_list_exit recurse ctx depth strategy _ sites bound boundValid)
    intro unit afterBody bodyValid _
    cases unit
    exact control.dispatch_frame_exit recurse ctx depth cfg (ctx.resolveBlock block) strategy afterBody bodyValid continuation

theorem ordinary_frame_cfg_exit (ctx : EvalContext) (cfg : CFG) (grammar : FrameCFG ctx cfg)
    (fuel depth : Nat) (pc : BlockId) (args : List Value) (strategy : PanicStrategy)
    (state : MachineState) (valid : WellMintedState state) (incoming : MintedArgs state.nextFrameLineage args) :
    FrameCalleeExit state (Sem.run (stepNWithContext ctx fuel depth cfg pc args strategy) state) := by
  induction fuel generalizing pc args state with
  | zero => exact True.intro
  | succ fuel ih =>
    rw [stepNWithContext_succ_layer]
    exact ordinary_frame_layer_exit _ ctx depth cfg pc args strategy state valid incoming grammar
      (fun next values before beforeValid transported => ih next values before beforeValid transported)

end TrustIr.FrameLifetime
