-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameSeqMapExits
import TrustIr.Proofs.FrameGlobalExits
import TrustIr.Proofs.FrameConstantPublication

namespace TrustIr.FrameLifetime
open GenericCoro GenericCoro.Prefix

inductive SequenceFrameInstruction : Inst → Prop where
  | static {inst : Inst} (site : StaticFrameInstruction inst) : SequenceFrameInstruction inst
  | constant (ty : Ty) (value : Constant) : SequenceFrameInstruction (.Const ty value)
  | global (id : GlobalId) : SequenceFrameInstruction (.GlobalAddr id)
  | memory {inst : Inst} (site : MemoryFrameInstruction inst) : SequenceFrameInstruction inst
  | map (ty : Ty) (operand : ValueId) (id : FuncId) : SequenceFrameInstruction (.SeqMap ty operand id)

theorem SequenceFrameInstruction.body_frame_exit {inst : Inst} (site : SequenceFrameInstruction inst)
    (recurse : Recurse) (ctx : EvalContext) (safe : StaticFunctionErrors ctx)
    (headers : HeaderContextErrors ctx) (memory : MemoryContextErrors ctx) (depth : Nat)
    (strategy : PanicStrategy) (dests : List ValueId) (callees : FrameCalleeExitContract recurse ctx strategy) :
    FrameActionValid (fun _ _ => True) (evalBodyStep recurse ctx depth strategy (inst,dests)) := by
  cases site with
  | static site => exact static_body_frame_exit recurse ctx depth strategy inst site dests
  | constant ty value => exact context_constant_body_exit recurse ctx depth strategy ty value dests
  | global id => exact context_global_body_frame_exit recurse ctx memory depth strategy id dests
  | memory site => exact site.body_frame_exit recurse ctx safe memory depth strategy dests callees
  | map ty operand id => exact seqmap_body_frame_exit recurse ctx safe headers memory depth strategy ty operand id dests callees

theorem sequence_frame_body_list_exit (recurse : Recurse) (ctx : EvalContext) (safe : StaticFunctionErrors ctx)
    (headers : HeaderContextErrors ctx) (memory : MemoryContextErrors ctx) (depth : Nat)
    (strategy : PanicStrategy) (rows : List (Inst × List ValueId))
    (sites : ∀ row ∈ rows, SequenceFrameInstruction row.1) (callees : FrameCalleeExitContract recurse ctx strategy) :
    FrameActionValid (fun _ _ => True) (evalBody recurse ctx depth strategy rows) :=
  frame_body_list_exit recurse ctx depth strategy rows
    (fun row member => (sites row member).body_frame_exit recurse ctx safe headers memory depth strategy row.2 callees)

def SequenceFrameCFG (ctx : EvalContext) (cfg : CFG) : Prop :=
  ∀ pc block, cfg pc = some block →
    (∀ row ∈ bodyInstsWithResultDests (ctx.resolveBlock block).body (ctx.resolveBlock block).bodyResultDests,
      SequenceFrameInstruction row.1) ∧ Nonempty (TerminalFrameControl (ctx.resolveBlock block).terminator)

def SequenceFrameProgram (ctx : EvalContext) : Prop :=
  ∀ id function, ctx.functions id = some function → SequenceFrameCFG ctx function.cfg

theorem SequenceFrameCFG.forFunction (ctx : EvalContext) (function : EvalFunction) (cfg : CFG)
    (grammar : SequenceFrameCFG ctx cfg) : SequenceFrameCFG (ctx.forFunction function) cfg := grammar

theorem SequenceFrameProgram.forFunction (ctx : EvalContext) (function : EvalFunction)
    (program : SequenceFrameProgram ctx) : SequenceFrameProgram (ctx.forFunction function) := program

theorem MemoryFrameCFG.toSequenceCFG (ctx : EvalContext) (cfg : CFG) (grammar : MemoryFrameCFG ctx cfg) :
    SequenceFrameCFG ctx cfg := by
  intro pc block found
  obtain ⟨sites, control⟩ := grammar pc block found
  exact ⟨fun row member => .memory (sites row member), control⟩

theorem MemoryFrameProgram.toSequenceProgram (ctx : EvalContext) (program : MemoryFrameProgram ctx) :
    SequenceFrameProgram ctx := fun id fn found => (program id fn found).toSequenceCFG ctx fn.cfg

theorem sequence_frame_layer_exit (recurse : Recurse) (ctx : EvalContext) (safe : StaticFunctionErrors ctx) (headers : HeaderContextErrors ctx) (memory : MemoryContextErrors ctx)
    (depth : Nat) (cfg : CFG) (pc : BlockId) (args : List Value) (strategy : PanicStrategy)
    (state : MachineState) (valid : WellMintedState state) (incoming : MintedArgs state.nextFrameLineage args)
    (grammar : SequenceFrameCFG ctx cfg) (callees : FrameCalleeExitContract recurse ctx strategy)
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
      (sequence_frame_body_list_exit recurse ctx safe headers memory depth strategy _ sites callees bound boundValid)
    intro unit afterBody bodyValid _
    cases unit
    exact control.dispatch_frame_exit recurse ctx safe depth cfg (ctx.resolveBlock block) strategy afterBody bodyValid callees continuation

/-- Full original bounded CFG exits with real raising, catching and rethrowing.
The callee and caller continuation contracts are both discharged by fuel
induction, across the actual forFunction contexts and their original scopes. -/
theorem sequence_frame_cfg_exit (ctx : EvalContext) (cfg : CFG) (grammar : SequenceFrameCFG ctx cfg)
    (program : SequenceFrameProgram ctx) (safe : StaticFunctionErrors ctx) (headers : HeaderContextErrors ctx) (memory : MemoryContextErrors ctx) (fuel depth : Nat)
    (pc : BlockId) (args : List Value) (strategy : PanicStrategy)
    (state : MachineState) (valid : WellMintedState state) (incoming : MintedArgs state.nextFrameLineage args) :
    FrameCalleeExit state (Sem.run (stepNWithContext ctx fuel depth cfg pc args strategy) state) := by
  induction fuel generalizing ctx cfg depth pc args state with
  | zero => exact True.intro
  | succ fuel ih =>
    rw [stepNWithContext_succ_layer]
    apply sequence_frame_layer_exit _ ctx safe headers memory depth cfg pc args strategy state valid incoming grammar
    · intro id callee found childDepth values before beforeValid transported
      exact ih (ctx.forFunction callee) callee.cfg
        (SequenceFrameCFG.forFunction ctx callee callee.cfg (program id callee found))
        (SequenceFrameProgram.forFunction ctx callee program)
        (StaticFunctionErrors.forFunction ctx callee safe) (HeaderContextErrors.forFunction ctx callee headers) (MemoryContextErrors.forFunction ctx callee memory) childDepth callee.entryBlock values before beforeValid transported
    · intro next values before beforeValid transported
      exact ih ctx cfg grammar program safe headers memory depth next values before beforeValid transported

theorem sequence_frame_entry_exit (ctx : EvalContext) (cfg : CFG) (grammar : SequenceFrameCFG ctx cfg)
    (program : SequenceFrameProgram ctx) (safe : StaticFunctionErrors ctx) (headers : HeaderContextErrors ctx) (memory : MemoryContextErrors ctx) (fuel depth : Nat)
    (pc : BlockId) (args : List Value) (strategy : PanicStrategy)
    (state : MachineState) (valid : WellMintedState state) (incoming : MintedArgs state.nextFrameLineage args) :
    FrameCalleeExit state (Sem.run (exitUnwinding strategy (stepNWithContext ctx fuel depth cfg pc args strategy)) state) :=
  exit_unwinding_frame_exit strategy _ state (sequence_frame_cfg_exit ctx cfg grammar program safe headers memory fuel depth pc args strategy state valid incoming)

/-- Original context assembly discharges all three service-error policies.
Grammar membership, initial identities and arguments remain explicit. -/
theorem decoded_sequence_frame_entry_exit (source : TrustIrEval.Module) (maxDepth : Nat)
    (ctx : EvalContext) (assembled : TrustIrEval.contextOf source maxDepth = .ok ctx)
    (cfg : CFG) (grammar : SequenceFrameCFG ctx cfg) (program : SequenceFrameProgram ctx)
    (fuel depth : Nat) (pc : BlockId) (args : List Value) (strategy : PanicStrategy)
    (state : MachineState) (valid : WellMintedState state) (incoming : MintedArgs state.nextFrameLineage args) :
    FrameCalleeExit state (Sem.run (exitUnwinding strategy
      (stepNWithContext ctx fuel depth cfg pc args strategy)) state) :=
  sequence_frame_entry_exit ctx cfg grammar program
    (decoded_context_errors_static source maxDepth ctx assembled)
    (decoded_context_header_errors source maxDepth ctx assembled)
    (decoded_context_memory_errors source maxDepth ctx assembled)
    fuel depth pc args strategy state valid incoming

end TrustIr.FrameLifetime
