-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameTerminalRecursion
import TrustIr.Proofs.FrameAggregateStores
import TrustIr.Proofs.FrameAtomicExits
import TrustIr.Proofs.FrameAllocationExits
import TrustIr.Proofs.FrameOwnershipExits

namespace TrustIr.FrameLifetime
open GenericCoro GenericCoro.Prefix

/-- The service inventory survives switching to a callee's SSA declarations. -/
theorem MemoryContextErrors.forFunction (ctx : EvalContext) (function : EvalFunction)
    (safe : MemoryContextErrors ctx) : MemoryContextErrors (ctx.forFunction function) := safe

/-- Original recursive bodies, including the proved memory and ownership families. -/
inductive MemoryFrameInstruction : Inst → Prop where
  | unwind {inst : Inst} (site : UnwindFrameInstruction inst) : MemoryFrameInstruction inst
  | load (ty : Ty) (pointer : ValueId) (strict : Bool) (align : Option Nat) :
      MemoryFrameInstruction (.Load ty pointer strict align)
  | store (ty : Ty) (pointer value : ValueId) (strict : Bool) (align : Option Nat) :
      MemoryFrameInstruction (.Store ty pointer value strict align)
  | atomic {inst : Inst} (site : AtomicFrameInst inst) : MemoryFrameInstruction inst
  | allocation {inst : Inst} (site : AllocationFrameInst inst) : MemoryFrameInstruction inst
  | gep (ty : Ty) (base : ValueId) (indices : List ValueId) (inbounds : Bool) :
      MemoryFrameInstruction (.GEP ty base indices inbounds)
  | bulk {inst : Inst} (site : BulkFrameInst inst) : MemoryFrameInstruction inst
  | ownership {inst : Inst} (site : OwnershipFrameInst inst) : MemoryFrameInstruction inst

theorem MemoryFrameInstruction.body_frame_exit {inst : Inst} (site : MemoryFrameInstruction inst)
    (recurse : Recurse) (ctx : EvalContext) (safe : StaticFunctionErrors ctx)
    (memory : MemoryContextErrors ctx) (depth : Nat) (strategy : PanicStrategy)
    (dests : List ValueId) (callees : FrameCalleeExitContract recurse ctx strategy) :
    FrameActionValid (fun _ _ => True) (evalBodyStep recurse ctx depth strategy (inst,dests)) := by
  cases site with
  | unwind site => exact site.body_frame_exit recurse ctx safe depth strategy dests callees
  | load ty pointer strict align => exact context_load_body_frame_exit recurse ctx memory depth strategy ty pointer strict align dests
  | store ty pointer value strict align => exact context_store_body_frame_exit recurse ctx memory depth strategy ty pointer value strict align dests
  | atomic site => exact atomic_body_frame_exit recurse ctx memory depth strategy _ site dests
  | allocation site => exact allocation_body_frame_exit recurse ctx memory depth strategy _ site dests
  | gep ty base indices inbounds => exact gep_body_frame_exit recurse ctx memory depth strategy ty base indices inbounds dests
  | bulk site => exact bulk_body_frame_exit recurse ctx depth strategy _ site dests
  | ownership site => exact ownership_body_frame_exit recurse ctx depth strategy _ site dests

theorem memory_frame_body_list_exit (recurse : Recurse) (ctx : EvalContext) (safe : StaticFunctionErrors ctx)
    (memory : MemoryContextErrors ctx) (depth : Nat) (strategy : PanicStrategy) (rows : List (Inst × List ValueId))
    (sites : ∀ row ∈ rows, MemoryFrameInstruction row.1) (callees : FrameCalleeExitContract recurse ctx strategy) :
    FrameActionValid (fun _ _ => True) (evalBody recurse ctx depth strategy rows) :=
  frame_body_list_exit recurse ctx depth strategy rows
    (fun row member => (sites row member).body_frame_exit recurse ctx safe memory depth strategy row.2 callees)

def MemoryFrameCFG (ctx : EvalContext) (cfg : CFG) : Prop :=
  ∀ pc block, cfg pc = some block →
    (∀ row ∈ bodyInstsWithResultDests (ctx.resolveBlock block).body (ctx.resolveBlock block).bodyResultDests,
      MemoryFrameInstruction row.1) ∧ Nonempty (TerminalFrameControl (ctx.resolveBlock block).terminator)

def MemoryFrameProgram (ctx : EvalContext) : Prop :=
  ∀ id function, ctx.functions id = some function → MemoryFrameCFG ctx function.cfg

theorem MemoryFrameCFG.forFunction (ctx : EvalContext) (function : EvalFunction) (cfg : CFG)
    (grammar : MemoryFrameCFG ctx cfg) : MemoryFrameCFG (ctx.forFunction function) cfg := grammar

theorem MemoryFrameProgram.forFunction (ctx : EvalContext) (function : EvalFunction)
    (program : MemoryFrameProgram ctx) : MemoryFrameProgram (ctx.forFunction function) := program

theorem TerminalFrameCFG.toMemoryCFG (ctx : EvalContext) (cfg : CFG) (grammar : TerminalFrameCFG ctx cfg) :
    MemoryFrameCFG ctx cfg := by
  intro pc block found
  obtain ⟨sites, control⟩ := grammar pc block found
  exact ⟨fun row member => .unwind (sites row member), control⟩

theorem TerminalFrameProgram.toMemoryProgram (ctx : EvalContext) (program : TerminalFrameProgram ctx) :
    MemoryFrameProgram ctx := fun id fn found => (program id fn found).toMemoryCFG ctx fn.cfg

theorem memory_frame_layer_exit (recurse : Recurse) (ctx : EvalContext) (safe : StaticFunctionErrors ctx) (memory : MemoryContextErrors ctx)
    (depth : Nat) (cfg : CFG) (pc : BlockId) (args : List Value) (strategy : PanicStrategy)
    (state : MachineState) (valid : WellMintedState state) (incoming : MintedArgs state.nextFrameLineage args)
    (grammar : MemoryFrameCFG ctx cfg) (callees : FrameCalleeExitContract recurse ctx strategy)
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
      (memory_frame_body_list_exit recurse ctx safe memory depth strategy _ sites callees bound boundValid)
    intro unit afterBody bodyValid _
    cases unit
    exact control.dispatch_frame_exit recurse ctx safe depth cfg (ctx.resolveBlock block) strategy afterBody bodyValid callees continuation

/-- Full original bounded CFG exits with real raising, catching and rethrowing.
The callee and caller continuation contracts are both discharged by fuel
induction, across the actual forFunction contexts and their original scopes. -/
theorem memory_frame_cfg_exit (ctx : EvalContext) (cfg : CFG) (grammar : MemoryFrameCFG ctx cfg)
    (program : MemoryFrameProgram ctx) (safe : StaticFunctionErrors ctx) (memory : MemoryContextErrors ctx) (fuel depth : Nat)
    (pc : BlockId) (args : List Value) (strategy : PanicStrategy)
    (state : MachineState) (valid : WellMintedState state) (incoming : MintedArgs state.nextFrameLineage args) :
    FrameCalleeExit state (Sem.run (stepNWithContext ctx fuel depth cfg pc args strategy) state) := by
  induction fuel generalizing ctx cfg depth pc args state with
  | zero => exact True.intro
  | succ fuel ih =>
    rw [stepNWithContext_succ_layer]
    apply memory_frame_layer_exit _ ctx safe memory depth cfg pc args strategy state valid incoming grammar
    · intro id callee found childDepth values before beforeValid transported
      exact ih (ctx.forFunction callee) callee.cfg
        (MemoryFrameCFG.forFunction ctx callee callee.cfg (program id callee found))
        (MemoryFrameProgram.forFunction ctx callee program)
        (StaticFunctionErrors.forFunction ctx callee safe) (MemoryContextErrors.forFunction ctx callee memory) childDepth callee.entryBlock values before beforeValid transported
    · intro next values before beforeValid transported
      exact ih ctx cfg grammar program safe memory depth next values before beforeValid transported

theorem memory_frame_entry_exit (ctx : EvalContext) (cfg : CFG) (grammar : MemoryFrameCFG ctx cfg)
    (program : MemoryFrameProgram ctx) (safe : StaticFunctionErrors ctx) (memory : MemoryContextErrors ctx) (fuel depth : Nat)
    (pc : BlockId) (args : List Value) (strategy : PanicStrategy)
    (state : MachineState) (valid : WellMintedState state) (incoming : MintedArgs state.nextFrameLineage args) :
    FrameCalleeExit state (Sem.run (exitUnwinding strategy (stepNWithContext ctx fuel depth cfg pc args strategy)) state) :=
  exit_unwinding_frame_exit strategy _ state (memory_frame_cfg_exit ctx cfg grammar program safe memory fuel depth pc args strategy state valid incoming)

/-- Prepared aggregate services discharge the error policy rather than asking
consumers to assume arbitrary cache entries cannot carry an unwind state. -/
theorem prepared_memory_frame_entry_exit (ctx : EvalContext) (source : SourceLayout.Environment)
    (roots : List Ty) (prepared : ctx.memoryService = some (AggregateMemory.prepare source roots))
    (cfg : CFG) (grammar : MemoryFrameCFG ctx cfg) (program : MemoryFrameProgram ctx)
    (safe : StaticFunctionErrors ctx) (fuel depth : Nat) (pc : BlockId) (args : List Value)
    (strategy : PanicStrategy) (state : MachineState) (valid : WellMintedState state)
    (incoming : MintedArgs state.nextFrameLineage args) :
    FrameCalleeExit state (Sem.run (exitUnwinding strategy
      (stepNWithContext ctx fuel depth cfg pc args strategy)) state) :=
  memory_frame_entry_exit ctx cfg grammar program safe
    (prepared_memory_context_errors ctx source roots prepared) fuel depth pc args strategy state valid incoming

end TrustIr.FrameLifetime
