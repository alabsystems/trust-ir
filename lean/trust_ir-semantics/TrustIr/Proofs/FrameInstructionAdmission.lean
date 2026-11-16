-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameSequenceRecursion

namespace TrustIr.FrameLifetime

local macro "admit_body" : tactic => `(tactic|
  first
    | exact .constant _ _
    | exact .global _
    | exact .map _ _ _
    | (solve | apply SequenceFrameInstruction.static; constructor)
    | exact .memory (.load _ _ _ _)
    | exact .memory (.store _ _ _ _ _)
    | exact .memory (.gep _ _ _ _)
    | exact .memory (.boxDeref _ _ _ _)
    | (solve | apply SequenceFrameInstruction.memory; apply MemoryFrameInstruction.atomic; constructor)
    | (solve | apply SequenceFrameInstruction.memory; apply MemoryFrameInstruction.allocation; constructor)
    | (solve | apply SequenceFrameInstruction.memory; apply MemoryFrameInstruction.bulk; constructor)
    | (solve | apply SequenceFrameInstruction.memory; apply MemoryFrameInstruction.ownership; constructor)
    | exact .memory (.unwind (.assert _ _ _))
    | exact .memory (.unwind (.pad _ _))
    | exact .memory (.unwind (.call (.indirect _ _ _ _)))
    | exact .memory (.unwind (.call (.direct (.call _ _))))
    | (solve
        | apply SequenceFrameInstruction.memory
          apply MemoryFrameInstruction.unwind
          apply UnwindFrameInstruction.call
          apply CallFrameInstruction.direct
          apply DirectFrameInstruction.value
          constructor))

/-- Exhaustive over the actual instruction datatype, including the original
structured refusals. It establishes admission, not successful execution. -/
theorem every_body_instruction_admitted (inst : Inst) (body : inst.isTerminator = false) :
    SequenceFrameInstruction inst := by
  cases inst <;> try cases body
  all_goals admit_body

/-- Every declared terminator has an original dispatch exit proof. -/
theorem every_terminator_admitted (inst : Inst) (terminal : inst.isTerminator = true) :
    Nonempty (TerminalFrameControl inst) := by
  cases inst <;> try cases terminal
  all_goals first
    | (solve | refine ⟨.unwind (.ordinary ?_)⟩; constructor)
    | exact ⟨.unwind (.invoke _ _ _ _ _)⟩
    | exact ⟨.unwind (.indirect _ _ _ _ _ _ _)⟩
    | exact ⟨.unwind (.assert _ _ _ _ _ _)⟩
    | exact ⟨.unwind (.resume _)⟩
    | exact ⟨.suspend _ _ _ _⟩
    | exact ⟨.dropInvoke _ _ _ _ _⟩

/-- Original destructor resolution retains the source instruction's position. -/
theorem resolve_drop_terminator_flag (ctx : EvalContext) (inst : Inst) :
    (ctx.resolveDrop inst).isTerminator = inst.isTerminator := by
  cases inst <;> try rfl
  case Drop ty pointer => cases selected : ctx.dropGlue ty <;> simp only [EvalContext.resolveDrop,selected,Inst.isTerminator]
  case DropInvoke ty pointer normal args unwind => cases selected : ctx.dropGlue ty <;> simp only [EvalContext.resolveDrop,selected,Inst.isTerminator]

private theorem body_row_instruction_member (body : List Inst) (dests : List (List ValueId))
    (row : Inst × List ValueId) (member : row ∈ bodyInstsWithResultDests body dests) : row.1 ∈ body := by
  induction body generalizing dests with
  | nil => cases member
  | cons inst rest ih =>
    cases dests <;> simp only [bodyInstsWithResultDests] at member
    all_goals cases member with
      | head => exact .head _
      | tail _ member => exact .tail _ (ih _ member)

/-- Only source block position is required for instruction admission. SSA,
type, memory and control-target errors keep their actual evaluator behavior. -/
def FrameBlockShape (cfg : CFG) : Prop :=
  ∀ pc block, cfg pc = some block →
    (∀ inst ∈ block.body, inst.isTerminator = false) ∧ block.terminator.isTerminator = true

def FrameProgramShape (ctx : EvalContext) : Prop :=
  ∀ id function, ctx.functions id = some function → FrameBlockShape function.cfg

theorem FrameBlockShape.admitted (ctx : EvalContext) (cfg : CFG) (shape : FrameBlockShape cfg) :
    SequenceFrameCFG ctx cfg := by
  intro pc block found
  obtain ⟨body,terminal⟩ := shape pc block found
  constructor
  · intro row member
    apply every_body_instruction_admitted
    have held := body_row_instruction_member _ _ row member
    change row.1 ∈ block.body.map ctx.resolveDrop at held
    obtain ⟨inst,member,same⟩ := List.mem_map.mp held
    rw [← same,resolve_drop_terminator_flag]
    exact body inst member
  · apply every_terminator_admitted
    change (ctx.resolveDrop block.terminator).isTerminator = true
    rw [resolve_drop_terminator_flag]
    exact terminal

theorem FrameProgramShape.admitted (ctx : EvalContext) (shape : FrameProgramShape ctx) :
    SequenceFrameProgram ctx := fun id function found => (shape id function found).admitted ctx function.cfg

/-- Original bounded execution now needs block shape rather than an
instruction-family whitelist; all service-error policies remain explicit. -/
theorem shaped_frame_entry_exit (ctx : EvalContext) (cfg : CFG) (shape : FrameBlockShape cfg)
    (program : FrameProgramShape ctx) (safe : StaticFunctionErrors ctx) (headers : HeaderContextErrors ctx)
    (memory : MemoryContextErrors ctx) (fuel depth : Nat) (pc : BlockId) (args : List Value)
    (strategy : PanicStrategy) (state : MachineState) (valid : WellMintedState state)
    (incoming : MintedArgs state.nextFrameLineage args) :
    FrameCalleeExit state (Sem.run (exitUnwinding strategy
      (stepNWithContext ctx fuel depth cfg pc args strategy)) state) :=
  sequence_frame_entry_exit ctx cfg (shape.admitted ctx cfg) (program.admitted ctx)
    safe headers memory fuel depth pc args strategy state valid incoming

/-- Actual context assembly discharges all three service-error policies. -/
theorem decoded_shaped_frame_entry_exit (source : TrustIrEval.Module) (maxDepth : Nat) (ctx : EvalContext)
    (assembled : TrustIrEval.contextOf source maxDepth = .ok ctx) (cfg : CFG) (shape : FrameBlockShape cfg)
    (program : FrameProgramShape ctx) (fuel depth : Nat) (pc : BlockId) (args : List Value)
    (strategy : PanicStrategy) (state : MachineState) (valid : WellMintedState state)
    (incoming : MintedArgs state.nextFrameLineage args) :
    FrameCalleeExit state (Sem.run (exitUnwinding strategy
      (stepNWithContext ctx fuel depth cfg pc args strategy)) state) :=
  decoded_sequence_frame_entry_exit source maxDepth ctx assembled cfg (shape.admitted ctx cfg)
    (program.admitted ctx) fuel depth pc args strategy state valid incoming

end TrustIr.FrameLifetime
