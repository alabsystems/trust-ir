-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Control flow semantics: Br, CondBr, Switch, Return.
-- Phase 1 of the formalization roadmap.

import TrustIr.Inst
import TrustIr.Semantics.Monad

namespace TrustIr

/-!
# Control Flow Semantics

Control flow instructions determine which basic block to execute next.
They are always the last instruction in a basic block (terminators).

## Block-parameter SSA

TrustIr uses block parameters instead of phi nodes. When branching to a
block, values are passed as arguments to the target block's parameters.
This is the same model used by MLIR and Swift SIL.

## Step result

Control flow instructions return a `StepResult` indicating:
- `Continue`: branch to the next block with arguments
- `Ret`: return from the function with values
- `Stuck`: execution is stuck (Unreachable reached)
-/

/-- Result of executing a terminator instruction. -/
inductive StepResult where
  | Continue : BlockId -> List Value -> StepResult    -- Branch to block with args
  | Ret      : List Value -> StepResult               -- Return from function
  | Stuck    : StepResult                             -- Unreachable / error
  -- Call request: the evaluator must push a frame and dispatch to the callee.
  -- calleeId is the function to call; args are the resolved argument values.
  | CallReq  : FuncId -> List Value -> StepResult
  -- Indirect call request: the evaluator resolves the function pointer
  -- address and validates it against the requested signature.
  | CallIndirectReq : Nat -> FuncTyId -> List Value -> StepResult
  -- Invoke request (`Inst.Invoke`): a call with two control-flow successors.
  -- Fields: callee, resolved argument values, normal destination, UNresolved
  -- normal-edge argument ids (they may reference the invoke's own results, so
  -- they are evaluated only AFTER the evaluator binds those — mirroring
  -- interpret.rs), and the unwind destination. Under `PanicStrategy.abort`
  -- (the panic=abort projection) the unwind edge is never taken; under
  -- `.unwind` the contextual evaluator enters it when the callee unwinds
  -- (amendment D, Part 2).
  | InvokeReq : FuncId -> List Value -> BlockId -> List ValueId -> BlockId
      -> StepResult
  -- Indirect invoke request (`Inst.InvokeIndirect`, amendment D Part 2):
  -- `CallIndirectReq`'s fields (callee address, signature, resolved argument
  -- values) then `InvokeReq`'s successor fields (normal destination,
  -- UNresolved normal-edge argument ids, unwind destination).
  | InvokeIndirectReq : Nat -> FuncTyId -> List Value -> BlockId -> List ValueId
      -> BlockId -> StepResult

  -- SeqMap request: the evaluator must apply the element function (first
  -- field) to every element of the resolved sequence (second field) via the
  -- function table, with frame save/restore per element call and ONE
  -- call-depth level for the whole map (depth bounds NESTING, not sequence
  -- length). Produced by `stepInst` for `Inst.SeqMap` — the per-element
  -- application is interprocedural, mirroring the Call/CallReq split.
  | SeqMapReq : FuncId -> List Value -> StepResult
  deriving Repr

/-- Evaluate a Br (unconditional branch) instruction. -/
def semBr (target : BlockId) (argIds : List ValueId) : Sem StepResult := do
  let args ← argIds.mapM Sem.lookupValue
  pure (.Continue target args)

/-- Evaluate a CondBr (conditional branch) instruction. -/
def semCondBr (condId : ValueId)
    (thenTarget : BlockId) (thenArgIds : List ValueId)
    (elseTarget : BlockId) (elseArgIds : List ValueId)
    : Sem StepResult := do
  let condVal ← Sem.lookupValue condId
  -- The branch condition is inspected: a poison condition is UB.
  Sem.rejectPartial condVal "CondBr"
  match condVal with
  | .bool true =>
    let args ← thenArgIds.mapM Sem.lookupValue
    pure (.Continue thenTarget args)
  | .bool false =>
    let args ← elseArgIds.mapM Sem.lookupValue
    pure (.Continue elseTarget args)
  | .int _ v =>
    -- Integer condition: nonzero = true
    if v != 0 then do
      let args ← thenArgIds.mapM Sem.lookupValue
      pure (.Continue thenTarget args)
    else do
      let args ← elseArgIds.mapM Sem.lookupValue
      pure (.Continue elseTarget args)
  | _ => Sem.throwTypeError "CondBr: condition is not a boolean or integer"

/-- Evaluate a Return instruction. -/
def semReturn (valueIds : List ValueId) : Sem StepResult := do
  let values ← valueIds.mapM Sem.lookupValue
  pure (.Ret values)

end TrustIr
