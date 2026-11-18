-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.GenericCoroPrefixLayer
import TrustIr.Proofs.GenericCoroProps

/-! Shared production return-block normalization. These original public
names and proof bodies are retained without importing an AY replay strategy. -/
namespace TrustIr.AYUnaryReplay
open GenericCoro.Prefix

/-- The production Return payload lookup, with its actual ordered values
and errors. No additional return policy is invented by the replay. -/
def returnValues (ids : List ValueId) : Sem (List Value) := ids.mapM Sem.lookupValue

/-- The exact contextual validation prefix before ordinary SSA binding. -/
def bindParameters (ctx : EvalContext) (block : BasicBlock) (args : List Value) : Sem Unit := do
  let _ ← Sem.fromMemoryExcept (checkFunctionItemValues ctx (block.params.map (·.snd)) args)
  bindBlockParamsChecked block.params args

/-- Ordered payload lookup followed by the actual contextual return check. -/
def checkedReturnValues (ctx : EvalContext) (ids : List ValueId) : Sem (List Value) := do
  let values ← returnValues ids
  GenericCoro.checkedReturn ctx values

theorem evalLayer_return (recurse : Recurse) (ctx : EvalContext) (depth : Nat) (cfg : CFG) (pc : BlockId)
    (args : List Value) (strategy : PanicStrategy) (block : BasicBlock) (found : cfg pc = some block)
    (ids : List ValueId) (returns : (ctx.resolveBlock block).terminator = .Return ids) :
    evalLayer recurse ctx depth cfg pc args strategy = (do
      bindParameters ctx (ctx.resolveBlock block) args
      evalBody recurse ctx depth strategy (bodyInstsWithResultDests (ctx.resolveBlock block).body (ctx.resolveBlock block).bodyResultDests)
      checkedReturnValues ctx ids) := by
  unfold evalLayer
  rw [found]
  dsimp only
  rw [returns]
  cases strategy <;> simp [stepTermWithContext, closureTermWithContext, stepTermUnwind, stepInst, semReturn,
    returnValues, checkedReturnValues, GenericCoro.checkedReturn, bindParameters, bind_assoc] <;> rfl

end TrustIr.AYUnaryReplay
