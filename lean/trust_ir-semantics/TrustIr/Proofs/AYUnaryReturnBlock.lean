-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYUnaryReplay

namespace TrustIr.AYUnaryReplay
open GenericCoro.Prefix

/-- The production Return payload lookup, with its actual ordered values
and errors. No additional return policy is invented by the replay. -/
def returnValues (ids : List ValueId) : Sem (List Value) := ids.mapM Sem.lookupValue

theorem evalLayer_return (recurse : Recurse) (ctx : EvalContext) (depth : Nat) (cfg : CFG) (pc : BlockId)
    (args : List Value) (strategy : PanicStrategy) (block : BasicBlock) (found : cfg pc = some block)
    (ids : List ValueId) (returns : (ctx.resolveBlock block).terminator = .Return ids) :
    evalLayer recurse ctx depth cfg pc args strategy = (do
      bindBlockParamsChecked (ctx.resolveBlock block).params args
      evalBody recurse ctx depth strategy (bodyInstsWithResultDests (ctx.resolveBlock block).body (ctx.resolveBlock block).bodyResultDests)
      returnValues ids) := by
  unfold evalLayer
  rw [found]
  dsimp only
  rw [returns]
  cases strategy <;> simp [stepTermWithContext, closureTermWithContext, stepTermUnwind, stepInst, semReturn,
    returnValues, bind_assoc]

/-- A point replay tied to the actual CFG lookup, resolved source block,
parameter outcome and original production body. A failed prefix keeps its
unreached terminator, without claiming it is statically supported. -/
inductive ReturnBlock (ctx : EvalContext) (cfg : CFG) (pc : BlockId) (args : List Value) (state : MachineState) where
  | missing (absent : cfg pc = none)
  | parameterError (block : BasicBlock) (found : cfg pc = some block) (error : SemError)
      (actual : Sem.run (bindBlockParamsChecked (ctx.resolveBlock block).params args) state = .error error)
  | bodyError (block : BasicBlock) (found : cfg pc = some block) (boundState : MachineState)
      (bound : Sem.run (bindBlockParamsChecked (ctx.resolveBlock block).params args) state = .ok ((),boundState))
      (trace : Trace ctx (bodyInstsWithResultDests (ctx.resolveBlock block).body (ctx.resolveBlock block).bodyResultDests) boundState)
      (error : SemError) (actual : trace.outcome = .error error)
  | returned (block : BasicBlock) (found : cfg pc = some block) (boundState : MachineState)
      (bound : Sem.run (bindBlockParamsChecked (ctx.resolveBlock block).params args) state = .ok ((),boundState))
      (trace : Trace ctx (bodyInstsWithResultDests (ctx.resolveBlock block).body (ctx.resolveBlock block).bodyResultDests) boundState)
      (after : MachineState) (actual : trace.outcome = .ok ((),after))
      (ids : List ValueId) (returns : (ctx.resolveBlock block).terminator = .Return ids)

def ReturnBlock.outcome {ctx cfg pc args state} : ReturnBlock ctx cfg pc args state → Except SemError (List Value × MachineState)
  | .missing _ => .error (.typeError s!"undefined block: {repr pc}")
  | .parameterError _ _ error _ => .error error
  | .bodyError _ _ _ _ _ error _ => .error error
  | .returned _ _ _ _ _ after _ ids _ => Sem.run (returnValues ids) after

def ReturnBlock.build (ctx : EvalContext) (cfg : CFG) (pc : BlockId) (args : List Value) (state : MachineState) :
    Except String (ReturnBlock ctx cfg pc args state) :=
  match found : cfg pc with
  | none => .ok (.missing found)
  | some block =>
    match bound : Sem.run (bindBlockParamsChecked (ctx.resolveBlock block).params args) state with
    | .error error => .ok (.parameterError block found error bound)
    | .ok ((),boundState) => do
      let trace ← Trace.build ctx (bodyInstsWithResultDests (ctx.resolveBlock block).body (ctx.resolveBlock block).bodyResultDests) boundState
      match actual : trace.outcome with
      | .error error => .ok (.bodyError block found boundState bound trace error actual)
      | .ok ((),after) =>
        match returns : (ctx.resolveBlock block).terminator with
        | .Return ids => .ok (.returned block found boundState bound trace after actual ids returns)
        | _ => .error "block replay requires a Return at the reached terminator"

theorem ReturnBlock.layer_correct {ctx cfg pc args state} (checked : ReturnBlock ctx cfg pc args state)
    (recurse : Recurse) (depth : Nat) (strategy : PanicStrategy) :
    Sem.run (evalLayer recurse ctx depth cfg pc args strategy) state = checked.outcome := by
  cases checked with
  | missing absent => simp only [evalLayer, absent]; rfl
  | parameterError block found error actual =>
    simp only [evalLayer, found]
    rw [Sem.run_bind, actual]
    rfl
  | bodyError block found boundState bound trace error actual =>
    simp only [evalLayer, found]
    rw [Sem.run_bind, bound]
    change Sem.run (do
      evalBody recurse ctx depth strategy _
      _) boundState = _
    rw [Sem.run_bind, trace.correct recurse depth strategy, actual]
    rfl
  | returned block found boundState bound trace after actual ids returns =>
    rw [evalLayer_return recurse ctx depth cfg pc args strategy block found ids returns, Sem.run_bind, bound]
    change Sem.run (do evalBody recurse ctx depth strategy _; returnValues ids) boundState = _
    rw [Sem.run_bind, trace.correct recurse depth strategy, actual]
    rfl

/-- Fuel zero is checked before CFG lookup and every replayed operation. -/
def ReturnBlock.runFuel {ctx cfg pc args state} (checked : ReturnBlock ctx cfg pc args state) :
    Nat → Except SemError (List Value × MachineState)
  | 0 => .error .outOfFuel
  | _+1 => checked.outcome

theorem ReturnBlock.correct {ctx cfg pc args state} (checked : ReturnBlock ctx cfg pc args state)
    (fuel depth : Nat) (strategy : PanicStrategy) :
    Sem.run (stepNWithContext ctx fuel depth cfg pc args strategy) state = checked.runFuel fuel := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    rw [stepNWithContext_succ_layer]
    exact checked.layer_correct _ depth strategy

theorem ReturnBlock.built_correct (ctx : EvalContext) (cfg : CFG) (pc : BlockId) (args : List Value) (state : MachineState)
    (checked : ReturnBlock ctx cfg pc args state) (_built : ReturnBlock.build ctx cfg pc args state = .ok checked)
    (fuel depth : Nat) (strategy : PanicStrategy) :
    Sem.run (stepNWithContext ctx fuel depth cfg pc args strategy) state = checked.runFuel fuel := checked.correct fuel depth strategy

end TrustIr.AYUnaryReplay
