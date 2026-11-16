-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYUnaryReturnBlock

namespace TrustIr.AYUnaryReplay
open GenericCoro.Prefix

/-- Original control syntax, retaining condition, case order and edge arguments. -/
inductive Control : Inst → Type where
  | br (target : BlockId) (args : List ValueId) : Control (.Br target args)
  | cond (id : ValueId) (yes : BlockId) (yesArgs : List ValueId) (no : BlockId) (noArgs : List ValueId) :
      Control (.CondBr id yes yesArgs no noArgs)
  | switch (id : ValueId) (default_ : BlockId) (args : List ValueId) (cases : List SwitchCase) (exhaustive : Bool) :
      Control (.Switch id default_ args cases exhaustive)
  | unreachable : Control .Unreachable

def Control.ofInst : (inst : Inst) → Except String (Control inst)
  | .Br target args => .ok (.br target args)
  | .CondBr id yes ys no ns => .ok (.cond id yes ys no ns)
  | .Switch id default_ args cases exhaustive => .ok (.switch id default_ args cases exhaustive)
  | .Unreachable => .ok .unreachable
  | _ => .error "CFG replay reached an unsupported control instruction"

def Control.action {inst : Inst} : Control inst → Sem StepResult
  | .br target args => semBr target args
  | .cond id yes ys no ns => semCondBr id yes ys no ns
  | .switch id default_ args cases _ => semSwitch id default_ args cases
  | .unreachable => pure .Stuck

theorem Control.stepTerm {inst : Inst} (control : Control inst) (ctx : EvalContext) (depth : Nat)
    (cfg : CFG) (strategy : PanicStrategy) :
    stepTermWithContext ctx depth cfg inst strategy = (do
      let result ← control.action
      pure (.terminator result)) := by
  cases control <;> cases strategy <;> rfl

/-- The actual successful block entry, before its original terminator. -/
structure Prefix (ctx : EvalContext) (cfg : CFG) (pc : BlockId) (args : List Value) (state : MachineState) where
  block : BasicBlock
  found : cfg pc = some block
  boundState : MachineState
  bound : Sem.run (bindParameters ctx (ctx.resolveBlock block) args) state = .ok ((),boundState)
  trace : Trace ctx (bodyInstsWithResultDests (ctx.resolveBlock block).body (ctx.resolveBlock block).bodyResultDests) boundState
  after : MachineState
  actual : trace.outcome = .ok ((),after)

private theorem Prefix.parameters_checked {ctx cfg pc args state} (entry : Prefix ctx cfg pc args state) :
    checkFunctionItemValues ctx ((ctx.resolveBlock entry.block).params.map (·.snd)) args = .ok () := by
  have bound := entry.bound
  cases checked : checkFunctionItemValues ctx ((ctx.resolveBlock entry.block).params.map (·.snd)) args with
  | error reason =>
    simp only [bindParameters, checked, Sem.fromMemoryExcept] at bound
    change Except.error reason = Except.ok ((),entry.boundState) at bound
    cases bound
  | ok unit => cases unit; rfl

private theorem Prefix.bound_parameters {ctx cfg pc args state} (entry : Prefix ctx cfg pc args state) :
    Sem.run (bindBlockParamsChecked (ctx.resolveBlock entry.block).params args) state = .ok ((),entry.boundState) := by
  simpa only [bindParameters, entry.parameters_checked, Sem.fromMemoryExcept, pure_bind] using entry.bound

theorem Prefix.control_error {ctx cfg pc args state} (entry : Prefix ctx cfg pc args state)
    (control : Control (ctx.resolveBlock entry.block).terminator) (error : SemError)
    (actual : Sem.run control.action entry.after = .error error)
    (recurse : Recurse) (depth : Nat) (strategy : PanicStrategy) :
    Sem.run (evalLayer recurse ctx depth cfg pc args strategy) state = .error error := by
  simp only [evalLayer, entry.found, entry.parameters_checked, Sem.fromMemoryExcept, pure_bind]
  rw [Sem.run_bind, entry.bound_parameters]
  change Sem.run (do evalBody recurse ctx depth strategy _; _) entry.boundState = _
  rw [Sem.run_bind, entry.trace.correct recurse depth strategy, entry.actual]
  change Sem.run (do let termResult ← stepTermWithContext ctx depth cfg _ strategy; _) entry.after = _
  rw [control.stepTerm ctx depth cfg strategy]
  simp only [bind_assoc, pure_bind]
  rw [Sem.run_bind, actual]
  rfl

theorem Prefix.unreachable {ctx cfg pc args state} (entry : Prefix ctx cfg pc args state)
    (control : Control (ctx.resolveBlock entry.block).terminator) (after : MachineState)
    (actual : Sem.run control.action entry.after = .ok (.Stuck,after))
    (recurse : Recurse) (depth : Nat) (strategy : PanicStrategy) :
    Sem.run (evalLayer recurse ctx depth cfg pc args strategy) state = .error (.ub "reached unreachable") := by
  simp only [evalLayer, entry.found, entry.parameters_checked, Sem.fromMemoryExcept, pure_bind]
  rw [Sem.run_bind, entry.bound_parameters]
  change Sem.run (do evalBody recurse ctx depth strategy _; _) entry.boundState = _
  rw [Sem.run_bind, entry.trace.correct recurse depth strategy, entry.actual]
  change Sem.run (do let termResult ← stepTermWithContext ctx depth cfg _ strategy; _) entry.after = _
  rw [control.stepTerm ctx depth cfg strategy]
  simp only [bind_assoc, pure_bind]
  rw [Sem.run_bind, actual]
  rfl

theorem Prefix.transfer {ctx cfg pc args state} (entry : Prefix ctx cfg pc args state)
    (control : Control (ctx.resolveBlock entry.block).terminator) (nextPc : BlockId) (nextArgs : List Value) (after : MachineState)
    (actual : Sem.run control.action entry.after = .ok (.Continue nextPc nextArgs,after))
    (recurse : Recurse) (depth : Nat) (strategy : PanicStrategy) :
    Sem.run (evalLayer recurse ctx depth cfg pc args strategy) state = Sem.run (recurse ctx depth cfg nextPc nextArgs strategy) after := by
  simp only [evalLayer, entry.found, entry.parameters_checked, Sem.fromMemoryExcept, pure_bind]
  rw [Sem.run_bind, entry.bound_parameters]
  change Sem.run (do evalBody recurse ctx depth strategy _; _) entry.boundState = _
  rw [Sem.run_bind, entry.trace.correct recurse depth strategy, entry.actual]
  change Sem.run (do let termResult ← stepTermWithContext ctx depth cfg _ strategy; _) entry.after = _
  rw [control.stepTerm ctx depth cfg strategy]
  simp only [bind_assoc, pure_bind]
  rw [Sem.run_bind, actual]
  rfl

/-- Bounded executions are indexed by original CFG, fuel, PC, arguments and
state. Successor receipts use the actual selected edge and one less fuel. -/
inductive CFGTrace (ctx : EvalContext) (cfg : CFG) : Nat → BlockId → List Value → MachineState → Type where
  | exhausted (pc args state) : CFGTrace ctx cfg 0 pc args state
  | terminal {fuel pc args state} (checked : ReturnBlock ctx cfg pc args state) : CFGTrace ctx cfg (fuel+1) pc args state
  | controlError {fuel pc args state} (entry : Prefix ctx cfg pc args state)
      (control : Control (ctx.resolveBlock entry.block).terminator) (error : SemError)
      (actual : Sem.run control.action entry.after = .error error) : CFGTrace ctx cfg (fuel+1) pc args state
  | unreachable {fuel pc args state} (entry : Prefix ctx cfg pc args state)
      (control : Control (ctx.resolveBlock entry.block).terminator) (after : MachineState)
      (actual : Sem.run control.action entry.after = .ok (.Stuck,after)) : CFGTrace ctx cfg (fuel+1) pc args state
  | next {fuel pc args state} (entry : Prefix ctx cfg pc args state)
      (control : Control (ctx.resolveBlock entry.block).terminator) (nextPc : BlockId) (nextArgs : List Value) (after : MachineState)
      (actual : Sem.run control.action entry.after = .ok (.Continue nextPc nextArgs,after))
      (tail : CFGTrace ctx cfg fuel nextPc nextArgs after) : CFGTrace ctx cfg (fuel+1) pc args state

def CFGTrace.outcome {ctx cfg fuel pc args state} : CFGTrace ctx cfg fuel pc args state → Except SemError (List Value × MachineState)
  | .exhausted _ _ _ => .error .outOfFuel
  | .terminal checked => checked.outcome
  | .controlError _ _ error _ => .error error
  | .unreachable _ _ _ _ => .error (.ub "reached unreachable")
  | .next _ _ _ _ _ _ tail => tail.outcome

def CFGTrace.blocks {ctx cfg fuel pc args state} : CFGTrace ctx cfg fuel pc args state → Nat
  | .exhausted _ _ _ => 0
  | .terminal _ | .controlError _ _ _ _ | .unreachable _ _ _ _ => 1
  | .next _ _ _ _ _ _ tail => 1+tail.blocks

def CFGTrace.build (ctx : EvalContext) (cfg : CFG) : (fuel : Nat) → (pc : BlockId) → (args : List Value) →
    (state : MachineState) → Except String (CFGTrace ctx cfg fuel pc args state)
  | 0,pc,args,state => .ok (.exhausted pc args state)
  | fuel+1,pc,args,state =>
    match found : cfg pc with
    | none => .ok (.terminal (.missing found))
    | some block =>
      match bound : Sem.run (bindParameters ctx (ctx.resolveBlock block) args) state with
      | .error error => .ok (.terminal (.parameterError block found error bound))
      | .ok ((),boundState) => do
        let trace ← Trace.build ctx (bodyInstsWithResultDests (ctx.resolveBlock block).body (ctx.resolveBlock block).bodyResultDests) boundState
        match actual : trace.outcome with
        | .error error => .ok (.terminal (.bodyError block found boundState bound trace error actual))
        | .ok ((),after) =>
          match returns : (ctx.resolveBlock block).terminator with
          | .Return ids => .ok (.terminal (.returned block found boundState bound trace after actual ids returns))
          | _ => do
            let entry : Prefix ctx cfg pc args state := ⟨block,found,boundState,bound,trace,after,actual⟩
            let control ← Control.ofInst (ctx.resolveBlock block).terminator
            match step : Sem.run control.action after with
            | .error error => .ok (.controlError entry control error step)
            | .ok (.Stuck,afterTerm) => .ok (.unreachable entry control afterTerm step)
            | .ok (.Continue nextPc nextArgs,afterTerm) =>
              let tail ← CFGTrace.build ctx cfg fuel nextPc nextArgs afterTerm
              .ok (.next entry control nextPc nextArgs afterTerm step tail)
            | .ok _ => .error "CFG replay encountered an unexpected nonlocal control result"

theorem CFGTrace.correct {ctx cfg fuel pc args state} (trace : CFGTrace ctx cfg fuel pc args state)
    (depth : Nat) (strategy : PanicStrategy) :
    Sem.run (stepNWithContext ctx fuel depth cfg pc args strategy) state = trace.outcome := by
  induction trace with
  | exhausted _ _ _ => rfl
  | terminal checked => rw [stepNWithContext_succ_layer]; exact checked.layer_correct _ depth strategy
  | controlError entry control error actual => rw [stepNWithContext_succ_layer]; exact entry.control_error control error actual _ depth strategy
  | unreachable entry control after actual => rw [stepNWithContext_succ_layer]; exact entry.unreachable control after actual _ depth strategy
  | next entry control nextPc nextArgs after actual tail ih =>
    rw [stepNWithContext_succ_layer, entry.transfer control nextPc nextArgs after actual]
    exact ih

theorem CFGTrace.blocks_le {ctx cfg fuel pc args state} (trace : CFGTrace ctx cfg fuel pc args state) : trace.blocks ≤ fuel := by
  induction trace with
  | exhausted _ _ _ => exact Nat.le_refl _
  | terminal _ | controlError _ _ _ _ | unreachable _ _ _ _ => simp [CFGTrace.blocks]
  | next _ _ _ _ _ _ _ ih => simp only [CFGTrace.blocks]; omega

theorem CFGTrace.build_zero (ctx : EvalContext) (cfg : CFG) (pc : BlockId) (args : List Value) (state : MachineState) :
    CFGTrace.build ctx cfg 0 pc args state = .ok (.exhausted pc args state) := rfl

theorem CFGTrace.built_correct (ctx : EvalContext) (cfg : CFG) (fuel : Nat) (pc : BlockId)
    (args : List Value) (state : MachineState) (trace : CFGTrace ctx cfg fuel pc args state)
    (_built : CFGTrace.build ctx cfg fuel pc args state = .ok trace) (depth : Nat) (strategy : PanicStrategy) :
    Sem.run (stepNWithContext ctx fuel depth cfg pc args strategy) state = trace.outcome := trace.correct depth strategy

end TrustIr.AYUnaryReplay
