-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FramePublicationExits
import TrustIr.Proofs.ConstantContextEquations

set_option smartUnfolding false

namespace TrustIr.FrameLifetime

private theorem pure_safe {α : Type} (value : α) : ExceptNoUnwind (pure value : Except SemError α) := by
  intro exception after same
  cases same

private theorem missing_safe (ty : Ty) (constant : Constant) (feature : UnsupportedFeature) (message : String) :
    ExceptNoUnwind (constMissingDefinition ty constant feature message) := by
  unfold constMissingDefinition
  split <;> intro exception after same <;> cases same

private theorem type_safe {α : Type} (message : String) : ExceptNoUnwind (throw (.typeError message) : Except SemError α) := by
  intro exception after same
  cases same
private theorem unsupported_safe {α : Type} (feature : UnsupportedFeature) (message : String) : ExceptNoUnwind (throw (.unsupported feature message) : Except SemError α) := by
  intro exception after same
  cases same

-- Dispatch on syntax before elaborating helper applications: attempting
-- definitional unification against every recursive matcher expands the whole
-- conversion graph. These tactics produce ordinary kernel-checked terms.
open Lean Elab Tactic in
elab "constant_errors" : tactic => do
  let target ← getMainTarget
  let some result := target.getAppArgs.back? | throwError "not an error policy"
  let reduced := match result with
    | .letE _ _ value body _ => body.instantiate1 value
    | _ => result.headBeta
  if reduced != result then
    let args := target.getAppArgs
    let changed := mkAppN target.getAppFn (args.set! (args.size - 1) reduced)
    let goal ← (← getMainGoal).replaceTargetDefEq changed
    replaceMainGoal [goal]
    return
  match reduced.getAppFn.constName? with
  | some ``Pure.pure | some ``Except.ok => evalTactic (← `(tactic| exact pure_safe _))
  | some ``constMissingDefinition => evalTactic (← `(tactic| exact missing_safe _ _ _ _))
  | some ``Bind.bind | some ``Except.bind =>
      evalTactic (← `(tactic| (refine ExceptNoUnwind.bind _ _ ?_ (fun value => ?_) <;> dsimp only)))
  | some ``MonadExceptOf.throw | some ``throw | some ``throwThe | some ``Except.error =>
      evalTactic (← `(tactic| first | exact type_safe _ | exact unsupported_safe _ _))
  | _ => evalTactic (← `(tactic| split))

open Lean Elab Tactic in
elab "constant_recurse" : tactic => do
  let target ← getMainTarget
  let some result := target.getAppArgs.back? | throwError "not an error policy"
  let name ← match result.getAppFn.constName? with
    | some `TrustIr.constValueAtChecked => pure `TrustIr.FrameLifetime.checked_constant_no_unwind
    | some `TrustIr.constFieldsAtChecked => pure `TrustIr.FrameLifetime.checked_fields_no_unwind
    | some `TrustIr.constLanesAtChecked => pure `TrustIr.FrameLifetime.checked_lanes_no_unwind
    | some `TrustIr.constValueAtWithDefsIn => pure `TrustIr.FrameLifetime.context_constant_no_unwind
    | some `TrustIr.constUninitFieldsAtWithDefsIn => pure `TrustIr.FrameLifetime.context_uninit_fields_no_unwind
    | some `TrustIr.constFieldsAtWithDefsIn => pure `TrustIr.FrameLifetime.context_fields_no_unwind
    | some `TrustIr.constLanesAtWithDefsIn => pure `TrustIr.FrameLifetime.context_lanes_no_unwind
    | some `TrustIr.constRecordFieldsAtWithDefsIn => pure `TrustIr.FrameLifetime.context_record_fields_no_unwind
    | _ => throwError "not a recursive constant conversion"
  let theoremName := mkIdent name
  if name == `TrustIr.FrameLifetime.context_uninit_fields_no_unwind then
    evalTactic (← `(tactic| exact $theoremName _ _ _ _))
  else if name == `TrustIr.FrameLifetime.context_fields_no_unwind ||
      name == `TrustIr.FrameLifetime.context_lanes_no_unwind || name == `TrustIr.FrameLifetime.context_record_fields_no_unwind ||
      name == `TrustIr.FrameLifetime.checked_lanes_no_unwind then
    evalTactic (← `(tactic| exact $theoremName _ _ _))
  else evalTactic (← `(tactic| exact $theoremName _ _ _ _))

open Lean Elab Tactic in
elab "prune_constant_recursion" : tactic => withMainContext do
  let mut goal ← getMainGoal
  for declaration in (← getLCtx) do
    if declaration.type.isForall then
      try goal ← goal.clear declaration.fvarId catch _ => pure ()
  replaceMainGoal [goal]

-- Scoped proof-elaboration ceiling for the complete mutually recursive
-- matcher, independent of evaluator fuel and validation budgets.
set_option maxHeartbeats 2000000 in
mutual

theorem checked_constant_no_unwind (ty : Ty) (constant : Constant) (model : ByteModel) (allow : Bool) :
    ExceptNoUnwind (constValueAtChecked ty constant model allow) := by
  rw [constValueAtChecked_eq]
  by_cases rejected : (!constPointerFormsSupported ty constant) = true
  · rw [if_pos rejected]
    exact type_safe _
  · rw [if_neg rejected]
    rw [pure_bind]
    clear rejected
    repeat' first
      | constant_recurse
      | constant_errors
termination_by sizeOf constant
decreasing_by
  trustIrCompilerProof {
    all_goals (prune_constant_recursion; subst_vars; simp_wf; (try simp_all only); omega)
  } {
    all_goals (prune_constant_recursion; subst_vars <;> simp_wf <;> (try simp_all only) <;> omega)
  }


theorem checked_fields_no_unwind (types : List Ty) (constants : List Constant) (model : ByteModel) (allow : Bool) :
    ExceptNoUnwind (constFieldsAtChecked types constants model allow) := by
  rw [constFieldsAtChecked_eq]
  repeat' first
    | constant_recurse
    | constant_errors
termination_by sizeOf constants
decreasing_by
  trustIrCompilerProof {
    all_goals (prune_constant_recursion; subst_vars; simp_wf; (try simp_all only); omega)
  } {
    all_goals (prune_constant_recursion; subst_vars <;> simp_wf <;> (try simp_all only) <;> omega)
  }


theorem checked_lanes_no_unwind (ty : Ty) (constants : List Constant) (model : ByteModel) :
    ExceptNoUnwind (constLanesAtChecked ty constants model) := by
  rw [constLanesAtChecked_eq]
  repeat' first
    | constant_recurse
    | constant_errors
termination_by sizeOf constants
decreasing_by
  trustIrCompilerProof {
    all_goals (prune_constant_recursion; subst_vars; simp_wf; (try simp_all only); omega)
  } {
    all_goals (prune_constant_recursion; subst_vars <;> simp_wf <;> (try simp_all only) <;> omega)
  }


end

-- Scoped proof-elaboration ceiling for the complete mutually recursive
-- matcher, independent of evaluator fuel and validation budgets.
set_option maxHeartbeats 2000000 in
mutual

theorem context_constant_no_unwind (ctx : ConstantEvalContext) (ty : Ty) (constant : Constant) (allow : Bool) :
    ExceptNoUnwind (constValueAtWithDefsIn ctx ty constant allow) := by
  rw [constValueAtWithDefsIn_eq ctx ty constant allow]
  by_cases rejected : (!constPointerFormsSupported ty constant) = true
  · rw [if_pos rejected]
    exact type_safe _
  · rw [if_neg rejected,pure_bind]
    clear rejected
    repeat' first
      | constant_recurse
      | constant_errors
termination_by sizeOf constant
decreasing_by
  trustIrCompilerProof {
    all_goals (prune_constant_recursion; subst_vars; simp_wf; (try simp_all only); omega)
  } {
    all_goals (prune_constant_recursion; subst_vars <;> simp_wf <;> (try simp_all only) <;> omega)
  }


theorem context_uninit_fields_no_unwind (ctx : ConstantEvalContext) (types : List Ty) (constants : List Constant) (allow : Bool) :
    ExceptNoUnwind (constUninitFieldsAtWithDefsIn ctx types constants allow) := by
  rw [constUninitFieldsAtWithDefsIn_eq]
  repeat' first
    | constant_recurse
    | constant_errors
termination_by sizeOf constants
decreasing_by
  trustIrCompilerProof {
    all_goals (prune_constant_recursion; subst_vars; simp_wf; (try simp_all only); omega)
  } {
    all_goals (prune_constant_recursion; subst_vars <;> simp_wf <;> (try simp_all only) <;> omega)
  }


theorem context_fields_no_unwind (ctx : ConstantEvalContext) (types : List Ty) (constants : List Constant) :
    ExceptNoUnwind (constFieldsAtWithDefsIn ctx types constants) := by
  rw [constFieldsAtWithDefsIn_eq]
  repeat' first
    | constant_recurse
    | constant_errors
termination_by sizeOf constants
decreasing_by
  trustIrCompilerProof {
    all_goals (prune_constant_recursion; subst_vars; simp_wf; (try simp_all only); omega)
  } {
    all_goals (prune_constant_recursion; subst_vars <;> simp_wf <;> (try simp_all only) <;> omega)
  }


theorem context_lanes_no_unwind (ctx : ConstantEvalContext) (ty : Ty) (constants : List Constant) :
    ExceptNoUnwind (constLanesAtWithDefsIn ctx ty constants) := by
  rw [constLanesAtWithDefsIn_eq]
  repeat' first
    | constant_recurse
    | constant_errors
termination_by sizeOf constants
decreasing_by
  trustIrCompilerProof {
    all_goals (prune_constant_recursion; subst_vars; simp_wf; (try simp_all only); omega)
  } {
    all_goals (prune_constant_recursion; subst_vars <;> simp_wf <;> (try simp_all only) <;> omega)
  }


theorem context_record_fields_no_unwind (ctx : ConstantEvalContext) (declared : List FieldDef) (fields : List (String × Constant)) :
    ExceptNoUnwind (constRecordFieldsAtWithDefsIn ctx declared fields) := by
  rw [constRecordFieldsAtWithDefsIn_eq]
  repeat' first
    | constant_recurse
    | constant_errors
termination_by sizeOf fields
decreasing_by
  trustIrCompilerProof {
    all_goals (prune_constant_recursion; subst_vars; simp_wf; (try simp_all only); omega)
  } {
    all_goals (prune_constant_recursion; subst_vars <;> simp_wf <;> (try simp_all only) <;> omega)
  }


end

end TrustIr.FrameLifetime
