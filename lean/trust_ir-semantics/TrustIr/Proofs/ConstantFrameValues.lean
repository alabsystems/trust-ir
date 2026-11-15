-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameConstantExits
import TrustIr.Proofs.FrameConstructionValidity

set_option smartUnfolding false
namespace TrustIr.FrameLifetime

/-! Successful original constant conversion carries no frame identity,
including in nested aggregate, closure and fat-pointer metadata payloads.
The mutual proofs recurse on the actual constant/list size. Syntax-directed
tactics construct ordinary proof terms from actual successful child runs. -/


private theorem bind_success {α β : Type} (action : Except SemError α) (next : α → Except SemError β)
    (result : β) (run : (action >>= next) = .ok result) :
    ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action with
  | error error => cases run
  | ok value => exact ⟨value,rfl,run⟩

private theorem null_fat_minted (kind : FatPtrKind) (model : ByteModel) :
    MintedValue 0 (constNullFatPointer kind model) := by
  trustIrCompilerProof {
    cases kind <;> simp [constNullFatPointer,mintedValue_iff_shape,ValueIdentityShape,Value.intAt]
  } {
    cases kind <;> (unfold constNullFatPointer; repeat' (rw [mintedValue_iff_shape]; simp only [ValueIdentityShape,Value.intAt]))
  }

set_option maxHeartbeats 2000000 in
private theorem integer_constant_minted (ty : Ty) (value : Int) (model : ByteModel) :
    MintedValue 0 (constValueAt ty (.int value) model) := by
  trustIrCompilerProof {
    cases ty <;> simp only [constValueAt]
    all_goals repeat' first
      | (solve | simp [mintedValue_iff_shape,ValueIdentityShape,Value.intAt])
      | split
  } {
    cases ty <;> simp only [constValueAt]
    all_goals repeat' first
      | (solve | (repeat' (rw [mintedValue_iff_shape]; simp only [ValueIdentityShape,Value.intAt])))
      | split
  }

private theorem nil_minted : MintedArgs 0 [] := fun _ member => nomatch member
private theorem cons_minted (value : Value) (values : List Value)
    (first : MintedValue 0 value) (rest : MintedArgs 0 values) : MintedArgs 0 (value :: values) := by
  intro held member
  cases member with
  | head => exact first
  | tail _ member => exact rest held member

private theorem empty_aggregate_minted : MintedValue 0 (.aggregate []) :=
  (mintedValue_iff_shape _ _).2 nil_minted

def MintedConstantFields (fields : List (String × Value)) : Prop :=
  ∀ name value, (name,value) ∈ fields → MintedValue 0 value

private theorem nil_fields_minted : MintedConstantFields [] := fun _ _ member => nomatch member
private theorem cons_fields_minted (name : String) (value : Value) (fields : List (String × Value))
    (first : MintedValue 0 value) (rest : MintedConstantFields fields) : MintedConstantFields ((name,value) :: fields) := by
  intro heldName heldValue member
  cases member with
  | head => exact first
  | tail _ member => exact rest heldName heldValue member

private theorem bytes_array_minted (bytes : List UInt8) :
    MintedValue 0 (.array (CompactArray.Packed.ofArray (bytes.map (fun byte => .int 8 (Int.ofNat byte.toNat))).toArray)) := by
  trustIrCompilerProof {
    apply array_from_lanes_minted
    induction bytes with
    | nil => exact nil_minted
    | cons byte rest ih =>
      apply cons_minted _ _ _ ih
      simp [mintedValue_iff_shape,ValueIdentityShape]
  } {
    apply array_from_lanes_minted
    induction bytes with
    | nil => exact nil_minted
    | cons byte rest ih =>
      apply cons_minted _ _ _ ih
      (repeat' (rw [mintedValue_iff_shape]; simp only [ValueIdentityShape]))
  }

local macro "constant_value_leaf" : tactic => `(tactic|
  trustIrCompilerProof {
    first
      | assumption
      | exact empty_aggregate_minted
      | exact nil_minted
      | exact nil_fields_minted
      | (apply cons_fields_minted <;> assumption)
      | (solve | exact record_lanes_minted 0 _ _ (by assumption))
      | (solve | exact enum_lanes_minted 0 _ _ _ (by assumption))
      | (solve | exact array_from_lanes_minted 0 _ (by assumption))
      | (solve | exact array_uniform_minted 0 _ _ (by assumption))
      | exact bytes_array_minted _
      | (apply cons_minted <;> first | assumption | simp [mintedValue_iff_shape,ValueIdentityShape])
      | exact null_fat_minted _ _
      | exact integer_constant_minted _ _ _
      | (solve | apply (mintedValue_iff_shape _ _).2; assumption)
      | (solve | simp [mintedValue_iff_shape,ValueIdentityShape,Value.intAt])
  } {
    first
      | assumption
      | exact empty_aggregate_minted
      | exact nil_minted
      | exact nil_fields_minted
      | (apply cons_fields_minted <;> assumption)
      | (solve | exact record_lanes_minted 0 _ _ (by assumption))
      | (solve | exact enum_lanes_minted 0 _ _ _ (by assumption))
      | (solve | exact array_from_lanes_minted 0 _ (by assumption))
      | (solve | exact array_uniform_minted 0 _ _ (by assumption))
      | exact bytes_array_minted _
      | (solve | apply cons_minted <;> first | assumption | (solve | repeat' (rw [mintedValue_iff_shape]; simp only [ValueIdentityShape])))
      | exact null_fat_minted _ _
      | exact integer_constant_minted _ _ _
      | (solve | apply (mintedValue_iff_shape _ _).2; assumption)
      | (solve | (repeat' (rw [mintedValue_iff_shape]; simp only [ValueIdentityShape,Value.intAt])))
  })

open Lean Elab Tactic in
elab "constant_child " success:ident : tactic => withMainContext do
  let proof ← getFVarId success
  let type ← Lean.Meta.inferType (.fvar proof)
  let type ← Lean.instantiateMVars type
  let args := type.getAppArgs
  if args.size < 2 then throwError "expected equality"
  let action := args[args.size - 2]!
  if action.getAppFn.constName? == some ``MonadExceptOf.throw || action.getAppFn.constName? == some ``throw ||
      action.getAppFn.constName? == some ``Pure.pure || action.getAppFn.constName? == some ``Except.error then
    evalTactic (← `(tactic| cases $success:ident))
    return
  let (name,arity) ← match action.getAppFn.constName? with
    | some `TrustIr.constValueAtChecked => pure (`TrustIr.FrameLifetime.checked_constant_minted,4)
    | some `TrustIr.constFieldsAtChecked => pure (`TrustIr.FrameLifetime.checked_fields_minted,4)
    | some `TrustIr.constLanesAtChecked => pure (`TrustIr.FrameLifetime.checked_lanes_minted,3)
    | some `TrustIr.constValueAtWithDefsIn => pure (`TrustIr.FrameLifetime.context_constant_minted,4)
    | some `TrustIr.constUninitFieldsAtWithDefsIn => pure (`TrustIr.FrameLifetime.context_uninit_fields_minted,4)
    | some `TrustIr.constFieldsAtWithDefsIn => pure (`TrustIr.FrameLifetime.context_fields_minted,3)
    | some `TrustIr.constLanesAtWithDefsIn => pure (`TrustIr.FrameLifetime.context_lanes_minted,3)
    | some `TrustIr.constRecordFieldsAtWithDefsIn => pure (`TrustIr.FrameLifetime.context_record_fields_minted,3)
    | _ => throwError "not a recursive constant result"
  let theoremName := mkIdent name
  if arity == 4 then
    evalTactic (← `(tactic| have minted := $theoremName _ _ _ _ _ $success))
  else evalTactic (← `(tactic| have minted := $theoremName _ _ _ _ $success))

open Lean Elab Tactic in
elab "constant_success_step " run:ident : tactic => withMainContext do
  let proof ← getFVarId run
  let type ← Meta.inferType (.fvar proof)
  let type ← Lean.instantiateMVars type
  let args := type.getAppArgs
  if args.size < 2 then throwError "expected equality"
  let action := args[args.size - 2]!
  let reduced := match action with
    | .letE _ _ value body _ => body.instantiate1 value
    | _ => action.headBeta
  if reduced != action then
    let changed := mkAppN type.getAppFn (args.set! (args.size - 2) reduced)
    let goal ← (← getMainGoal).replaceLocalDeclDefEq proof changed
    replaceMainGoal [goal]
    return
  let location ← `(Lean.Parser.Tactic.locationHyp| $run:ident)
  match action.getAppFn.constName? with
  | some ``Pure.pure | some ``Except.ok =>
      evalTactic (← `(tactic| (simp only [exceptSem_pure,Except.ok.injEq] at $location; subst_vars; constant_value_leaf)))
  | some ``MonadExceptOf.throw | some ``throw | some ``throwThe | some ``Except.error =>
      evalTactic (← `(tactic| cases $run:ident))
  | some ``constValueAtChecked =>
      let theoremName := mkIdent `TrustIr.FrameLifetime.checked_constant_minted
      evalTactic (← `(tactic| exact $theoremName _ _ _ _ _ $run))
  | some ``constMissingDefinition => evalTactic (← `(tactic| unfold constMissingDefinition at $location))
  | some ``Bind.bind | some ``Except.bind =>
      evalTactic (← `(tactic| (obtain ⟨value, firstRun, $run⟩ := bind_success _ _ _ $run; try constant_child firstRun)))
  | _ =>
      if action.isLet || action.getAppFn.isLambda then
        evalTactic (← `(tactic| dsimp only at $location))
      else evalTactic (← `(tactic| split at $location))

local macro "constant_success " run:ident : tactic => `(tactic| repeat' first | contradiction | constant_success_step $run)

set_option maxHeartbeats 2000000 in
mutual

theorem checked_constant_minted (ty : Ty) (constant : Constant) (model : ByteModel) (allow : Bool)
    (result : Value) (run : constValueAtChecked ty constant model allow = .ok result) : MintedValue 0 result := by
  rw [constValueAtChecked_eq] at run
  by_cases rejected : (!constPointerFormsSupported ty constant) = true
  · rw [if_pos rejected] at run; cases run
  · rw [if_neg rejected,pure_bind] at run
    clear rejected
    constant_success run
termination_by sizeOf constant
decreasing_by
  trustIrCompilerProof {
    all_goals (prune_constant_recursion; subst_vars; simp_wf; (try simp_all only); (try omega))
  } {
    all_goals (prune_constant_recursion; subst_vars <;> simp_wf <;> omega)
  }


theorem checked_fields_minted (types : List Ty) (constants : List Constant) (model : ByteModel) (allow : Bool)
    (result : List Value) (run : constFieldsAtChecked types constants model allow = .ok result) : MintedArgs 0 result := by
  rw [constFieldsAtChecked_eq] at run
  constant_success run
termination_by sizeOf constants
decreasing_by
  trustIrCompilerProof {
    all_goals (prune_constant_recursion; subst_vars; simp_wf; (try simp_all only); (try omega))
  } {
    all_goals (prune_constant_recursion; subst_vars <;> simp_wf <;> omega)
  }


theorem checked_lanes_minted (ty : Ty) (constants : List Constant) (model : ByteModel)
    (result : List Value) (run : constLanesAtChecked ty constants model = .ok result) : MintedArgs 0 result := by
  rw [constLanesAtChecked_eq] at run
  constant_success run
termination_by sizeOf constants
decreasing_by
  trustIrCompilerProof {
    all_goals (prune_constant_recursion; subst_vars; simp_wf; (try simp_all only); (try omega))
  } {
    all_goals (prune_constant_recursion; subst_vars <;> simp_wf <;> omega)
  }


end
set_option maxHeartbeats 2000000 in
mutual

theorem context_constant_minted (ctx : ConstantEvalContext) (ty : Ty) (constant : Constant) (allow : Bool)
    (result : Value) (run : constValueAtWithDefsIn ctx ty constant allow = .ok result) : MintedValue 0 result := by
  rw [constValueAtWithDefsIn_eq ctx ty constant allow] at run
  by_cases rejected : (!constPointerFormsSupported ty constant) = true
  · rw [if_pos rejected] at run; cases run
  · rw [if_neg rejected,pure_bind] at run
    clear rejected
    constant_success run
termination_by sizeOf constant
decreasing_by
  trustIrCompilerProof {
    all_goals (prune_constant_recursion; subst_vars; simp_wf; (try simp_all only); (try omega))
  } {
    all_goals (prune_constant_recursion; subst_vars <;> simp_wf <;> omega)
  }


theorem context_uninit_fields_minted (ctx : ConstantEvalContext) (types : List Ty) (constants : List Constant) (allow : Bool)
    (result : List Value) (run : constUninitFieldsAtWithDefsIn ctx types constants allow = .ok result) : MintedArgs 0 result := by
  rw [constUninitFieldsAtWithDefsIn_eq] at run
  constant_success run
termination_by sizeOf constants
decreasing_by
  trustIrCompilerProof {
    all_goals (prune_constant_recursion; subst_vars; simp_wf; (try simp_all only); (try omega))
  } {
    all_goals (prune_constant_recursion; subst_vars <;> simp_wf <;> omega)
  }


theorem context_fields_minted (ctx : ConstantEvalContext) (types : List Ty) (constants : List Constant)
    (result : List Value) (run : constFieldsAtWithDefsIn ctx types constants = .ok result) : MintedArgs 0 result := by
  rw [constFieldsAtWithDefsIn_eq] at run
  constant_success run
termination_by sizeOf constants
decreasing_by
  trustIrCompilerProof {
    all_goals (prune_constant_recursion; subst_vars; simp_wf; (try simp_all only); (try omega))
  } {
    all_goals (prune_constant_recursion; subst_vars <;> simp_wf <;> omega)
  }


theorem context_lanes_minted (ctx : ConstantEvalContext) (ty : Ty) (constants : List Constant)
    (result : List Value) (run : constLanesAtWithDefsIn ctx ty constants = .ok result) : MintedArgs 0 result := by
  rw [constLanesAtWithDefsIn_eq] at run
  constant_success run
termination_by sizeOf constants
decreasing_by
  trustIrCompilerProof {
    all_goals (prune_constant_recursion; subst_vars; simp_wf; (try simp_all only); (try omega))
  } {
    all_goals (prune_constant_recursion; subst_vars <;> simp_wf <;> omega)
  }


theorem context_record_fields_minted (ctx : ConstantEvalContext) (declared : List FieldDef) (fields : List (String × Constant))
    (result : List (String × Value)) (run : constRecordFieldsAtWithDefsIn ctx declared fields = .ok result) : MintedConstantFields result := by
  rw [constRecordFieldsAtWithDefsIn_eq] at run
  constant_success run
termination_by sizeOf fields
decreasing_by
  trustIrCompilerProof {
    all_goals (prune_constant_recursion; subst_vars; simp_wf; (try simp_all only); (try omega))
  } {
    all_goals (prune_constant_recursion; subst_vars <;> simp_wf <;> omega)
  }


end
end TrustIr.FrameLifetime
