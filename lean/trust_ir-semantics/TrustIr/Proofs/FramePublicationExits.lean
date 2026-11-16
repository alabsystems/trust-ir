-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameContextSafety
import TrustIr.Proofs.FrameDecodeFreedom

namespace TrustIr.FrameLifetime

private theorem except_ok_no_unwind {α : Type} (value : α) : ExceptNoUnwind (.ok value) := by
  intro exception after run
  cases run

private theorem except_type_no_unwind {α : Type} (message : String) : ExceptNoUnwind (.error (.typeError message) : Except SemError α) := by
  intro exception after run
  cases run

private theorem except_ub_no_unwind {α : Type} (message : String) : ExceptNoUnwind (.error (.ub message) : Except SemError α) := by
  intro exception after run
  cases run

private theorem except_unsupported_no_unwind {α : Type} (feature : UnsupportedFeature) (message : String) :
    ExceptNoUnwind (.error (.unsupported feature message) : Except SemError α) := by
  intro exception after run
  cases run

theorem ExceptNoUnwind.bind {α β : Type} (action : Except SemError α) (next : α → Except SemError β)
    (first : ExceptNoUnwind action) (rest : ∀ value, ExceptNoUnwind (next value)) : ExceptNoUnwind (action >>= next) := by
  intro exception after run
  cases action with
  | error error =>
    change Except.error error = Except.error (SemError.unwinding exception after) at run
    cases run
    exact first exception after rfl
  | ok value => exact rest value exception after run

theorem ExceptNoUnwind.mapM {α β : Type} (items : List α) (action : α → Except SemError β)
    (safe : ∀ item, ExceptNoUnwind (action item)) : ExceptNoUnwind (items.mapM action) := by
  induction items with
  | nil => exact except_ok_no_unwind _
  | cons item rest ih =>
    rw [List.mapM_cons]
    exact ExceptNoUnwind.bind _ _ (safe item) (fun _ => ExceptNoUnwind.bind _ _ ih (fun _ => except_ok_no_unwind _))

-- Shared finite-validation composition belongs below the ordinary control
-- exit proofs; closure and nominal-item validation use the same checked laws.
private theorem ok_safe {α : Type} (value : α) : ExceptNoUnwind (.ok value) :=
  except_ok_no_unwind value

theorem ExceptNoUnwind.forIn {α β : Type} (items : List α) (initial : β)
    (action : α → β → Except SemError (ForInStep β))
    (safe : ∀ item value, ExceptNoUnwind (action item value)) :
    ExceptNoUnwind (forIn items initial action) := by
  induction items generalizing initial with
  | nil => exact ok_safe _
  | cons item rest ih =>
    rw [List.forIn_cons]
    apply ExceptNoUnwind.bind _ _ (safe item initial)
    intro step
    cases step with
    | done value => exact ok_safe _
    | yield value => exact ih value

theorem ExceptNoUnwind.forM {α : Type} (items : List α) (action : α → Except SemError Unit)
    (safe : ∀ item, ExceptNoUnwind (action item)) : ExceptNoUnwind (items.forM action) := by
  induction items with
  | nil => exact ok_safe _
  | cons item rest ih =>
    change ExceptNoUnwind (action item >>= fun _ => rest.forM action)
    exact ExceptNoUnwind.bind _ _ (safe item) (fun _ => ih)

private theorem leaf_range_no_unwind {α : Type} (check : α → Except SemError Unit)
    (safe : ∀ value, ExceptNoUnwind (check value)) {size : Nat} (leaf : CompactArray.Leaf α size)
    (offset count : Nat) : ExceptNoUnwind (leaf.checkRangeSpec check offset count) := by
  induction leaf generalizing offset count with
  | nil => simp only [CompactArray.Leaf.checkRangeSpec]; split <;> exact ok_safe _
  | cons head tail ih =>
    rw [CompactArray.Leaf.checkRangeSpec]
    split
    · exact ok_safe _
    · split
      · exact ExceptNoUnwind.bind _ _ (safe head) (fun _ => ih 0 (count-1))
      · exact ih (offset-1) count

/-- Pure compressed-array validation propagates only callback errors, including
clipped periodic windows; it cannot invent a runtime throw state. -/
theorem tree_range_no_unwind {α : Type} (check : α → Except SemError Unit)
    (safe : ∀ value, ExceptNoUnwind (check value)) {size : Nat} (tree : CompactArray.Tree α size)
    (offset count : Nat) : ExceptNoUnwind (tree.checkRangeSpec check offset count) := by
  induction tree generalizing offset count with
  | uniform n value =>
    rw [CompactArray.Tree.checkRangeSpec]
    split
    · exact ok_safe _
    · exact safe value
  | dense small values =>
    rw [CompactArray.Tree.checkRangeSpec]
    split
    · exact ok_safe _
    · exact leaf_range_no_unwind check safe values _ _
  | split large left right ihl ihr =>
    rw [CompactArray.Tree.checkRangeSpec]
    split
    · exact ok_safe _
    · exact ExceptNoUnwind.bind _ _ (ihl _ _) (fun _ => ihr _ _)
  | periodic unit positive phase n ih =>
    rw [CompactArray.Tree.checkRangeSpec]
    split
    · exact ok_safe _
    · exact ExceptNoUnwind.bind _ _ (ih _ _) (fun _ => ih _ _)

theorem tree_stored_no_unwind {α : Type} (check : α → Except SemError Unit)
    (safe : ∀ value, ExceptNoUnwind (check value)) {size : Nat} (tree : CompactArray.Tree α size) :
    ExceptNoUnwind (tree.checkStored check) := by
  rw [← tree.checkRangeSpec_full]
  exact tree_range_no_unwind check safe tree 0 size

theorem char_value_no_unwind (ty : Ty) (value : Value) : ExceptNoUnwind (checkSSACharValue ty value) := by
  unfold checkSSACharValue
  repeat' first
    | exact except_ok_no_unwind _
    | exact except_ub_no_unwind _
    | (rw [HistoryEffects.conditional_property_iff ExceptNoUnwind]; constructor <;> intro selected)
    | split

theorem char_values_no_unwind (types : List Ty) (values : List Value) : ExceptNoUnwind (checkSSACharValues types values) := by
  induction types generalizing values with
  | nil => cases values <;> first | exact except_ok_no_unwind _ | exact except_type_no_unwind _
  | cons ty types ih =>
    cases values with
    | nil => exact except_type_no_unwind _
    | cons value values =>
      exact ExceptNoUnwind.bind _ _ (char_value_no_unwind ty value) (fun _ => ih values)

theorem result_source_type_no_unwind (original : Option LocalTypeTable) (source : LocalTypeSource) :
    ExceptNoUnwind (ssaResultSourceType original source) := by
  unfold ssaResultSourceType
  repeat' first
    | exact except_ok_no_unwind _
    | exact except_type_no_unwind _
    | exact except_unsupported_no_unwind _ _
    | split

local macro "pure_validation_leaves" : tactic => `(tactic|
  repeat' first
    | exact except_ok_no_unwind _
    | exact except_type_no_unwind _
    | exact except_unsupported_no_unwind _ _
    | exact result_source_type_no_unwind _ _
    | (refine ExceptNoUnwind.mapM _ _ (fun value => ?_))
    | (rw [HistoryEffects.conditional_property_iff ExceptNoUnwind]; constructor <;> intro selected)
    | (refine ExceptNoUnwind.bind _ _ ?_ (fun value => ?_) <;> dsimp only)
    | split)

/-- Original declaration association and header-derived classifications retain
all conflicts and absent-metadata refusals without creating unwind states. -/
theorem instruction_types_no_unwind (original : Option LocalTypeTable)
    (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (inst : Inst) (dests : List ValueId) (produced : Nat) :
    ExceptNoUnwind (ssaInstructionResultTypes original direct indirect inst dests produced) := by
  unfold ssaInstructionResultTypes
  pure_validation_leaves

theorem lift_validation_no_unwind {α : Type} (result : Except SemError α) (safe : ExceptNoUnwind result) :
    CallCheckNoUnwind (Sem.fromMemoryExcept result) := by
  intro state exception after run
  cases result with
  | ok value => cases run
  | error error =>
    cases run
    exact safe exception after rfl

/-- Original item lookup can refuse only with a static type diagnostic. -/
theorem function_item_declaration_no_unwind (ctx : EvalContext) (target : FuncId) :
    ExceptNoUnwind (functionItemDeclaration ctx target) := by
  intro exception after failed
  obtain ⟨message, impossible⟩ :=
    functionItemDeclaration_error_is_typeError ctx target (.unwinding exception after) failed
  cases impossible

theorem function_item_callee_type_no_unwind (ctx : EvalContext) (operand : ValueId) (value : Value) :
    ExceptNoUnwind (checkFunctionItemCalleeType ctx operand value) := by
  unfold checkFunctionItemCalleeType
  repeat' first
    | exact except_ok_no_unwind _
    | exact except_type_no_unwind _
    | split

/-- Nominal call-header validation is static and retains all original
signature, calling-convention and ABI refusals. -/
theorem function_item_call_no_unwind (ctx : EvalContext) (target : FuncId)
    (signature : FuncTyId) (convention : CallingConv) :
    ExceptNoUnwind (functionItemCall ctx target signature convention) := by
  unfold functionItemCall
  repeat' first
    | exact except_ok_no_unwind _
    | exact except_type_no_unwind _
    | exact except_unsupported_no_unwind _ _
    | exact function_item_declaration_no_unwind _ _
    | (refine ExceptNoUnwind.bind _ _ ?_ (fun input => ?_) <;> dsimp only)
    | split

/-- Lazy body resolution obeys the original static body-error contract. -/
theorem function_item_body_no_unwind (ctx : EvalContext) (safe : StaticFunctionErrors ctx)
    (target : FuncId) : ExceptNoUnwind (resolveFunctionItemBody ctx target) := by
  intro exception after failed
  unfold resolveFunctionItemBody at failed
  repeat' first
    | (solve | cases failed)
    | (solve | cases failed; exact safe.no_unwind ctx target _ _ (by assumption))
    | split at failed

/-- Frame origin authentication reads complete finite declarations and cannot
manufacture a dynamic unwind world. -/
theorem binding_frame_types_no_unwind (ctx : EvalContext) (value : Value) :
    ExceptNoUnwind (bindingFrameTypes ctx value) := by
  unfold bindingFrameTypes
  repeat' first
    | exact except_ok_no_unwind _
    | exact except_type_no_unwind _
    | (refine ExceptNoUnwind.bind _ _ ?_ (fun input => ?_) <;> dsimp only)
    | split

private theorem function_item_fields_no_unwind
    (recurse : Ty → Value → Except SemError Unit)
    (safe : ∀ ty value, ExceptNoUnwind (recurse ty value))
    (relevant : Bool) (types : List Ty) (values : List Value) :
    ExceptNoUnwind (do
      if relevant && types.length != values.length then
        throw (.typeError "FnItem: container field census differs from its declaration")
      ((types ++ List.replicate values.length Ty.Error).zip values).forM
        (fun (ty, value) => recurse ty value)) := by
  split
  · intro exception after impossible
    cases impossible
  · try simp only [pure_bind]
    exact ExceptNoUnwind.forM _ _ (fun pair => safe pair.1 pair.2)

private theorem function_item_record_fields_no_unwind (ctx : EvalContext)
    (recurse : Ty → Value → Except SemError Unit)
    (safe : ∀ ty value, ExceptNoUnwind (recurse ty value))
    (relevant : Bool) (id : RecordId) (values : List (String × Value)) :
    ExceptNoUnwind (values.forM fun (name, value) => do
      let field := (ctx.records id).bind (fun definition => definition.fields.find? (fun field => field.name == name))
      if relevant && field.isNone then
        throw (.typeError "FnItem: record field is not declared")
      recurse ((field.map (·.ty)).getD .Error) value) := by
  apply ExceptNoUnwind.forM
  intro pair
  rcases pair with ⟨name, value⟩
  dsimp only
  split
  · intro exception after impossible
    cases impossible
  · try simp only [pure_bind]
    exact safe _ value

-- Constructor-specific laws stage the real checker decision tree. Each
-- declaration retains the original default heartbeat and recursion budgets.
local macro "item_leaf_safety" : tactic => `(tactic|
  repeat' first
    | exact except_ok_no_unwind _
    | exact except_type_no_unwind _
    | exact function_item_declaration_no_unwind _ _
    | (refine ExceptNoUnwind.bind _ _ ?_ (fun input => ?_) <;> dsimp only)
    | split)

local macro "item_container_safety" c:ident rec:ident saf:ident : tactic => `(tactic|
  repeat' first
    | exact except_ok_no_unwind _
    | exact except_type_no_unwind _
    | exact function_item_declaration_no_unwind _ _
    | exact binding_frame_types_no_unwind _ _
    | exact $saf _ _
    | exact function_item_fields_no_unwind $rec $saf _ _ _
    | exact function_item_record_fields_no_unwind $c $rec $saf _ _ _
    | exact ExceptNoUnwind.forM _ _ (fun pair => $saf pair.1 pair.2)
    | exact ExceptNoUnwind.forM _ _ (fun pair => $saf _ pair.2)
    | exact ExceptNoUnwind.forM _ _ ($saf _)
    | (refine tree_stored_no_unwind _ (fun value => ?_) _)
    | (refine ExceptNoUnwind.bind _ _ ?_ (fun input => ?_) <;> dsimp only)
    | split)

set_option smartUnfolding false in
private theorem item_int_layer_no_unwind (ctx : EvalContext)
    (recurse : Ty → Value → Except SemError Unit) (ty : Ty) (width : Nat) (raw : Int) :
    ExceptNoUnwind (checkFunctionItemLayer ctx recurse ty (.int width raw)) := by
  by_cases relevant : ctx.valueSource.hasFnItem ty = true
  all_goals cases ty <;>
    simp only [checkFunctionItemLayer, Value.isUninit, relevant, pure_bind, ↓reduceIte]
  all_goals item_leaf_safety

set_option smartUnfolding false in
private theorem item_float_layer_no_unwind (ctx : EvalContext)
    (recurse : Ty → Value → Except SemError Unit) (ty : Ty) (number : Float) :
    ExceptNoUnwind (checkFunctionItemLayer ctx recurse ty (.float number)) := by
  by_cases relevant : ctx.valueSource.hasFnItem ty = true
  all_goals cases ty <;>
    simp only [checkFunctionItemLayer, Value.isUninit, relevant, pure_bind, ↓reduceIte]
  all_goals item_leaf_safety

set_option smartUnfolding false in
private theorem item_bool_layer_no_unwind (ctx : EvalContext)
    (recurse : Ty → Value → Except SemError Unit) (ty : Ty) (bit : Bool) :
    ExceptNoUnwind (checkFunctionItemLayer ctx recurse ty (.bool bit)) := by
  by_cases relevant : ctx.valueSource.hasFnItem ty = true
  all_goals cases ty <;>
    simp only [checkFunctionItemLayer, Value.isUninit, relevant, pure_bind, ↓reduceIte]
  all_goals item_leaf_safety

set_option smartUnfolding false in
private theorem item_ptr_layer_no_unwind (ctx : EvalContext)
    (recurse : Ty → Value → Except SemError Unit) (ty : Ty) (address : Nat) (provenance : Option AllocId) :
    ExceptNoUnwind (checkFunctionItemLayer ctx recurse ty (.ptr address provenance)) := by
  by_cases relevant : ctx.valueSource.hasFnItem ty = true
  all_goals cases ty <;>
    simp only [checkFunctionItemLayer, Value.isUninit, relevant, pure_bind, ↓reduceIte]
  all_goals item_leaf_safety

set_option smartUnfolding false in
private theorem item_array_layer_no_unwind (ctx : EvalContext)
    (recurse : Ty → Value → Except SemError Unit)
    (safe : ∀ ty value, ExceptNoUnwind (recurse ty value)) (ty : Ty) (values : CompactArray.Packed Value) :
    ExceptNoUnwind (checkFunctionItemLayer ctx recurse ty (.array values)) := by
  by_cases relevant : ctx.valueSource.hasFnItem ty = true
  all_goals cases ty <;>
    simp only [checkFunctionItemLayer, Value.isUninit, relevant, pure_bind, ↓reduceIte]
  all_goals item_container_safety ctx recurse safe

set_option smartUnfolding false in
private theorem item_aggregate_layer_no_unwind (ctx : EvalContext)
    (recurse : Ty → Value → Except SemError Unit)
    (safe : ∀ ty value, ExceptNoUnwind (recurse ty value)) (ty : Ty) (values : List Value) :
    ExceptNoUnwind (checkFunctionItemLayer ctx recurse ty (.aggregate values)) := by
  by_cases relevant : ctx.valueSource.hasFnItem ty = true
  all_goals cases ty <;>
    simp only [checkFunctionItemLayer, Value.isUninit, relevant, pure_bind, ↓reduceIte]
  all_goals item_container_safety ctx recurse safe

set_option smartUnfolding false in
private theorem item_vector_layer_no_unwind (ctx : EvalContext)
    (recurse : Ty → Value → Except SemError Unit)
    (safe : ∀ ty value, ExceptNoUnwind (recurse ty value)) (ty : Ty) (values : List Value) :
    ExceptNoUnwind (checkFunctionItemLayer ctx recurse ty (.vector values)) := by
  by_cases relevant : ctx.valueSource.hasFnItem ty = true
  all_goals cases ty <;>
    simp only [checkFunctionItemLayer, Value.isUninit, relevant, pure_bind, ↓reduceIte]
  all_goals item_container_safety ctx recurse safe

set_option smartUnfolding false in
private theorem item_frame_layer_no_unwind (ctx : EvalContext)
    (recurse : Ty → Value → Except SemError Unit)
    (safe : ∀ ty value, ExceptNoUnwind (recurse ty value)) (ty : Ty) (lineage : Nat) (values : List Value) :
    ExceptNoUnwind (checkFunctionItemLayer ctx recurse ty (.frame lineage values)) := by
  by_cases relevant : ctx.valueSource.hasFnItem ty = true
  all_goals cases ty <;>
    simp only [checkFunctionItemLayer, Value.isUninit, relevant, pure_bind, ↓reduceIte]
  all_goals item_container_safety ctx recurse safe

set_option smartUnfolding false in
private theorem item_set_layer_no_unwind (ctx : EvalContext)
    (recurse : Ty → Value → Except SemError Unit)
    (safe : ∀ ty value, ExceptNoUnwind (recurse ty value)) (ty : Ty) (values : List Value) :
    ExceptNoUnwind (checkFunctionItemLayer ctx recurse ty (.set values)) := by
  by_cases relevant : ctx.valueSource.hasFnItem ty = true
  all_goals cases ty <;>
    simp only [checkFunctionItemLayer, Value.isUninit, relevant, pure_bind, ↓reduceIte]
  all_goals item_container_safety ctx recurse safe

set_option smartUnfolding false in
private theorem item_sequence_layer_no_unwind (ctx : EvalContext)
    (recurse : Ty → Value → Except SemError Unit)
    (safe : ∀ ty value, ExceptNoUnwind (recurse ty value)) (ty : Ty) (values : List Value) :
    ExceptNoUnwind (checkFunctionItemLayer ctx recurse ty (.sequence values)) := by
  by_cases relevant : ctx.valueSource.hasFnItem ty = true
  all_goals cases ty <;>
    simp only [checkFunctionItemLayer, Value.isUninit, relevant, pure_bind, ↓reduceIte]
  all_goals item_container_safety ctx recurse safe

set_option smartUnfolding false in
private theorem item_record_layer_no_unwind (ctx : EvalContext)
    (recurse : Ty → Value → Except SemError Unit)
    (safe : ∀ ty value, ExceptNoUnwind (recurse ty value)) (ty : Ty) (values : List (String × Value)) :
    ExceptNoUnwind (checkFunctionItemLayer ctx recurse ty (.record values)) := by
  by_cases relevant : ctx.valueSource.hasFnItem ty = true
  all_goals cases ty <;>
    simp only [checkFunctionItemLayer, Value.isUninit, relevant, pure_bind, ↓reduceIte]
  all_goals item_container_safety ctx recurse safe

set_option smartUnfolding false in
private theorem item_closure_layer_no_unwind (ctx : EvalContext)
    (recurse : Ty → Value → Except SemError Unit)
    (safe : ∀ ty value, ExceptNoUnwind (recurse ty value)) (ty : Ty) (function : FuncId) (captures : List Value) :
    ExceptNoUnwind (checkFunctionItemLayer ctx recurse ty (.closure function captures)) := by
  by_cases relevant : ctx.valueSource.hasFnItem ty = true
  all_goals cases ty <;>
    simp only [checkFunctionItemLayer, Value.isUninit, relevant, pure_bind, ↓reduceIte]
  all_goals item_container_safety ctx recurse safe

set_option smartUnfolding false in
private theorem item_fnDef_layer_no_unwind (ctx : EvalContext)
    (recurse : Ty → Value → Except SemError Unit) (ty : Ty) (signature : FuncTyId) (function : FuncId) :
    ExceptNoUnwind (checkFunctionItemLayer ctx recurse ty (.fnDef signature function)) := by
  by_cases relevant : ctx.valueSource.hasFnItem ty = true
  all_goals cases ty <;>
    simp only [checkFunctionItemLayer, Value.isUninit, relevant, pure_bind, ↓reduceIte]
  all_goals item_leaf_safety

set_option smartUnfolding false in
private theorem item_typedClosure_layer_no_unwind (ctx : EvalContext)
    (recurse : Ty → Value → Except SemError Unit)
    (safe : ∀ ty value, ExceptNoUnwind (recurse ty value)) (ty : Ty) (identity : ClosureTyId) (function : FuncId) (captures : List Value) :
    ExceptNoUnwind (checkFunctionItemLayer ctx recurse ty (.typedClosure identity function captures)) := by
  by_cases relevant : ctx.valueSource.hasFnItem ty = true
  all_goals cases ty <;>
    simp only [checkFunctionItemLayer, Value.isUninit, relevant, pure_bind, ↓reduceIte]
  all_goals item_container_safety ctx recurse safe

set_option smartUnfolding false in
private theorem item_fatPtr_layer_no_unwind (ctx : EvalContext)
    (recurse : Ty → Value → Except SemError Unit)
    (safe : ∀ ty value, ExceptNoUnwind (recurse ty value)) (ty : Ty) (address : Nat) (provenance : Option AllocId) (metadata : Value) :
    ExceptNoUnwind (checkFunctionItemLayer ctx recurse ty (.fatPtr address provenance metadata)) := by
  by_cases relevant : ctx.valueSource.hasFnItem ty = true
  all_goals cases ty <;>
    simp only [checkFunctionItemLayer, Value.isUninit, relevant, pure_bind, ↓reduceIte]
  all_goals item_container_safety ctx recurse safe

set_option smartUnfolding false in
private theorem item_partial_layer_no_unwind (ctx : EvalContext)
    (recurse : Ty → Value → Except SemError Unit) (ty : Ty) (image : List (Option UInt8)) :
    ExceptNoUnwind (checkFunctionItemLayer ctx recurse ty (.«partial» image)) := by
  by_cases relevant : ctx.valueSource.hasFnItem ty = true
  all_goals cases ty <;>
    simp only [checkFunctionItemLayer, Value.isUninit, relevant, pure_bind, ↓reduceIte]
  all_goals item_leaf_safety

set_option smartUnfolding false in
private theorem item_undef_layer_no_unwind (ctx : EvalContext)
    (recurse : Ty → Value → Except SemError Unit) (ty : Ty) (declared : Ty) :
    ExceptNoUnwind (checkFunctionItemLayer ctx recurse ty (.undef declared)) := by
  by_cases relevant : ctx.valueSource.hasFnItem ty = true
  all_goals cases ty <;>
    simp only [checkFunctionItemLayer, Value.isUninit, relevant, pure_bind, ↓reduceIte]
  all_goals item_leaf_safety

set_option smartUnfolding false in
private theorem item_nullPtr_layer_no_unwind (ctx : EvalContext)
    (recurse : Ty → Value → Except SemError Unit) (ty : Ty) :
    ExceptNoUnwind (checkFunctionItemLayer ctx recurse ty (.nullPtr)) := by
  by_cases relevant : ctx.valueSource.hasFnItem ty = true
  all_goals cases ty <;>
    simp only [checkFunctionItemLayer, Value.isUninit, relevant, pure_bind, ↓reduceIte]
  all_goals item_leaf_safety

set_option smartUnfolding false in
private theorem item_uninit_layer_no_unwind (ctx : EvalContext)
    (recurse : Ty → Value → Except SemError Unit) (ty : Ty) :
    ExceptNoUnwind (checkFunctionItemLayer ctx recurse ty (.uninit)) := by
  intro exception after impossible
  cases impossible

set_option smartUnfolding false in
private theorem item_fnItem_layer_no_unwind (ctx : EvalContext)
    (recurse : Ty → Value → Except SemError Unit) (ty : Ty) (target : FuncId) :
    ExceptNoUnwind (checkFunctionItemLayer ctx recurse ty (.fnItem target)) := by
  by_cases relevant : ctx.valueSource.hasFnItem ty = true
  all_goals cases ty <;>
    simp only [checkFunctionItemLayer, Value.isUninit, relevant, pure_bind, ↓reduceIte]
  all_goals item_leaf_safety

set_option smartUnfolding false in
private theorem item_sourceFrame_layer_no_unwind (ctx : EvalContext)
    (recurse : Ty → Value → Except SemError Unit)
    (safe : ∀ ty value, ExceptNoUnwind (recurse ty value)) (ty : Ty) (lineage : Nat) (function : FuncId) (declaration : BindingFrameDef) (values : List Value) :
    ExceptNoUnwind (checkFunctionItemLayer ctx recurse ty (.sourceFrame lineage function declaration values)) := by
  by_cases relevant : ctx.valueSource.hasFnItem ty = true
  all_goals cases ty <;>
    simp only [checkFunctionItemLayer, Value.isUninit, relevant, pure_bind, ↓reduceIte]
  all_goals item_container_safety ctx recurse safe

/-- Each real structural check layer propagates only static callback errors. -/
theorem function_item_layer_no_unwind (ctx : EvalContext)
    (recurse : Ty → Value → Except SemError Unit)
    (safe : ∀ ty value, ExceptNoUnwind (recurse ty value)) (ty : Ty) (value : Value) :
    ExceptNoUnwind (checkFunctionItemLayer ctx recurse ty value) := by
  cases value with
  | int width raw => exact item_int_layer_no_unwind ctx recurse ty width raw
  | float number => exact item_float_layer_no_unwind ctx recurse ty number
  | bool bit => exact item_bool_layer_no_unwind ctx recurse ty bit
  | ptr address provenance => exact item_ptr_layer_no_unwind ctx recurse ty address provenance
  | array values => exact item_array_layer_no_unwind ctx recurse safe ty values
  | aggregate values => exact item_aggregate_layer_no_unwind ctx recurse safe ty values
  | vector values => exact item_vector_layer_no_unwind ctx recurse safe ty values
  | frame lineage values => exact item_frame_layer_no_unwind ctx recurse safe ty lineage values
  | set values => exact item_set_layer_no_unwind ctx recurse safe ty values
  | sequence values => exact item_sequence_layer_no_unwind ctx recurse safe ty values
  | record values => exact item_record_layer_no_unwind ctx recurse safe ty values
  | closure function captures => exact item_closure_layer_no_unwind ctx recurse safe ty function captures
  | fnDef signature function => exact item_fnDef_layer_no_unwind ctx recurse ty signature function
  | typedClosure identity function captures => exact item_typedClosure_layer_no_unwind ctx recurse safe ty identity function captures
  | fatPtr address provenance metadata => exact item_fatPtr_layer_no_unwind ctx recurse safe ty address provenance metadata
  | «partial» image => exact item_partial_layer_no_unwind ctx recurse ty image
  | undef declared => exact item_undef_layer_no_unwind ctx recurse ty declared
  | nullPtr => exact item_nullPtr_layer_no_unwind ctx recurse ty
  | uninit => exact item_uninit_layer_no_unwind ctx recurse ty
  | fnItem target => exact item_fnItem_layer_no_unwind ctx recurse ty target
  | sourceFrame lineage function declaration values => exact item_sourceFrame_layer_no_unwind ctx recurse safe ty lineage function declaration values

theorem function_item_lanes_no_unwind (ctx : EvalContext) (fuel : Nat)
    (ty : Ty) (value : Value) : ExceptNoUnwind (checkFunctionItemLanes ctx fuel ty value) := by
  induction fuel generalizing ty value with
  | zero =>
    unfold checkFunctionItemLanes
    split <;> first | exact except_ok_no_unwind _ | exact except_type_no_unwind _
  | succ fuel ih => exact function_item_layer_no_unwind ctx _ ih ty value

/-- The actual entry/return lane checker cannot inject unwind states, for any
finite source carrier, including malformed headers and duplicate rows. -/
theorem function_item_values_no_unwind (ctx : EvalContext) (types : List Ty) (values : List Value) :
    ExceptNoUnwind (checkFunctionItemValues ctx types values) := by
  unfold checkFunctionItemValues
  apply ExceptNoUnwind.forM
  intro pair
  exact function_item_lanes_no_unwind ctx (pair.2.depth + 1) pair.1 pair.2

/-- A lifted finite validation result preserves the original world on success,
and has no embedded dynamic-world outcome when its errors are static. -/
theorem static_check_frame_exit {α : Type} (result : Except SemError α)
    (safe : ExceptNoUnwind result) (post : Nat → α → Prop)
    (state : MachineState) (valid : WellMintedState state)
    (passed : ∀ value, result = .ok value → post state.nextFrameLineage value) :
    FrameActionExit post state (Sem.run (Sem.fromMemoryExcept result) state) := by
  cases result with
  | ok value => exact ⟨valid, passed value rfl, .refl _⟩
  | error error =>
    cases error <;> first
      | exact True.intro
      | exact False.elim (safe _ _ rfl)

/-- Successful item checks preserve incoming recursive identities as well as
state; rejected static metadata does not create a synthetic exception world. -/
theorem function_item_checks_frame_exit (ctx : EvalContext) (types : List Ty) (values : List Value)
    (state : MachineState) (valid : WellMintedState state)
    (incoming : MintedArgs state.nextFrameLineage values) :
    FrameActionExit (fun bound _ => MintedArgs bound values) state
      (Sem.run (Sem.fromMemoryExcept (checkFunctionItemValues ctx types values)) state) :=
  static_check_frame_exit _ (function_item_values_no_unwind ctx types values) _ state valid
    (fun _ _ => incoming)

/-- Original return postchecking retains its refusal behavior and the complete
frame validity/history contract, without assuming that the check succeeds. -/
theorem checked_return_frame_exit (ctx : EvalContext) (values : List Value)
    (state : MachineState) (valid : WellMintedState state)
    (incoming : MintedArgs state.nextFrameLineage values) :
    FrameCalleeExit state (Sem.run (GenericCoro.checkedReturn ctx values) state) := by
  unfold GenericCoro.checkedReturn
  cases returnTypes : ctx.functionReturnTypes with
  | none => exact ⟨valid, incoming, .refl _⟩
  | some types =>
    apply (FrameActionExit.callee state _).1
    apply FrameActionExit.bind (fun bound _ => MintedArgs bound values) MintedArgs _ _ state
      (function_item_checks_frame_exit ctx types values state valid incoming)
    intro unit middle middleValid transported
    exact ⟨middleValid, transported, .refl _⟩

/-- Actual result checks do not use the potentially arbitrary functionErrors
field: source types and top-level Char validation have their own no-unwind laws. -/
theorem result_checks_no_unwind (ctx : EvalContext) (inst : Inst) (dests : List ValueId) (values : List Value) :
    CallCheckNoUnwind (ctx.checkInstructionResults inst dests values) := by
  have typesSafe : ExceptNoUnwind (ctx.instructionResultTypes inst dests values.length) := instruction_types_no_unwind _ _ _ _ _ _
  cases types : ctx.instructionResultTypes inst dests values.length with
  | error error =>
    intro state exception after run
    simp only [EvalContext.checkInstructionResults,types] at run
    change Except.error error = Except.error (SemError.unwinding exception after) at run
    cases run
    exact typesSafe exception after types
  | ok resolved =>
    cases chars : checkSSACharValues resolved values with
    | error error =>
      intro state exception after run
      simp only [EvalContext.checkInstructionResults,types,chars,pure_bind] at run
      cases run
      exact char_values_no_unwind resolved values exception after chars
    | ok unit =>
      cases unit
      intro state exception after run
      simp only [EvalContext.checkInstructionResults,types,chars,pure_bind] at run
      cases run

private theorem pure_no_unwind {α : Type} (value : α) : CallCheckNoUnwind (pure value : Sem α) := by
  intro state exception after run
  cases run

private theorem get_no_unwind : CallCheckNoUnwind Sem.getState := by
  intro state exception after run
  cases run

private theorem set_no_unwind (state : MachineState) : CallCheckNoUnwind (Sem.setState state) := by
  intro before exception after run
  cases run

private theorem type_no_unwind {α : Type} (message : String) : CallCheckNoUnwind (Sem.throwTypeError message : Sem α) := by
  intro state exception after run
  cases run

private theorem lookup_no_unwind (id : ValueId) : CallCheckNoUnwind (Sem.lookupValue id) := by
  unfold Sem.lookupValue
  refine CallCheckNoUnwind.bind _ _ get_no_unwind ?_
  intro state
  split <;> first | exact pure_no_unwind _ | exact type_no_unwind _

local macro "publication_leaves" : tactic => `(tactic|
  first
    | exact pure_no_unwind _
    | exact get_no_unwind
    | exact set_no_unwind _
    | exact type_no_unwind _
    | exact lookup_no_unwind _
    | exact lookup_arguments_no_unwind _
    | exact result_checks_no_unwind _ _ _ _
    | (refine CallCheckNoUnwind.bind _ _ ?_ (fun value => ?_) <;> dsimp only)
    | split)

theorem result_dests_no_unwind (dests : List ValueId) (values : List Value) : CallCheckNoUnwind (bindResultDests dests values) := by
  unfold bindResultDests
  rw [HistoryEffects.conditional_property_iff CallCheckNoUnwind]
  constructor <;> intro selected <;> repeat' publication_leaves

theorem instruction_dests_no_unwind (result : InstrResult) (dests : List ValueId) :
    CallCheckNoUnwind (bindInstrResultDests result dests) := by
  unfold bindInstrResultDests
  repeat' first
    | exact result_dests_no_unwind _ _
    | (rw [HistoryEffects.conditional_property_iff CallCheckNoUnwind]; constructor <;> intro selected)
    | publication_leaves
    | split

theorem call_results_no_unwind (ctx : EvalContext) (inst : Inst) (dests : List ValueId) (values : List Value) :
    CallCheckNoUnwind (ctx.bindCallResults inst dests values) := by
  unfold EvalContext.bindCallResults
  rw [HistoryEffects.conditional_property_iff CallCheckNoUnwind]
  constructor
  · intro selected
    exact result_dests_no_unwind _ _
  · intro selected
    exact CallCheckNoUnwind.bind _ _ (result_checks_no_unwind _ _ _ _) (fun _ => result_dests_no_unwind _ _)

theorem instruction_results_no_unwind (ctx : EvalContext) (inst : Inst) (result : InstrResult) (dests : List ValueId) :
    CallCheckNoUnwind (ctx.bindInstructionResults inst result dests) := by
  unfold EvalContext.bindInstructionResults
  repeat' first
    | exact instruction_dests_no_unwind _ _
    | (rw [HistoryEffects.conditional_property_iff CallCheckNoUnwind]; constructor <;> intro selected)
    | publication_leaves
    | split

private theorem exit_at_no_unwind {α : Type} (post : Nat → α → Prop) (action : Sem α) (state : MachineState)
    (safe : CallCheckNoUnwind action)
    (success : ∀ after value, Sem.run action state = .ok (value,after) →
      WellMintedState after ∧ post after.nextFrameLineage value ∧ HistoryExtends state after) :
    FrameActionExit post state (Sem.run action state) := by
  cases executed : Sem.run action state with
  | ok pair => exact success pair.2 pair.1 executed
  | error error =>
    cases error <;> first | exact True.intro | exact False.elim (safe state _ _ executed)

theorem result_checks_frame_action (ctx : EvalContext) (inst : Inst) (dests : List ValueId) (values : List Value) :
    FrameActionValid (fun _ _ => True) (ctx.checkInstructionResults inst dests values) := by
  apply frame_action_of_success_no_unwind _ _ (result_checks_no_unwind ctx inst dests values)
  intro state after unit valid run
  cases unit
  have same := result_checks_success_state ctx inst dests values state after run
  subst after
  exact ⟨valid,True.intro,.refl _⟩

theorem result_dests_frame_exit (dests : List ValueId) (values : List Value) (state : MachineState)
    (valid : WellMintedState state) (incoming : MintedArgs state.nextFrameLineage values) :
    FrameActionExit (fun _ _ => True) state (Sem.run (bindResultDests dests values) state) := by
  have successful : ∀ after unit,
      Sem.run (bindResultDests dests values) state = .ok (unit,after) →
      WellMintedState after ∧ True ∧ HistoryExtends state after := by
    intro after unit run
    cases unit
    have history := (result_dests_history dests values).extends state after () run
    exact ⟨valid.bind_result_dests_success dests values state after incoming run,True.intro,history⟩
  exact exit_at_no_unwind _ _ _ (result_dests_no_unwind dests values) successful

/-- Full call/Invoke normal-edge publication, consuming original guards. -/
theorem call_results_frame_exit (ctx : EvalContext) (inst : Inst) (dests : List ValueId) (values : List Value)
    (state : MachineState) (valid : WellMintedState state) (incoming : MintedArgs state.nextFrameLineage values) :
    FrameActionExit (fun _ _ => True) state (Sem.run (ctx.bindCallResults inst dests values) state) := by
  have successful : ∀ after unit,
      Sem.run (ctx.bindCallResults inst dests values) state = .ok (unit,after) →
      WellMintedState after ∧ True ∧ HistoryExtends state after := by
    intro after unit run
    cases unit
    have history := (call_results_history ctx inst dests values).extends state after () run
    exact ⟨valid.call_results_success ctx inst dests values state after incoming run,True.intro,history⟩
  exact exit_at_no_unwind _ _ _ (call_results_no_unwind ctx inst dests values) successful

/-- Arbitrary original instruction result shapes/destination collisions and
private-SSA retirement preserve state/history through all exits. -/
theorem instruction_results_frame_action (ctx : EvalContext) (inst : Inst) (result : InstrResult) (dests : List ValueId) :
    FrameActionValid (fun _ _ => True) (ctx.bindInstructionResults inst result dests) := by
  have successful : ∀ state after unit, WellMintedState state →
      Sem.run (ctx.bindInstructionResults inst result dests) state = .ok (unit,after) →
      WellMintedState after ∧ True ∧ HistoryExtends state after := by
    intro state after unit valid run
    cases unit
    exact ⟨valid.bind_instruction_success ctx inst result dests state after run,True.intro,
      (instruction_results_history ctx inst result dests).extends state after () run⟩
  exact frame_action_of_success_no_unwind _ _
    (instruction_results_no_unwind ctx inst result dests) successful

theorem block_params_no_unwind (params : List (ValueId × Ty)) (args : List Value) :
    CallCheckNoUnwind (bindBlockParams params args) := by
  unfold bindBlockParams
  repeat' publication_leaves

theorem checked_params_no_unwind (params : List (ValueId × Ty)) (args : List Value) :
    CallCheckNoUnwind (bindBlockParamsChecked params args) := by
  unfold bindBlockParamsChecked
  split
  · exact block_params_no_unwind _ _
  · cases checked : checkSSACharValues (params.map Prod.snd) args with
    | ok unit => cases unit; exact block_params_no_unwind _ _
    | error error =>
      intro state exception after run
      cases run
      exact char_values_no_unwind _ _ exception after checked

theorem checked_params_frame_exit (params : List (ValueId × Ty)) (args : List Value) (state : MachineState)
    (valid : WellMintedState state) (incoming : MintedArgs state.nextFrameLineage args) :
    FrameActionExit (fun _ _ => True) state (Sem.run (bindBlockParamsChecked params args) state) := by
  apply exit_at_no_unwind _ _ _ (checked_params_no_unwind params args)
  intro after unit run
  cases unit
  exact ⟨valid.checked_params_success params args state after incoming run,True.intro,
    (checked_params_history params args).extends state after () run⟩

end TrustIr.FrameLifetime
