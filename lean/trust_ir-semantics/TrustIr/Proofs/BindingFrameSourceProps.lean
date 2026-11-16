-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Semantics.Eval

namespace TrustIr.BindingFrameSourceProps

private def declaration : BindingFrameDef :=
  { id := ⟨3⟩, name := "items", slots := [{ name := "item", ty := .FnItem ⟨7⟩ }] }

private def itemHeader : FunctionItemHeader :=
  { signatureId := ⟨0⟩
    header := { signature := { params := [], returns := [], isVararg := false }, callingConv := .C } }

private def declarations : FunctionItemPresence.Source :=
  { functions :=
      [{ id := ⟨53⟩, frames := some [declaration], header := .ok itemHeader },
       { id := ⟨7⟩, frames := none, header := .ok itemHeader }] }

private def context : EvalContext :=
  { valueSource := FunctionItemPresence.prepare declarations
    functions := fun _ => none
    funcPtrs := fun _ => none
    funcTys := fun _ => none
    maxCallDepth := 1
    globalsTable := fun _ => none }

private theorem singleton_check (ctx : EvalContext) (ty : Ty) (value : Value) :
    checkFunctionItemValues ctx [ty] [value] =
      checkFunctionItemLanes ctx (value.depth + 1) ty value := by
  change (checkFunctionItemLanes ctx (value.depth + 1) ty value >>= fun _ => .ok ()) = _
  cases checkFunctionItemLanes ctx (value.depth + 1) ty value with
  | error error => rfl
  | ok result => cases result; rfl

private theorem source_frame_depth (lineage : Nat) (origin : FuncId)
    (frame : BindingFrameDef) (values : List Value) :
    (Value.sourceFrame lineage origin frame values).depth = valueListDepthSpec values + 1 := by
  rw [Value.depth, Value.depthSpec]

theorem source_handle_has_ptr_transport (lineage : Nat) (origin : FuncId) (frame : BindingFrameDef)
    (values : List Value) :
    (Value.sourceFrame lineage origin frame values).ty = .Ptr := rfl

theorem bind_retains_source_origin (lineage : Nat) (origin : FuncId) (frame : BindingFrameDef)
    (value previous : Value) :
    bindSlot (.sourceFrame lineage origin frame [previous]) 0 value =
      some (.sourceFrame lineage origin frame [value]) := rfl

theorem authentic_frame_uses_declared_item_type :
    checkFunctionItemValues context [.Ptr] [.sourceFrame 0 ⟨53⟩ declaration [.fnItem ⟨7⟩]] = .ok () := by
  rw [singleton_check, source_frame_depth]
  simp only [valueListDepthSpec, Value.depthSpec]
  trustIrReduce

theorem unwritten_declared_slot_transports_without_inspection :
    checkFunctionItemValues context [.Ptr] [.sourceFrame 0 ⟨53⟩ declaration [.uninit]] = .ok () := by
  rw [singleton_check, source_frame_depth]
  simp only [valueListDepthSpec, Value.depthSpec]
  trustIrReduce

theorem same_shape_without_source_origin_is_refused :
    checkFunctionItemValues context [.Ptr] [.sourceFrame 0 ⟨54⟩ declaration [.fnItem ⟨7⟩]] =
      .error (.typeError "binding frame: original declaration is absent or ambiguous") := by
  rw [singleton_check, source_frame_depth]
  simp only [valueListDepthSpec, Value.depthSpec]
  rfl

theorem wrong_declared_slot_identity_is_refused :
    checkFunctionItemValues context [.Ptr] [.sourceFrame 0 ⟨53⟩ declaration [.fnItem ⟨8⟩]] =
      .error (.typeError "FnItem: runtime identity differs from declared type") := by
  rw [singleton_check, source_frame_depth]
  simp only [valueListDepthSpec, Value.depthSpec]
  trustIrReduce

theorem incomplete_snapshot_is_refused :
    checkFunctionItemValues context [.Ptr] [.sourceFrame 0 ⟨53⟩ declaration []] =
      .error (.typeError "binding frame: slot census differs from original declaration") := by
  rw [singleton_check, source_frame_depth]
  simp only [valueListDepthSpec, Value.depthSpec]
  trustIrReduce

/-- An all-unbound snapshot still authenticates its complete original row. -/
theorem changed_frame_name_is_refused_before_unwritten_slots :
    checkFunctionItemValues context [.Ptr]
      [.sourceFrame 0 ⟨53⟩ { declaration with name := "different" } [.uninit]] =
      .error (.typeError "binding frame: original declaration differs from held origin") := by
  rw [singleton_check, source_frame_depth]
  simp only [valueListDepthSpec, Value.depthSpec]
  rfl

theorem changed_slot_name_is_refused_before_unwritten_slots :
    checkFunctionItemValues context [.Ptr]
      [.sourceFrame 0 ⟨53⟩ { declaration with slots := [{ name := "different", ty := .FnItem ⟨7⟩ }] } [.uninit]] =
      .error (.typeError "binding frame: original declaration differs from held origin") := by
  rw [singleton_check, source_frame_depth]
  simp only [valueListDepthSpec, Value.depthSpec]
  rfl

theorem changed_slot_type_is_refused_before_unwritten_slots :
    checkFunctionItemValues context [.Ptr]
      [.sourceFrame 0 ⟨53⟩ { declaration with slots := [{ name := "item", ty := .FnItem ⟨8⟩ }] } [.uninit]] =
      .error (.typeError "binding frame: original declaration differs from held origin") := by
  rw [singleton_check, source_frame_depth]
  simp only [valueListDepthSpec, Value.depthSpec]
  trustIrReduce

theorem duplicate_function_origin_is_refused :
    ({ functions := declarations.functions ++ declarations.functions } : FunctionItemPresence.Source).bindingFrame ⟨53⟩ ⟨3⟩ = none := rfl

theorem duplicate_local_origin_is_refused :
    ({ functions := [{ id := ⟨53⟩, header := .error "invalid original signature", frames := some [declaration, declaration] }] } :
      FunctionItemPresence.Source).bindingFrame ⟨53⟩ ⟨3⟩ = none := rfl

/-- A malformed duplicate counts as an original row before either lookup can
    grant authority. Identical frame payloads cannot repair the ambiguity. -/
theorem malformed_duplicate_refuses_header_and_frame :
    let source : FunctionItemPresence.Source :=
      { functions := declarations.functions ++
          [{ id := ⟨53⟩, header := .error "invalid original signature", frames := some [declaration] }] }
    source.functionItem ⟨53⟩ =
      some (.error "FnItem: function 53 has ambiguous declarations") ∧
      source.bindingFrame ⟨53⟩ ⟨3⟩ = none := by constructor <;> rfl

theorem malformed_unique_header_preserves_static_error :
    let source : FunctionItemPresence.Source :=
      { functions := [{ id := ⟨53⟩, header := .error "invalid original signature", frames := some [declaration] }] }
    source.functionItem ⟨53⟩ = some (.error "invalid original signature") ∧
      source.bindingFrame ⟨53⟩ ⟨3⟩ = some declaration := by constructor <;> rfl

end TrustIr.BindingFrameSourceProps
