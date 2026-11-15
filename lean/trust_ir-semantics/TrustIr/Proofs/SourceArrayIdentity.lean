-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceEnumPlan
import TrustIr.Proofs.SourceArrayCoverage

namespace TrustIr.AggregateMemory
open SourceLayout

/-- Successful checked compilation identifies the source array constructor,
count, actual child origin, and typed layout summary together. -/
theorem prepared_array_identity (source : Environment) (roots : List Ty)
    (sourceTy planTy : Ty) (layout : MemoryTypeLayout) (count : Nat) (element : Plan)
    (run : (prepare source roots).query sourceTy = .ok (.array planTy layout count element)) :
    ∃ id : TyId, sourceTy = .Array id count ∧ planTy = .Array id count ∧
      Plan.Origin (SourceElement source) (ActualSummary source) element.ty element ∧
      ∃ value, ActualSummary source sourceTy value ∧ layout.size = value.size ∧
        value.align = some layout.alignment :=
  (prepared_plan_origin source roots sourceTy _ run).array_view

/-- The plan's logical count is the original requested source count. -/
theorem prepared_array_count (source : Environment) (roots : List Ty)
    (id : TyId) (sourceCount : Nat) (planTy : Ty) (layout : MemoryTypeLayout)
    (count : Nat) (element : Plan)
    (run : (prepare source roots).query (.Array id sourceCount) =
      .ok (.array planTy layout count element)) : count = sourceCount := by
  obtain ⟨actual,shape,_⟩ := prepared_array_identity source roots _ _ layout count element run
  cases shape
  rfl

/-- Actual successful encoding checks the same count retained from the source;
no logical materialization of the compact value is required. -/
theorem prepared_array_encoded_census (source : Environment) (roots : List Ty)
    (id : TyId) (sourceCount : Nat) (planTy : Ty) (layout : MemoryTypeLayout)
    (count : Nat) (element : Plan)
    (prepared : (prepare source roots).query (.Array id sourceCount) =
      .ok (.array planTy layout count element))
    (model : ByteModel) (order : FunctionAddressOrder) (value : Value) (image : Image)
    (encoded : encode model order (.array planTy layout count element) value false = .ok image) :
    ∃ values, value = .array values ∧ values.size = sourceCount ∧
      ArrayImageEncoded (fun child => do
        pure (← encode model order element child false).bytes) values.tree image.bytes := by
  have countEq := prepared_array_count source roots id sourceCount planTy layout count element prepared
  obtain ⟨values,shape,census,fold⟩ := encode_array_steps model order planTy layout count element value image encoded
  exact ⟨values,shape,census.trans countEq,fold⟩

/-- Scalar requests cannot produce a checked array plan. -/
theorem prepared_scalar_array_refusal (source : Environment) (roots : List Ty)
    (planTy : Ty) (layout : MemoryTypeLayout) (count : Nat) (element : Plan) :
    (prepare source roots).query .U8 ≠ .ok (.array planTy layout count element) := by
  intro run
  obtain ⟨id,shape,_⟩ := prepared_array_identity source roots _ _ layout count element run
  cases shape

/-- A mismatched source count cannot acquire a compilation certificate. -/
theorem prepared_wrong_array_count_refusal (source : Environment) (roots : List Ty)
    (id : TyId) (sourceCount : Nat) (planTy : Ty) (layout : MemoryTypeLayout)
    (count : Nat) (element : Plan) (different : count ≠ sourceCount) :
    (prepare source roots).query (.Array id sourceCount) ≠
      .ok (.array planTy layout count element) := by
  intro run
  exact different (prepared_array_count source roots id sourceCount planTy layout count element run)

/-- The compiled element has the exact type resolved by the original source
row, including when the array plan is returned from a prepared cache. -/
theorem prepared_array_element_binding (source : Environment) (roots : List Ty)
    (id : TyId) (sourceCount : Nat) (planTy : Ty) (layout : MemoryTypeLayout)
    (count : Nat) (element : Plan)
    (run : (prepare source roots).query (.Array id sourceCount) =
      .ok (.array planTy layout count element)) : SourceElement source id element.ty := by
  obtain ⟨actual,shape,_,binding,_⟩ := (prepared_plan_origin source roots _ _ run).array_binding_view
  cases shape
  exact binding

/-- Original row identity and the actual typed child-query extent are retained
as separate facts; byte size alone cannot authenticate a type. -/
theorem prepared_array_element_query (source : Environment) (roots : List Ty)
    (id : TyId) (sourceCount : Nat) (planTy : Ty) (layout : MemoryTypeLayout)
    (count : Nat) (element : Plan)
    (run : (prepare source roots).query (.Array id sourceCount) =
      .ok (.array planTy layout count element)) :
    (trustIrListGet? source.types id.index) = some (some element.ty) ∧
      ∃ value, ActualSummary source element.ty value ∧
        element.layout.size = value.size ∧ value.align = some element.layout.alignment := by
  have binding := prepared_array_element_binding source roots id sourceCount planTy layout count element run
  obtain ⟨_,_,_,_,child,_⟩ := (prepared_plan_origin source roots _ _ run).array_binding_view
  exact ⟨binding.row,child.layout_view⟩

/-- An existing source row excludes every differently typed element plan. -/
theorem prepared_wrong_element_refusal (source : Environment) (roots : List Ty)
    (id : TyId) (sourceCount : Nat) (expected planTy : Ty) (layout : MemoryTypeLayout)
    (count : Nat) (element : Plan) (row : SourceElement source id expected)
    (different : element.ty ≠ expected) :
    (prepare source roots).query (.Array id sourceCount) ≠
      .ok (.array planTy layout count element) := by
  intro run
  exact different ((prepared_array_element_binding source roots id sourceCount planTy layout count element run).functional row)

/-- Source association identifies the plan element with the actual evaluation
context's resolved type, rather than just another type of equal extent. -/
theorem prepared_array_context_element (source : Environment) (ctx : EvalContext)
    (associated : CaptureSource source ctx) (roots : List Ty)
    (id : TyId) (sourceCount : Nat) (expected : Ty) (resolved : ctx.types id = some expected)
    (planTy : Ty) (layout : MemoryTypeLayout) (count : Nat) (element : Plan)
    (run : (prepare source roots).query (.Array id sourceCount) =
      .ok (.array planTy layout count element)) : element.ty = expected := by
  have row := associated.types id expected resolved
  have actual := (prepared_array_element_binding source roots id sourceCount planTy layout count element run).row
  rw [actual] at row
  cases row
  rfl

/-- Equally sized signed and unsigned byte types do not share source identity. -/
theorem source_element_signed_byte_refusal :
    ¬ SourceElement { types := [some .U8,some .I8] } ⟨0⟩ .I8 := by
  intro resolved
  cases resolved

/-- An omitted source row cannot acquire an element type. -/
theorem source_element_missing_refusal (ty : Ty) :
    ¬ SourceElement { types := [none] } ⟨0⟩ ty := by
  intro resolved
  cases resolved

end TrustIr.AggregateMemory
