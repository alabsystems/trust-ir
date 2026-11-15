-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceArrayIdentity
import TrustIr.Proofs.SourceSiblingGeometry

namespace TrustIr.AggregateMemory
open SourceLayout

/-- Successful checked planning has the exact constructor dictated by the
original request, including its type identity and logical array count. -/
theorem prepared_plan_source_shape (source : Environment) (roots : List Ty)
    (ty : Ty) (plan : Plan) (run : (prepare source roots).query ty = .ok plan) :
    Plan.SourceShape ty plan :=
  (prepared_plan_origin source roots ty plan run).source_shape

/-- A successful source array request supplies the plan shape; callers need
not assume the result is an array before obtaining element custody. -/
theorem prepared_array_source_view (source : Environment) (roots : List Ty)
    (id : TyId) (count : Nat) (plan : Plan)
    (run : (prepare source roots).query (.Array id count) = .ok plan) :
    ∃ layout element, plan = .array (.Array id count) layout count element ∧
      SourceElement source id element.ty ∧
      Plan.Origin (SourceElement source) (ActualSummary source) element.ty element ∧
      ∃ value, ActualSummary source (.Array id count) value ∧
        layout.size = value.size ∧ value.align = some layout.alignment := by
  obtain ⟨layout,element,rfl⟩ := prepared_plan_source_shape source roots (.Array id count) plan run
  obtain ⟨actual,identity,_,binding,child,value,summary,size,align⟩ :=
    (prepared_plan_origin source roots _ _ run).array_binding_view
  cases identity
  exact ⟨layout,element,rfl,binding,child,value,summary,size,align⟩

/-- Actual encoding and source planning jointly supply array shape, exact
source element identity, original logical count, and the real compact fold. -/
theorem prepared_source_array_encoding (source : Environment) (roots : List Ty)
    (id : TyId) (count : Nat) (plan : Plan)
    (planned : (prepare source roots).query (.Array id count) = .ok plan)
    (model : ByteModel) (order : FunctionAddressOrder) (value : Value) (image : Image)
    (encoded : encode model order plan value false = .ok image) :
    ∃ layout element values, plan = .array (.Array id count) layout count element ∧
      SourceElement source id element.ty ∧ value = .array values ∧ values.size = count ∧
      ArrayImageEncoded (fun child => do
        pure (← encode model order element child false).bytes) values.tree image.bytes := by
  obtain ⟨layout,element,shape,binding,_⟩ := prepared_array_source_view source roots id count plan planned
  subst plan
  obtain ⟨values,valueShape,census,fold⟩ := encode_array_steps model order _ layout count element value image encoded
  exact ⟨layout,element,values,rfl,binding,valueShape,census,fold⟩

/-- Even an empty source array cannot acquire a leaf certificate. -/
theorem source_array_leaf_refusal (resolves : TyId → Ty → Prop)
    (valid : Ty → Summary → Prop) (id : TyId) (count : Nat) (ty : Ty) (layout : MemoryTypeLayout) :
    ¬ Plan.Origin resolves valid (.Array id count) (.leaf ty layout) := by
  intro origin
  obtain ⟨_,_,shape⟩ := origin.source_shape
  cases shape

/-- A scalar cannot acquire a field-list certificate, regardless of extent. -/
theorem source_scalar_fields_refusal (resolves : TyId → Ty → Prop)
    (valid : Ty → Summary → Prop) (ty : Ty) (layout : MemoryTypeLayout) (fields : List (Nat × Plan)) :
    ¬ Plan.Origin resolves valid .U8 (.fields ty layout fields) := by
  intro origin
  obtain ⟨_,shape⟩ := origin.source_shape
  cases shape

/-- Tuple identity is retained even for an empty field list. -/
theorem empty_tuple_field_shape (layout : MemoryTypeLayout) :
    Plan.SourceShape (.Tuple []) (.fields (.Tuple []) layout []) :=
  ⟨layout,[],rfl⟩

/-- An empty tuple cannot be silently substituted by a leaf plan. -/
theorem source_empty_tuple_leaf_refusal (resolves : TyId → Ty → Prop)
    (valid : Ty → Summary → Prop) (ty : Ty) (layout : MemoryTypeLayout) :
    ¬ Plan.Origin resolves valid (.Tuple []) (.leaf ty layout) := by
  intro origin
  obtain ⟨_,_,shape⟩ := origin.source_shape
  cases shape

end TrustIr.AggregateMemory
