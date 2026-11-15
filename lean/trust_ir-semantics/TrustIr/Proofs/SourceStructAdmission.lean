-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceStructGraph
import TrustIr.Proofs.SourceCheckedAdmission

namespace TrustIr.AggregateMemory
open SourceLayout

/-- The evaluator resolves the exact physical row selected by execution layout,
    including sparse IDs and repeated nominal IDs. -/
def StructContextAgreement (source : Environment) (ctx : EvalContext) (id : StructId) : Prop :=
  ∀ position definition,
    (Index.ofEnvironment source).structPositions.find id.index = some position →
    (trustIrListGet? source.structs position) = some definition → ctx.structs id = some definition

theorem Plan.Origin.struct_types_and_children {source : Environment} {ctx : EvalContext} {id : StructId}
    {layout : MemoryTypeLayout} {fields : List (Nat × Plan)}
    (origin : Plan.Origin (SourceElement source) (ActualSummary source) (.Struct id) (.fields (.Struct id) layout fields))
    (agreement : StructContextAgreement source ctx id) :
    ∃ definition, ctx.structs id = some definition ∧
      fields.map (fun field => field.2.ty) = definition.fields.map (·.ty) ∧
      ∀ field ∈ fields, Plan.Origin (SourceElement source) (ActualSummary source) field.2.ty field.2 := by
  obtain ⟨value,actual,extent,children,bindings,sizes⟩ := origin.fields_metadata_view
  obtain ⟨before,next,history,queried⟩ := actual
  obtain ⟨position,definition,selected,row,identity,typed⟩ := history.query_struct_origin .execution id value queried
  refine ⟨definition,agreement position definition selected row,bindings.1.trans typed,children⟩

/-- A source-indexed extension of checked readback policy. Every visible nominal
    row is tied to the actual source selector; aggregate constructors allow
    nominal children at arbitrary nesting depth. -/
inductive SourceNominalReadbackShape (source : Environment) (ctx : EvalContext) : Plan → Prop where
  | existing {plan : Plan} (shape : SourceReadbackShape ctx plan) : SourceNominalReadbackShape source ctx plan
  | nominal (id : StructId) (layout : MemoryTypeLayout) (fields : List (Nat × Plan))
      (agreement : StructContextAgreement source ctx id)
      (children : ∀ offset child, (offset,child) ∈ fields → SourceNominalReadbackShape source ctx child) :
      SourceNominalReadbackShape source ctx (.fields (.Struct id) layout fields)
  | tuple (types : List Ty) (layout : MemoryTypeLayout) (fields : List (Nat × Plan))
      (children : ∀ offset child, (offset,child) ∈ fields → SourceNominalReadbackShape source ctx child) :
      SourceNominalReadbackShape source ctx (.fields (.Tuple types) layout fields)
  | array (id : TyId) (layout : MemoryTypeLayout) (count : Nat) (element : Plan)
      (resolved : ctx.types id = some element.ty) (child : SourceNominalReadbackShape source ctx element) :
      SourceNominalReadbackShape source ctx (.array (.Array id count) layout count element)
  | emptyArray (id : TyId) (layout : MemoryTypeLayout) (element : Plan) :
      SourceNominalReadbackShape source ctx (.array (.Array id 0) layout 0 element)

theorem SourceNominalReadbackShape.admit {source : Environment} {ctx : EvalContext} {plan : Plan} (shape : SourceNominalReadbackShape source ctx plan)
    (order : FunctionAddressOrder) (memory : Memory) :
    Plan.Origin (SourceElement source) (ActualSummary source) plan.ty plan →
    ∀ fuel input stored, checkClosureValueAt ctx fuel plan.ty input = .ok () →
      encode ctx.byteModel order plan input false = .ok stored → ReadbackInput ctx.byteModel order memory plan input := by
  trustIrCompilerProof {
    induction shape with
    | existing existing =>
      intro origin fuel input stored checked encoded
      exact existing.admit order memory source origin fuel input stored checked encoded
    | nominal id layout fields agreement children ih =>
      intro origin fuel input stored checked encoded
      cases fuel with
      | zero => cases checked
      | succ fuel =>
        obtain ⟨inputs,inputShape,run⟩ := encode_fields_steps ctx.byteModel order (.Struct id) layout fields input stored encoded
        subst input
        obtain ⟨definition,resolved,typed,origins⟩ := origin.struct_types_and_children agreement
        obtain ⟨census,traversal⟩ := SourceValueMembership.struct_checked ctx fuel id definition resolved inputs checked
        have fieldCount := congrArg List.length typed
        simp only [List.length_map] at fieldCount
        apply ReadbackInput.fields (.Struct id) layout fields inputs (fieldCount.trans census)
        intro position offset child input found selected
        obtain ⟨actual,earlier,childImage,placed,actualGet,earlierRun,childEncoded,written,suffix⟩ := run.at position offset child found
        rw [selected] at actualGet
        cases actualGet
        have typeGet : (trustIrListGet? (definition.fields.map (·.ty)) position) = some child.ty := by
          rw [← typed,List.get?_map,found]
          rfl
        obtain ⟨field,fieldGet,fieldType⟩ : ∃ field, (trustIrListGet? definition.fields position) = some field ∧ field.ty = child.ty := by
          rw [List.get?_map] at typeGet
          cases row : (trustIrListGet? definition.fields position) with
          | none => rw [row] at typeGet; cases typeGet
          | some field => exact ⟨field,rfl,Option.some.inj (by simpa only [row,Option.map_some] using typeGet)⟩
        have member := list_zip_member_of_get definition.fields inputs position field input fieldGet selected
        have childChecked := SourceValueMembership.forM_checked_member _ _ traversal (field,input) member
        have initialized := encode_ordinary_not_uninit ctx.byteModel order child input childImage childEncoded
        have checkedChild : checkClosureValueAt ctx fuel child.ty input = .ok () := by
          simpa only [initialized,Bool.false_eq_true,ite_false,fieldType] using childChecked
        obtain ⟨inside,same⟩ := List.get?_eq_some.mp found
        have fieldMember : (offset,child) ∈ fields := List.mem_iff_get.mpr ⟨⟨position,inside⟩,same⟩
        exact ih offset child fieldMember (origins (offset,child) fieldMember) fuel input childImage checkedChild childEncoded
    | tuple types layout fields children ih =>
      intro origin fuel input stored checked encoded
      cases fuel with
      | zero => cases checked
      | succ fuel =>
        obtain ⟨inputs,inputShape,run⟩ := encode_fields_steps ctx.byteModel order (.Tuple types) layout fields input stored encoded
        subst input
        obtain ⟨typed,origins⟩ := origin.tuple_types_and_children
        obtain ⟨census,traversal⟩ := SourceValueMembership.tuple_checked ctx fuel types inputs checked
        have fieldCount := congrArg List.length typed
        simp only [List.length_map] at fieldCount
        apply ReadbackInput.fields (.Tuple types) layout fields inputs (fieldCount.trans census)
        intro position offset child input found selected
        obtain ⟨actual,earlier,childImage,placed,actualGet,earlierRun,childEncoded,written,suffix⟩ := run.at position offset child found
        rw [selected] at actualGet
        cases actualGet
        have typeGet : (trustIrListGet? types position) = some child.ty := by
          rw [← typed,List.get?_map,found]
          rfl
        have member := list_zip_member_of_get types inputs position child.ty input typeGet selected
        have childChecked := SourceValueMembership.forM_checked_member _ _ traversal (child.ty,input) member
        have initialized := encode_ordinary_not_uninit ctx.byteModel order child input childImage childEncoded
        have checkedChild : checkClosureValueAt ctx fuel child.ty input = .ok () := by
          simpa only [initialized,Bool.false_eq_true,ite_false] using childChecked
        obtain ⟨inside,same⟩ := List.get?_eq_some.mp found
        have fieldMember : (offset,child) ∈ fields := List.mem_iff_get.mpr ⟨⟨position,inside⟩,same⟩
        exact ih offset child fieldMember (origins (offset,child) fieldMember) fuel input childImage checkedChild childEncoded
    | array id layout count element resolved child ih =>
      intro origin fuel input stored checked encoded
      cases fuel with
      | zero => cases checked
      | succ fuel =>
        obtain ⟨inputs,inputShape,census,run⟩ := encode_array_steps ctx.byteModel order (.Array id count) layout count element input stored encoded
        subst input
        have childOrigin : Plan.Origin (SourceElement source) (ActualSummary source) element.ty element := by
          cases origin with
          | array _ _ _ _ child _ _ _ _ => exact child
        have childChecks := (SourceValueMembership.array_checked ctx fuel id count inputs element.ty resolved checked).2
        apply ReadbackInput.array (.Array id count) layout count element inputs census
        intro position input inside found
        obtain ⟨childImage,childEncoded,lane⟩ := encode_array_slot ctx.byteModel order (.Array id count) layout count element inputs stored encoded
          position input (by rw [census]; exact inside) found
        have checkedChild := inputs.tree.checkStored_get _ position input childChecks found
        exact ih childOrigin fuel input childImage checkedChild childEncoded
    | emptyArray id layout element =>
      intro origin fuel input stored checked encoded
      obtain ⟨inputs,inputShape,census,run⟩ := encode_array_steps ctx.byteModel order (.Array id 0) layout 0 element input stored encoded
      subst input
      apply ReadbackInput.array (.Array id 0) layout 0 element inputs census
      intro position input inside found
      omega
  } {
    induction shape with
    | existing existing =>
      intro origin fuel input stored checked encoded
      exact existing.admit order memory source origin fuel input stored checked encoded
    | nominal id layout fields agreement children ih =>
      intro origin fuel input stored checked encoded
      cases fuel with
      | zero => cases checked
      | succ fuel =>
        obtain ⟨inputs,inputShape,run⟩ := encode_fields_steps ctx.byteModel order (.Struct id) layout fields input stored encoded
        subst input
        obtain ⟨definition,resolved,typed,origins⟩ := origin.struct_types_and_children agreement
        obtain ⟨census,traversal⟩ := SourceValueMembership.struct_checked ctx fuel id definition resolved inputs checked
        have fieldCount := congrArg List.length typed
        simp only [List.length_map] at fieldCount
        apply ReadbackInput.fields (.Struct id) layout fields inputs (fieldCount.trans census)
        intro position offset child input found selected
        obtain ⟨actual,earlier,childImage,placed,actualGet,earlierRun,childEncoded,written,suffix⟩ := run.at position offset child found
        rw [selected] at actualGet
        cases actualGet
        have typeGet : (trustIrListGet? (definition.fields.map (·.ty)) position) = some child.ty := by
          rw [← typed,CompilerCompat.listGetConstructive_map,found]
          rfl
        obtain ⟨field,fieldGet,fieldType⟩ : ∃ field, (trustIrListGet? definition.fields position) = some field ∧ field.ty = child.ty := by
          rw [CompilerCompat.listGetConstructive_map] at typeGet
          cases row : (trustIrListGet? definition.fields position) with
          | none => rw [row] at typeGet; cases typeGet
          | some field => exact ⟨field,rfl,Option.some.inj (by simpa only [row,Option.map_some] using typeGet)⟩
        have member := list_zip_member_of_get definition.fields inputs position field input fieldGet selected
        have childChecked := SourceValueMembership.forM_checked_member _ _ traversal (field,input) member
        have initialized := encode_ordinary_not_uninit ctx.byteModel order child input childImage childEncoded
        have checkedChild : checkClosureValueAt ctx fuel child.ty input = .ok () := by
          simpa only [initialized,Bool.false_eq_true,ite_false,fieldType] using childChecked
        have fieldMember : (offset,child) ∈ fields := CompilerCompat.listGetConstructive_mem found
        exact ih offset child fieldMember (origins (offset,child) fieldMember) fuel input childImage checkedChild childEncoded
    | tuple types layout fields children ih =>
      intro origin fuel input stored checked encoded
      cases fuel with
      | zero => cases checked
      | succ fuel =>
        obtain ⟨inputs,inputShape,run⟩ := encode_fields_steps ctx.byteModel order (.Tuple types) layout fields input stored encoded
        subst input
        obtain ⟨typed,origins⟩ := origin.tuple_types_and_children
        obtain ⟨census,traversal⟩ := SourceValueMembership.tuple_checked ctx fuel types inputs checked
        have fieldCount := congrArg List.length typed
        simp only [List.length_map] at fieldCount
        apply ReadbackInput.fields (.Tuple types) layout fields inputs (fieldCount.trans census)
        intro position offset child input found selected
        obtain ⟨actual,earlier,childImage,placed,actualGet,earlierRun,childEncoded,written,suffix⟩ := run.at position offset child found
        rw [selected] at actualGet
        cases actualGet
        have typeGet : (trustIrListGet? types position) = some child.ty := by
          rw [← typed,CompilerCompat.listGetConstructive_map,found]
          rfl
        have member := list_zip_member_of_get types inputs position child.ty input typeGet selected
        have childChecked := SourceValueMembership.forM_checked_member _ _ traversal (child.ty,input) member
        have initialized := encode_ordinary_not_uninit ctx.byteModel order child input childImage childEncoded
        have checkedChild : checkClosureValueAt ctx fuel child.ty input = .ok () := by
          simpa only [initialized,Bool.false_eq_true,ite_false] using childChecked
        have fieldMember : (offset,child) ∈ fields := CompilerCompat.listGetConstructive_mem found
        exact ih offset child fieldMember (origins (offset,child) fieldMember) fuel input childImage checkedChild childEncoded
    | array id layout count element resolved child ih =>
      intro origin fuel input stored checked encoded
      cases fuel with
      | zero => cases checked
      | succ fuel =>
        obtain ⟨inputs,inputShape,census,run⟩ := encode_array_steps ctx.byteModel order (.Array id count) layout count element input stored encoded
        subst input
        have childOrigin : Plan.Origin (SourceElement source) (ActualSummary source) element.ty element := by
          cases origin with
          | array _ _ _ _ child _ _ _ _ => exact child
        have childChecks := (SourceValueMembership.array_checked ctx fuel id count inputs element.ty resolved checked).2
        apply ReadbackInput.array (.Array id count) layout count element inputs census
        intro position input inside found
        obtain ⟨childImage,childEncoded,lane⟩ := encode_array_slot ctx.byteModel order (.Array id count) layout count element inputs stored encoded
          position input (by rw [census]; exact inside) found
        have checkedChild := inputs.tree.checkStored_get _ position input childChecks found
        exact ih childOrigin fuel input childImage checkedChild childEncoded
    | emptyArray id layout element =>
      intro origin fuel input stored checked encoded
      obtain ⟨inputs,inputShape,census,run⟩ := encode_array_steps ctx.byteModel order (.Array id 0) layout 0 element input stored encoded
      subst input
      apply ReadbackInput.array (.Array id 0) layout 0 element inputs census
      intro position input inside found
      omega
  }

theorem source_checked_nominal_readback {source : Environment} {ctx : EvalContext} {plan : Plan} (shape : SourceNominalReadbackShape source ctx plan)
    (origin : Plan.Origin (SourceElement source) (ActualSummary source) plan.ty plan)
    (fuel : Nat) (order : FunctionAddressOrder) (memory : Memory) (input : Value) (stored : Image)
    (checked : checkClosureValueAt ctx fuel plan.ty input = .ok ())
    (encoded : encode ctx.byteModel order plan input false = .ok stored)
    (loaded : ByteImage) (extent : loaded.size = plan.layout.size)
    (bytes : ∀ index, loaded.get index = stored.bytes.get index) :
    ∃ output, decode ctx.byteModel order memory plan loaded = .ok output ∧ ValueReadback ctx.byteModel memory input output :=
  (shape.admit order memory origin fuel input stored checked encoded).top_readback source origin stored encoded loaded extent bytes
    (top_char_ready_of_checked_closure ctx fuel plan input checked)

/-- Real prepared queries and the actual finite-depth value-checking entry
    supply recursive readback. Target width and code order are the context's;
    no per-child value, Unicode or initialization certificates are supplied. -/
theorem prepared_checked_nominal_value_readback (source : Environment) (roots : List Ty) (ty : Ty) (plan : Plan)
    (prepared : (prepare source roots).query ty = .ok plan) (ctx : EvalContext) (shape : SourceNominalReadbackShape source ctx plan)
    (memory : Memory) (input : Value) (stored : Image)
    (checked : checkClosureValue ctx plan.ty input = .ok ())
    (encoded : encode ctx.byteModel ctx.functionOrder plan input false = .ok stored) :
    ∃ output, decode ctx.byteModel ctx.functionOrder memory plan stored.bytes = .ok output ∧
      ValueReadback ctx.byteModel memory input output :=
  source_checked_nominal_readback shape (prepared_plan_origin source roots ty plan prepared).own
    (input.depth + 1) ctx.functionOrder memory input stored checked encoded stored.bytes
    (encode_extent ctx.byteModel ctx.functionOrder plan input false stored encoded) (fun _ => rfl)

end TrustIr.AggregateMemory
