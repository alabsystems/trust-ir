-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.ScalarEncodedAdmission
import TrustIr.Proofs.SourceValueMembership

namespace TrustIr.AggregateMemory
open SourceLayout

/-- Successful recursive checking supplies the real immediate integer-lane
    check. The canonical value/range checks remain stronger source obligations. -/
theorem closure_checked_integer_lane (ctx : EvalContext) (fuel : Nat) (ty : Ty) (input : Value)
    (integer : ty.isInteger = true) (checked : checkClosureValueAt ctx fuel ty input = .ok ()) :
    checkAggregateLane ctx.byteModel ty input = .ok () := by
  cases fuel with
  | zero => cases checked
  | succ fuel =>
    cases ty <;> simp only [Ty.isInteger] at integer <;> try cases integer
    all_goals cases input <;> try cases checked
    all_goals
      apply Classical.byContradiction
      intro notLane
      simp [checkAggregateLane,Value.isPoison,Value.isUninit,Bind.bind,Except.bind,Pure.pure,Except.pure] at notLane
      cases modelEq : ctx.byteModel <;> try simp only [modelEq,ByteModel.pointerBits,ByteModel.pointerBytes] at notLane
      all_goals have reversed := Ne.symm notLane
      all_goals simp [checkClosureValueAt,Value.isPoison,Value.isUninit,Ty.isInteger,Ty.bitWidthFor,
          Ty.bitWidthAtModel,Ty.bitWidth,Ty.bitWidthAtPointerBits,ByteModel.pointerBits,ByteModel.pointerBytes,
          modelEq,notLane,reversed,Bind.bind,Except.bind,Pure.pure,Except.pure] at checked

theorem closure_checked_pointer_lane (ctx : EvalContext) (fuel : Nat) (ty : Ty) (input : Value)
    (pointer : ty.isPointerLike = true) (checked : checkClosureValueAt ctx fuel ty input = .ok ()) :
    checkAggregateLane ctx.byteModel ty input = .ok () := by
  cases fuel with
  | zero => cases checked
  | succ fuel =>
    cases ty <;> simp only [Ty.isPointerLike,Ty.isReference] at pointer <;> try cases pointer
    all_goals cases input <;> try rfl <;> try cases checked
    all_goals
      simp [checkClosureValueAt,Value.isPoison,Value.isUninit,Ty.isInteger,
        Bind.bind,Except.bind,Pure.pure,Except.pure] at checked

theorem closure_checked_boolean_lane (ctx : EvalContext) (fuel : Nat) (input : Value)
    (checked : checkClosureValueAt ctx fuel .Bool input = .ok ()) :
    checkAggregateLane ctx.byteModel .Bool input = .ok () := by
  cases fuel with
  | zero => cases checked
  | succ fuel =>
    cases input <;> try rfl <;> try cases checked
    all_goals simp [checkClosureValueAt,Value.isPoison,Value.isUninit,Ty.isInteger,
      Bind.bind,Except.bind,Pure.pure,Except.pure] at checked

theorem closure_checked_unit_lane (ctx : EvalContext) (fuel : Nat) (input : Value)
    (checked : checkClosureValueAt ctx fuel .Unit input = .ok ()) :
    checkAggregateLane ctx.byteModel .Unit input = .ok () := by
  cases fuel with
  | zero => cases checked
  | succ fuel =>
    cases input with
    | aggregate values =>
      cases values with
      | nil => rfl
      | cons value rest => cases checked
    | _ =>
      simp [checkClosureValueAt,Value.isPoison,Value.isUninit,Ty.isInteger,
        Bind.bind,Except.bind,Pure.pure,Except.pure] at checked
      all_goals try cases checked

theorem ScalarReadbackPlan.input_of_source_checked {plan : Plan} (shape : ScalarReadbackPlan plan)
    (ctx : EvalContext) (fuel : Nat) (order : FunctionAddressOrder) (input : Value) (stored : Image)
    (checked : checkClosureValueAt ctx fuel plan.ty input = .ok ())
    (encoded : encode ctx.byteModel order plan input false = .ok stored) :
    ScalarReadbackInput ctx.byteModel plan input ∨ FunctionReadbackInput ctx.byteModel order plan input := by
  cases shape with
  | integer ty layout integer =>
    exact Or.inl (.integer_of_checked_encoded ctx.byteModel order ty layout input stored integer
      (closure_checked_integer_lane ctx fuel ty input integer checked) encoded)
  | pointer ty layout pointer =>
    exact Or.inl (.pointer_of_checked_encoded ctx.byteModel order ty layout input stored pointer
      (closure_checked_pointer_lane ctx fuel ty input pointer checked) encoded)
  | boolean => exact Or.inl (.boolean_of_checked ctx.byteModel input (closure_checked_boolean_lane ctx fuel input checked))
  | unit => exact Or.inl (.unit_of_checked ctx.byteModel input (closure_checked_unit_lane ctx fuel input checked))
  | fat kind layout => exact Or.inl (.fat_of_encoded ctx.byteModel order kind layout input stored encoded)
  | vector count ty layout lane _nonzero =>
    obtain ⟨values,rfl,_census,_positive,_ready⟩ := vector_source_checked ctx fuel count ty input lane checked
    obtain ⟨size,typed,positive,census,extent,ready⟩ := vector_leaf_admission_of_encoded ctx.byteModel order count ty layout values lane stored encoded
    exact Or.inl (.vector count ty layout values lane size typed positive census extent ready)
  | function signature layout => exact Or.inr (.of_encoded ctx.byteModel order signature layout input stored encoded)

theorem ScalarReadbackPlan.admit_of_source_checked {plan : Plan} (shape : ScalarReadbackPlan plan)
    (ctx : EvalContext) (fuel : Nat) (order : FunctionAddressOrder) (memory : Memory) (input : Value) (stored : Image)
    (checked : checkClosureValueAt ctx fuel plan.ty input = .ok ())
    (encoded : encode ctx.byteModel order plan input false = .ok stored) :
    ReadbackInput ctx.byteModel order memory plan input := by
  rcases shape.input_of_source_checked ctx fuel order input stored checked encoded with scalar | function
  · exact .scalar scalar
  · exact .function function

/-- Ordinary successful storage excludes whole unwritten carriers at each
    actual recursive call. Zero-length unused templates are not calls. Poison
    and partial carriers retain their own checker/store refusal rules. -/
theorem encode_ordinary_not_uninit (model : ByteModel) (order : FunctionAddressOrder) (plan : Plan)
    (input : Value) (stored : Image) (encoded : encode model order plan input false = .ok stored) :
    input.isUninit = false := by
  by_cases uninit : input.isUninit = true
  · trustIrCompilerProof {
      cases plan <;> rw [encode] at encoded
      all_goals simp only [uninit,ite_true,Bool.false_eq_true,ite_false] at encoded
      all_goals cases encoded
    } {
      rw [encode.eq_def] at encoded
      simp only [uninit,ite_true,Bool.false_eq_true,ite_false] at encoded
      cases encoded
    }
  · cases flag : input.isUninit with
    | false => rfl
    | true => exact False.elim (uninit flag)

theorem Plan.Origin.tuple_types_and_children {source : Environment} {types : List Ty}
    {layout : MemoryTypeLayout} {fields : List (Nat × Plan)}
    (origin : Plan.Origin (SourceElement source) (ActualSummary source) (.Tuple types) (.fields (.Tuple types) layout fields)) :
    fields.map (fun field => field.2.ty) = types ∧
      ∀ field ∈ fields, Plan.Origin (SourceElement source) (ActualSummary source) field.2.ty field.2 := by
  cases origin with
  | fields ty layout fields kind children value summary extent bindings metadata sizes => exact ⟨bindings.1,children⟩

theorem list_zip_member_of_get {α β : Type} (left : List α) (right : List β) (position : Nat) (a : α) (b : β)
    (first : (trustIrListGet? left position) = some a) (second : (trustIrListGet? right position) = some b) : (a,b) ∈ left.zip right := by
  trustIrCompilerProof {
    have found : (trustIrListGet? (left.zip right) position) = some (a,b) := by
      change (trustIrListGet? (left.zipWith Prod.mk right) position) = some (a,b)
      rw [List.zipWith_get?,first,second]
    obtain ⟨inside,same⟩ := List.get?_eq_some.mp found
    exact List.mem_iff_get.mpr ⟨⟨position,inside⟩,same⟩
  } {
    have found : (trustIrListGet? (left.zip right) position) = some (a,b) := by
      change (trustIrListGet? (left.zipWith Prod.mk right) position) = some (a,b)
      rw [CompilerCompat.listGetConstructive_zipWith,first,second]
    exact CompilerCompat.listGetConstructive_mem found
  }

/-- Supported source plans, with actual context lookup agreement for visible
    array elements. Empty arrays impose no policy on unused element templates.
    Tuple child types are authenticated by real source origins in admission. -/
inductive SourceReadbackShape (ctx : EvalContext) : Plan → Prop where
  | scalar {plan : Plan} (shape : ScalarReadbackPlan plan) : SourceReadbackShape ctx plan
  | tuple (types : List Ty) (layout : MemoryTypeLayout) (fields : List (Nat × Plan))
      (children : ∀ offset child, (offset,child) ∈ fields → SourceReadbackShape ctx child) :
      SourceReadbackShape ctx (.fields (.Tuple types) layout fields)
  | array (id : TyId) (layout : MemoryTypeLayout) (count : Nat) (element : Plan)
      (resolved : ctx.types id = some element.ty) (child : SourceReadbackShape ctx element) :
      SourceReadbackShape ctx (.array (.Array id count) layout count element)
  | emptyArray (id : TyId) (layout : MemoryTypeLayout) (element : Plan) :
      SourceReadbackShape ctx (.array (.Array id 0) layout 0 element)

/-- Actual recursive checking and successful ordinary storage derive all
    visible input certificates. Source origins retain nominal binding/geometry;
    no parent decoder or separate initialization certificate is assumed. -/
theorem SourceReadbackShape.admit {ctx : EvalContext} {plan : Plan} (shape : SourceReadbackShape ctx plan)
    (order : FunctionAddressOrder) (memory : Memory) :
    ∀ source, Plan.Origin (SourceElement source) (ActualSummary source) plan.ty plan →
    ∀ fuel input stored, checkClosureValueAt ctx fuel plan.ty input = .ok () →
      encode ctx.byteModel order plan input false = .ok stored → ReadbackInput ctx.byteModel order memory plan input := by
  trustIrCompilerProof {
    induction shape with
    | scalar scalar =>
      intro source origin fuel input stored checked encoded
      exact scalar.admit_of_source_checked ctx fuel order memory input stored checked encoded
    | tuple types layout fields children ih =>
      intro source origin fuel input stored checked encoded
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
        exact ih offset child fieldMember source (origins (offset,child) fieldMember) fuel input childImage checkedChild childEncoded
    | array id layout count element resolved child ih =>
      intro source origin fuel input stored checked encoded
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
        exact ih source childOrigin fuel input childImage checkedChild childEncoded
    | emptyArray id layout element =>
      intro source origin fuel input stored checked encoded
      obtain ⟨inputs,inputShape,census,run⟩ := encode_array_steps ctx.byteModel order (.Array id 0) layout 0 element input stored encoded
      subst input
      apply ReadbackInput.array (.Array id 0) layout 0 element inputs census
      intro position input inside found
      omega
  } {
    induction shape with
    | scalar scalar =>
      intro source origin fuel input stored checked encoded
      exact scalar.admit_of_source_checked ctx fuel order memory input stored checked encoded
    | tuple types layout fields children ih =>
      intro source origin fuel input stored checked encoded
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
        exact ih offset child fieldMember source (origins (offset,child) fieldMember) fuel input childImage checkedChild childEncoded
    | array id layout count element resolved child ih =>
      intro source origin fuel input stored checked encoded
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
        exact ih source childOrigin fuel input childImage checkedChild childEncoded
    | emptyArray id layout element =>
      intro source origin fuel input stored checked encoded
      obtain ⟨inputs,inputShape,census,run⟩ := encode_array_steps ctx.byteModel order (.Array id 0) layout 0 element input stored encoded
      subst input
      apply ReadbackInput.array (.Array id 0) layout 0 element inputs census
      intro position input inside found
      omega
  }

theorem source_checked_recursive_readback {ctx : EvalContext} {plan : Plan} (shape : SourceReadbackShape ctx plan)
    (source : Environment) (origin : Plan.Origin (SourceElement source) (ActualSummary source) plan.ty plan)
    (fuel : Nat) (order : FunctionAddressOrder) (memory : Memory) (input : Value) (stored : Image)
    (checked : checkClosureValueAt ctx fuel plan.ty input = .ok ())
    (encoded : encode ctx.byteModel order plan input false = .ok stored)
    (loaded : ByteImage) (extent : loaded.size = plan.layout.size)
    (bytes : ∀ index, loaded.get index = stored.bytes.get index) :
    ∃ output, decode ctx.byteModel order memory plan loaded = .ok output ∧ ValueReadback ctx.byteModel memory input output :=
  (shape.admit order memory source origin fuel input stored checked encoded).top_readback source origin stored encoded loaded extent bytes
    (top_char_ready_of_checked_closure ctx fuel plan input checked)

/-- Real prepared queries and the actual finite-depth value-checking entry
    supply recursive readback. Target width and code order are the context's;
    no per-child value, Unicode or initialization certificates are supplied. -/
theorem prepared_checked_value_readback (source : Environment) (roots : List Ty) (ty : Ty) (plan : Plan)
    (prepared : (prepare source roots).query ty = .ok plan) (ctx : EvalContext) (shape : SourceReadbackShape ctx plan)
    (memory : Memory) (input : Value) (stored : Image)
    (checked : checkClosureValue ctx plan.ty input = .ok ())
    (encoded : encode ctx.byteModel ctx.functionOrder plan input false = .ok stored) :
    ∃ output, decode ctx.byteModel ctx.functionOrder memory plan stored.bytes = .ok output ∧
      ValueReadback ctx.byteModel memory input output :=
  source_checked_recursive_readback shape source (prepared_plan_origin source roots ty plan prepared).own
    (input.depth + 1) ctx.functionOrder memory input stored checked encoded stored.bytes
    (encode_extent ctx.byteModel ctx.functionOrder plan input false stored encoded) (fun _ => rfl)

end TrustIr.AggregateMemory
