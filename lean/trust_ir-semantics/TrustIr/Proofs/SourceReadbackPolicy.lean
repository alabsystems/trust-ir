-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceStructAdmission

namespace TrustIr.AggregateMemory
open SourceLayout

/-- Kernel-backed type equality, using the total recursive closure comparator. -/
private def policyTyDecEq (a b : Ty) : Decidable (a = b) :=
  if same : closureTyEq a b = true then isTrue (closureTyEq_sound a b same)
  else isFalse (fun equality => same ((closureTyEq_iff a b).mpr equality))

local instance : DecidableEq Ty := policyTyDecEq

deriving instance DecidableEq for FieldDef, StructRepr, StructDef

/-- Compare the evaluator's full definition with the physical source row selected
    by execution layout. Missing rows cannot certify a nominal plan. -/
def selectedStructAgrees (source : Environment) (ctx : EvalContext) (id : StructId) : Bool :=
  match (Index.ofEnvironment source).structPositions.find id.index with
  | none => false
  | some position => match (trustIrListGet? source.structs position) with
    | none => false
    | some definition => decide (ctx.structs id = some definition)

theorem selectedStructAgrees_sound (source : Environment) (ctx : EvalContext) (id : StructId)
    (accepted : selectedStructAgrees source ctx id = true) : StructContextAgreement source ctx id := by
  intro position definition selected row
  simp only [selectedStructAgrees, selected, row] at accepted
  exact of_decide_eq_true accepted

/- Structural mutual recursion follows the plan and its immediate field list.
    Empty array templates and unproved enumeration families are not classified
    recursively. Both functions are total in the kernel and require no caller
    budget. Lean 4.8 also emits compiler-only partial helpers; safe proofs do
    not depend on those helpers. -/
mutual
  def sourceReadbackPolicy (source : Environment) (ctx : EvalContext) : Plan → Bool
    | .leaf ty layout =>
      ty.isInteger || ty.isPointerLike ||
      match ty with
      | .Bool => layout.size == 1 && layout.alignment == 1
      | .Unit => layout.size == 0 && layout.alignment == 1
      | .Vector count element => count != 0 && vectorReadbackLane element
      | .FatPtr _ | .Func _ => true
      | _ => false
    | .fields ty _ fields =>
      (match ty with
      | .Tuple _ => true
      | .Struct id => selectedStructAgrees source ctx id
      | _ => false) && sourceReadbackPolicyFields source ctx fields
    | .array (.Array id declared) _ count element =>
      declared == count && (count == 0 ||
        (match ctx.types id with
         | none => false
         | some ty => closureTyEq ty element.ty) && sourceReadbackPolicy source ctx element)
    | .array _ _ _ _ => false
    | .enumeration _ _ _ _ => false
  private def sourceReadbackPolicyFields (source : Environment) (ctx : EvalContext) : List (Nat × Plan) → Bool
    | [] => true
    | (_,child) :: rest => sourceReadbackPolicy source ctx child && sourceReadbackPolicyFields source ctx rest
end

private theorem policyFields_iff (source : Environment) (ctx : EvalContext) (fields : List (Nat × Plan)) :
    sourceReadbackPolicyFields source ctx fields = true ↔
      ∀ field ∈ fields, sourceReadbackPolicy source ctx field.2 = true := by
  induction fields with
  | nil => simp [sourceReadbackPolicyFields]
  | cons first rest ih =>
    cases first
    simp [sourceReadbackPolicyFields, ih]

theorem sourceReadbackPolicy_sound (source : Environment) (ctx : EvalContext) (plan : Plan)
    (accepted : sourceReadbackPolicy source ctx plan = true) :
    SourceNominalReadbackShape source ctx plan := by
  trustIrCompilerProof {
    cases plan with
    | leaf ty layout =>
      rw [sourceReadbackPolicy] at accepted
      simp only [Bool.or_eq_true, Bool.and_eq_true] at accepted
      rcases accepted with previous | special
      · rcases previous with integer | pointer
        · exact .existing (.scalar (.integer ty layout integer))
        · exact .existing (.scalar (.pointer ty layout pointer))
      · cases ty with
        | Bool =>
          cases layout with
          | mk size alignment =>
            simp only [Bool.and_eq_true, beq_iff_eq] at special
            rcases special with ⟨rfl,rfl⟩
            exact .existing (.scalar .boolean)
        | Unit =>
          cases layout with
          | mk size alignment =>
            simp only [Bool.and_eq_true, beq_iff_eq] at special
            rcases special with ⟨rfl,rfl⟩
            exact .existing (.scalar .unit)
        | Vector count element =>
          simp only [Bool.and_eq_true,bne_iff_ne] at special
          exact .existing (.scalar (.vector count element layout ((vectorReadbackLane_iff element).mp special.2) special.1))
        | FatPtr kind => exact .existing (.scalar (.fat kind layout))
        | Func signature => exact .existing (.scalar (.function signature layout))
        | _ => cases special
    | fields ty layout fields =>
      rw [sourceReadbackPolicy] at accepted
      simp only [Bool.and_eq_true] at accepted
      have kind := accepted.1
      have children := (policyFields_iff source ctx fields).mp accepted.2
      have shapes : ∀ offset child, (offset,child) ∈ fields → SourceNominalReadbackShape source ctx child := by
        intro offset child member
        exact sourceReadbackPolicy_sound source ctx child (children (offset,child) member)
      cases ty with
      | Tuple types => exact .tuple types layout fields shapes
      | Struct id => exact .nominal id layout fields (selectedStructAgrees_sound source ctx id kind) shapes
      | _ => cases kind
    | array ty layout count element =>
      cases ty with
      | Array id declared =>
        rw [sourceReadbackPolicy] at accepted
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at accepted
        have census : declared = count := accepted.1
        subst declared
        rcases accepted.2 with empty | nonempty
        · have empty : count = 0 := empty
          subst count
          exact .emptyArray id layout element
        · have lookup := nonempty.1
          have child := sourceReadbackPolicy_sound source ctx element nonempty.2
          cases resolved : ctx.types id with
          | none => simp only [resolved] at lookup
          | some ty =>
            have same := closureTyEq_sound ty element.ty (by simpa only [resolved] using lookup)
            exact .array id layout count element (by simpa only [same] using resolved) child
      | _ => simp only [sourceReadbackPolicy] at accepted
    | enumeration ty layout info variants => simp only [sourceReadbackPolicy] at accepted
  } {
    cases plan with
    | leaf ty layout =>
      unfold sourceReadbackPolicy at accepted
      simp only [Bool.or_eq_true, Bool.and_eq_true] at accepted
      rcases accepted with previous | special
      · rcases previous with integer | pointer
        · exact .existing (.scalar (.integer ty layout integer))
        · exact .existing (.scalar (.pointer ty layout pointer))
      · cases ty with
        | Bool =>
          cases layout with
          | mk size alignment =>
            simp only [Bool.and_eq_true, beq_iff_eq] at special
            rcases special with ⟨rfl,rfl⟩
            exact .existing (.scalar .boolean)
        | Unit =>
          cases layout with
          | mk size alignment =>
            simp only [Bool.and_eq_true, beq_iff_eq] at special
            rcases special with ⟨rfl,rfl⟩
            exact .existing (.scalar .unit)
        | Vector count element =>
          simp only [Bool.and_eq_true,bne_iff_ne] at special
          exact .existing (.scalar (.vector count element layout ((vectorReadbackLane_iff element).mp special.2) special.1))
        | FatPtr kind => exact .existing (.scalar (.fat kind layout))
        | Func signature => exact .existing (.scalar (.function signature layout))
        | _ => cases special
    | fields ty layout fields =>
      unfold sourceReadbackPolicy at accepted
      simp only [Bool.and_eq_true] at accepted
      have kind := accepted.1
      have children := (policyFields_iff source ctx fields).mp accepted.2
      have shapes : ∀ offset child, (offset,child) ∈ fields → SourceNominalReadbackShape source ctx child := by
        intro offset child member
        exact sourceReadbackPolicy_sound source ctx child (children (offset,child) member)
      cases ty with
      | Tuple types => exact .tuple types layout fields shapes
      | Struct id => exact .nominal id layout fields (selectedStructAgrees_sound source ctx id kind) shapes
      | _ => cases kind
    | array ty layout count element =>
      cases ty with
      | Array id declared =>
        unfold sourceReadbackPolicy at accepted
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at accepted
        have census : declared = count := accepted.1
        subst declared
        rcases accepted.2 with empty | nonempty
        · have empty : count = 0 := empty
          subst count
          exact .emptyArray id layout element
        · have lookup := nonempty.1
          have child := sourceReadbackPolicy_sound source ctx element nonempty.2
          cases resolved : ctx.types id with
          | none => simp only [resolved] at lookup; cases lookup
          | some ty =>
            have same := closureTyEq_sound ty element.ty (by simpa only [resolved] using lookup)
            exact .array id layout count element (by simpa only [same] using resolved) child
      | _ => simp only [sourceReadbackPolicy] at accepted; cases accepted
    | enumeration ty layout info variants => simp only [sourceReadbackPolicy] at accepted; cases accepted
  }

termination_by sizeOf plan
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have inside := List.sizeOf_lt_of_mem member; simp_all; omega)
    | (simp_all; omega)

theorem scalarReadbackPolicy_complete {plan : Plan} (shape : ScalarReadbackPlan plan)
    (source : Environment) (ctx : EvalContext) : sourceReadbackPolicy source ctx plan = true := by
  cases shape <;> simp [sourceReadbackPolicy, vectorReadbackLane_iff, *]

theorem sourceReadbackShape_policy_complete {ctx : EvalContext} {plan : Plan}
    (shape : SourceReadbackShape ctx plan) (source : Environment)
    (origin : Plan.Origin (SourceElement source) (ActualSummary source) plan.ty plan) :
    sourceReadbackPolicy source ctx plan = true := by
  induction shape with
  | scalar scalar => exact scalarReadbackPolicy_complete scalar source ctx
  | tuple types layout fields _children ih =>
    rw [sourceReadbackPolicy]
    simp only [Bool.true_and]
    apply (policyFields_iff source ctx fields).mpr
    intro field member
    exact ih field.1 field.2 member ((origin.tuple_types_and_children).2 field member)
  | array id layout count element resolved _child ih =>
    have childOrigin : Plan.Origin (SourceElement source) (ActualSummary source) element.ty element := by
      cases origin with
      | array _ _ _ _ child _ _ _ _ => exact child
    simp [sourceReadbackPolicy, resolved, closureTyEq_refl, ih childOrigin]
  | emptyArray id layout element => simp [sourceReadbackPolicy]

theorem selectedStructAgrees_complete {source : Environment} {ctx : EvalContext} {id : StructId}
    {layout : MemoryTypeLayout} {fields : List (Nat × Plan)}
    (origin : Plan.Origin (SourceElement source) (ActualSummary source) (.Struct id) (.fields (.Struct id) layout fields))
    (agreement : StructContextAgreement source ctx id) : selectedStructAgrees source ctx id = true := by
  obtain ⟨value,actual,_extent,_children,_bindings,_sizes⟩ := origin.fields_metadata_view
  obtain ⟨_before,_next,history,queried⟩ := actual
  obtain ⟨position,definition,selected,row,_identity,_typed⟩ := history.query_struct_origin .execution id value queried
  change (Index.ofEnvironment source).structPositions.find id.index = some position at selected
  simp only [selectedStructAgrees, selected, row]
  exact decide_eq_true (agreement position definition selected row)

/-- Completeness is relative to the existing proved readback policy and a real
    source origin. Unsupported families are not silently granted new laws. -/
theorem sourceNominalReadbackShape_policy_complete {source : Environment} {ctx : EvalContext} {plan : Plan}
    (shape : SourceNominalReadbackShape source ctx plan)
    (origin : Plan.Origin (SourceElement source) (ActualSummary source) plan.ty plan) :
    sourceReadbackPolicy source ctx plan = true := by
  induction shape with
  | existing existing => exact sourceReadbackShape_policy_complete existing source origin
  | nominal id layout fields agreement _children ih =>
    obtain ⟨_definition,_resolved,_typed,origins⟩ := origin.struct_types_and_children agreement
    rw [sourceReadbackPolicy]
    simp only [Bool.and_eq_true]
    exact ⟨selectedStructAgrees_complete origin agreement, (policyFields_iff source ctx fields).mpr (by
      intro field member
      exact ih field.1 field.2 member (origins field member))⟩
  | tuple types layout fields _children ih =>
    rw [sourceReadbackPolicy]
    simp only [Bool.true_and]
    apply (policyFields_iff source ctx fields).mpr
    intro field member
    exact ih field.1 field.2 member ((origin.tuple_types_and_children).2 field member)
  | array id layout count element resolved _child ih =>
    have childOrigin : Plan.Origin (SourceElement source) (ActualSummary source) element.ty element := by
      cases origin with
      | array _ _ _ _ child _ _ _ _ => exact child
    simp [sourceReadbackPolicy, resolved, closureTyEq_refl, ih childOrigin]
  | emptyArray id layout element => simp [sourceReadbackPolicy]

theorem sourceReadbackPolicy_iff (source : Environment) (ctx : EvalContext) (plan : Plan)
    (origin : Plan.Origin (SourceElement source) (ActualSummary source) plan.ty plan) :
    sourceReadbackPolicy source ctx plan = true ↔ SourceNominalReadbackShape source ctx plan :=
  ⟨sourceReadbackPolicy_sound source ctx plan, fun shape => sourceNominalReadbackShape_policy_complete shape origin⟩

/-- The prepared entry point derives its recursive policy certificate by actual
    executable classification, then uses the real source checker and store. -/
theorem prepared_policy_checked_value_readback (source : Environment) (roots : List Ty) (ty : Ty) (plan : Plan)
    (prepared : (prepare source roots).query ty = .ok plan) (ctx : EvalContext)
    (accepted : sourceReadbackPolicy source ctx plan = true)
    (memory : Memory) (input : Value) (stored : Image)
    (checked : checkClosureValue ctx plan.ty input = .ok ())
    (encoded : encode ctx.byteModel ctx.functionOrder plan input false = .ok stored) :
    ∃ output, decode ctx.byteModel ctx.functionOrder memory plan stored.bytes = .ok output ∧
      ValueReadback ctx.byteModel memory input output :=
  prepared_checked_nominal_value_readback source roots ty plan prepared ctx
    (sourceReadbackPolicy_sound source ctx plan accepted) memory input stored checked encoded

end TrustIr.AggregateMemory
