-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceEnumImage
import TrustIr.Proofs.SourceLayoutCorrespondence

/- Enable kernel reduction through the imported mutual compiler equations.
The metadata is local to these proofs; no executable definition is replaced. -/
run_cmd do
  if Lean.versionString == "4.30.0-rc2" then
    let env ← Lean.getEnv
    let mut registered := 0
    for (n, _) in env.constants.map₁.toList do
      if n.toString.endsWith "TrustIr.SourceLayout.compileTy.eq_def" ||
         n.toString.endsWith "TrustIr.SourceLayout.compileTypes.eq_def" then
        Lean.Elab.Command.elabCommand (← `(command| attribute [local cbv_eval] $(Lean.mkIdent n):ident))
        registered := registered + 1
    unless registered == 2 do
      Lean.throwError "expected the two original layout compiler equations"
  else if Lean.versionString != "4.8.0" then
    Lean.throwError "unsupported compiler for layout equation reduction"

namespace TrustIr.AggregateMemory
open SourceLayout

/-- Actual successful source queries have one complete summary for each type. -/
theorem ActualSummary.functional {source : Environment} {ty : Ty} {first second : Summary}
    (left : ActualSummary source ty first) (right : ActualSummary source ty second) : first = second := by
  obtain ⟨before,next,history,run⟩ := left
  obtain ⟨other,otherNext,otherHistory,otherRun⟩ := right
  exact history.forked_typed_summary otherHistory .execution ty first second run otherRun

theorem prepared_plan_layout_unique (source : Environment) (leftRoots rightRoots : List Ty)
    (ty : Ty) (left right : Plan)
    (leftRun : (prepare source leftRoots).query ty = .ok left)
    (rightRun : (prepare source rightRoots).query ty = .ok right) :
    left.layout.size = right.layout.size ∧ left.layout.alignment = right.layout.alignment := by
  obtain ⟨first,leftActual,leftSize,leftAlign⟩ :=
    (prepared_plan_origin source leftRoots ty left leftRun).layout_view
  obtain ⟨second,rightActual,rightSize,rightAlign⟩ :=
    (prepared_plan_origin source rightRoots ty right rightRun).layout_view
  have same := leftActual.functional rightActual
  cases same
  exact ⟨leftSize.trans rightSize.symm,Option.some.inj (leftAlign.symm.trans rightAlign)⟩

/-- An independently queried typed element agrees with its original source
row, including rows installed by copying and by a forward-reference alias. -/
theorem ActualSummary.prepared_type_row {source : Environment} {ty : Ty} {value original : Summary}
    (actual : ActualSummary source ty value) (position : Nat)
    (found : (trustIrListGet? source.types position) = some (some ty))
    (derived : NodeDerivation (SourceLayout.prepare source).graph
      ((Index.ofEnvironment source).node .execution position) original) : original = value := by
  obtain ⟨before,next,history,run⟩ := actual
  exact history.prepared_type_summary .execution position ty original value found derived run

/-- Array scaling is tied to the actual independently queried element type;
no parent/child size-consistency premise is supplied by the caller. -/
theorem ActualSummary.array_element_extent {source : Environment} {id : TyId} {count : Nat}
    {ty : Ty} {parent child : Summary} (array : ActualSummary source (.Array id count) parent)
    (element : ActualSummary source ty child) (resolved : SourceElement source id ty) :
    parent.size = child.size * count ∧ parent.align = child.align ∧ count ≤ word64Max := by
  obtain ⟨before,next,history,run⟩ := array
  obtain ⟨original,derived,size,align,bound⟩ := history.query_array_prepared_child .execution id count parent run
  have same := element.prepared_type_row id.index resolved.row derived
  cases same
  exact ⟨size,align,bound⟩

/-- Actual array origins authenticate the retained child stride against the
parent extent, even across independent source-query and cache histories. -/
theorem Plan.Origin.source_array_extent {source : Environment} {id : TyId}
    {layout : MemoryTypeLayout} {count : Nat} {element : Plan}
    (origin : Plan.Origin (SourceElement source) (ActualSummary source) (.Array id count)
      (.array (.Array id count) layout count element)) :
    layout.size = element.layout.size * count ∧ layout.alignment = element.layout.alignment ∧ count ≤ word64Max := by
  obtain ⟨actualId,same,_,resolved,childOrigin,parent,parentActual,parentSize,parentAlign⟩ := origin.array_binding_view
  have sameId : actualId = id := by cases same; rfl
  subst actualId
  obtain ⟨child,childActual,childSize,childAlign⟩ := childOrigin.layout_view
  obtain ⟨size,align,bound⟩ := parentActual.array_element_extent childActual resolved
  refine ⟨parentSize.trans (size.trans (congrArg (fun n => n * count) childSize.symm)),?_,bound⟩
  exact Option.some.inj (parentAlign.symm.trans (align.trans childAlign))

theorem prepared_array_element_extent (source : Environment) (roots : List Ty) (id : TyId)
    (layout : MemoryTypeLayout) (count : Nat) (element : Plan)
    (run : (prepare source roots).query (.Array id count) = .ok (.array (.Array id count) layout count element)) :
    layout.size = element.layout.size * count ∧ layout.alignment = element.layout.alignment ∧ count ≤ word64Max :=
  (prepared_plan_origin source roots (.Array id count) _ run).source_array_extent

/-- Full array summaries agree across independently reached source sessions. -/
theorem ActualSummary.array_unique {source : Environment} {id : TyId} {count : Nat} {first second : Summary}
    (left : ActualSummary source (.Array id count) first) (right : ActualSummary source (.Array id count) second) :
    first = second := left.functional right

/-- Different root-preparation lists and cache histories cannot change an
actual array plan's parent layout. Child/source correspondence remains separate. -/
theorem prepared_array_layout_unique (source : Environment) (leftRoots rightRoots : List Ty)
    (id : TyId) (count : Nat) (left right : Plan)
    (leftRun : (prepare source leftRoots).query (.Array id count) = .ok left)
    (rightRun : (prepare source rightRoots).query (.Array id count) = .ok right) :
    left.layout.size = right.layout.size ∧ left.layout.alignment = right.layout.alignment :=
  prepared_plan_layout_unique source leftRoots rightRoots (.Array id count) left right leftRun rightRun

/-- Every actual retained plan exposes its own typed source-query extent. -/
theorem prepared_plan_query_extent (source : Environment) (roots : List Ty) (ty : Ty) (plan : Plan)
    (run : (prepare source roots).query ty = .ok plan) :
    ∃ value, ActualSummary source ty value ∧ plan.layout.size = value.size ∧
      value.align = some plan.layout.alignment :=
  (prepared_plan_origin source roots ty plan run).layout_view

/-- Exact compiled field positions retain queried field types/offsets and the
    actual typed child-query extent. Equality to each parent field's stored
    size remains a separate cross-query consistency obligation. -/
theorem prepared_enum_field_queries (source : Environment) (roots : List Ty) (id : EnumId)
    (plan : Plan) (run : (prepare source roots).query (.Enum id) = .ok plan) :
    ∃ layout info variants value,
      plan = .enumeration (.Enum id) layout info variants ∧
      ActualSummary source (.Enum id) value ∧ value.enumeration = some info ∧
      (layout.size = value.size ∧ value.align = some layout.alignment) ∧
      ∀ position fields, (trustIrListGet? variants position) = some (some fields) →
        ∃ sourceFields, (trustIrListGet? info.variants position) = some sourceFields ∧
          FieldBindings (sourceFields.map (·.ty)) (sourceFields.map (·.offset)) fields ∧
          ∀ fieldPosition offset child, (trustIrListGet? fields fieldPosition) = some (offset,child) →
            ∃ sourceField childValue, (trustIrListGet? sourceFields fieldPosition) = some sourceField ∧
              child.ty = sourceField.ty ∧ offset = sourceField.offset ∧
              ActualSummary source sourceField.ty childValue ∧
              child.layout.size = childValue.size ∧ childValue.align = some child.layout.alignment := by
  trustIrCompilerProof {
    obtain ⟨layout,info,variants,value,shape,actual,present,extent,children,bindings⟩ :=
      (prepared_plan_origin source roots (.Enum id) plan run).enum_binding_view
    refine ⟨layout,info,variants,value,shape,actual,present,extent,?_⟩
    intro position fields found
    obtain ⟨sourceFields,sourceRow,fieldBindings⟩ := bindings.source_at position fields found
    refine ⟨sourceFields,sourceRow,fieldBindings,?_⟩
    intro fieldPosition offset child fieldRow
    obtain ⟨sourceField,sourceFieldRow,typed,placed⟩ := fieldBindings.source_child fieldPosition offset child fieldRow
    obtain ⟨inside,fieldGet⟩ := List.get?_eq_some.mp fieldRow
    have member : (offset,child) ∈ fields := List.mem_iff_get.mpr ⟨⟨fieldPosition,inside⟩,fieldGet⟩
    obtain ⟨childValue,childActual,childExtent,childAlign⟩ :=
      (children.children_at position fields found (offset,child) member).layout_view
    rw [typed] at childActual
    exact ⟨sourceField,childValue,sourceFieldRow,typed,placed,childActual,childExtent,childAlign⟩
  } {
    obtain ⟨layout,info,variants,value,shape,actual,present,extent,children,bindings⟩ :=
      (prepared_plan_origin source roots (.Enum id) plan run).enum_binding_view
    refine ⟨layout,info,variants,value,shape,actual,present,extent,?_⟩
    intro position fields found
    obtain ⟨sourceFields,sourceRow,fieldBindings⟩ := bindings.source_at position fields found
    refine ⟨sourceFields,sourceRow,fieldBindings,?_⟩
    intro fieldPosition offset child fieldRow
    obtain ⟨sourceField,sourceFieldRow,typed,placed⟩ := fieldBindings.source_child fieldPosition offset child fieldRow
    have member : (offset,child) ∈ fields := CompilerCompat.listGetConstructive_mem fieldRow
    obtain ⟨childValue,childActual,childExtent,childAlign⟩ :=
      (children.children_at position fields found (offset,child) member).layout_view
    rw [typed] at childActual
    exact ⟨sourceField,childValue,sourceFieldRow,typed,placed,childActual,childExtent,childAlign⟩
  }

end TrustIr.AggregateMemory

namespace TrustIr.AggregateMemory.FieldBindingControls
open SourceLayout

private def arraySource : Environment := { types := [some .U16] }
private def arrayPlan : Plan := .array (.Array ⟨0⟩ 3) ⟨6,2⟩ 3 (.leaf .U16 ⟨2,2⟩)

private def tupleTy : Ty := .Tuple [.U8,.Bool,.U16]
private def tuplePlan : Plan := .fields tupleTy ⟨4,2⟩
  [(0,.leaf .U8 ⟨1,1⟩),(1,.leaf .Bool ⟨1,1⟩),(2,.leaf .U16 ⟨2,2⟩)]

theorem tuple_plan_after_byte_preparation :
    (prepare arraySource [.U8]).query tupleTy = .ok tuplePlan := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem tuple_plan_after_wide_and_array_preparation :
    (prepare arraySource [.U64,.Array ⟨0⟩ 5]).query tupleTy = .ok tuplePlan := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem array_plan_after_byte_preparation :
    (prepare arraySource [.U8]).query (.Array ⟨0⟩ 3) = .ok arrayPlan := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem array_plan_after_wide_and_other_count_preparation :
    (prepare arraySource [.U64,.Array ⟨0⟩ 5]).query (.Array ⟨0⟩ 3) = .ok arrayPlan := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

private def byte : Plan := .leaf .U8 ⟨1,1⟩
private def bool : Plan := .leaf .Bool ⟨1,1⟩
private def wide : Plan := .leaf .U8 ⟨2,1⟩
private def summary : Summary := { size := 1, align := some 1 }

/-- Equal byte size does not authenticate a field's source type. -/
theorem same_size_wrong_type_refuses : ¬ FieldBindings [.U8] [0] [(0,bool)] := by
  intro bindings
  have types := bindings.1
  cases types

theorem wrong_offset_refuses : ¬ FieldBindings [.U8] [1] [(2,byte)] := by
  intro bindings
  have offsets := bindings.2
  cases offsets

theorem swapped_same_size_fields_refuse : ¬ FieldBindings [.U8,.Bool] [0,1] [(0,bool),(1,byte)] := by
  intro bindings
  have types := bindings.1
  cases types

theorem missing_child_refuses : ¬ FieldBindings [.U8] [0] [] := by
  intro bindings
  have types := bindings.1
  cases types

/-- Descriptor-only Never fields remain omitted in a genuinely dead row. -/
theorem dead_row_does_not_compile_never : VariantBindings [[.Never]] [[]] [true] [none] :=
  .omitted [.Never] [] .nil

theorem live_row_cannot_disappear : ¬ VariantBindings [[.U8]] [[0]] [false] [none] := by
  intro bindings
  cases bindings

/-- Exact type/offset bindings alone are weaker than a typed query extent. -/
theorem right_type_and_offset_do_not_authenticate_size :
    FieldBindings [.U8] [0] [(0,wide)] ∧
    ¬ Plan.Origin (fun _ _ => True) (fun _ actual => actual = summary) .U8 wide := by
  refine ⟨⟨rfl,rfl⟩,?_⟩
  intro origin
  obtain ⟨value,actual,extent,aligned⟩ := origin.layout_view
  subst value
  have wrong : 2 = 1 := extent
  cases wrong

theorem wrong_child_alignment_refuses :
    ¬ Plan.Origin (fun _ _ => True) (fun _ actual => actual = summary) .U8 (.leaf .U8 ⟨1,2⟩) := by
  intro origin
  obtain ⟨value,actual,extent,aligned⟩ := origin.layout_view
  subst value
  have wrong : (some 1 : Option Nat) = some 2 := aligned
  cases wrong

theorem tuple_types_follow_original_input :
    Plan.fieldInputTypes (.Tuple [.U8,.Bool])
      { size := 2, align := some 1,
        fields := [{ ty := .Bool, offset := 0, size := 1, align := 1 },
                   { ty := .U8, offset := 1, size := 1, align := 1 }] } = [.U8,.Bool] := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

end TrustIr.AggregateMemory.FieldBindingControls
