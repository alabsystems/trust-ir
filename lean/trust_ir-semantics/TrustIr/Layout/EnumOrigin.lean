-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Layout.Metadata
import TrustIr.Layout.Inhabit

namespace TrustIr.SourceLayout

/-- A successful real enum finalizer with the exact source definition and
    the exact flag computation used by preparation. The finalizer arguments are retained; authenticity of each child field
    layout is a separate property. -/
def EnumOrigin (index : Index) (facts : NatIndexTree Unit) (mode : Mode) (definition : EnumDef) (value : Summary) : Prop :=
  ∃ tag values children, canonicalTag definition = some tag ∧
    discriminants definition = some values ∧ EnumConstruction mode definition tag values
      (definition.variants.map (fun variant => variantUninhabited index facts variant.fields)) children value

/-- Only reserved original enum slots impose this obligation. Dynamic/type/
    struct/closure nodes are not silently treated as nominal enum origins. -/
def EnumSourceAt (index : Index) (facts : NatIndexTree Unit) (node : Nat) (value : Summary) : Prop :=
  ∀ mode position definition, position < index.enumCount →
    trustIrListGet? index.source.enums position = some definition →
    node = index.node mode (index.enumBase + position) → EnumOrigin index facts mode definition value

abbrev Graph.EnumOriginInvariant (index : Index) (facts : NatIndexTree Unit) (graph : Graph) :=
  graph.IndexedInvariant (EnumSourceAt index facts)

theorem Index.node_injective (index : Index) (leftMode rightMode : Mode) (left right : Nat)
    (leftBound : left < index.count) (rightBound : right < index.count)
    (same : index.node leftMode left = index.node rightMode right) :
    leftMode = rightMode ∧ left = right := by
  cases leftMode <;> cases rightMode <;> simp only [Index.node, show (Mode.shape == Mode.shape) = true from rfl,
    show (Mode.execution == Mode.shape) = false from rfl, ite_true, Bool.false_eq_true, ite_false, Nat.zero_add] at same
  all_goals constructor <;> first | rfl | omega

theorem EnumSourceAt.above (index : Index) (facts : NatIndexTree Unit) (node : Nat)
    (outside : 2 * index.count ≤ node) (value : Summary) : EnumSourceAt index facts node value := by
  intro mode position definition bound _row same
  have slot : index.enumBase + position < index.count := by
    unfold Index.count Index.closureBase
    omega
  have inside : index.node mode (index.enumBase + position) < 2 * index.count := by
    cases mode <;> simp only [Index.node, show (Mode.shape == Mode.shape) = true from rfl,
      show (Mode.execution == Mode.shape) = false from rfl, ite_true, Bool.false_eq_true, ite_false, Nat.zero_add] <;> omega
  rw [← same] at inside
  omega

theorem EnumSourceAt.other_slot (index : Index) (facts : NatIndexTree Unit) (mode : Mode) (slot : Nat)
    (inside : slot < index.count) (outside : slot < index.enumBase ∨ index.closureBase ≤ slot)
    (value : Summary) : EnumSourceAt index facts (index.node mode slot) value := by
  intro otherMode position definition bound _row same
  have target : index.enumBase + position < index.count := by
    unfold Index.count Index.closureBase
    omega
  have equal := (index.node_injective mode otherMode slot _ inside target same).2
  unfold Index.closureBase at outside
  rcases outside with before | after <;> omega

theorem Equation.Executes.enum_origin (index : Index) (facts : NatIndexTree Unit) (mode : Mode)
    (definition : EnumDef) (nodes : List Nat) (graph : Graph) (value : Summary)
    (run : (enumEquation mode definition
      (definition.variants.map (fun variant => variantUninhabited index facts variant.fields)) nodes).Executes graph value) :
    EnumOrigin index facts mode definition value := by
  cases authored : definition.layout with
  | none =>
    obtain ⟨tag, values, children, tagged, numbered, _collected, constructed⟩ :=
      run.canonicalEnum_view mode definition _ nodes authored
    exact ⟨tag, values, children.reverse, tagged, numbered, constructed⟩
  | some descriptor =>
    obtain ⟨tag, values, children, tagged, numbered, _admitted, _collected, constructed⟩ :=
      run.descriptorEnum_view mode definition _ nodes descriptor authored
    exact ⟨tag, values, children.reverse, tagged, numbered, constructed⟩

theorem Equation.IndexedRule.enum_origin (index : Index) (facts : NatIndexTree Unit) (mode : Mode)
    (definition : EnumDef) (position : Nat) (bound : position < index.enumCount)
    (row : trustIrListGet? index.source.enums position = some definition) (nodes : List Nat) :
    (enumEquation mode definition
      (definition.variants.map (fun variant => variantUninhabited index facts variant.fields)) nodes).IndexedRule
      (EnumSourceAt index facts) (index.node mode (index.enumBase + position)) := by
  apply Equation.IndexedRule.guarded
  intro graph value run otherMode otherPosition otherDefinition otherBound otherRow same
  have left : index.enumBase + position < index.count := by unfold Index.count Index.closureBase; omega
  have right : index.enumBase + otherPosition < index.count := by unfold Index.count Index.closureBase; omega
  have equal := index.node_injective mode otherMode _ _ left right same
  have modes := equal.1
  subst otherMode
  have slots := equal.2
  have positions : position = otherPosition := by omega
  subst otherPosition
  have definitions := Option.some.inj (row.symm.trans otherRow)
  subst otherDefinition
  exact run.enum_origin index facts mode definition nodes graph value

theorem EnumOrigin.flags {index : Index} {facts : NatIndexTree Unit} {mode : Mode} {definition : EnumDef} {value : Summary}
    (origin : EnumOrigin index facts mode definition value) (enumeration : Enumeration)
    (present : value.enumeration = some enumeration) :
    enumeration.uninhabited = definition.variants.map (fun variant => variantUninhabited index facts variant.fields) := by
  obtain ⟨tag, values, children, _tagged, _numbered, constructed⟩ := origin
  cases authored : definition.layout with
  | none =>
    obtain ⟨offset, extent, size, _placed, _bounded, _rounded, finished⟩ := constructed.canonical_view authored
    rw [((finish_ok_iff mode _ value).mp finished).1] at present
    cases present
    rfl
  | some descriptor =>
    rw [constructed.descriptor_exact descriptor authored] at present
    cases present
    rfl

/-- Exact logical tag and effective discriminants retained by the real finalizer. -/
theorem EnumOrigin.tag_data {index : Index} {facts : NatIndexTree Unit} {mode : Mode} {definition : EnumDef} {value : Summary}
    (origin : EnumOrigin index facts mode definition value) (enumeration : Enumeration)
    (present : value.enumeration = some enumeration) :
    canonicalTag definition = some enumeration.tag ∧ discriminants definition = some enumeration.discriminants := by
  obtain ⟨tag,values,children,tagged,numbered,constructed⟩ := origin
  cases authored : definition.layout with
  | none =>
    obtain ⟨offset,extent,size,_placed,_bounded,_rounded,finished⟩ := constructed.canonical_view authored
    rw [((finish_ok_iff mode _ value).mp finished).1] at present
    cases present
    exact ⟨tagged,numbered⟩
  | some descriptor =>
    rw [constructed.descriptor_exact descriptor authored] at present
    cases present
    exact ⟨tagged,numbered⟩

end TrustIr.SourceLayout
