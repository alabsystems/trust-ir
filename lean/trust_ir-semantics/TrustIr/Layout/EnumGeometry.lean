-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Layout.Geometry
import TrustIr.Layout.Extension

namespace TrustIr.SourceLayout

theorem Field.Separated.translate (offset : Nat) {left right : Field} (safe : left.Separated right) :
    ({ left with offset := offset + left.offset } : Field).Separated
      { right with offset := offset + right.offset } := by
  rcases safe with zero | zero | before | after
  · exact .inl zero
  · exact .inr (.inl zero)
  · apply Or.inr; apply Or.inr; apply Or.inl; dsimp; omega
  · apply Or.inr; apply Or.inr; apply Or.inr; dsimp; omega

theorem FieldsSeparated.translate (offset : Nat) {fields : List Field} (safe : FieldsSeparated fields) :
    FieldsSeparated (fields.map (fun field => { field with offset := offset + field.offset })) := by
  induction fields with
  | nil => trivial
  | cons first rest ih =>
    refine ⟨?_, ih safe.2⟩
    intro field member
    rcases List.mem_map.mp member with ⟨original, present, same⟩
    subst field
    exact (safe.1 original present).translate offset

theorem FieldsContained.translate (offset : Nat) {size : Nat} {fields : List Field}
    (safe : FieldsContained size fields) :
    FieldsContained (offset + size) (fields.map (fun field => { field with offset := offset + field.offset })) := by
  intro field member
  rcases List.mem_map.mp member with ⟨original, present, same⟩
  subst field
  have bound := safe original present
  dsimp
  omega

theorem FieldsContained.weaken {small large : Nat} {fields : List Field}
    (safe : FieldsContained small fields) (bound : small ≤ large) : FieldsContained large fields :=
  fun field member => Nat.le_trans (safe field member) bound

theorem payload_field_lower_bound (offset : Nat) (variants : List Summary) (fields : List Field)
    (variant : fields ∈ placePayload offset variants) (field : Field) (present : field ∈ fields) :
    offset ≤ field.offset := by
  rcases List.mem_map.mp variant with ⟨summary, member, same⟩
  subst fields
  rcases List.mem_map.mp present with ⟨original, member, same⟩
  subst field
  dsimp
  omega

private theorem fold_max_monotone (variants : List Summary) (initial : Nat) :
    initial ≤ variants.foldl (fun out value => max out value.size) initial := by
  induction variants generalizing initial with
  | nil => exact Nat.le_refl _
  | cons first rest ih =>
    exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

theorem variant_size_le_payload (variants : List Summary) (summary : Summary) (member : summary ∈ variants) :
    summary.size ≤ variants.foldl (fun out value => max out value.size) 0 := by
  have bound : ∀ initial, summary.size ≤ variants.foldl (fun out value => max out value.size) initial := by
    induction variants with
    | nil => cases member
    | cons first rest ih =>
      intro initial
      cases member with
      | head => exact Nat.le_trans (Nat.le_max_right _ _) (fold_max_monotone rest _)
      | tail _ later => exact ih later _
  exact bound 0

/-- Every logical variant has non-overlapping storage contained in the enum.
This says nothing about field typing, discriminant authenticity or codecs. -/
def EnumerationGeometry (value : Summary) : Prop :=
  ∀ enumeration, value.enumeration = some enumeration →
    ∀ fields, fields ∈ enumeration.variants → FieldsSeparated fields ∧ FieldsContained value.size fields

theorem placePayload_geometry (offset size : Nat) (variants : List Summary)
    (children : ∀ summary, summary ∈ variants → FieldGeometry summary)
    (bound : offset + variants.foldl (fun out value => max out value.size) 0 ≤ size) :
    ∀ fields, fields ∈ placePayload offset variants → FieldsSeparated fields ∧ FieldsContained size fields := by
  intro fields member
  rcases List.mem_map.mp member with ⟨summary, present, same⟩
  subst fields
  have child := children summary present
  exact ⟨child.1.translate offset, (child.2.translate offset).weaken
    (by have sizeBound := variant_size_le_payload variants summary present; omega)⟩

theorem EnumConstruction.canonical_geometry {mode : Mode} {definition : EnumDef} {tag : EnumTagRepr}
    {values : List Int} {uninhabited : List Bool} {variants : List Summary} {output : Summary}
    (constructed : EnumConstruction mode definition tag values uninhabited variants output)
    (canonical : definition.layout = none)
    (children : ∀ summary, summary ∈ variants → FieldGeometry summary) :
    EnumerationGeometry output := by
  rcases constructed.canonical_view canonical with ⟨offset, extent, size, placed, bounded, rounded, finished⟩
  have same := (finish_ok_iff mode _ output).mp finished
  rw [same.1]
  intro enumeration actual fields member
  cases actual
  apply placePayload_geometry offset size variants children _ fields member
  have exactExtent := (checked_ok _ _ bounded).1
  have roundedSize := alignUp_lower_bound _ _ _ rounded
  omega

theorem EnumConstruction.canonical_tag_separated {mode : Mode} {definition : EnumDef} {tag : EnumTagRepr}
    {values : List Int} {uninhabited : List Bool} {variants : List Summary} {output : Summary}
    (constructed : EnumConstruction mode definition tag values uninhabited variants output)
    (canonical : definition.layout = none) :
    ∀ enumeration, output.enumeration = some enumeration →
      ∀ fields, fields ∈ enumeration.variants →
        ∀ field, field ∈ fields → overlap 0 (tagBits tag / 8) field.offset field.size = false := by
  rcases constructed.canonical_view canonical with ⟨offset, extent, size, placed, bounded, rounded, finished⟩
  have same := (finish_ok_iff mode _ output).mp finished
  rw [same.1]
  intro enumeration actual fields member field present
  cases actual
  have lower := payload_field_lower_bound offset variants fields member field present
  have tagBound := alignUp_lower_bound _ _ _ placed
  have separated : (tagBits tag / 8 ≤ field.offset) := by omega
  simp [overlap, Nat.not_lt.mpr separated]

private theorem member_append {α : Type} (value : α) (left right : List α) :
    value ∈ left ++ right ↔ value ∈ left ∨ value ∈ right := by
  induction left with
  | nil => simp
  | cons first rest ih => simp [List.cons_append, ih, or_assoc]

private theorem member_reverse {α : Type} (value : α) (values : List α) :
    value ∈ values.reverse ↔ value ∈ values := by
  induction values with
  | nil => simp
  | cons first rest ih => simp [List.reverse_cons, member_append, ih, or_comm]

theorem enum_children_geometry (graph : Graph) (nodes : List Nat) (first last : List Summary)
    (initial : ∀ summary, summary ∈ first → FieldGeometry summary)
    (children : ∀ node, node ∈ nodes → ∀ summary, NodeDerivation graph node summary → FieldGeometry summary)
    (steps : StepsDerivation graph
      (nodes.map (fun child => .child child fun value state => .ok (value :: state))) first last) :
    ∀ summary, summary ∈ last → FieldGeometry summary := by
  have walk : ∀ (nodes : List Nat) (first last : List Summary),
      (∀ summary, summary ∈ first → FieldGeometry summary) →
      (∀ node, node ∈ nodes → ∀ summary, NodeDerivation graph node summary → FieldGeometry summary) →
      StepsDerivation graph (nodes.map (fun child => .child child fun value state => .ok (value :: state))) first last →
      ∀ summary, summary ∈ last → FieldGeometry summary := by
    intro nodes
    induction nodes with
    | nil => intro first last initial children steps; cases steps; exact initial
    | cons node rest ih =>
      intro first last initial children steps
      cases steps with
      | child solved updated later =>
        have childGeometry := children node ((trustIrListMemConsSelf _ _)) _ solved
        cases updated
        apply ih _ _ _ (fun node member => children node (List.mem_cons_of_mem _ member)) later
        intro summary member
        cases member with
        | head => exact childGeometry
        | tail _ member => exact initial summary member
  exact walk nodes first last initial children steps

theorem enum_children_property (graph : Graph) (property : Summary → Prop) (nodes : List Nat) (first last : List Summary)
    (initial : ∀ summary, summary ∈ first → property summary)
    (children : ∀ node, node ∈ nodes → ∀ summary, NodeDerivation graph node summary → property summary)
    (steps : StepsDerivation graph
      (nodes.map (fun child => .child child fun value state => .ok (value :: state))) first last) :
    ∀ summary, summary ∈ last → property summary := by
  have walk : ∀ (nodes : List Nat) (first last : List Summary),
      (∀ summary, summary ∈ first → property summary) →
      (∀ node, node ∈ nodes → ∀ summary, NodeDerivation graph node summary → property summary) →
      StepsDerivation graph (nodes.map (fun child => .child child fun value state => .ok (value :: state))) first last →
      ∀ summary, summary ∈ last → property summary := by
    intro nodes
    induction nodes with
    | nil => intro first last initial children steps; cases steps; exact initial
    | cons node rest ih =>
      intro first last initial children steps
      cases steps with
      | child solved updated later =>
        have childGeometry := children node ((trustIrListMemConsSelf _ _)) _ solved
        cases updated
        apply ih _ _ _ (fun node member => children node (List.mem_cons_of_mem _ member)) later
        intro summary member
        cases member with
        | head => exact childGeometry
        | tail _ member => exact initial summary member
  exact walk nodes first last initial children steps

theorem Equation.Executes.canonicalEnum_geometry {graph : Graph} {output : Summary}
    (mode : Mode) (definition : EnumDef) (uninhabited : List Bool) (nodes : List Nat)
    (canonical : definition.layout = none)
    (children : ∀ node, node ∈ nodes → ∀ summary, NodeDerivation graph node summary → FieldGeometry summary)
    (run : (enumEquation mode definition uninhabited nodes).Executes graph output) :
    EnumerationGeometry output := by
  rcases run.canonicalEnum_view mode definition uninhabited nodes canonical with
    ⟨tag, values, state, tagged, numbered, steps, constructed⟩
  have collected := enum_children_geometry graph nodes [] state
    (by intro summary impossible; cases impossible) children steps
  exact constructed.canonical_geometry canonical (fun summary member =>
    collected summary ((member_reverse summary state).mp member))

theorem EnumConstruction.canonical_tag {mode : Mode} {definition : EnumDef} {tag : EnumTagRepr}
    {values : List Int} {uninhabited : List Bool} {variants : List Summary} {output : Summary}
    (constructed : EnumConstruction mode definition tag values uninhabited variants output)
    (canonical : definition.layout = none) (enumeration : Enumeration)
    (actual : output.enumeration = some enumeration) : enumeration.tag = tag := by
  rcases constructed.canonical_view canonical with ⟨offset, extent, size, placed, bounded, rounded, finished⟩
  have same := (finish_ok_iff mode _ output).mp finished
  rw [same.1] at actual
  cases actual
  rfl

theorem Equation.Executes.canonicalEnum_tag_separated {graph : Graph} {output : Summary}
    (mode : Mode) (definition : EnumDef) (uninhabited : List Bool) (nodes : List Nat)
    (canonical : definition.layout = none)
    (run : (enumEquation mode definition uninhabited nodes).Executes graph output) :
    ∀ enumeration, output.enumeration = some enumeration →
      ∀ fields, fields ∈ enumeration.variants → ∀ field, field ∈ fields →
        overlap 0 (tagBits enumeration.tag / 8) field.offset field.size = false := by
  rcases run.canonicalEnum_view mode definition uninhabited nodes canonical with
    ⟨tag, values, state, tagged, numbered, steps, constructed⟩
  intro enumeration actual fields member field present
  rw [constructed.canonical_tag canonical enumeration actual]
  exact constructed.canonical_tag_separated canonical enumeration actual fields member field present

theorem NodeDerivation.canonicalEnum_geometry {graph : Graph} {node : Nat} {output : Summary}
    (mode : Mode) (definition : EnumDef) (uninhabited : List Bool) (nodes : List Nat)
    (canonical : definition.layout = none)
    (children : ∀ child, child ∈ nodes → ∀ summary, NodeDerivation graph child summary → FieldGeometry summary)
    (found : graph.nodes.find node = some (enumEquation mode definition uninhabited nodes))
    (derived : NodeDerivation graph node output) : EnumerationGeometry output :=
  (NodeDerivation.execution found derived).canonicalEnum_geometry mode definition uninhabited nodes canonical children

theorem NodeDerivation.canonicalEnum_tag_separated {graph : Graph} {node : Nat} {output : Summary}
    (mode : Mode) (definition : EnumDef) (uninhabited : List Bool) (nodes : List Nat)
    (canonical : definition.layout = none)
    (found : graph.nodes.find node = some (enumEquation mode definition uninhabited nodes))
    (derived : NodeDerivation graph node output) :
    ∀ enumeration, output.enumeration = some enumeration →
      ∀ fields, fields ∈ enumeration.variants → ∀ field, field ∈ fields →
        overlap 0 (tagBits enumeration.tag / 8) field.offset field.size = false :=
  (NodeDerivation.execution found derived).canonicalEnum_tag_separated mode definition uninhabited nodes canonical

theorem EnumConstruction.descriptor_exact {mode : Mode} {definition : EnumDef} {tag : EnumTagRepr}
    {values : List Int} {uninhabited : List Bool} {variants : List Summary} {output : Summary}
    (constructed : EnumConstruction mode definition tag values uninhabited variants output)
    (descriptor : EnumLayoutDescriptor) (authored : definition.layout = some descriptor) :
    output = { size := descriptor.size, align := some descriptor.align, enumeration := some { tag, discriminants := values, encoding := descriptor.encoding, variants := variants.map (·.fields), uninhabited } } :=
  ((finish_ok_iff mode _ output).mp (constructed.descriptor_finish descriptor authored)).1

/-- Descriptor children must fit the actual parent size, not merely a
potentially unrelated size claimed by an arbitrary supplied child summary. -/
theorem EnumConstruction.descriptor_geometry {mode : Mode} {definition : EnumDef} {tag : EnumTagRepr}
    {values : List Int} {uninhabited : List Bool} {variants : List Summary} {output : Summary}
    (constructed : EnumConstruction mode definition tag values uninhabited variants output)
    (descriptor : EnumLayoutDescriptor) (authored : definition.layout = some descriptor)
    (children : ∀ summary, summary ∈ variants →
      FieldsSeparated summary.fields ∧ FieldsContained descriptor.size summary.fields) :
    EnumerationGeometry output := by
  rw [constructed.descriptor_exact descriptor authored]
  intro enumeration actual fields member
  cases actual
  rcases List.mem_map.mp member with ⟨summary, present, same⟩
  subst fields
  exact children summary present

private theorem any_false_iff {α : Type} (predicate : α → Bool) (values : List α) :
    values.any predicate = false ↔ ∀ value, value ∈ values → predicate value = false := by
  induction values with
  | nil => simp
  | cons first rest ih => simp [List.any_cons, Bool.or_eq_false_iff, ih, List.forall_mem_cons]

theorem EnumConstruction.direct_lane {mode : Mode} {definition : EnumDef} {tag : EnumTagRepr}
    {values : List Int} {uninhabited : List Bool} {variants : List Summary} {output : Summary}
    (constructed : EnumConstruction mode definition tag values uninhabited variants output)
    (descriptor : EnumLayoutDescriptor) (authored : definition.layout = some descriptor)
    (offset : Nat) (encoding : descriptor.encoding = .direct offset) :
    EnumLaneBounds descriptor.size descriptor.align offset (tagBits tag / 8) (tagBits tag / 8) := by
  have checks := constructed.descriptor_checks descriptor authored
  unfold EnumDescriptorChecks at checks
  rw [encoding] at checks
  exact checks.1

theorem EnumConstruction.direct_tag_separated {mode : Mode} {definition : EnumDef} {tag : EnumTagRepr}
    {values : List Int} {uninhabited : List Bool} {variants : List Summary} {output : Summary}
    (constructed : EnumConstruction mode definition tag values uninhabited variants output)
    (descriptor : EnumLayoutDescriptor) (authored : definition.layout = some descriptor)
    (offset : Nat) (encoding : descriptor.encoding = .direct offset) :
    ∀ enumeration, output.enumeration = some enumeration →
      ∀ fields, fields ∈ enumeration.variants → ∀ field, field ∈ fields →
        overlap offset (tagBits enumeration.tag / 8) field.offset field.size = false := by
  have checks := constructed.descriptor_checks descriptor authored
  unfold EnumDescriptorChecks at checks
  rw [encoding] at checks
  rw [constructed.descriptor_exact descriptor authored]
  intro enumeration actual fields member field present
  cases actual
  exact (any_false_iff _ fields).mp ((any_false_iff _ _).mp checks.2 fields member) field present

theorem EnumConstruction.niche_lane {mode : Mode} {definition : EnumDef} {tag : EnumTagRepr}
    {values : List Int} {uninhabited : List Bool} {variants : List Summary} {output : Summary}
    (constructed : EnumConstruction mode definition tag values uninhabited variants output)
    (descriptor : EnumLayoutDescriptor) (authored : definition.layout = some descriptor)
    (untagged start stop first offset : Nat) (repr : EnumTagRepr)
    (encoding : descriptor.encoding = .niche untagged start stop first offset repr) :
    EnumLaneBounds descriptor.size descriptor.align offset (tagBits repr / 8) (tagBits repr / 8) := by
  have checks := constructed.descriptor_checks descriptor authored
  unfold EnumDescriptorChecks at checks
  rw [encoding] at checks
  exact checks.2.1

theorem EnumConstruction.niche_carrier {mode : Mode} {definition : EnumDef} {tag : EnumTagRepr}
    {values : List Int} {uninhabited : List Bool} {variants : List Summary} {output : Summary}
    (constructed : EnumConstruction mode definition tag values uninhabited variants output)
    (descriptor : EnumLayoutDescriptor) (authored : definition.layout = some descriptor)
    (untagged start stop first offset : Nat) (repr : EnumTagRepr)
    (encoding : descriptor.encoding = .niche untagged start stop first offset repr) :
    ∀ enumeration, output.enumeration = some enumeration →
      ∃ field, field ∈ (trustIrListGet? enumeration.variants untagged).getD [] ∧ field.size ≠ 0 ∧
        field.offset ≤ offset ∧ offset + tagBits repr / 8 ≤ field.offset + field.size := by
  have checks := constructed.descriptor_checks descriptor authored
  unfold EnumDescriptorChecks at checks
  rw [encoding] at checks
  rw [constructed.descriptor_exact descriptor authored]
  intro enumeration actual
  cases actual
  rcases List.any_eq_true.mp checks.2.2.2.1 with ⟨field, present, accepted⟩
  refine ⟨field, present, ?_, ?_, ?_⟩
  · intro zero
    simp [zero] at accepted
  · by_cases good : field.offset ≤ offset
    · exact good
    · simp [good] at accepted
  · by_cases good : offset + tagBits repr / 8 ≤ field.offset + field.size
    · exact good
    · simp [good] at accepted

theorem EnumConstruction.niche_other_fields_separated {mode : Mode} {definition : EnumDef} {tag : EnumTagRepr}
    {values : List Int} {uninhabited : List Bool} {variants : List Summary} {output : Summary}
    (constructed : EnumConstruction mode definition tag values uninhabited variants output)
    (descriptor : EnumLayoutDescriptor) (authored : definition.layout = some descriptor)
    (untagged start stop first offset : Nat) (repr : EnumTagRepr)
    (encoding : descriptor.encoding = .niche untagged start stop first offset repr) :
    ∀ enumeration, output.enumeration = some enumeration →
      ∀ fields position, (fields, position) ∈ numbered enumeration.variants →
        position ≠ untagged → start ≤ position → position ≤ stop →
        ∀ field, field ∈ fields → overlap offset (tagBits repr / 8) field.offset field.size = false := by
  have checks := constructed.descriptor_checks descriptor authored
  unfold EnumDescriptorChecks at checks
  rw [encoding] at checks
  rw [constructed.descriptor_exact descriptor authored]
  intro enumeration actual fields position member other lower upper field present
  cases actual
  have row := (any_false_iff _ _).mp checks.2.2.2.2 (fields, position) member
  have gate : (position != untagged && start ≤ position && position ≤ stop) = true := by simp [other, lower, upper]
  simp only [gate, Bool.true_and] at row
  exact (any_false_iff _ fields).mp row field present

theorem enum_children_length (graph : Graph) (nodes : List Nat) (first last : List Summary)
    (steps : StepsDerivation graph
      (nodes.map (fun child => .child child fun value state => .ok (value :: state))) first last) :
    last.length = first.length + nodes.length := by
  have walk : ∀ (nodes : List Nat) (first last : List Summary),
      StepsDerivation graph (nodes.map (fun child => .child child fun value state => .ok (value :: state))) first last →
      last.length = first.length + nodes.length := by
    intro nodes
    induction nodes with
    | nil => intro first last steps; cases steps; rfl
    | cons node rest ih =>
      intro first last steps
      cases steps with
      | child solved updated later =>
        cases updated
        have tail := ih _ _ later
        simp only [List.length_cons] at tail ⊢
        omega
  exact walk nodes first last steps

theorem Equation.Executes.descriptorEnum_header {graph : Graph} {output : Summary}
    (mode : Mode) (definition : EnumDef) (uninhabited : List Bool) (nodes : List Nat)
    (descriptor : EnumLayoutDescriptor) (authored : definition.layout = some descriptor)
    (run : (enumEquation mode definition uninhabited nodes).Executes graph output) :
    powerOfTwo descriptor.align = true ∧ descriptor.size % descriptor.align = 0 ∧
      descriptor.variantFieldOffsets.length = nodes.length := by
  rcases run.descriptorEnum_view mode definition uninhabited nodes descriptor authored with
    ⟨tag, values, state, tagged, numbered, admitted, steps, constructed⟩
  have power : powerOfTwo descriptor.align = true := by
    cases h : powerOfTwo descriptor.align <;> simp_all
  have multiple : descriptor.size % descriptor.align = 0 := by
    by_cases good : descriptor.size % descriptor.align = 0
    · exact good
    · simp [good] at admitted
  have count : descriptor.variantFieldOffsets.length = nodes.length := by
    by_cases good : descriptor.variantFieldOffsets.length = nodes.length
    · exact good
    · simp [good] at admitted
  exact ⟨power, multiple, count⟩

theorem Equation.Executes.descriptorEnum_geometry {graph : Graph} {output : Summary}
    (mode : Mode) (definition : EnumDef) (uninhabited : List Bool) (nodes : List Nat)
    (descriptor : EnumLayoutDescriptor) (authored : definition.layout = some descriptor)
    (children : ∀ node, node ∈ nodes → ∀ summary, NodeDerivation graph node summary →
      FieldsSeparated summary.fields ∧ FieldsContained descriptor.size summary.fields)
    (run : (enumEquation mode definition uninhabited nodes).Executes graph output) :
    EnumerationGeometry output := by
  rcases run.descriptorEnum_view mode definition uninhabited nodes descriptor authored with
    ⟨tag, values, state, tagged, numbered, admitted, steps, constructed⟩
  have collected := enum_children_property graph
    (fun summary => FieldsSeparated summary.fields ∧ FieldsContained descriptor.size summary.fields) nodes [] state
    (by intro summary impossible; cases impossible) children steps
  exact constructed.descriptor_geometry descriptor authored (fun summary member =>
    collected summary ((member_reverse summary state).mp member))

theorem Equation.Executes.descriptorEnum_variant_count {graph : Graph} {output : Summary}
    (mode : Mode) (definition : EnumDef) (uninhabited : List Bool) (nodes : List Nat)
    (descriptor : EnumLayoutDescriptor) (authored : definition.layout = some descriptor)
    (run : (enumEquation mode definition uninhabited nodes).Executes graph output) :
    ∀ enumeration, output.enumeration = some enumeration →
      enumeration.variants.length = descriptor.variantFieldOffsets.length := by
  rcases run.descriptorEnum_view mode definition uninhabited nodes descriptor authored with
    ⟨tag, values, state, tagged, numbered, admitted, steps, constructed⟩
  have count := (run.descriptorEnum_header mode definition uninhabited nodes descriptor authored).2.2
  have collected := enum_children_length graph nodes [] state steps
  rw [constructed.descriptor_exact descriptor authored]
  intro enumeration actual
  cases actual
  simpa only [List.length_map, List.length_reverse, List.length_nil, Nat.zero_add, count] using collected

theorem Equation.Executes.descriptorEnum_direct_separated {graph : Graph} {output : Summary}
    (mode : Mode) (definition : EnumDef) (uninhabited : List Bool) (nodes : List Nat)
    (descriptor : EnumLayoutDescriptor) (authored : definition.layout = some descriptor)
    (offset : Nat) (encoding : descriptor.encoding = .direct offset)
    (run : (enumEquation mode definition uninhabited nodes).Executes graph output) :
    ∀ enumeration, output.enumeration = some enumeration →
      ∀ fields, fields ∈ enumeration.variants → ∀ field, field ∈ fields →
        overlap offset (tagBits enumeration.tag / 8) field.offset field.size = false := by
  rcases run.descriptorEnum_view mode definition uninhabited nodes descriptor authored with
    ⟨tag, values, state, tagged, numbered, admitted, steps, constructed⟩
  exact constructed.direct_tag_separated descriptor authored offset encoding

theorem EnumConstruction.niche_range_bounds {mode : Mode} {definition : EnumDef} {tag : EnumTagRepr}
    {values : List Int} {uninhabited : List Bool} {variants : List Summary} {output : Summary}
    (constructed : EnumConstruction mode definition tag values uninhabited variants output)
    (descriptor : EnumLayoutDescriptor) (authored : definition.layout = some descriptor)
    (untagged start stop first offset : Nat) (repr : EnumTagRepr)
    (encoding : descriptor.encoding = .niche untagged start stop first offset repr) :
    variants.length < 2 ^ 32 ∧ untagged < variants.length ∧ start ≤ stop ∧ stop < variants.length ∧
      first ≤ 2 ^ tagBits repr - 1 ∧ stop - start ≤ 2 ^ tagBits repr - 1 := by
  have checks := constructed.descriptor_checks descriptor authored
  unfold EnumDescriptorChecks at checks
  rw [encoding] at checks
  have ranges := checks.1
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_le, Nat.not_lt, and_assoc] at ranges
  exact ranges

theorem NodeDerivation.descriptorEnum_geometry {graph : Graph} {node : Nat} {output : Summary}
    (mode : Mode) (definition : EnumDef) (uninhabited : List Bool) (nodes : List Nat)
    (descriptor : EnumLayoutDescriptor) (authored : definition.layout = some descriptor)
    (children : ∀ child, child ∈ nodes → ∀ summary, NodeDerivation graph child summary →
      FieldsSeparated summary.fields ∧ FieldsContained descriptor.size summary.fields)
    (found : graph.nodes.find node = some (enumEquation mode definition uninhabited nodes))
    (derived : NodeDerivation graph node output) : EnumerationGeometry output :=
  (NodeDerivation.execution found derived).descriptorEnum_geometry mode definition uninhabited nodes descriptor authored children

theorem Equation.Executes.descriptorEnum_niche_carrier {graph : Graph} {output : Summary}
    (mode : Mode) (definition : EnumDef) (uninhabited : List Bool) (nodes : List Nat)
    (descriptor : EnumLayoutDescriptor) (authored : definition.layout = some descriptor)
    (untagged start stop first offset : Nat) (repr : EnumTagRepr)
    (encoding : descriptor.encoding = .niche untagged start stop first offset repr)
    (run : (enumEquation mode definition uninhabited nodes).Executes graph output) :
    ∀ enumeration, output.enumeration = some enumeration →
      ∃ field, field ∈ (trustIrListGet? enumeration.variants untagged).getD [] ∧ field.size ≠ 0 ∧
        field.offset ≤ offset ∧ offset + tagBits repr / 8 ≤ field.offset + field.size := by
  rcases run.descriptorEnum_view mode definition uninhabited nodes descriptor authored with
    ⟨tag, values, state, tagged, numbered, admitted, steps, constructed⟩
  exact constructed.niche_carrier descriptor authored untagged start stop first offset repr encoding

theorem Equation.Executes.descriptorEnum_niche_separated {graph : Graph} {output : Summary}
    (mode : Mode) (definition : EnumDef) (uninhabited : List Bool) (nodes : List Nat)
    (descriptor : EnumLayoutDescriptor) (authored : definition.layout = some descriptor)
    (untagged start stop first offset : Nat) (repr : EnumTagRepr)
    (encoding : descriptor.encoding = .niche untagged start stop first offset repr)
    (run : (enumEquation mode definition uninhabited nodes).Executes graph output) :
    ∀ enumeration, output.enumeration = some enumeration →
      ∀ fields position, (fields, position) ∈ numbered enumeration.variants →
        position ≠ untagged → start ≤ position → position ≤ stop →
        ∀ field, field ∈ fields → overlap offset (tagBits repr / 8) field.offset field.size = false := by
  rcases run.descriptorEnum_view mode definition uninhabited nodes descriptor authored with
    ⟨tag, values, state, tagged, numbered, admitted, steps, constructed⟩
  exact constructed.niche_other_fields_separated descriptor authored untagged start stop first offset repr encoding

theorem NodeDerivation.descriptorEnum_direct_separated {graph : Graph} {node : Nat} {output : Summary}
    (mode : Mode) (definition : EnumDef) (uninhabited : List Bool) (nodes : List Nat)
    (descriptor : EnumLayoutDescriptor) (authored : definition.layout = some descriptor)
    (offset : Nat) (encoding : descriptor.encoding = .direct offset)
    (found : graph.nodes.find node = some (enumEquation mode definition uninhabited nodes))
    (derived : NodeDerivation graph node output) :
    ∀ enumeration, output.enumeration = some enumeration →
      ∀ fields, fields ∈ enumeration.variants → ∀ field, field ∈ fields →
        overlap offset (tagBits enumeration.tag / 8) field.offset field.size = false :=
  (NodeDerivation.execution found derived).descriptorEnum_direct_separated mode definition uninhabited nodes descriptor authored offset encoding

theorem NodeDerivation.descriptorEnum_niche_carrier {graph : Graph} {node : Nat} {output : Summary}
    (mode : Mode) (definition : EnumDef) (uninhabited : List Bool) (nodes : List Nat)
    (descriptor : EnumLayoutDescriptor) (authored : definition.layout = some descriptor)
    (untagged start stop first offset : Nat) (repr : EnumTagRepr)
    (encoding : descriptor.encoding = .niche untagged start stop first offset repr)
    (found : graph.nodes.find node = some (enumEquation mode definition uninhabited nodes))
    (derived : NodeDerivation graph node output) :
    ∀ enumeration, output.enumeration = some enumeration →
      ∃ field, field ∈ (trustIrListGet? enumeration.variants untagged).getD [] ∧ field.size ≠ 0 ∧
        field.offset ≤ offset ∧ offset + tagBits repr / 8 ≤ field.offset + field.size :=
  (NodeDerivation.execution found derived).descriptorEnum_niche_carrier mode definition uninhabited nodes descriptor authored untagged start stop first offset repr encoding

theorem NodeDerivation.descriptorEnum_niche_separated {graph : Graph} {node : Nat} {output : Summary}
    (mode : Mode) (definition : EnumDef) (uninhabited : List Bool) (nodes : List Nat)
    (descriptor : EnumLayoutDescriptor) (authored : definition.layout = some descriptor)
    (untagged start stop first offset : Nat) (repr : EnumTagRepr)
    (encoding : descriptor.encoding = .niche untagged start stop first offset repr)
    (found : graph.nodes.find node = some (enumEquation mode definition uninhabited nodes))
    (derived : NodeDerivation graph node output) :
    ∀ enumeration, output.enumeration = some enumeration →
      ∀ fields position, (fields, position) ∈ numbered enumeration.variants →
        position ≠ untagged → start ≤ position → position ≤ stop →
        ∀ field, field ∈ fields → overlap offset (tagBits repr / 8) field.offset field.size = false :=
  (NodeDerivation.execution found derived).descriptorEnum_niche_separated mode definition uninhabited nodes descriptor authored untagged start stop first offset repr encoding

/-- A child equation itself establishes field storage in a specified parent
 size. Unlike local child geometry, this contract cannot accept a child whose
 declared storage exceeds the enum's descriptor. -/
def Equation.ParentFieldGuarded (size : Nat) (equation : Equation) : Prop :=
  ∀ graph value, equation.Executes graph value →
    FieldsSeparated value.fields ∧ FieldsContained size value.fields

theorem Equation.ParentFieldGuarded.done (size : Nat) (result : Except Error Summary)
    (safe : ∀ value, result = .ok value →
      FieldsSeparated value.fields ∧ FieldsContained size value.fields) :
    (Equation.done result).ParentFieldGuarded size := by
  intro graph value run
  rcases run with ⟨first, last, initial, steps, finished⟩
  cases steps
  exact safe value (initial.trans finished)

theorem Equation.ParentFieldGuarded.failed (size : Nat) (error : Error) :
    (Equation.done (.error error)).ParentFieldGuarded size := by
  intro graph value run
  rcases run with ⟨first, last, initial, steps, finished⟩
  cases initial

theorem Equation.ParentFieldGuarded.declaredFields (mode : Mode) (kind : String)
    (id size align clamp : Nat) (transparent : Bool) (fields : List (Ty × Option Nat × Nat)) :
    (declaredFields mode kind id size align clamp transparent fields).ParentFieldGuarded size := by
  intro graph value run
  have geometry := run.declaredFields_geometry mode kind id size align clamp transparent fields
  rcases run with ⟨first, last, initial, steps, finished⟩
  have exactValue := declaredFields_finish_exact mode kind id size align clamp transparent fields last value finished
  have exactSize : value.size = size := by rw [exactValue]
  exact ⟨geometry.1, exactSize ▸ geometry.2⟩

/-- The exact descriptor-variant branch used by preparation establishes the
 parent contract on every success; malformed rows remain failed equations. -/
theorem Equation.ParentFieldGuarded.descriptorVariant (mode : Mode) (id : Nat)
    (descriptor : EnumLayoutDescriptor) (children : List (Ty × Nat)) (variantIndex : Nat) :
    Equation.ParentFieldGuarded descriptor.size (match trustIrListGet? descriptor.variantFieldOffsets variantIndex with
      | none => Equation.done (.error (.incoherent "enum" id))
      | some offsets =>
        if offsets.length != children.length then .done (.error (.incoherent "enum" id))
        else TrustIr.SourceLayout.declaredFields mode "enum" id descriptor.size descriptor.align word64Max false
          (children.zip offsets |>.map (fun ((ty, child), offset) => (ty, some offset, child))))
       := by
  repeat first
    | exact Equation.ParentFieldGuarded.failed _ _
    | exact Equation.ParentFieldGuarded.declaredFields _ _ _ _ _ _ _ _
    | split

/-- Certificates name the installed equations, rather than trusting a summary
 or an external table of desired child sizes. -/
def Graph.ParentFieldCertificates (size : Nat) (nodes : List Nat) (graph : Graph) : Prop :=
  ∀ node, node ∈ nodes → ∃ equation, graph.nodes.find node = some equation ∧
    equation.ParentFieldGuarded size

theorem Graph.ParentFieldCertificates.weaken {before after : Graph} {size : Nat} {nodes : List Nat}
    (safe : before.ParentFieldCertificates size nodes) (extended : before.Extends after) :
    after.ParentFieldCertificates size nodes := by
  intro node member
  rcases safe node member with ⟨equation, found, guarded⟩
  exact ⟨equation, extended node equation found, guarded⟩

theorem Graph.ParentFieldCertificates.child {graph : Graph} {size : Nat} {nodes : List Nat}
    (safe : graph.ParentFieldCertificates size nodes) {node : Nat} (member : node ∈ nodes)
    {value : Summary} (derived : NodeDerivation graph node value) :
    FieldsSeparated value.fields ∧ FieldsContained size value.fields := by
  rcases safe node member with ⟨equation, found, guarded⟩
  exact guarded graph value (derived.execution found)

theorem Equation.ContextualRule.descriptorEnum_geometry (graph : Graph) (owner : Nat)
    (mode : Mode) (definition : EnumDef) (uninhabited : List Bool) (nodes : List Nat)
    (descriptor : EnumLayoutDescriptor) (authored : definition.layout = some descriptor)
    (children : graph.ParentFieldCertificates descriptor.size nodes) :
    (enumEquation mode definition uninhabited nodes).ContextualRule graph
      (fun _ value => FieldGeometry value ∧ EnumerationGeometry value) owner := by
  intro first last value initial steps finished
  have run : (enumEquation mode definition uninhabited nodes).Executes graph value :=
    ⟨first, last, initial, steps.derivation, finished⟩
  rcases run.descriptorEnum_view mode definition uninhabited nodes descriptor authored with
    ⟨tag, values, state, tagged, numbered, admitted, collected, constructed⟩
  refine ⟨?_, ?_⟩
  · rw [constructed.descriptor_exact descriptor authored]
    exact ⟨trivial, by intro field impossible; cases impossible⟩
  · exact (Equation.Executes.descriptorEnum_geometry mode definition uninhabited nodes descriptor authored
    (fun node member summary derived => children.child member derived)
    ⟨first, last, initial, steps.derivation, finished⟩)

theorem Graph.ParentFieldCertificates.allocate {graph : Graph} {size : Nat} {nodes : List Nat}
    (safe : graph.ParentFieldCertificates size nodes) (bounded : graph.Bounded)
    (equation : Equation) (guarded : equation.ParentFieldGuarded size) :
    ({ graph with nodes := graph.nodes.insert graph.count equation, count := graph.count + 1 } : Graph).ParentFieldCertificates size (graph.count :: nodes) := by
  have old := safe.weaken (Graph.Extends.allocate bounded equation)
  intro node member
  cases member with
  | head =>
    refine ⟨equation, ?_, guarded⟩
    change (graph.nodes.insert graph.count equation).find graph.count = some equation
    rw [NatIndexTree.find_insert, if_pos rfl]
  | tail _ member => exact old node member

/-- Writes to reserved slots do not destroy certificates for dynamically
 allocated variants beyond that reserved prefix. -/
theorem Graph.ParentFieldCertificates.put_below {graph : Graph} {size lower node : Nat} {nodes : List Nat}
    (safe : graph.ParentFieldCertificates size nodes)
    (outside : ∀ child, child ∈ nodes → lower ≤ child) (inside : node < lower) (equation : Equation) :
    ({ graph with nodes := graph.nodes.insert node equation } : Graph).ParentFieldCertificates size nodes := by
  intro child member
  rcases safe child member with ⟨original, found, guarded⟩
  refine ⟨original, ?_, guarded⟩
  change (graph.nodes.insert node equation).find child = some original
  rw [NatIndexTree.find_insert, if_neg (by have bound := outside child member; omega)]
  exact found

theorem Graph.ParentFieldCertificates.reverse {graph : Graph} {size : Nat} {nodes : List Nat}
    (safe : graph.ParentFieldCertificates size nodes) : graph.ParentFieldCertificates size nodes.reverse :=
  fun node member => safe node ((member_reverse node nodes).mp member)

/-- Collection consumes each induction hypothesis together with the exact
 child's derivation. The result predicate may use both pieces of evidence. -/
theorem enum_certified_children_property (graph : Graph) (property : Nat → Summary → Prop)
    (result : Summary → Prop) (nodes : List Nat) (first last : List Summary)
    (initial : ∀ summary, summary ∈ first → result summary)
    (children : ∀ node, node ∈ nodes → ∀ summary, NodeDerivation graph node summary →
      property node summary → result summary)
    (steps : StepsCertified graph property
      (nodes.map (fun child => .child child fun value state => .ok (value :: state))) first last) :
    ∀ summary, summary ∈ last → result summary := by
  induction nodes generalizing first with
  | nil => cases steps; exact initial
  | cons node rest ih =>
    cases steps with
    | child solved good updated later =>
      have childResult := children node ((trustIrListMemConsSelf _ _)) _ solved good
      cases updated
      apply ih _ _ (fun node member => children node (List.mem_cons_of_mem _ member)) later
      intro summary member
      cases member with
      | head => exact childResult
      | tail _ member => exact initial summary member

theorem EnumConstruction.field_geometry {mode : Mode} {definition : EnumDef} {tag : EnumTagRepr}
    {values : List Int} {uninhabited : List Bool} {variants : List Summary} {output : Summary}
    (constructed : EnumConstruction mode definition tag values uninhabited variants output) :
    FieldGeometry output := by
  cases layout : definition.layout with
  | none =>
    rcases constructed.canonical_view layout with ⟨offset, extent, size, placed, bounded, rounded, finished⟩
    rw [((finish_ok_iff mode _ output).mp finished).1]
    exact ⟨trivial, by intro field impossible; cases impossible⟩
  | some descriptor =>
    rw [constructed.descriptor_exact descriptor layout]
    exact ⟨trivial, by intro field impossible; cases impossible⟩

theorem Equation.ContextualRule.canonicalEnum_geometry (graph : Graph) (owner : Nat)
    (mode : Mode) (definition : EnumDef) (uninhabited : List Bool) (nodes : List Nat)
    (canonical : definition.layout = none) :
    (enumEquation mode definition uninhabited nodes).ContextualRule graph
      (fun _ value => FieldGeometry value ∧ EnumerationGeometry value) owner := by
  cases ht : canonicalTag definition with
  | none =>
    have selected : enumEquation mode definition uninhabited nodes =
        Equation.done (.error (.incoherent "enum" definition.id.index)) := by
      unfold enumEquation; rw [ht]
    rw [selected]
    intro first last value initial steps finished
    cases initial
  | some tag =>
    cases hv : discriminants definition with
    | none =>
      have selected : enumEquation mode definition uninhabited nodes =
          Equation.done (.error (.incoherent "enum" definition.id.index)) := by
        unfold enumEquation; rw [ht, hv]
      rw [selected]
      intro first last value initial steps finished
      cases initial
    | some values =>
      unfold enumEquation
      rw [ht, hv]
      dsimp only
      rw [canonical]
      intro first last value initial steps finished
      cases initial
      have children := enum_certified_children_property graph
        (fun _ value => FieldGeometry value ∧ EnumerationGeometry value) FieldGeometry nodes [] last
        (by intro summary impossible; cases impossible)
        (fun node member summary derived safe => safe.1) steps
      have constructed : EnumConstruction mode definition tag values uninhabited last.reverse value := finished
      exact ⟨constructed.field_geometry, constructed.canonical_geometry canonical
        (fun summary member => children summary ((member_reverse summary last).mp member))⟩

end TrustIr.SourceLayout
