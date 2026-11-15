-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Layout.EnumGeometry
import TrustIr.Layout.Scalar

namespace TrustIr.SourceLayout

def EnumTagSeparated (enumeration : Enumeration) (offset width : Nat) : Prop :=
  ∀ fields, fields ∈ enumeration.variants → ∀ field, field ∈ fields →
    overlap offset width field.offset field.size = false

def EnumNicheCarrier (enumeration : Enumeration) (untagged offset width : Nat) : Prop :=
  ∃ field, field ∈ (trustIrListGet? enumeration.variants untagged).getD [] ∧ field.size ≠ 0 ∧
    field.offset ≤ offset ∧ offset + width ≤ field.offset + field.size

def EnumNicheSeparated (enumeration : Enumeration) (untagged start stop offset width : Nat) : Prop :=
  ∀ fields position, (fields, position) ∈ numbered enumeration.variants →
    position ≠ untagged → start ≤ position → position ≤ stop →
    ∀ field, field ∈ fields → overlap offset width field.offset field.size = false

/-- Intrinsic lane geometry and the actual selector/coverage checks. Boolean
inhabitedness facts are retained as data; their semantic truth is not assumed. -/
def EnumEncodingGeometry (value : Summary) : Prop :=
  ∀ enumeration, value.enumeration = some enumeration →
    match enumeration.encoding with
    | .untagged => enumeration.variants.length = 1
    | .singleInhabited selected =>
      selected < enumeration.variants.length ∧ selected < 2 ^ 32 ∧
      enumeration.uninhabited.length = enumeration.variants.length ∧
      (numbered enumeration.uninhabited).all (fun (impossible, position) =>
        if position == selected then !impossible else impossible) = true
    | .direct offset =>
      ∃ align, value.align = some align ∧
        EnumLaneBounds value.size align offset (tagBits enumeration.tag / 8) (tagBits enumeration.tag / 8) ∧
        EnumTagSeparated enumeration offset (tagBits enumeration.tag / 8)
    | .niche untagged start stop first offset repr =>
      ∃ align, value.align = some align ∧
        EnumLaneBounds value.size align offset (tagBits repr / 8) (tagBits repr / 8) ∧
        enumeration.variants.length < 2 ^ 32 ∧ untagged < enumeration.variants.length ∧
        start ≤ stop ∧ stop < enumeration.variants.length ∧
        first ≤ 2 ^ tagBits repr - 1 ∧ stop - start ≤ 2 ^ tagBits repr - 1 ∧
        (numbered enumeration.uninhabited).all (fun (impossible, position) =>
          impossible || position == untagged || (start ≤ position && position ≤ stop)) = true ∧
        EnumNicheCarrier enumeration untagged offset (tagBits repr / 8) ∧
        EnumNicheSeparated enumeration untagged start stop offset (tagBits repr / 8)

theorem EnumEncodingGeometry.no_enum {value : Summary} (absent : value.enumeration = none) :
    EnumEncodingGeometry value := by
  intro enumeration impossible
  rw [absent] at impossible
  cases impossible

private theorem single_checks (definition : EnumDef) (descriptor : EnumLayoutDescriptor)
    (uninhabited : List Bool) (selected : Nat)
    (valid : singleInhabitedValid definition descriptor uninhabited selected = true) :
    selected < definition.variants.length ∧ selected < 2 ^ 32 ∧
    uninhabited.length = definition.variants.length ∧
    descriptor.variantFieldOffsets.length = definition.variants.length ∧
    (numbered uninhabited).all (fun (impossible, position) =>
      if position == selected then !impossible else impossible) = true := by
  have inside : selected < definition.variants.length := by
    by_cases good : selected < definition.variants.length
    · exact good
    · simp [singleInhabitedValid, good] at valid
  have bounded : selected < 2 ^ 32 := by
    by_cases good : selected < 2 ^ 32
    · exact good
    · simp [singleInhabitedValid, good] at valid
  have flags : uninhabited.length = definition.variants.length := by
    by_cases good : uninhabited.length = definition.variants.length
    · exact good
    · simp [singleInhabitedValid, good] at valid
  have rows : descriptor.variantFieldOffsets.length = definition.variants.length := by
    by_cases good : descriptor.variantFieldOffsets.length = definition.variants.length
    · exact good
    · simp [singleInhabitedValid, good] at valid
  have checked : (numbered uninhabited).all (fun (impossible, position) =>
      if position == selected then !impossible
      else impossible && ((trustIrListGet? descriptor.variantFieldOffsets position).getD []).isEmpty) = true := by
    simpa [singleInhabitedValid, inside, bounded, flags, rows] using valid
  refine ⟨inside, bounded, flags, rows, ?_⟩
  apply List.all_eq_true.mpr
  intro row member
  rcases row with ⟨impossible, position⟩
  have actual := List.all_eq_true.mp checked (impossible, position) member
  cases active : position == selected with
  | false =>
    simp only [active, Bool.false_eq_true, ite_false] at actual ⊢
    trustIrCompilerProof {
      exact ((Bool.and_eq_true_iff _ _).mp actual).1
    } {
      exact (Bool.and_eq_true_iff.mp actual).1
    }
  | true => simpa only [active, ite_true] using actual

theorem EnumConstruction.canonical_encoding_geometry {mode : Mode} {definition : EnumDef} {tag : EnumTagRepr}
    {values : List Int} {uninhabited : List Bool} {variants : List Summary} {output : Summary}
    (constructed : EnumConstruction mode definition tag values uninhabited variants output)
    (canonical : definition.layout = none) : EnumEncodingGeometry output := by
  have separated := constructed.canonical_tag_separated canonical
  rcases constructed.canonical_view canonical with ⟨offset, extent, size, placed, bounded, rounded, finished⟩
  have result := (finish_ok_iff mode _ output).mp finished
  rw [result.1] at separated ⊢
  intro enumeration actual
  cases actual
  refine ⟨_, rfl, ?_, separated _ rfl⟩
  have offsetLower := alignUp_lower_bound _ _ _ placed
  have extentExact := (checked_ok _ _ bounded).1
  have sizeLower := alignUp_lower_bound _ _ _ rounded
  have sizeBound := result.2.1.1
  simp only [Nat.one_mul] at sizeBound
  refine ⟨Nat.zero_mod _, Nat.le_max_left _ _, ?_, ?_⟩ <;> dsimp only <;> omega

theorem Equation.Executes.enum_encoding_geometry {graph : Graph} {output : Summary}
    (mode : Mode) (definition : EnumDef) (uninhabited : List Bool) (nodes : List Nat)
    (run : (enumEquation mode definition uninhabited nodes).Executes graph output) :
    EnumEncodingGeometry output := by
  cases authored : definition.layout with
  | none =>
    rcases run.canonicalEnum_view mode definition uninhabited nodes authored with
      ⟨tag, values, state, tagged, numbered, collected, constructed⟩
    exact constructed.canonical_encoding_geometry authored
  | some descriptor =>
    have count := run.descriptorEnum_variant_count mode definition uninhabited nodes descriptor authored
    rcases run.descriptorEnum_view mode definition uninhabited nodes descriptor authored with
      ⟨tag, values, state, tagged, numberedValues, admitted, collected, constructed⟩
    have checks := constructed.descriptor_checks descriptor authored
    have exactValue := constructed.descriptor_exact descriptor authored
    rw [exactValue] at count ⊢
    intro enumeration actual
    cases actual
    have actualCount := count _ rfl
    dsimp only at actualCount
    cases encoding : descriptor.encoding with
    | untagged =>
      unfold EnumDescriptorChecks at checks
      rw [encoding] at checks
      simpa only [EnumEncodingGeometry, encoding, List.length_map] using checks
    | singleInhabited selected =>
      unfold EnumDescriptorChecks at checks
      rw [encoding] at checks
      have facts := single_checks definition descriptor uninhabited selected checks
      dsimp only [EnumEncodingGeometry]
      exact ⟨by omega, facts.2.1, by omega, facts.2.2.2.2⟩
    | direct offset =>
      have lane := constructed.direct_lane descriptor authored offset encoding
      have separated := constructed.direct_tag_separated descriptor authored offset encoding
      rw [exactValue, encoding] at separated
      dsimp only [EnumEncodingGeometry]
      exact ⟨descriptor.align, rfl, lane, separated _ rfl⟩
    | niche untagged start stop first offset repr =>
      have lane := constructed.niche_lane descriptor authored untagged start stop first offset repr encoding
      have ranges := constructed.niche_range_bounds descriptor authored untagged start stop first offset repr encoding
      have carrier := constructed.niche_carrier descriptor authored untagged start stop first offset repr encoding
      have separated := constructed.niche_other_fields_separated descriptor authored untagged start stop first offset repr encoding
      rw [exactValue, encoding] at carrier separated
      unfold EnumDescriptorChecks at checks
      rw [encoding] at checks
      dsimp only [EnumEncodingGeometry]
      refine ⟨descriptor.align, rfl, lane, ?_, ?_, ranges.2.2.1, ?_, ranges.2.2.2.2.1,
        ranges.2.2.2.2.2, checks.2.2.1, carrier _ rfl, separated _ rfl⟩
      · simpa only [List.length_map, List.length_reverse] using ranges.1
      · simpa only [List.length_map, List.length_reverse] using ranges.2.1
      · simpa only [List.length_map, List.length_reverse] using ranges.2.2.2.1

/-- Every actual enum execution enforces its lane and selector checks,
independently of assumptions about arbitrary child geometry. -/
def Equation.EncodingGuarded (equation : Equation) : Prop :=
  ∀ graph value, equation.Executes graph value → EnumEncodingGeometry value

abbrev Graph.EncodingInvariant (graph : Graph) := graph.SummaryInvariant EnumEncodingGeometry

theorem Equation.EncodingGuarded.rule {equation : Equation} (safe : equation.EncodingGuarded) :
    equation.InvariantRule EnumEncodingGeometry := .guarded safe

theorem Equation.EncodingGuarded.enumeration (mode : Mode) (definition : EnumDef)
    (uninhabited : List Bool) (nodes : List Nat) :
    (enumEquation mode definition uninhabited nodes).EncodingGuarded :=
  fun graph value run => run.enum_encoding_geometry mode definition uninhabited nodes

theorem Equation.EncodingGuarded.failed (error : Error) : (Equation.done (.error error)).EncodingGuarded := by
  intro graph value run
  rcases run with ⟨first, last, initial, steps, finished⟩
  cases initial

theorem Equation.EncodingGuarded.done (result : Result Summary)
    (safe : ∀ value, result = .ok value → EnumEncodingGeometry value) :
    (Equation.done result).EncodingGuarded := by
  intro graph value run
  rcases run with ⟨first, last, initial, steps, finished⟩
  cases steps
  exact safe value (initial.trans finished)

theorem Equation.EncodingGuarded.canonicalFields (mode : Mode) (kind : String) (id : Nat)
    (fields : List (Ty × Nat)) : (canonicalFields mode kind id fields).EncodingGuarded := by
  intro graph value run
  apply EnumEncodingGeometry.no_enum
  rcases run with ⟨first, last, initial, steps, finished⟩
  dsimp only [TrustIr.SourceLayout.canonicalFields] at finished
  cases rounded : alignUp last.cursor last.align with
  | error error => simp [rounded, Except.bind, Bind.bind] at finished
  | ok size =>
    simp only [rounded, Except.bind, Bind.bind] at finished
    rw [((finish_ok_iff mode _ value).mp finished).1]

theorem Equation.EncodingGuarded.declaredFields (mode : Mode) (kind : String)
    (id size align clamp : Nat) (transparent : Bool) (fields : List (Ty × Option Nat × Nat)) :
    (declaredFields mode kind id size align clamp transparent fields).EncodingGuarded := by
  intro graph value run
  apply EnumEncodingGeometry.no_enum
  rcases run with ⟨first, last, initial, steps, finished⟩
  rw [declaredFields_finish_exact mode kind id size align clamp transparent fields last value finished]

theorem Equation.EncodingGuarded.scaled (mode : Mode) (count child : Nat) :
    (scaled mode count child).EncodingGuarded := by
  intro graph value run
  rcases run with ⟨first, last, initial, steps, finished⟩
  cases steps with
  | child solved updated later =>
    cases later
    cases finished
    dsimp only [scaled] at updated
    simp only [Except.bind, Bind.bind] at updated
    split at updated
    · cases updated
    · rw [((finish_ok_iff mode _ _).mp updated).1]
      exact EnumEncodingGeometry.no_enum rfl

theorem Equation.EncodingGuarded.sequence (children : List Nat) {next : Equation}
    (safe : next.EncodingGuarded) : (Equation.sequence children next).EncodingGuarded :=
  fun graph value run => safe graph value run.sequence_body

theorem Equation.EncodingGuarded.unit (steps : List (Step Unit)) :
    ({ kind := .unit, initial := .ok (), steps, finish := fun _ => .ok { size := 0, align := some 1 } } : Equation).EncodingGuarded := by
  intro graph value run
  rcases run with ⟨first, last, initial, steps, finished⟩
  cases finished
  exact EnumEncodingGeometry.no_enum rfl

theorem ScalarSummary.enum_encoding_geometry {pointerBytes : Nat} {value : Summary}
    (scalar : ScalarSummary pointerBytes value) : EnumEncodingGeometry value := by
  cases scalar <;> exact EnumEncodingGeometry.no_enum rfl

end TrustIr.SourceLayout
