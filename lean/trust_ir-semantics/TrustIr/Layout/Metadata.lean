-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Layout.EncodingGeometry

namespace TrustIr.SourceLayout

/-- Logical uniqueness, without a runtime checker or partial recursion. -/
inductive UniqueDiscriminants : List Int → Prop where
  | nil : UniqueDiscriminants []
  | cons {first : Int} {rest : List Int} (fresh : first ∉ rest)
      (unique : UniqueDiscriminants rest) : UniqueDiscriminants (first :: rest)

private theorem metadata_mem_append {α : Type} (value : α) (left right : List α) :
    value ∈ left ++ right ↔ value ∈ left ∨ value ∈ right := by
  induction left with
  | nil => simp
  | cons first rest ih => simp [List.cons_append, ih, or_assoc]

private theorem metadata_mem_reverse {α : Type} (value : α) (values : List α) :
    value ∈ values.reverse ↔ value ∈ values := by
  induction values with
  | nil => simp
  | cons first rest ih => simp [List.reverse_cons, metadata_mem_append, ih, or_comm]

theorem UniqueDiscriminants.snoc {values : List Int} (safe : UniqueDiscriminants values)
    (value : Int) (fresh : value ∉ values) : UniqueDiscriminants (values ++ [value]) := by
  induction safe with
  | nil => exact .cons (by intro impossible; cases impossible) .nil
  | @cons first rest absent unique ih =>
    apply UniqueDiscriminants.cons
    · intro member
      rcases (metadata_mem_append first rest [value]).mp member with old | singleton
      · exact absent old
      · cases singleton with
        | head => exact fresh ((trustIrListMemConsSelf _ _))
        | tail _ impossible => cases impossible
    · exact ih (fun member => fresh (List.mem_cons_of_mem _ member))

theorem UniqueDiscriminants.reverse {values : List Int} (safe : UniqueDiscriminants values) :
    UniqueDiscriminants values.reverse := by
  induction safe with
  | nil => exact .nil
  | @cons first rest absent unique ih =>
    rw [List.reverse_cons]
    exact ih.snoc first (fun member => absent ((metadata_mem_reverse first rest).mp member))

private theorem int_contains_of_mem (values : List Int) (value : Int) (member : value ∈ values) :
    values.contains value = true := by
  trustIrCompilerProof {
    induction values with
    | nil => cases member
    | cons first rest ih =>
      cases member with
      | head => simp [List.contains, List.elem]
      | tail _ later =>
        cases accepted : value == first <;> simp [List.contains, List.elem, accepted, ih later]
  } {
    exact List.contains_iff_mem.mpr member
  }

private theorem range_loop_length (count : Nat) (tail : List Nat) :
    (List.range.loop count tail).length = count + tail.length := by
  induction count generalizing tail with
  | zero => simp only [List.range.loop, Nat.zero_add]
  | succ count ih =>
    rw [List.range.loop, ih]
    simp only [List.length_cons]
    omega

theorem metadata_range_length (count : Nat) : (List.range count).length = count := by
  simpa only [List.range, List.length_nil, Nat.add_zero] using range_loop_length count []

/-- Successful completion preserves the number of authored rows and rejects
any repeated effective discriminant, including implicit/explicit collisions. -/
theorem discriminants_go_facts (explicit : List (Option Int)) (next : Option Int) (out values : List Int)
    (safe : UniqueDiscriminants out) (run : discriminants.go explicit next out = some values) :
    values.length = out.length + explicit.length ∧ UniqueDiscriminants values := by
  induction explicit generalizing next out values with
  | nil =>
    simp only [discriminants.go] at run
    cases run
    exact ⟨by simp, safe.reverse⟩
  | cons first rest ih =>
    simp only [discriminants.go] at run
    cases chosen : first.orElse (fun _ => next) with
    | none =>
      trustIrCompilerProof {
        simp [chosen, Bind.bind, Option.bind] at run
      } {
        simp only [chosen, Bind.bind, Option.bind] at run
        cases run
      }
    | some value =>
      simp only [chosen, Bind.bind, Option.bind] at run
      split at run
      · cases run
      · rename_i accepted
        have fresh : value ∉ out := fun member => accepted (int_contains_of_mem out value member)
        have later := ih _ (value :: out) values (.cons fresh safe) run
        refine ⟨?_, later.2⟩
        simp only [List.length_cons] at later ⊢
        omega

theorem discriminants_facts (definition : EnumDef) (values : List Int)
    (run : discriminants definition = some values) :
    values.length = definition.variants.length ∧ UniqueDiscriminants values := by
  have facts := discriminants_go_facts _ (some 0) [] values .nil run
  simpa only [List.length_nil, Nat.zero_add, List.length_map, metadata_range_length] using facts

private theorem find_accepted {α : Type} (predicate : α → Bool) (values : List α) (value : α)
    (run : values.find? predicate = some value) : predicate value = true := by
  induction values with
  | nil => cases run
  | cons first rest ih =>
    rw [List.find?_cons] at run
    cases accepted : predicate first with
    | false => rw [accepted] at run; exact ih run
    | true => rw [accepted] at run; cases run; exact accepted

theorem canonicalTag_fits (definition : EnumDef) (tag : EnumTagRepr) (values : List Int)
    (selected : canonicalTag definition = some tag) (numbered : discriminants definition = some values) :
    values.all (tagFits tag) = true := by
  unfold canonicalTag at selected
  simp only [Bind.bind, Option.bind, numbered] at selected
  split at selected
  · cases selected
  · cases actual : definition.tagRepr with
    | some repr =>
      simp only [actual] at selected
      split at selected
      · cases selected; assumption
      · cases selected
    | none =>
      simp only [actual] at selected
      exact find_accepted (fun repr => values.all (tagFits repr)) _ tag selected

/-- Counts and logical discriminants correspond to actual logical rows. This
records flag-list shape, not semantic truth of the inhabitedness flags. -/
def EnumMetadata (value : Summary) : Prop :=
  ∀ enumeration, value.enumeration = some enumeration →
    enumeration.discriminants.length = enumeration.variants.length ∧
    enumeration.uninhabited.length = enumeration.variants.length ∧
    UniqueDiscriminants enumeration.discriminants ∧
    enumeration.discriminants.all (tagFits enumeration.tag) = true

theorem EnumMetadata.no_enum {value : Summary} (absent : value.enumeration = none) : EnumMetadata value := by
  intro enumeration impossible
  rw [absent] at impossible
  cases impossible

private theorem zip_metadata_length {α β : Type} (left : List α) (right : List β) :
    (left.zip right).length = min left.length right.length := by
  induction left generalizing right with
  | nil => cases right <;> rfl
  | cons first rest ih =>
    cases right with
    | nil => rfl
    | cons next later =>
      change (rest.zip later).length + 1 = min (rest.length + 1) (later.length + 1)
      have step : min (rest.length + 1) (later.length + 1) = min rest.length later.length + 1 := by
        simp only [Nat.min_def]
        split <;> split <;> omega
      rw [step, ih later]

theorem numbered_metadata_length {α : Type} (rows : List α) : (numbered rows).length = rows.length := by
  rw [numbered, zip_metadata_length, metadata_range_length, Nat.min_self]

theorem EnumConstruction.metadata {mode : Mode} {definition : EnumDef} {tag : EnumTagRepr}
    {values : List Int} {uninhabited : List Bool} {variants : List Summary} {output : Summary}
    (constructed : EnumConstruction mode definition tag values uninhabited variants output)
    (tagged : canonicalTag definition = some tag) (numbered : discriminants definition = some values)
    (count : variants.length = definition.variants.length)
    (flags : uninhabited.length = definition.variants.length) : EnumMetadata output := by
  have facts := discriminants_facts definition values numbered
  have fits := canonicalTag_fits definition tag values tagged numbered
  cases authored : definition.layout with
  | none =>
    rcases constructed.canonical_view authored with ⟨offset, extent, size, placed, bounded, rounded, finished⟩
    rw [((finish_ok_iff mode _ output).mp finished).1]
    intro enumeration actual
    cases actual
    exact ⟨by simpa only [placePayload, List.length_map, count] using facts.1,
      by simpa only [placePayload, List.length_map, count] using flags, facts.2, fits⟩
  | some descriptor =>
    rw [constructed.descriptor_exact descriptor authored]
    intro enumeration actual
    cases actual
    exact ⟨by simpa only [List.length_map, count] using facts.1,
      by simpa only [List.length_map, count] using flags, facts.2, fits⟩

theorem Equation.Executes.enum_metadata {graph : Graph} {output : Summary}
    (mode : Mode) (definition : EnumDef) (uninhabited : List Bool) (nodes : List Nat)
    (nodeCount : nodes.length = definition.variants.length)
    (flagCount : uninhabited.length = definition.variants.length)
    (run : (enumEquation mode definition uninhabited nodes).Executes graph output) : EnumMetadata output := by
  cases authored : definition.layout with
  | none =>
    rcases run.canonicalEnum_view mode definition uninhabited nodes authored with
      ⟨tag, values, state, tagged, numbered, collected, constructed⟩
    have count := enum_children_length graph nodes [] state collected
    apply constructed.metadata tagged numbered _ flagCount
    simpa only [List.length_reverse, List.length_nil, Nat.zero_add, nodeCount] using count
  | some descriptor =>
    rcases run.descriptorEnum_view mode definition uninhabited nodes descriptor authored with
      ⟨tag, values, state, tagged, numbered, admitted, collected, constructed⟩
    have count := enum_children_length graph nodes [] state collected
    apply constructed.metadata tagged numbered _ flagCount
    simpa only [List.length_reverse, List.length_nil, Nat.zero_add, nodeCount] using count

/-- Metadata checks depend on actual compiler row/flag counts, not a promise
that arbitrary enum equations have authentic source-sized child lists. -/
def Equation.MetadataGuarded (equation : Equation) : Prop :=
  ∀ graph value, equation.Executes graph value → EnumMetadata value

abbrev Graph.MetadataInvariant (graph : Graph) := graph.SummaryInvariant EnumMetadata

theorem Equation.MetadataGuarded.rule {equation : Equation} (safe : equation.MetadataGuarded) :
    equation.InvariantRule EnumMetadata := .guarded safe

theorem Equation.MetadataGuarded.enumeration (mode : Mode) (definition : EnumDef)
    (uninhabited : List Bool) (nodes : List Nat)
    (nodeCount : nodes.length = definition.variants.length)
    (flagCount : uninhabited.length = definition.variants.length) :
    (enumEquation mode definition uninhabited nodes).MetadataGuarded :=
  fun graph value run => run.enum_metadata mode definition uninhabited nodes nodeCount flagCount

theorem Equation.MetadataGuarded.failed (error : Error) : (Equation.done (.error error)).MetadataGuarded := by
  intro graph value run
  rcases run with ⟨first, last, initial, steps, finished⟩
  cases initial

theorem Equation.MetadataGuarded.done (result : Result Summary)
    (safe : ∀ value, result = .ok value → EnumMetadata value) :
    (Equation.done result).MetadataGuarded := by
  intro graph value run
  rcases run with ⟨first, last, initial, steps, finished⟩
  cases steps
  exact safe value (initial.trans finished)

theorem Equation.MetadataGuarded.canonicalFields (mode : Mode) (kind : String) (id : Nat)
    (fields : List (Ty × Nat)) : (canonicalFields mode kind id fields).MetadataGuarded := by
  intro graph value run
  apply EnumMetadata.no_enum
  rcases run with ⟨first, last, initial, steps, finished⟩
  dsimp only [TrustIr.SourceLayout.canonicalFields] at finished
  cases rounded : alignUp last.cursor last.align with
  | error error => simp [rounded, Except.bind, Bind.bind] at finished
  | ok size =>
    simp only [rounded, Except.bind, Bind.bind] at finished
    rw [((finish_ok_iff mode _ value).mp finished).1]

theorem Equation.MetadataGuarded.declaredFields (mode : Mode) (kind : String)
    (id size align clamp : Nat) (transparent : Bool) (fields : List (Ty × Option Nat × Nat)) :
    (declaredFields mode kind id size align clamp transparent fields).MetadataGuarded := by
  intro graph value run
  apply EnumMetadata.no_enum
  rcases run with ⟨first, last, initial, steps, finished⟩
  rw [declaredFields_finish_exact mode kind id size align clamp transparent fields last value finished]

theorem Equation.MetadataGuarded.scaled (mode : Mode) (count child : Nat) :
    (scaled mode count child).MetadataGuarded := by
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
      exact EnumMetadata.no_enum rfl

theorem Equation.MetadataGuarded.sequence (children : List Nat) {next : Equation}
    (safe : next.MetadataGuarded) : (Equation.sequence children next).MetadataGuarded :=
  fun graph value run => safe graph value run.sequence_body

theorem Equation.MetadataGuarded.unit (steps : List (Step Unit)) :
    ({ kind := .unit, initial := .ok (), steps, finish := fun _ => .ok { size := 0, align := some 1 } } : Equation).MetadataGuarded := by
  intro graph value run
  rcases run with ⟨first, last, initial, steps, finished⟩
  cases finished
  exact EnumMetadata.no_enum rfl

theorem ScalarSummary.enum_metadata {pointerBytes : Nat} {value : Summary}
    (scalar : ScalarSummary pointerBytes value) : EnumMetadata value := by
  cases scalar <;> exact EnumMetadata.no_enum rfl

end TrustIr.SourceLayout
