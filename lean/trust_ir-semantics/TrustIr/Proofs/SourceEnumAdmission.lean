-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceEnumPayload
import TrustIr.Layout.EnumAdmission

namespace TrustIr.SourceLayout

/-- Pairwise distinct original row identifiers, retaining source order. -/
def EnumIdsDistinct : List EnumDef → Prop
  | [] => True
  | first :: rest => (∀ row ∈ rest, row.id.index ≠ first.id.index) ∧ EnumIdsDistinct rest

def EnumFreshIds (seen : NatIndexTree Unit) (rows : List EnumDef) : Prop :=
  ∀ row ∈ rows, seen.find row.id.index = none

private theorem fresh_insert (seen : NatIndexTree Unit) (key : Nat) (rows : List EnumDef) :
    EnumFreshIds (seen.insert key ()) rows ↔
      EnumFreshIds seen rows ∧ (∀ row ∈ rows, row.id.index ≠ key) := by
  constructor
  · intro fresh
    have different : ∀ row ∈ rows, row.id.index ≠ key := by
      intro row member same
      have absent := fresh row member
      simp [NatIndexTree.find_insert, same] at absent
    exact ⟨fun row member => by
      have absent := fresh row member
      simpa [NatIndexTree.find_insert, different row member] using absent, different⟩
  · intro fresh row member
    rw [NatIndexTree.find_insert, if_neg (fresh.2 row member)]
    exact fresh.1 row member

def EnumIdsInRange (rows : List EnumDef) : Prop :=
  ∀ row ∈ rows, row.id.index < 2 ^ 32

/-- Exact success characterization of the actual sparse scan. This proves
    admission soundness and completeness, including the Rust ID width. No
    external container law or Rust validation result is assumed. -/
theorem enumIdScan_spec (seen : NatIndexTree Unit) (rows : List EnumDef) :
    enumIdScan seen rows = true ↔
      EnumFreshIds seen rows ∧ EnumIdsDistinct rows ∧ EnumIdsInRange rows := by
  induction rows generalizing seen with
  | nil => simp [enumIdScan, EnumFreshIds, EnumIdsDistinct, EnumIdsInRange]
  | cons first rest ih =>
    by_cases bounded : first.id.index < 2 ^ 32
    · cases present : seen.find first.id.index with
      | some unit =>
        constructor
        · intro accepted
          simp [enumIdScan, bounded, present] at accepted
        · intro valid
          have absent := valid.1 first ((trustIrListMemConsSelf _ _))
          rw [present] at absent
          cases absent
      | none =>
        simp only [enumIdScan, if_pos bounded, present]
        rw [ih, fresh_insert]
        constructor
        · intro valid
          refine ⟨?_, ⟨valid.1.2, valid.2.1⟩, ?_⟩
          · intro row member
            cases member with
            | head => exact present
            | tail _ member => exact valid.1.1 row member
          · intro row member
            cases member with
            | head => exact bounded
            | tail _ member => exact valid.2.2 row member
        · intro valid
          exact ⟨⟨fun row member => valid.1 row (List.mem_cons_of_mem first member), valid.2.1.1⟩,
            valid.2.1.2, fun row member => valid.2.2 row (List.mem_cons_of_mem first member)⟩
    · constructor
      · intro accepted
        simp [enumIdScan, bounded] at accepted
      · intro valid
        exact False.elim (bounded (valid.2.2 first ((trustIrListMemConsSelf _ _))))

theorem enumIdsAdmitted_iff (rows : List EnumDef) :
    enumIdsAdmitted rows = true ↔ EnumIdsDistinct rows ∧ EnumIdsInRange rows := by
  have exactScan := enumIdScan_spec .empty rows
  constructor
  · intro accepted
    exact (exactScan.mp accepted).2
  · intro valid
    exact exactScan.mpr ⟨fun _ _ => rfl, valid⟩

private theorem distinct_identity (rows : List EnumDef) (distinct : EnumIdsDistinct rows)
    (left right : EnumDef) (leftMember : left ∈ rows) (rightMember : right ∈ rows)
    (identity : left.id.index = right.id.index) : left = right := by
  induction rows with
  | nil => cases leftMember
  | cons first rest ih =>
    cases leftMember with
    | head =>
      cases rightMember with
      | head => rfl
      | tail _ member => exact False.elim (distinct.1 right member identity.symm)
    | tail _ member =>
      cases rightMember with
      | head => exact False.elim (distinct.1 left member identity)
      | tail _ otherMember => exact ih distinct.2 member otherMember

/-- Successful admission establishes the local definition-identity premise
    for the definition actually returned by the evaluator. -/
theorem enum_lookup_agrees_of_admission (source : Environment) (ctx : EvalContext)
    (associated : CaptureSource source ctx) (admitted : enumIdsAdmitted source.enums = true)
    (id : EnumId) (definition : EnumDef) (resolved : ctx.enums id = some definition) :
    EnumLookupAgrees source id definition := by
  obtain ⟨member, identity⟩ := associated.enums id definition resolved
  intro row present sameId
  exact distinct_identity source.enums ((enumIdsAdmitted_iff source.enums).mp admitted).1
    row definition present member (congrArg EnumId.index (sameId.trans identity.symm))

/-- Compose checked original-row admission with the actual indexed execution
    guard and capture check. No separate lookup-agreement premise remains. -/
theorem enum_execution_active_of_admission (source : Environment) (ctx : EvalContext)
    (associated : CaptureSource source ctx) (admitted : enumIdsAdmitted source.enums = true)
    (id : EnumId) (definition : EnumDef) (resolved : ctx.enums id = some definition)
    (position : Nat) (indexed : (Index.ofEnvironment source).enumPositions.find id.index = some position)
    (layoutDefinition : EnumDef) (row : (trustIrListGet? source.enums position) = some layoutDefinition)
    (descriptor : EnumLayoutDescriptor) (selected : Nat)
    (valid : singleInhabitedValid layoutDefinition descriptor
      (layoutDefinition.variants.map (fun variant => variantUninhabited (Index.ofEnvironment source)
        (uninhabitedFacts (Index.ofEnvironment source)) variant.fields)) selected = true)
    (fuel : Nat) (values : List Value) (initialized : (Value.aggregate values).Initialized)
    (checked : checkClosureValueAt ctx (fuel + 1) (.Enum id) (.aggregate values) = .ok ()) :
    ∃ tag payload variant, values = tag :: payload ∧ EnumTagSelects definition tag selected ∧
      (trustIrListGet? definition.variants selected) = some variant ∧
      variantUninhabited (Index.ofEnvironment source)
        (uninhabitedFacts (Index.ofEnvironment source)) variant.fields = false :=
  enum_execution_single_inhabited_active source ctx associated id definition resolved
    (enum_lookup_agrees_of_admission source ctx associated admitted id definition resolved)
    position indexed layoutDefinition row descriptor selected valid fuel values initialized checked

end TrustIr.SourceLayout

namespace TrustIr.SourceLayout.EnumAdmissionControls

private def row (id : Nat) : EnumDef :=
  { id := ⟨id⟩, name := "Enum", variants := [{ name := "Unit", fields := [] }] }
private def altered : EnumDef :=
  { row 7 with name := "Different", variants := [{ name := "Never", fields := [.Never] }] }

theorem empty_admitted : enumIdsAdmitted [] = true := rfl

theorem sparse_ids_admitted : enumIdsAdmitted [row 4294967295, row 0, row 65537] = true := rfl

theorem sparse_permutation_admitted : enumIdsAdmitted [row 65537, row 4294967295, row 0] = true := rfl

theorem identical_duplicate_refused : enumIdsAdmitted [row 7, row 7] = false := rfl

theorem altered_duplicate_refused : enumIdsAdmitted [row 7, altered] = false := rfl

theorem nonadjacent_duplicate_refused : enumIdsAdmitted [row 7, row 4294967295, row 7] = false := rfl

theorem reserved_key_refused : enumIdScan ((NatIndexTree.empty : NatIndexTree Unit).insert 7 ())
    [row 7] = false := rfl

theorem other_reserved_key_admitted : enumIdScan ((NatIndexTree.empty : NatIndexTree Unit).insert 8 ())
    [row 7] = true := rfl

theorem sparse_rows_distinct : EnumIdsDistinct [row 4294967295, row 0, row 65537] :=
  ((enumIdsAdmitted_iff _).mp sparse_ids_admitted).1

private def raw : TrustIrEval.Module :=
  { hasTargetInfo := true, functions := [], funcTys := [], globals := [], enums := [row 7, altered],
    structs := [], records := [], types := [] }
private def ctx : EvalContext :=
  match TrustIrEval.contextOf raw 0 with | .ok context => context | .error _ => EvalContext.empty

theorem raw_duplicate_context_still_prepares : TrustIrEval.contextOf raw 0 = .ok ctx := rfl

theorem raw_duplicate_context_has_no_admission : enumIdsAdmitted raw.enums = false := rfl

theorem raw_duplicate_distinctness_impossible : ¬ EnumIdsDistinct raw.enums := by
  intro distinct
  exact distinct.1 altered ((trustIrListMemConsSelf _ _)) rfl

theorem out_of_range_refused : enumIdsAdmitted [row (2 ^ 32)] = false := rfl

theorem wide_out_of_range_refused : enumIdsAdmitted [row (2 ^ 64)] = false := rfl

end TrustIr.SourceLayout.EnumAdmissionControls
