-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceInhabitSound

namespace TrustIr.SourceLayout
open SourceValueMembership

/-- The actual discriminant-residue lookup, with the same effective values and
    canonical tag width used by the capture checker. -/
def EnumTagSelects (definition : EnumDef) (tag : Value) (position : Nat) : Prop :=
  ∃ discriminants repr width number, tag = Value.int width number ∧
    enumEffectiveDiscriminants definition = some discriminants ∧
    enumCanonicalTagRepr definition = some repr ∧
    listIndexOf? (discriminants.map (fun value => value % ((2 : Int) ^ repr.bitWidth))) number = some position

theorem EnumTagSelects.functional (definition : EnumDef) (tag : Value) (left right : Nat)
    (first : EnumTagSelects definition tag left) (second : EnumTagSelects definition tag right) : left = right := by
  obtain ⟨discs, repr, width, number, shape, actualDiscs, actualRepr, selected⟩ := first
  obtain ⟨otherDiscs, otherRepr, otherWidth, otherNumber, otherShape, otherActualDiscs, otherActualRepr, otherSelected⟩ := second
  have equalDiscs := Option.some.inj (actualDiscs.symm.trans otherActualDiscs)
  have equalRepr := Option.some.inj (actualRepr.symm.trans otherActualRepr)
  subst otherDiscs
  subst otherRepr
  have equalTag := shape.symm.trans otherShape
  cases equalTag
  exact Option.some.inj (selected.symm.trans otherSelected)

theorem enum_checked_tag_selection (ctx : EvalContext) (fuel : Nat) (id : EnumId) (definition : EnumDef)
    (resolved : ctx.enums id = some definition) (values : List Value)
    (checked : checkClosureValueAt ctx (fuel + 1) (.Enum id) (.aggregate values) = .ok ()) :
    ∃ tag payload position variant, values = tag :: payload ∧ EnumTagSelects definition tag position ∧
      (trustIrListGet? definition.variants position) = some variant ∧ variant.fields.length = payload.length ∧
      (variant.fields.zip payload).forM (fun (ty, value) => checkClosureValueAt ctx fuel ty value) = .ok () := by
  trustIrCompilerProof {
    rw [checkClosureValueAt.eq_2] at checked
    simp only [Value.isPoison, Value.isUninit, Bool.false_or, Bool.false_eq_true, ite_false,
      resolved, Except.bind, Except.pure, Bind.bind, Pure.pure] at checked
    split at checked
    · rename_i discs discsEq
      split at checked
      · rename_i repr reprEq
        cases values with
        | nil => cases checked
        | cons tag payload =>
          dsimp only at checked
          split at checked
          · cases checked
          · rename_i unit _tagChecked
            cases unit
            cases tag with
            | int width number =>
              dsimp only at checked
              split at checked
              · rename_i position selected
                split at checked
                · rename_i variant found
                  by_cases same : variant.fields.length = payload.length
                  · exact ⟨.int width number, payload, position, variant, rfl,
                      ⟨discs, repr, width, number, rfl, discsEq, reprEq, selected⟩, found, same,
                      by simpa [same] using checked⟩
                  · have different : (variant.fields.length != payload.length) = true := by simp [same]
                    simp [different] at checked
                · cases checked
              · cases checked
            | _ => cases checked
      · cases checked
    · cases checked
  } {
    rw [checkClosureValueAt] at checked
    simp only [Value.isPoison, Value.isUninit, Bool.false_or, Bool.false_eq_true, ite_false,
      resolved, Except.bind, Except.pure, Bind.bind, Pure.pure] at checked
    split at checked
    · rename_i discs discsEq
      split at checked
      · rename_i repr reprEq
        cases values with
        | nil => cases checked
        | cons tag payload =>
          dsimp only at checked
          split at checked
          · cases checked
          · rename_i unit _tagChecked
            cases unit
            cases tag with
            | int width number =>
              dsimp only at checked
              split at checked
              · rename_i position selected
                split at checked
                · rename_i variant found
                  by_cases same : variant.fields.length = payload.length
                  · exact ⟨.int width number, payload, position, variant, rfl,
                      ⟨discs, repr, width, number, rfl, discsEq, reprEq, selected⟩, found, same,
                      by simpa [same] using checked⟩
                  · have different : (variant.fields.length != payload.length) = true := by simp [same]
                    simp [different] at checked
                · cases checked
              · cases checked
            | _ => cases checked
      · cases checked
    · cases checked
  }

/-- The actual capture check selects a source variant with a false actual
    solver flag. The witness retains the exact evaluator-resolved definition;
    it does not substitute a layout-selected nominal duplicate. -/
theorem enum_capture_active_flag_false (source : Environment) (ctx : EvalContext)
    (associated : CaptureSource source ctx) (id : EnumId) (definition : EnumDef)
    (resolved : ctx.enums id = some definition) (fuel : Nat) (values : List Value)
    (initialized : (Value.aggregate values).Initialized)
    (checked : checkClosureValueAt ctx (fuel + 1) (.Enum id) (.aggregate values) = .ok ()) :
    ∃ tag payload position variant, values = tag :: payload ∧ EnumTagSelects definition tag position ∧
      (trustIrListGet? definition.variants position) = some variant ∧
      variantUninhabited (Index.ofEnvironment source)
        (uninhabitedFacts (Index.ofEnvironment source)) variant.fields = false := by
  obtain ⟨tag, payload, position, variant, shape, tagSelected, selected, length, traversal⟩ :=
    enum_checked_tag_selection ctx fuel id definition resolved values checked
  refine ⟨tag, payload, position, variant, shape, tagSelected, selected, ?_⟩
  cases flagged : variantUninhabited (Index.ofEnvironment source)
      (uninhabitedFacts (Index.ofEnvironment source)) variant.fields with
  | false => rfl
  | true =>
      have payloadInitialized : (Value.aggregate payload).Initialized :=
        .aggregate payload (fun value member => initialized.aggregate_child value
          (by rw [shape]; exact List.mem_cons_of_mem tag member))
      exact False.elim (variant_uninhabited_no_initialized_payload source ctx associated
        variant.fields flagged payload length payloadInitialized fuel traversal)

/-- The early physical selector guard marks every inactive original row.
    This uses the actual numbered guard, including its offset-row check. -/
theorem singleInhabitedValid_inactive_flag (definition : EnumDef)
    (descriptor : EnumLayoutDescriptor) (uninhabited : List Bool) (selected position : Nat)
    (valid : singleInhabitedValid definition descriptor uninhabited selected = true)
    (inactive : position ≠ selected) (flag : Bool)
    (found : (trustIrListGet? uninhabited position) = some flag) : flag = true := by
  trustIrCompilerProof {
    have guarded : (numbered uninhabited).all (fun (impossible, index) =>
        if index == selected then !impossible
        else impossible && (((trustIrListGet? descriptor.variantFieldOffsets index)).getD []).isEmpty) = true := by
      unfold singleInhabitedValid at valid
      exact (Bool.and_eq_true_iff _ _).mp valid |>.2
    have actual := List.all_eq_true.mp guarded (flag, position)
      ((numbered_member_iff_get uninhabited flag position).2 found)
    have different : (position == selected) = false := by simp [inactive]
    simp only [different, Bool.false_eq_true, ite_false] at actual
    exact ((Bool.and_eq_true_iff _ _).mp actual).1
  } {
    have guarded : (numbered uninhabited).all (fun (impossible, index) =>
        if index == selected then !impossible
        else impossible && (((trustIrListGet? descriptor.variantFieldOffsets index)).getD []).isEmpty) = true := by
      unfold singleInhabitedValid at valid
      exact Bool.and_eq_true_iff.mp valid |>.2
    have actual := List.all_eq_true.mp guarded (flag, position)
      ((numbered_member_iff_get uninhabited flag position).2 found)
    have different : (position == selected) = false := by simp [inactive]
    simp only [different, Bool.false_eq_true, ite_false] at actual
    exact (Bool.and_eq_true_iff.mp actual).1
  }

/-- An initialized accepted enum can only use the selected physical row when
    the no-tag guard belongs to its exact evaluator-resolved definition. -/
theorem enum_capture_single_inhabited_active (source : Environment) (ctx : EvalContext)
    (associated : CaptureSource source ctx) (id : EnumId) (definition : EnumDef)
    (resolved : ctx.enums id = some definition) (descriptor : EnumLayoutDescriptor)
    (selected : Nat)
    (valid : singleInhabitedValid definition descriptor
      (definition.variants.map (fun variant => variantUninhabited (Index.ofEnvironment source)
        (uninhabitedFacts (Index.ofEnvironment source)) variant.fields)) selected = true)
    (fuel : Nat) (values : List Value) (initialized : (Value.aggregate values).Initialized)
    (checked : checkClosureValueAt ctx (fuel + 1) (.Enum id) (.aggregate values) = .ok ()) :
    ∃ tag payload variant, values = tag :: payload ∧ EnumTagSelects definition tag selected ∧
      (trustIrListGet? definition.variants selected) = some variant ∧
      variantUninhabited (Index.ofEnvironment source)
        (uninhabitedFacts (Index.ofEnvironment source)) variant.fields = false := by
  trustIrCompilerProof {
    obtain ⟨tag, payload, position, variant, shape, tagSelected, found, live⟩ :=
      enum_capture_active_flag_false source ctx associated id definition resolved fuel values initialized checked
    have active : position = selected := by
      by_cases same : position = selected
      · exact same
      · have inactive := same
        have flagFound : (trustIrListGet? (definition.variants.map (fun variant => variantUninhabited
          (Index.ofEnvironment source) (uninhabitedFacts (Index.ofEnvironment source))
          variant.fields)) position) = some false := by
          rw [List.get?_map, found]
          simp only [Option.map, live]
        have impossible := singleInhabitedValid_inactive_flag definition descriptor _ selected position
          valid inactive false flagFound
        cases impossible
    subst position
    exact ⟨tag, payload, variant, shape, tagSelected, found, live⟩
  } {
    obtain ⟨tag, payload, position, variant, shape, tagSelected, found, live⟩ :=
      enum_capture_active_flag_false source ctx associated id definition resolved fuel values initialized checked
    have active : position = selected := by
      by_cases same : position = selected
      · exact same
      · have inactive := same
        have flagFound : (trustIrListGet? (definition.variants.map (fun variant => variantUninhabited
          (Index.ofEnvironment source) (uninhabitedFacts (Index.ofEnvironment source))
          variant.fields)) position) = some false := by
          rw [CompilerCompat.listGetConstructive_map, found]
          simp only [Option.map, live]
        have impossible := singleInhabitedValid_inactive_flag definition descriptor _ selected position
          valid inactive false flagFound
        cases impossible
    subst position
    exact ⟨tag, payload, variant, shape, tagSelected, found, live⟩
  }

/-- A local identity condition, weaker than globally unique nominal IDs.
    Equal duplicate enum rows are allowed. It must be established before
    transferring facts from a layout-selected row to an evaluator lookup. -/
def EnumLookupAgrees (source : Environment) (id : EnumId) (definition : EnumDef) : Prop :=
  ∀ row, row ∈ source.enums → row.id = id → row = definition

theorem enum_execution_position_resolves (source : Environment) (id : EnumId) (definition : EnumDef)
    (agrees : EnumLookupAgrees source id definition)
    (position : Nat) (selected : (Index.ofEnvironment source).enumPositions.find id.index = some position) :
    (trustIrListGet? source.enums position) = some definition := by
  obtain ⟨row, numberedRow, same⟩ := positionIndex_witness source.enums (·.id.index) id.index position selected
  have identity : row.id = id := congrArg EnumId.mk same
  have equal := agrees row (numbered_source_member _ _ _ numberedRow) identity
  exact equal ▸ numbered_get _ _ _ numberedRow

theorem enum_shape_position_resolves (source : Environment) (id : EnumId) (definition : EnumDef)
    (agrees : EnumLookupAgrees source id definition) (position : Nat)
    (selected : (Index.ofEnvironment source).enumShapePositions.find id.index = some position) :
    (trustIrListGet? source.enums position) = some definition := by
  obtain ⟨row, numberedRow, same⟩ := firstPositionIndex_witness source.enums (·.id.index) id.index position selected
  have identity : row.id = id := congrArg EnumId.mk same
  have equal := agrees row (numbered_source_member _ _ _ numberedRow) identity
  exact equal ▸ numbered_get _ _ _ numberedRow

/-- Transfer an actual execution-row guard only after proving nominal lookup
    agreement. Merely sharing an ID does not establish this premise. -/
theorem enum_execution_single_inhabited_active (source : Environment) (ctx : EvalContext)
    (associated : CaptureSource source ctx) (id : EnumId) (definition : EnumDef)
    (resolved : ctx.enums id = some definition) (agrees : EnumLookupAgrees source id definition)
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
        (uninhabitedFacts (Index.ofEnvironment source)) variant.fields = false := by
  have actual := enum_execution_position_resolves source id definition agrees position indexed
  have same : layoutDefinition = definition := Option.some.inj (row.symm.trans actual)
  subst layoutDefinition
  exact enum_capture_single_inhabited_active source ctx associated id definition resolved descriptor
    selected valid fuel values initialized checked

namespace ActiveEnumControls

private def descriptor : EnumLayoutDescriptor :=
  { encoding := .singleInhabited 1, size := 0, align := 1, variantFieldOffsets := [[], []] }
private def first : EnumDef :=
  { id := ⟨1⟩, name := "FirstLive", variants := [{ name := "InactiveButLive", fields := [.U8] },
      { name := "Active", fields := [] }] }
private def second : EnumDef :=
  { id := ⟨1⟩, name := "LayoutSelected", variants := [{ name := "Impossible", fields := [.Never] },
      { name := "Active", fields := [] }], layout := some descriptor }
private def module : TrustIrEval.Module :=
  { hasTargetInfo := true, functions := [], funcTys := [], globals := [], enums := [first, second],
    structs := [], records := [], types := [] }
private def ctx : EvalContext :=
  match TrustIrEval.contextOf module 0 with
  | .ok context => context
  | .error _ => EvalContext.empty
private def source : Environment := decodedCaptureSource module ctx.byteModel
private def facts : NatIndexTree Unit := uninhabitedFacts (Index.ofEnvironment source)

theorem duplicate_context_prepares : TrustIrEval.contextOf module 0 = .ok ctx := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem duplicate_capture_source : CaptureSource source ctx :=
  contextOf_capture_source module 0 ctx duplicate_context_prepares (by
    intro id definition member
    change (id, some definition) ∈ ([] : List (RecordId × Option RecordDef)) at member
    cases member)

theorem duplicate_evaluator_selects_first : ctx.enums ⟨1⟩ = some first := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem duplicate_execution_selects_second :
    (Index.ofEnvironment source).enumPositions.find 1 = some 1 := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem duplicate_shape_selects_first :
    (Index.ofEnvironment source).enumShapePositions.find 1 = some 0 := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem duplicate_selected_row : (trustIrListGet? source.enums 1) = some second := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem duplicate_layout_guard_accepts : singleInhabitedValid second descriptor
    (second.variants.map (fun variant => variantUninhabited (Index.ofEnvironment source) facts variant.fields))
    1 = true := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem duplicate_evaluator_guard_refuses : singleInhabitedValid first descriptor
    (first.variants.map (fun variant => variantUninhabited (Index.ofEnvironment source) facts variant.fields))
    1 = false := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem duplicate_inactive_value_initialized :
    (Value.aggregate [.int 8 0, .int 8 7]).Initialized :=
  .aggregate _ (by
    intro value member
    cases member with
    | head => exact .int 8 0
    | tail _ member =>
      cases member with
      | head => exact .int 8 7
      | tail _ impossible => cases impossible)

set_option maxRecDepth 4096 in
theorem duplicate_inactive_value_accepted :
    checkClosureValueAt ctx 2 (.Enum ⟨1⟩) (.aggregate [.int 8 0, .int 8 7]) = .ok () := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem duplicate_lookup_agreement_fails : ¬ EnumLookupAgrees source ⟨1⟩ first := by
  intro agrees
  have same := agrees second (List.mem_cons_of_mem first ((trustIrListMemConsSelf _ _))) rfl
  have names := congrArg EnumDef.name same
  have different : second.name ≠ first.name := by decide
  exact different names

private def identical : Environment := { source with enums := [first, first] }

theorem equal_duplicates_agree : EnumLookupAgrees identical ⟨1⟩ first := by
  intro row member _identity
  change row ∈ [first, first] at member
  cases member with
  | head => rfl
  | tail _ member =>
    cases member with
    | head => rfl
    | tail _ impossible => cases impossible

theorem equal_duplicates_execution_resolves :
    (trustIrListGet? identical.enums 1) = some first :=
  enum_execution_position_resolves identical ⟨1⟩ first equal_duplicates_agree 1 rfl

theorem equal_duplicates_shape_resolves :
    (trustIrListGet? identical.enums 0) = some first :=
  enum_shape_position_resolves identical ⟨1⟩ first equal_duplicates_agree 0 rfl

private def positiveModule : TrustIrEval.Module := { module with enums := [second] }
private def positiveCtx : EvalContext :=
  match TrustIrEval.contextOf positiveModule 0 with
  | .ok context => context
  | .error _ => EvalContext.empty
private def positiveSource : Environment := decodedCaptureSource positiveModule positiveCtx.byteModel

theorem positive_context_prepares : TrustIrEval.contextOf positiveModule 0 = .ok positiveCtx := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem positive_capture_source : CaptureSource positiveSource positiveCtx :=
  contextOf_capture_source positiveModule 0 positiveCtx positive_context_prepares (by
    intro id definition member
    change (id, some definition) ∈ ([] : List (RecordId × Option RecordDef)) at member
    cases member)

theorem positive_lookup_agrees : EnumLookupAgrees positiveSource ⟨1⟩ second := by
  intro row member _identity
  change row ∈ [second] at member
  cases member with
  | head => rfl
  | tail _ impossible => cases impossible

set_option maxRecDepth 4096 in
theorem positive_selected_value_accepted :
    checkClosureValueAt positiveCtx 2 (.Enum ⟨1⟩) (.aggregate [.int 8 1]) = .ok () := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem positive_selected_value_initialized : (Value.aggregate [.int 8 1]).Initialized :=
  .aggregate _ (by
    intro value member
    cases member with
    | head => exact .int 8 1
    | tail _ impossible => cases impossible)

theorem positive_guard_selects_actual_payload :
    ∃ tag payload variant, [Value.int 8 1] = tag :: payload ∧ EnumTagSelects second tag 1 ∧
      (trustIrListGet? second.variants 1) = some variant ∧
      variantUninhabited (Index.ofEnvironment positiveSource)
        (uninhabitedFacts (Index.ofEnvironment positiveSource)) variant.fields = false :=
  enum_execution_single_inhabited_active positiveSource positiveCtx positive_capture_source ⟨1⟩ second
    rfl positive_lookup_agrees 0 rfl second rfl descriptor 1 rfl 1 [.int 8 1]
    positive_selected_value_initialized positive_selected_value_accepted

end ActiveEnumControls
end TrustIr.SourceLayout
