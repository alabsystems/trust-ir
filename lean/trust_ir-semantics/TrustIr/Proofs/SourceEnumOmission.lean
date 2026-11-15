-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceEnumAdmission

namespace TrustIr.SourceLayout

/-- The named compiler selector has exactly its original inline body. -/
theorem enumPhysicalSelection_eq_original (definition : EnumDef) (uninhabited : List Bool) :
    enumPhysicalSelection definition uninhabited =
      (match definition.layout with
      | some descriptor => match descriptor.encoding with
        | .singleInhabited selected =>
          if singleInhabitedValid definition descriptor uninhabited selected then some selected else none
        | _ => none
      | none => none) := rfl

/-- A real selection authenticates the original authored descriptor, encoding
    and complete early guard. It cannot arise from a caller-chosen flag. -/
theorem enumPhysicalSelection_some (definition : EnumDef) (uninhabited : List Bool) (selected : Nat)
    (chosen : enumPhysicalSelection definition uninhabited = some selected) :
    ∃ descriptor, definition.layout = some descriptor ∧ descriptor.encoding = .singleInhabited selected ∧
      singleInhabitedValid definition descriptor uninhabited selected = true := by
  cases authored : definition.layout with
  | none => simp [enumPhysicalSelection, authored] at chosen
  | some descriptor =>
    cases encoding : descriptor.encoding with
    | singleInhabited position =>
      by_cases valid : singleInhabitedValid definition descriptor uninhabited position = true
      · have same : position = selected := by
          simpa [enumPhysicalSelection, authored, encoding, valid] using chosen
        subst selected
        exact ⟨descriptor, rfl, encoding, valid⟩
      · simp [enumPhysicalSelection, authored, encoding, valid] at chosen
    | _ => simp [enumPhysicalSelection, authored, encoding] at chosen

/-- The actual omission branch cannot skip an initialized active variant
    accepted by the actual checker for that same resolved definition. -/
theorem enum_physical_omission_refuses_initialized (source : Environment) (ctx : EvalContext)
    (associated : CaptureSource source ctx) (id : EnumId) (definition : EnumDef)
    (resolved : ctx.enums id = some definition) (tag : Value) (payload : List Value) (position : Nat)
    (tagSelects : EnumTagSelects definition tag position)
    (omitted : (enumPhysicalSelection definition (definition.variants.map (fun variant =>
      variantUninhabited (Index.ofEnvironment source) (uninhabitedFacts (Index.ofEnvironment source))
        variant.fields))).any (fun active => position != active) = true)
    (initialized : (Value.aggregate (tag :: payload)).Initialized) (fuel : Nat)
    (checked : checkClosureValueAt ctx (fuel + 1) (.Enum id) (.aggregate (tag :: payload)) = .ok ()) : False := by
  cases selection : enumPhysicalSelection definition (definition.variants.map (fun variant =>
      variantUninhabited (Index.ofEnvironment source) (uninhabitedFacts (Index.ofEnvironment source))
        variant.fields)) with
  | none => simp [selection, Option.any] at omitted
  | some selected =>
    obtain ⟨descriptor, _authored, _encoding, valid⟩ := enumPhysicalSelection_some definition _ selected selection
    obtain ⟨actualTag, _actualPayload, _variant, shape, activeTag, _found, _live⟩ :=
      enum_capture_single_inhabited_active source ctx associated id definition resolved descriptor selected valid
        fuel (tag :: payload) initialized checked
    have actualSelection : EnumTagSelects definition tag selected := by
      rw [(List.cons.inj shape).1]
      exact activeTag
    have active := EnumTagSelects.functional definition tag position selected tagSelects actualSelection
    simp [selection, active, Option.any] at omitted

/-- Apply the actual compiler omission decision at the actual execution-index
    row. Checked original-row admission discharges nominal lookup identity. -/
theorem enum_execution_omission_refuses_initialized (source : Environment) (ctx : EvalContext)
    (associated : CaptureSource source ctx) (admitted : enumIdsAdmitted source.enums = true)
    (id : EnumId) (definition : EnumDef) (resolved : ctx.enums id = some definition)
    (sourcePosition : Nat)
    (indexed : (Index.ofEnvironment source).enumPositions.find id.index = some sourcePosition)
    (layoutDefinition : EnumDef) (row : (trustIrListGet? source.enums sourcePosition) = some layoutDefinition)
    (tag : Value) (payload : List Value) (position : Nat)
    (tagSelects : EnumTagSelects definition tag position)
    (omitted : (enumPhysicalSelection layoutDefinition (layoutDefinition.variants.map (fun variant =>
      variantUninhabited (Index.ofEnvironment source) (uninhabitedFacts (Index.ofEnvironment source))
        variant.fields))).any (fun active => position != active) = true)
    (initialized : (Value.aggregate (tag :: payload)).Initialized) (fuel : Nat)
    (checked : checkClosureValueAt ctx (fuel + 1) (.Enum id) (.aggregate (tag :: payload)) = .ok ()) : False := by
  have actual := enum_execution_position_resolves source id definition
    (enum_lookup_agrees_of_admission source ctx associated admitted id definition resolved) sourcePosition indexed
  have same := Option.some.inj (row.symm.trans actual)
  subst layoutDefinition
  exact enum_physical_omission_refuses_initialized source ctx associated id definition resolved
    tag payload position tagSelects omitted initialized fuel checked

/-- A successful initialized capture retains its exact tag/variant witness and
    proves that the compiler's actual physical omission condition is false. -/
theorem enum_capture_active_not_omitted (source : Environment) (ctx : EvalContext)
    (associated : CaptureSource source ctx) (admitted : enumIdsAdmitted source.enums = true)
    (id : EnumId) (definition : EnumDef) (resolved : ctx.enums id = some definition)
    (sourcePosition : Nat)
    (indexed : (Index.ofEnvironment source).enumPositions.find id.index = some sourcePosition)
    (layoutDefinition : EnumDef) (row : (trustIrListGet? source.enums sourcePosition) = some layoutDefinition)
    (fuel : Nat) (values : List Value) (initialized : (Value.aggregate values).Initialized)
    (checked : checkClosureValueAt ctx (fuel + 1) (.Enum id) (.aggregate values) = .ok ()) :
    ∃ tag payload position variant, values = tag :: payload ∧ EnumTagSelects definition tag position ∧
      (trustIrListGet? definition.variants position) = some variant ∧
      (enumPhysicalSelection layoutDefinition (layoutDefinition.variants.map (fun variant =>
        variantUninhabited (Index.ofEnvironment source) (uninhabitedFacts (Index.ofEnvironment source))
          variant.fields))).any (fun active => position != active) = false := by
  obtain ⟨tag, payload, position, variant, shape, selected, found, _live⟩ :=
    enum_capture_active_flag_false source ctx associated id definition resolved fuel values initialized checked
  refine ⟨tag, payload, position, variant, shape, selected, found, ?_⟩
  cases omitted : (enumPhysicalSelection layoutDefinition (layoutDefinition.variants.map (fun variant =>
      variantUninhabited (Index.ofEnvironment source) (uninhabitedFacts (Index.ofEnvironment source))
        variant.fields))).any (fun active => position != active) with
  | false => rfl
  | true =>
    rw [shape] at initialized checked
    exact False.elim (enum_execution_omission_refuses_initialized source ctx associated admitted id definition
      resolved sourcePosition indexed layoutDefinition row tag payload position selected omitted initialized fuel checked)

end TrustIr.SourceLayout

namespace TrustIr.SourceLayout.PhysicalOmissionControls

private def descriptor : EnumLayoutDescriptor :=
  { encoding := .singleInhabited 1, size := 4, align := 4, variantFieldOffsets := [[], [0]] }
private def definition : EnumDef :=
  { id := ⟨7⟩, name := "Omission", variants := [{ name := "Dead", fields := [.Never] },
      { name := "Live", fields := [.U32] }], layout := some descriptor }
private def raw : TrustIrEval.Module :=
  { hasTargetInfo := true, functions := [], funcTys := [], globals := [], enums := [definition],
    structs := [], records := [], types := [] }
private def context (m : TrustIrEval.Module) : EvalContext :=
  match TrustIrEval.contextOf m 0 with | .ok ctx => ctx | .error _ => EvalContext.empty
private def ctx : EvalContext := context raw
private def source : Environment := decodedCaptureSource raw ctx.byteModel
private def flags : List Bool := definition.variants.map (fun variant =>
  variantUninhabited (Index.ofEnvironment source) (uninhabitedFacts (Index.ofEnvironment source)) variant.fields)

private theorem prepares : TrustIrEval.contextOf raw 0 = .ok ctx := rfl
private theorem associated : CaptureSource source ctx :=
  contextOf_capture_source raw 0 ctx prepares (by
    intro id row member
    change (id, some row) ∈ ([] : List (RecordId × Option RecordDef)) at member
    cases member)

theorem actual_selection : enumPhysicalSelection definition flags = some 1 := rfl

theorem actual_dead_omitted : (enumPhysicalSelection definition flags).any (fun active => 0 != active) = true := rfl

theorem actual_live_retained : (enumPhysicalSelection definition flags).any (fun active => 1 != active) = false := rfl

theorem active_value_initialized : (Value.aggregate [.int 8 1, .int 32 7]).Initialized :=
  .aggregate _ (by
    intro value member
    cases member with
    | head => exact .int 8 1
    | tail _ member =>
      cases member with
      | head => exact .int 32 7
      | tail _ impossible => cases impossible)

set_option maxRecDepth 4096 in
theorem active_value_accepted :
    checkClosureValueAt ctx 2 (.Enum ⟨7⟩) (.aggregate [.int 8 1, .int 32 7]) = .ok () := rfl

theorem actual_capture_never_omits_active :
    ∃ tag payload position variant, [Value.int 8 1, .int 32 7] = tag :: payload ∧
      EnumTagSelects definition tag position ∧ (trustIrListGet? definition.variants position) = some variant ∧
      (enumPhysicalSelection definition flags).any (fun active => position != active) = false :=
  enum_capture_active_not_omitted source ctx associated rfl ⟨7⟩ definition rfl 0 rfl definition rfl
    1 [.int 8 1, .int 32 7] active_value_initialized active_value_accepted

private def transportDefinition : EnumDef :=
  { definition with variants := [{ name := "Dead", fields := [.Tuple [.Never]] }, { name := "Live", fields := [.U32] }] }
private def transportModule : TrustIrEval.Module := { raw with enums := [transportDefinition] }
private def transportCtx : EvalContext := context transportModule
private def transportSource : Environment := decodedCaptureSource transportModule transportCtx.byteModel

set_option maxRecDepth 4096 in
theorem unwritten_inactive_value_accepted :
    checkClosureValueAt transportCtx 3 (.Enum ⟨7⟩)
      (.aggregate [.int 8 0, .aggregate [.uninit]]) = .ok () := rfl

theorem unwritten_inactive_not_initialized :
    ¬ (Value.aggregate [.int 8 0, .aggregate [.uninit]]).Initialized := by
  intro initialized
  have tuple := initialized.aggregate_child (.aggregate [.uninit])
    (List.mem_cons_of_mem (Value.int 8 0) ((trustIrListMemConsSelf _ _)))
  have impossible := tuple.aggregate_child .uninit ((trustIrListMemConsSelf _ _))
  cases impossible

theorem unwritten_definition_omits_inactive :
    (enumPhysicalSelection transportDefinition (transportDefinition.variants.map (fun variant =>
      variantUninhabited (Index.ofEnvironment transportSource) (uninhabitedFacts (Index.ofEnvironment transportSource))
        variant.fields))).any (fun active => 0 != active) = true := rfl

theorem inactive_offset_blocks_selection :
    enumPhysicalSelection { definition with layout := some { descriptor with variantFieldOffsets := [[0], [0]] } }
      flags = none := rfl

theorem selected_never_blocks_selection :
    enumPhysicalSelection { definition with layout := some { descriptor with encoding := .singleInhabited 0 } }
      flags = none := rfl

theorem canonical_has_no_physical_skip : enumPhysicalSelection { definition with layout := none } flags = none := rfl

private def first : EnumDef :=
  { id := ⟨1⟩, name := "First", variants := [{ name := "Live0", fields := [.U8] }, { name := "Live1", fields := [] }] }
private def second : EnumDef :=
  { id := ⟨1⟩, name := "Second", variants := [{ name := "Dead0", fields := [.Never] }, { name := "Live1", fields := [] }],
    layout := some { descriptor with size := 0, align := 1, variantFieldOffsets := [[], []] } }
private def duplicate : TrustIrEval.Module := { raw with enums := [first, second] }
private def dupCtx : EvalContext := context duplicate
private def dupSource : Environment := decodedCaptureSource duplicate dupCtx.byteModel

theorem duplicate_context_prepares : TrustIrEval.contextOf duplicate 0 = .ok dupCtx := rfl

theorem duplicate_execution_selects_other :
    (Index.ofEnvironment dupSource).enumPositions.find 1 = some 1 := rfl

theorem duplicate_layout_omits_live_capture_row :
    (enumPhysicalSelection second (second.variants.map (fun variant =>
      variantUninhabited (Index.ofEnvironment dupSource) (uninhabitedFacts (Index.ofEnvironment dupSource))
        variant.fields))).any (fun active => 0 != active) = true := rfl

theorem duplicate_value_initialized : (Value.aggregate [.int 8 0, .int 8 7]).Initialized :=
  .aggregate _ (by
    intro value member
    cases member with
    | head => exact .int 8 0
    | tail _ member =>
      cases member with
      | head => exact .int 8 7
      | tail _ impossible => cases impossible)

set_option maxRecDepth 4096 in
theorem duplicate_live_capture_accepted :
    checkClosureValueAt dupCtx 2 (.Enum ⟨1⟩) (.aggregate [.int 8 0, .int 8 7]) = .ok () := rfl

theorem duplicate_has_no_admission : enumIdsAdmitted dupSource.enums = false := rfl

private theorem transport_associated : CaptureSource transportSource transportCtx :=
  contextOf_capture_source transportModule 0 transportCtx rfl (by
    intro id row member
    change (id, some row) ∈ ([] : List (RecordId × Option RecordDef)) at member
    cases member)

/-- All source/admission/tag/check premises hold while deep initialization
    fails: nested tuple unwritten transport is a real excluded carrier. -/
theorem initialization_hypothesis_needed :
    CaptureSource transportSource transportCtx ∧ enumIdsAdmitted transportSource.enums = true ∧
      transportCtx.enums ⟨7⟩ = some transportDefinition ∧ EnumTagSelects transportDefinition (.int 8 0) 0 ∧
      (enumPhysicalSelection transportDefinition (transportDefinition.variants.map (fun variant =>
        variantUninhabited (Index.ofEnvironment transportSource) (uninhabitedFacts (Index.ofEnvironment transportSource))
          variant.fields))).any (fun active => 0 != active) = true ∧
      checkClosureValueAt transportCtx 3 (.Enum ⟨7⟩) (.aggregate [.int 8 0, .aggregate [.uninit]]) = .ok () ∧
      ¬ (Value.aggregate [.int 8 0, .aggregate [.uninit]]).Initialized :=
  ⟨transport_associated, rfl, rfl, ⟨[0, 1], .u8, 8, 0, rfl, rfl, rfl, rfl⟩,
    unwritten_definition_omits_inactive, unwritten_inactive_value_accepted, unwritten_inactive_not_initialized⟩

private theorem duplicate_associated : CaptureSource dupSource dupCtx :=
  contextOf_capture_source duplicate 0 dupCtx duplicate_context_prepares (by
    intro id row member
    change (id, some row) ∈ ([] : List (RecordId × Option RecordDef)) at member
    cases member)

/-- Actual execution indexing and initialized capture disagree on this raw
    duplicate table. Every relevant lookup/tag/check is retained, and the ID
    admission premise is explicitly false. -/
theorem nominal_admission_hypothesis_needed :
    CaptureSource dupSource dupCtx ∧ dupCtx.enums ⟨1⟩ = some first ∧
      (Index.ofEnvironment dupSource).enumPositions.find 1 = some 1 ∧
      (trustIrListGet? dupSource.enums 1) = some second ∧ EnumTagSelects first (.int 8 0) 0 ∧
      (enumPhysicalSelection second (second.variants.map (fun variant =>
        variantUninhabited (Index.ofEnvironment dupSource) (uninhabitedFacts (Index.ofEnvironment dupSource))
          variant.fields))).any (fun active => 0 != active) = true ∧
      (Value.aggregate [.int 8 0, .int 8 7]).Initialized ∧
      checkClosureValueAt dupCtx 2 (.Enum ⟨1⟩) (.aggregate [.int 8 0, .int 8 7]) = .ok () ∧
      enumIdsAdmitted dupSource.enums = false :=
  ⟨duplicate_associated, rfl, duplicate_execution_selects_other, rfl,
    ⟨[0, 1], .u8, 8, 0, rfl, rfl, rfl, rfl⟩, duplicate_layout_omits_live_capture_row,
    duplicate_value_initialized, duplicate_live_capture_accepted, duplicate_has_no_admission⟩

end TrustIr.SourceLayout.PhysicalOmissionControls
