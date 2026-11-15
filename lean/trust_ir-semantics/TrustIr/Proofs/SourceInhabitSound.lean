-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceNodeMeaning
import TrustIr.Proofs.SourceValueMembership
import TrustIr.DecodedContext

namespace TrustIr.SourceLayout
open SourceValueMembership

/-- Successful evaluator lookups retain actual source membership and identity.
    Missing/unsupported entries may still refuse. No unique-ID assumption or
    equality between shape and execution selection is imposed. Records need
    the actual outer-key/inner-ID coherence supplied by successful decoding. -/
structure CaptureSource (source : Environment) (ctx : EvalContext) : Prop where
  types : ∀ id ty, ctx.types id = some ty → (trustIrListGet? source.types id.index) = some (some ty)
  structs : ∀ id definition, ctx.structs id = some definition →
    definition ∈ source.structs ∧ definition.id = id
  enums : ∀ id definition, ctx.enums id = some definition →
    definition ∈ source.enums ∧ definition.id = id
  records : ∀ id definition, ctx.records id = some definition →
    definition ∈ source.records ∧ definition.id = id

def CaptureNodeSound (source : Environment) (ctx : EvalContext) (node : Nat) : Prop :=
  ∀ ty, SourceNodeDenotes source node ty → NoInitializedCapture ctx ty

def CaptureFactsSound (source : Environment) (ctx : EvalContext) (facts : NatIndexTree Unit) : Prop :=
  ∀ node, facts.find node = some () → CaptureNodeSound source ctx node

private theorem ref_fact (facts : NatIndexTree Unit) (node : Nat)
    (enabled : (Formula.ref node).holds facts = true) : facts.find node = some () := by
  cases found : facts.find node with
  | none => simp [Formula.holds, found] at enabled
  | some unit => cases unit; rfl

private theorem array_resolved_empty (ctx : EvalContext) (id : TyId) (count : Nat) (positive : 0 < count)
    (every : ∀ element, ctx.types id = some element → NoInitializedCapture ctx element) :
    NoInitializedCapture ctx (.Array id count) := by
  trustIrCompilerProof {
    cases resolved : ctx.types id with
    | some element => exact array_empty_of_element ctx id element resolved count positive (every element resolved)
    | none =>
        intro fuel value _initialized checked
        cases fuel with
        | zero => cases checked
        | succ fuel =>
            obtain ⟨values, rfl⟩ := array_shape ctx _ id count value checked
            rw [checkClosureValueAt.eq_2] at checked
            simp only [Value.isPoison, Value.isUninit, Bool.false_or, Bool.false_eq_true, ite_false,
              resolved, Except.bind, Except.pure, Bind.bind, Pure.pure] at checked
  } {
    cases resolved : ctx.types id with
    | some element => exact array_empty_of_element ctx id element resolved count positive (every element resolved)
    | none =>
        intro fuel value _initialized checked
        cases fuel with
        | zero => cases checked
        | succ fuel =>
            obtain ⟨values, rfl⟩ := array_shape ctx _ id count value checked
            rw [checkClosureValueAt] at checked
            simp only [Value.isPoison, Value.isUninit, Bool.false_or, Bool.false_eq_true, ite_false,
              resolved, Except.bind, Except.pure, Bind.bind, Pure.pure] at checked
            cases checked
  }

private theorem struct_resolved_empty (ctx : EvalContext) (id : StructId)
    (every : ∀ definition, ctx.structs id = some definition →
      ∃ field, field ∈ definition.fields ∧ NoInitializedCapture ctx field.ty) :
    NoInitializedCapture ctx (.Struct id) := by
  trustIrCompilerProof {
    cases resolved : ctx.structs id with
    | some definition =>
        obtain ⟨field, member, empty⟩ := every definition resolved
        exact struct_empty_of_field ctx id definition resolved field member empty
    | none =>
        intro fuel value _initialized checked
        cases fuel with
        | zero => cases checked
        | succ fuel =>
            obtain ⟨values, rfl⟩ := struct_shape ctx _ id value checked
            rw [checkClosureValueAt.eq_2] at checked
            simp only [Value.isPoison, Value.isUninit, Bool.false_or, Bool.false_eq_true, ite_false,
              resolved, Except.bind, Except.pure, Bind.bind, Pure.pure] at checked
  } {
    cases resolved : ctx.structs id with
    | some definition =>
        obtain ⟨field, member, empty⟩ := every definition resolved
        exact struct_empty_of_field ctx id definition resolved field member empty
    | none =>
        intro fuel value _initialized checked
        cases fuel with
        | zero => cases checked
        | succ fuel =>
            obtain ⟨values, rfl⟩ := struct_shape ctx _ id value checked
            rw [checkClosureValueAt] at checked
            simp only [Value.isPoison, Value.isUninit, Bool.false_or, Bool.false_eq_true, ite_false,
              resolved, Except.bind, Except.pure, Bind.bind, Pure.pure] at checked
            cases checked
  }

private theorem record_resolved_empty (ctx : EvalContext) (id : RecordId)
    (every : ∀ definition, ctx.records id = some definition →
      ∃ field, field ∈ definition.fields ∧ NoInitializedCapture ctx field.ty) :
    NoInitializedCapture ctx (.Record id) := by
  trustIrCompilerProof {
    cases resolved : ctx.records id with
    | some definition =>
        obtain ⟨field, member, empty⟩ := every definition resolved
        exact record_empty_of_field ctx id definition resolved field member empty
    | none =>
        intro fuel value _initialized checked
        cases fuel with
        | zero => cases checked
        | succ fuel =>
            obtain ⟨fields, rfl⟩ := record_shape ctx _ id value checked
            rw [checkClosureValueAt.eq_2] at checked
            simp only [Value.isPoison, Value.isUninit, Bool.false_or, Bool.false_eq_true, ite_false,
              resolved, Except.bind, Except.pure, Bind.bind, Pure.pure] at checked
  } {
    cases resolved : ctx.records id with
    | some definition =>
        obtain ⟨field, member, empty⟩ := every definition resolved
        exact record_empty_of_field ctx id definition resolved field member empty
    | none =>
        intro fuel value _initialized checked
        cases fuel with
        | zero => cases checked
        | succ fuel =>
            obtain ⟨fields, rfl⟩ := record_shape ctx _ id value checked
            rw [checkClosureValueAt] at checked
            simp only [Value.isPoison, Value.isUninit, Bool.false_or, Bool.false_eq_true, ite_false,
              resolved, Except.bind, Except.pure, Bind.bind, Pure.pure] at checked
            cases checked
  }

private theorem enum_resolved_empty (ctx : EvalContext) (id : EnumId)
    (every : ∀ definition, ctx.enums id = some definition → ∀ variant ∈ definition.variants,
      ∃ ty, ty ∈ variant.fields ∧ NoInitializedCapture ctx ty) :
    NoInitializedCapture ctx (.Enum id) := by
  trustIrCompilerProof {
    cases resolved : ctx.enums id with
    | some definition => exact enum_empty_of_variants ctx id definition resolved (every definition resolved)
    | none =>
        intro fuel value _initialized checked
        cases fuel with
        | zero => cases checked
        | succ fuel =>
            obtain ⟨values, rfl⟩ := enum_shape ctx _ id value checked
            rw [checkClosureValueAt.eq_2] at checked
            simp only [Value.isPoison, Value.isUninit, Bool.false_or, Bool.false_eq_true, ite_false,
              resolved, Except.bind, Except.pure, Bind.bind, Pure.pure] at checked
  } {
    cases resolved : ctx.enums id with
    | some definition => exact enum_empty_of_variants ctx id definition resolved (every definition resolved)
    | none =>
        intro fuel value _initialized checked
        cases fuel with
        | zero => cases checked
        | succ fuel =>
            obtain ⟨values, rfl⟩ := enum_shape ctx _ id value checked
            rw [checkClosureValueAt] at checked
            simp only [Value.isPoison, Value.isUninit, Bool.false_or, Bool.false_eq_true, ite_false,
              resolved, Except.bind, Except.pure, Bind.bind, Pure.pure] at checked
            cases checked
  }

/-- Refine currently has no capture-carrier rule. This is a checker refusal,
    not a semantic emptiness or implementation-support claim for refinements. -/
private theorem refine_capture_refuses (ctx : EvalContext) (id : TyId) (predicate : PredId) :
    NoInitializedCapture ctx (.Refine id predicate) := by
  intro fuel value _initialized checked
  cases fuel with
  | zero => cases checked
  | succ fuel =>
      cases value <;> simp [checkClosureValueAt, Value.isPoison, Value.isUninit, Ty.isInteger] at checked
      all_goals cases checked

private theorem fields_witness (index : Index) (facts : NatIndexTree Unit) (fields : List Ty)
    (enabled : Formula.someHold facts (inhabitFormulas index fields) = true) :
    ∃ ty, ty ∈ fields ∧ (inhabitFormula index ty).holds facts = true := by
  revert enabled
  induction fields with
  | nil => intro enabled; simp only [inhabitFormulas, Formula.someHold, Bool.false_eq_true] at enabled
  | cons first rest ih =>
      intro enabled
      simp only [inhabitFormulas, Formula.someHold] at enabled
      cases firstEnabled : (inhabitFormula index first).holds facts
      · obtain ⟨ty, member, accepted⟩ := ih (by simpa [firstEnabled] using enabled)
        exact ⟨ty, List.mem_cons_of_mem first member, accepted⟩
      · exact ⟨first, (trustIrListMemConsSelf _ _), firstEnabled⟩

theorem inhabitFormula_capture_sound (source : Environment) (ctx : EvalContext)
    (associated : CaptureSource source ctx) (facts : NatIndexTree Unit)
    (valid : CaptureFactsSound source ctx facts) (ty : Ty) :
    (inhabitFormula (Index.ofEnvironment source) ty).holds facts = true → NoInitializedCapture ctx ty := by
  induction ty using Ty.rec
      (motive_2 := fun fields => ∀ ty ∈ fields,
        (inhabitFormula (Index.ofEnvironment source) ty).holds facts = true → NoInitializedCapture ctx ty) with
  | Never => intro _enabled; exact never_empty ctx
  | Tuple fields ih =>
      intro enabled
      obtain ⟨ty, member, accepted⟩ := fields_witness (Index.ofEnvironment source) facts fields
        (by simpa only [inhabitFormula, Formula.holds] using enabled)
      exact tuple_empty_of_field ctx fields ty member (ih ty member accepted)
  | Array id count =>
      intro enabled
      simp only [inhabitFormula] at enabled
      split at enabled
      · simp only [Formula.holds, Bool.false_eq_true] at enabled
      · rename_i available
        have positive : 0 < count := by
          by_cases zero : count = 0
          · simp [zero] at available
          · omega
        apply array_resolved_empty ctx id count positive
        intro element resolved
        have member := (numbered_member_iff_get source.types (some element) id.index).2
          (associated.types id element resolved)
        exact valid id.index (ref_fact facts id.index enabled) element (.typeRow element id.index member)
  | Struct id =>
      intro enabled
      simp only [inhabitFormula] at enabled
      cases selected : (Index.ofEnvironment source).structPositions.find id.index with
      | none => simp [selected, Formula.holds] at enabled
      | some position =>
          apply valid _ (ref_fact facts _ (by simpa only [selected] using enabled)) _
          exact SourceNodeDenotes.struct_alias source id position selected
  | Enum id =>
      intro enabled
      simp only [inhabitFormula] at enabled
      cases selected : (Index.ofEnvironment source).enumPositions.find id.index with
      | none => simp [selected, Formula.holds] at enabled
      | some position =>
          apply valid _ (ref_fact facts _ (by simpa only [selected] using enabled)) _
          exact SourceNodeDenotes.enum_alias source id position selected
  | Record id =>
      intro enabled
      simp only [inhabitFormula] at enabled
      cases selected : (Index.ofEnvironment source).recordPositions.find id.index with
      | none => simp [selected, Formula.holds] at enabled
      | some position =>
          apply valid _ (ref_fact facts _ (by simpa only [selected] using enabled)) _
          exact SourceNodeDenotes.record_alias source id position selected
  | Refine id predicate => intro _enabled; exact refine_capture_refuses ctx id predicate
  | nil ty member _enabled => cases member
  | cons first rest ihFirst ihRest ty member enabled =>
      cases member with
      | head => exact ihFirst enabled
      | tail _ member => exact ihRest ty member enabled
  | _ => intro enabled; simp only [inhabitFormula, Formula.holds, Bool.false_eq_true] at enabled

theorem inhabitFormulas_capture_sound (source : Environment) (ctx : EvalContext)
    (associated : CaptureSource source ctx) (facts : NatIndexTree Unit)
    (valid : CaptureFactsSound source ctx facts) (fields : List Ty)
    (enabled : Formula.someHold facts (inhabitFormulas (Index.ofEnvironment source) fields) = true) :
    ∃ ty, ty ∈ fields ∧ NoInitializedCapture ctx ty := by
  obtain ⟨ty, member, accepted⟩ := fields_witness (Index.ofEnvironment source) facts fields enabled
  exact ⟨ty, member, inhabitFormula_capture_sound source ctx associated facts valid ty accepted⟩

private theorem group_member_holds {α : Type} (facts : NatIndexTree Unit) (rows : List α)
    (rule : α → Formula) (enabled : (Formula.all (rows.map rule)).holds facts = true)
    (row : α) (member : row ∈ rows) : (rule row).holds facts = true :=
  Formula.allHold_member facts _ (by simpa only [Formula.holds] using enabled) (rule row)
    (List.mem_map.mpr ⟨row, member, rfl⟩)

private theorem struct_group_sound (source : Environment) (ctx : EvalContext)
    (associated : CaptureSource source ctx) (facts : NatIndexTree Unit)
    (valid : CaptureFactsSound source ctx facts) (id : StructId)
    (enabled : (Formula.all ((((Index.ofEnvironment source).structDefinitions.find id.index).getD []).map
      (fun row => Formula.any (inhabitFormulas (Index.ofEnvironment source) (row.fields.map (·.ty)))))).holds facts = true) :
    NoInitializedCapture ctx (.Struct id) := by
  apply struct_resolved_empty ctx id
  intro definition resolved
  obtain ⟨member, identity⟩ := associated.structs id definition resolved
  have grouped : definition ∈ (((Index.ofEnvironment source).structDefinitions.find id.index).getD []) :=
    (definitionGroups_member source.structs (·.id.index) id.index definition).2
      ⟨member, congrArg StructId.index identity⟩
  have accepted := group_member_holds facts _ _ enabled definition grouped
  obtain ⟨ty, present, empty⟩ := inhabitFormulas_capture_sound source ctx associated facts valid
    (definition.fields.map (·.ty)) (by simpa only [Formula.holds] using accepted)
  obtain ⟨field, member, same⟩ := List.mem_map.mp present
  exact ⟨field, member, by simpa only [same] using empty⟩

private theorem record_group_sound (source : Environment) (ctx : EvalContext)
    (associated : CaptureSource source ctx) (facts : NatIndexTree Unit)
    (valid : CaptureFactsSound source ctx facts) (id : RecordId)
    (enabled : (Formula.all ((((Index.ofEnvironment source).recordDefinitions.find id.index).getD []).map
      (fun row => Formula.any (inhabitFormulas (Index.ofEnvironment source) (row.fields.map (·.ty)))))).holds facts = true) :
    NoInitializedCapture ctx (.Record id) := by
  apply record_resolved_empty ctx id
  intro definition resolved
  obtain ⟨member, identity⟩ := associated.records id definition resolved
  have grouped : definition ∈ (((Index.ofEnvironment source).recordDefinitions.find id.index).getD []) :=
    (definitionGroups_member source.records (·.id.index) id.index definition).2
      ⟨member, congrArg RecordId.index identity⟩
  have accepted := group_member_holds facts _ _ enabled definition grouped
  obtain ⟨ty, present, empty⟩ := inhabitFormulas_capture_sound source ctx associated facts valid
    (definition.fields.map (·.ty)) (by simpa only [Formula.holds] using accepted)
  obtain ⟨field, member, same⟩ := List.mem_map.mp present
  exact ⟨field, member, by simpa only [same] using empty⟩

private theorem enum_group_sound (source : Environment) (ctx : EvalContext)
    (associated : CaptureSource source ctx) (facts : NatIndexTree Unit)
    (valid : CaptureFactsSound source ctx facts) (id : EnumId)
    (enabled : (Formula.all ((((Index.ofEnvironment source).enumDefinitions.find id.index).getD []).map
      (fun row => Formula.all (row.variants.map (fun variant =>
        Formula.any (inhabitFormulas (Index.ofEnvironment source) variant.fields)))))).holds facts = true) :
    NoInitializedCapture ctx (.Enum id) := by
  apply enum_resolved_empty ctx id
  intro definition resolved variant variantMember
  obtain ⟨member, identity⟩ := associated.enums id definition resolved
  have grouped : definition ∈ (((Index.ofEnvironment source).enumDefinitions.find id.index).getD []) :=
    (definitionGroups_member source.enums (·.id.index) id.index definition).2
      ⟨member, congrArg EnumId.index identity⟩
  have outer := group_member_holds facts _ _ enabled definition grouped
  have inner := group_member_holds facts _ _ outer variant variantMember
  exact inhabitFormulas_capture_sound source ctx associated facts valid variant.fields
    (by simpa only [Formula.holds] using inner)

private theorem node_sound_of_type (source : Environment) (ctx : EvalContext) (node : Nat) (ty : Ty)
    (denotes : SourceNodeDenotes source node ty) (empty : NoInitializedCapture ctx ty) :
    CaptureNodeSound source ctx node := by
  intro other assigned
  have same := denotes.functional assigned
  simpa only [← same] using empty

private theorem canonical_alias_denotes (source : Environment) (base fallback : Nat)
    (selected : Option Nat) (ty : Ty)
    (admitted : ∀ position, selected = some position → SourceNodeDenotes source (base + position) ty)
    (different : ¬ (selected.getD fallback == fallback) = true) :
    SourceNodeDenotes source (base + selected.getD fallback) ty := by
  cases selected with
  | none => simp at different
  | some position => exact admitted position rfl

/-- Every actual generated source rule preserves the checker interpretation.
    Conservative groups cover each successfully resolved source definition;
    canonical aliases transfer only the same nominal source type. -/
theorem source_equation_capture_sound (source : Environment) (ctx : EvalContext)
    (associated : CaptureSource source ctx) (facts : NatIndexTree Unit)
    (valid : CaptureFactsSound source ctx facts) (node : Nat) (formula : Formula)
    (equation : SourceEquation (Index.ofEnvironment source) node formula)
    (enabled : formula.holds facts = true) : CaptureNodeSound source ctx node := by
  cases equation with
  | typeRow row position member =>
      cases row with
      | none => simp only [Formula.holds, Bool.false_eq_true] at enabled
      | some ty =>
          exact node_sound_of_type source ctx node ty (.typeRow ty node member)
            (inhabitFormula_capture_sound source ctx associated facts valid ty enabled)
  | structureRow definition position member =>
      have denotes : SourceNodeDenotes source ((Index.ofEnvironment source).structBase + position)
          (.Struct definition.id) := by
        simpa only [Index.structBase_ofEnvironment] using
          (SourceNodeDenotes.structureRow definition position member)
      apply node_sound_of_type source ctx _ _ denotes
      dsimp only at enabled
      split at enabled
      · exact struct_group_sound source ctx associated facts valid definition.id enabled
      · rename_i different
        exact valid _ (ref_fact facts _ enabled) _
          (canonical_alias_denotes source _ position _ (.Struct definition.id)
            (SourceNodeDenotes.struct_alias source definition.id) different)
  | enumerationRow definition position member =>
      have denotes : SourceNodeDenotes source ((Index.ofEnvironment source).enumBase + position)
          (.Enum definition.id) := by
        simpa only [Index.enumBase_ofEnvironment] using
          (SourceNodeDenotes.enumerationRow definition position member)
      apply node_sound_of_type source ctx _ _ denotes
      dsimp only at enabled
      split at enabled
      · exact enum_group_sound source ctx associated facts valid definition.id enabled
      · rename_i different
        exact valid _ (ref_fact facts _ enabled) _
          (canonical_alias_denotes source _ position _ (.Enum definition.id)
            (SourceNodeDenotes.enum_alias source definition.id) different)
  | recordRow definition position member =>
      have denotes : SourceNodeDenotes source ((Index.ofEnvironment source).closureBase + position)
          (.Record definition.id) := by
        simpa only [Index.closureBase_ofEnvironment] using
          (SourceNodeDenotes.recordRow definition position member)
      apply node_sound_of_type source ctx _ _ denotes
      dsimp only at enabled
      split at enabled
      · exact record_group_sound source ctx associated facts valid definition.id enabled
      · rename_i different
        exact valid _ (ref_fact facts _ enabled) _
          (canonical_alias_denotes source _ position _ (.Record definition.id)
            (SourceNodeDenotes.record_alias source definition.id) different)

/-- Actual finite solver facts exclude initialized captures of their exact
    source meanings, under explicit evaluator/source lookup association. -/
theorem uninhabitedFacts_capture_sound (source : Environment) (ctx : EvalContext)
    (associated : CaptureSource source ctx) :
    CaptureFactsSound source ctx (uninhabitedFacts (Index.ofEnvironment source)) := by
  intro node found
  exact uninhabitedFacts_source_induction (Index.ofEnvironment source) (CaptureNodeSound source ctx)
    (fun facts key formula provenance enabled valid =>
      source_equation_capture_sound source ctx associated facts valid key formula provenance enabled)
    node found

theorem source_type_uninhabited_capture_empty (source : Environment) (ctx : EvalContext)
    (associated : CaptureSource source ctx) (ty : Ty)
    (flag : (inhabitFormula (Index.ofEnvironment source) ty).holds
      (uninhabitedFacts (Index.ofEnvironment source)) = true) : NoInitializedCapture ctx ty :=
  inhabitFormula_capture_sound source ctx associated _
    (uninhabitedFacts_capture_sound source ctx associated) ty flag

theorem variant_uninhabited_capture_field (source : Environment) (ctx : EvalContext)
    (associated : CaptureSource source ctx) (fields : List Ty)
    (flag : variantUninhabited (Index.ofEnvironment source)
      (uninhabitedFacts (Index.ofEnvironment source)) fields = true) :
    ∃ ty, ty ∈ fields ∧ NoInitializedCapture ctx ty :=
  inhabitFormulas_capture_sound source ctx associated _
    (uninhabitedFacts_capture_sound source ctx associated) fields
    (by simpa only [variantUninhabited, Formula.holds] using flag)

private theorem payload_member (fields : List Ty) (values : List Value)
    (length : fields.length = values.length) (ty : Ty) (member : ty ∈ fields) :
    ∃ value, value ∈ values ∧ (ty, value) ∈ fields.zip values := by
  trustIrCompilerProof {
    obtain ⟨⟨position, inside⟩, atIndex⟩ := List.get_of_mem member
    have available : position < values.length := by omega
    let value := values.get ⟨position, available⟩
    have indexed : (trustIrListGet? (fields.zip values) position) = some (ty, value) := by
      rw [List.zip, List.zipWith_get?, List.get?_eq_get inside, List.get?_eq_get available, atIndex]
    obtain ⟨bound, atPair⟩ := List.get?_eq_some.mp indexed
    exact ⟨value, List.get_mem values position available, List.mem_iff_get.mpr ⟨⟨position, bound⟩, atPair⟩⟩
  } {
    obtain ⟨⟨position, inside⟩, atIndex⟩ := List.get_of_mem member
    have available : position < values.length := by omega
    let value := values.get ⟨position, available⟩
    have indexed : (trustIrListGet? (fields.zip values) position) = some (ty, value) := by
      rw [List.zip, CompilerCompat.listGetConstructive_zipWith, CompilerCompat.listGet?_eq_get inside, CompilerCompat.listGet?_eq_get available, atIndex] <;> rfl
    exact ⟨value, List.get_mem values ⟨position, available⟩, CompilerCompat.listGetConstructive_mem indexed⟩
  }

/-- A true actual variant flag excludes an initialized payload checked at that
    exact field list. Applying this to physical omission additionally requires
    association with the active evaluator definition/variant. -/
theorem variant_uninhabited_no_initialized_payload (source : Environment) (ctx : EvalContext)
    (associated : CaptureSource source ctx) (fields : List Ty)
    (flag : variantUninhabited (Index.ofEnvironment source)
      (uninhabitedFacts (Index.ofEnvironment source)) fields = true)
    (values : List Value) (length : fields.length = values.length)
    (initialized : (Value.aggregate values).Initialized) (fuel : Nat)
    (checked : (fields.zip values).forM (fun (ty, value) => checkClosureValueAt ctx fuel ty value) = .ok ()) : False := by
  obtain ⟨ty, member, empty⟩ := variant_uninhabited_capture_field source ctx associated fields flag
  obtain ⟨value, valueMember, pairMember⟩ := payload_member fields values length ty member
  exact empty fuel value (initialized.aggregate_child value valueMember)
    (forM_checked_member _ _ checked (ty, value) pairMember)

private theorem find_source_member {α : Type} (rows : List α) (test : α → Bool) (row : α)
    (found : rows.find? test = some row) : row ∈ rows ∧ test row = true := by
  induction rows with
  | nil => cases found
  | cons first rest ih =>
      by_cases accepted : test first = true
      · simp [List.find?, accepted] at found
        cases found
        exact ⟨(trustIrListMemConsSelf _ _), accepted⟩
      · simp [List.find?, accepted] at found
        obtain ⟨member, checked⟩ := ih found
        exact ⟨List.mem_cons_of_mem _ member, checked⟩

private theorem filterMap_retains {α β : Type} (rows : List α) (project : α → Option β)
    (row : α) (value : β) (member : row ∈ rows) (kept : project row = some value) :
    value ∈ rows.filterMap project := by
  induction rows with
  | nil => cases member
  | cons first rest ih =>
      cases member with
      | head => simp [List.filterMap, kept]
      | tail _ member =>
          have later := ih member
          cases projected : project first with
          | none => simpa [List.filterMap, projected] using later
          | some other =>
              simpa [List.filterMap, projected] using (List.mem_cons_of_mem other later)

/-- The exact source argument of decoded context memory preparation, as
    exposed by `TrustIrEval.memoryServiceOf_eq`. This is a proof view, not a
    second context builder or preparer. -/
def decodedCaptureSource (m : TrustIrEval.Module) (model : ByteModel) : Environment :=
  { model, canonicalScalars := true, hasTargetInfo := m.hasTargetInfo,
    types := m.types, structs := m.structs, enums := m.enums,
    records := m.records.filterMap (·.2), closures := m.closureTys,
    tupleLayouts := m.tupleLayouts, closureLayouts := m.closureLayouts }

/-- Retained record payloads must keep the key read for their row. A successful
    wire-decoding proof must establish this coherence; arbitrary raw
    `Module` values need not satisfy it. Unsupported `none` rows are allowed. -/
def RecordKeysAgree (m : TrustIrEval.Module) : Prop :=
  ∀ id definition, (id, some definition) ∈ m.records → definition.id = id

/-- The proof view is the source of the memory service actually installed by
    context construction. Original prepared roots are retained existentially;
    this theorem does not build another context or choose replacement roots. -/
theorem contextOf_capture_service (m : TrustIrEval.Module) (maxDepth : Nat) (ctx : EvalContext)
    (prepared : TrustIrEval.contextOf m maxDepth = .ok ctx) :
    ∃ roots, ctx.memoryService = some (AggregateMemory.prepare (decodedCaptureSource m ctx.byteModel) roots) := by
  unfold TrustIrEval.contextOf at prepared
  cases model : m.byteModel with
  | error error => simp [model, Except.bind, Bind.bind] at prepared
  | ok selectedModel =>
      simp only [model, Except.bind, Except.pure, Bind.bind, Pure.pure] at prepared
      split at prepared
      · cases prepared
      · cases prepared
        exact ⟨_, congrArg some (TrustIrEval.memoryServiceOf_eq m selectedModel)⟩

theorem contextOf_capture_source (m : TrustIrEval.Module) (maxDepth : Nat) (ctx : EvalContext)
    (prepared : TrustIrEval.contextOf m maxDepth = .ok ctx) (recordKeys : RecordKeysAgree m) :
    CaptureSource (decodedCaptureSource m ctx.byteModel) ctx := by
  unfold TrustIrEval.contextOf at prepared
  cases model : m.byteModel with
  | error error => simp [model, Except.bind, Bind.bind] at prepared
  | ok selectedModel =>
      simp only [model, Except.bind, Except.pure, Bind.bind, Pure.pure] at prepared
      split at prepared
      · cases prepared
      · cases prepared
        constructor
        · intro id ty resolved
          change ((trustIrListGet? m.types id.index)).join = some ty at resolved
          change (trustIrListGet? m.types id.index) = some (some ty)
          cases row : (trustIrListGet? m.types id.index) with
          | none => simp [row] at resolved
          | some slot =>
              cases slot with
              | none => simp [row] at resolved
              | some actual =>
                  have same : actual = ty := by simpa [row] using resolved
                  subst ty
                  rfl
        · intro id definition resolved
          change m.structs.find? (fun row => row.id == id) = some definition at resolved
          obtain ⟨member, same⟩ := find_source_member _ _ definition resolved
          exact ⟨member, by simpa using same⟩
        · intro id definition resolved
          change m.enums.find? (fun row => row.id == id) = some definition at resolved
          obtain ⟨member, same⟩ := find_source_member _ _ definition resolved
          exact ⟨member, by simpa using same⟩
        · intro id definition resolved
          change ((m.records.find? (fun row => row.fst == id)).map (·.snd)).join = some definition at resolved
          cases selected : m.records.find? (fun row => row.fst == id) with
          | none => simp [selected] at resolved
          | some row =>
              rcases row with ⟨key, payload⟩
              cases payload with
              | none => simp [selected] at resolved
              | some actual =>
                  have same : actual = definition := by simpa [selected] using resolved
                  subst definition
                  obtain ⟨member, acceptedKey⟩ := find_source_member _ _ (key, some actual) selected
                  have identity : key = id := by simpa using acceptedKey
                  exact ⟨filterMap_retains m.records (·.2) (key, some actual) actual member rfl,
                    (recordKeys key actual member).trans identity⟩

theorem contextOf_uninhabited_capture_empty (m : TrustIrEval.Module) (maxDepth : Nat) (ctx : EvalContext)
    (prepared : TrustIrEval.contextOf m maxDepth = .ok ctx) (recordKeys : RecordKeysAgree m) (ty : Ty)
    (flag : (inhabitFormula (Index.ofEnvironment (decodedCaptureSource m ctx.byteModel)) ty).holds
      (uninhabitedFacts (Index.ofEnvironment (decodedCaptureSource m ctx.byteModel))) = true) :
    NoInitializedCapture ctx ty :=
  source_type_uninhabited_capture_empty _ ctx (contextOf_capture_source m maxDepth ctx prepared recordKeys) ty flag

namespace CaptureSoundControls

private def emptyField : FieldDef := { name := "empty", ty := .Never, offset := none }
private def firstStruct : StructDef :=
  { id := ⟨1⟩, name := "First", fields := [emptyField], size := none, align := none }
private def canonicalStruct : StructDef := { firstStruct with name := "Canonical" }
private def goodRecord : RecordDef := { id := ⟨7⟩, name := "EmptyRecord", fields := [emptyField] }

private def positive : TrustIrEval.Module :=
  { hasTargetInfo := true, functions := [], funcTys := [], globals := [],
    enums := [{ id := ⟨2⟩, name := "EmptyPayload", variants := [{ name := "Only", fields := [.Never] }] }],
    structs := [firstStruct, canonicalStruct], records := [(⟨7⟩, some goodRecord)], types := [some .Never] }

private def actualContext (m : TrustIrEval.Module) : EvalContext :=
  match TrustIrEval.contextOf m 0 with
  | .ok ctx => ctx
  | .error _ => EvalContext.empty

private def ctx : EvalContext := actualContext positive
private def source : Environment := decodedCaptureSource positive ctx.byteModel

theorem actual_context_prepares : TrustIrEval.contextOf positive 0 = .ok ctx := rfl

theorem actual_record_keys : RecordKeysAgree positive := by
  intro id definition member
  change (id, some definition) ∈ [(⟨7⟩, some goodRecord)] at member
  cases member with
  | head => rfl
  | tail _ impossible => cases impossible

theorem actual_first_struct_resolves : ctx.structs ⟨1⟩ = some firstStruct := rfl
theorem actual_canonical_position_differs :
    (Index.ofEnvironment source).structPositions.find 1 = some 1 := rfl

theorem actual_alias_struct_empty : NoInitializedCapture ctx (.Struct ⟨1⟩) := by
  trustIrCompilerProof {
    exact contextOf_uninhabited_capture_empty positive 0 ctx actual_context_prepares actual_record_keys (.Struct ⟨1⟩) rfl
  } {
    exact contextOf_uninhabited_capture_empty positive 0 ctx actual_context_prepares actual_record_keys (.Struct ⟨1⟩) (by trustIrReduce)
  }

theorem actual_record_empty : NoInitializedCapture ctx (.Record ⟨7⟩) := by
  trustIrCompilerProof {
    exact contextOf_uninhabited_capture_empty positive 0 ctx actual_context_prepares actual_record_keys (.Record ⟨7⟩) rfl
  } {
    exact contextOf_uninhabited_capture_empty positive 0 ctx actual_context_prepares actual_record_keys (.Record ⟨7⟩) (by trustIrReduce)
  }

theorem actual_enum_empty : NoInitializedCapture ctx (.Enum ⟨2⟩) := by
  trustIrCompilerProof {
    exact contextOf_uninhabited_capture_empty positive 0 ctx actual_context_prepares actual_record_keys (.Enum ⟨2⟩) rfl
  } {
    exact contextOf_uninhabited_capture_empty positive 0 ctx actual_context_prepares actual_record_keys (.Enum ⟨2⟩) (by trustIrReduce)
  }

theorem actual_array_empty : NoInitializedCapture ctx (.Array ⟨0⟩ 3) := by
  trustIrCompilerProof {
    exact contextOf_uninhabited_capture_empty positive 0 ctx actual_context_prepares actual_record_keys (.Array ⟨0⟩ 3) rfl
  } {
    exact contextOf_uninhabited_capture_empty positive 0 ctx actual_context_prepares actual_record_keys (.Array ⟨0⟩ 3) (by trustIrReduce)
  }

theorem flagged_struct_payload_refuses (values : List Value) (length : [Ty.Struct ⟨1⟩].length = values.length)
    (initialized : (Value.aggregate values).Initialized) (fuel : Nat)
    (checked : ([Ty.Struct ⟨1⟩].zip values).forM (fun (ty, value) =>
      checkClosureValueAt ctx fuel ty value) = .ok ()) : False := by
  trustIrCompilerProof {
    exact variant_uninhabited_no_initialized_payload source ctx
      (contextOf_capture_source positive 0 ctx actual_context_prepares actual_record_keys)
      [.Struct ⟨1⟩] rfl values length initialized fuel checked
  } {
    exact variant_uninhabited_no_initialized_payload source ctx
      (contextOf_capture_source positive 0 ctx actual_context_prepares actual_record_keys)
      [.Struct ⟨1⟩] (by trustIrReduce) values length initialized fuel checked
  }

private def unitRecord : RecordDef := { id := ⟨8⟩, name := "Unit", fields := [] }
private def skewed : TrustIrEval.Module :=
  { positive with records := [(⟨7⟩, some unitRecord), (⟨8⟩, some goodRecord)] }
private def skewCtx : EvalContext := actualContext skewed
private def skewSource : Environment := decodedCaptureSource skewed skewCtx.byteModel

theorem skewed_context_prepares : TrustIrEval.contextOf skewed 0 = .ok skewCtx := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem skewed_source_flag_is_true :
    (inhabitFormula (Index.ofEnvironment skewSource) (.Record ⟨7⟩)).holds
      (uninhabitedFacts (Index.ofEnvironment skewSource)) = true := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem skewed_value_is_accepted :
    checkClosureValueAt skewCtx 1 (.Record ⟨7⟩) (.record []) = .ok () := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem skewed_keys_disagree : ¬ RecordKeysAgree skewed := by
  intro agree
  have wrong := agree ⟨7⟩ unitRecord ((trustIrListMemConsSelf _ _))
  have impossible : (8 : Nat) = 7 := congrArg RecordId.index wrong
  omega

theorem skewed_context_not_associated : ¬ CaptureSource skewSource skewCtx := by
  intro associated
  have wrong := (associated.records ⟨7⟩ unitRecord rfl).2
  have impossible : (8 : Nat) = 7 := congrArg RecordId.index wrong
  omega

theorem skewed_type_not_empty : ¬ NoInitializedCapture skewCtx (.Record ⟨7⟩) := by
  intro empty
  have initialized : (Value.record []).Initialized := by
    apply Value.Initialized.record
    intro name value impossible
    cases impossible
  exact empty 1 (.record []) initialized skewed_value_is_accepted

private def shadowed : TrustIrEval.Module :=
  { positive with records := [(⟨7⟩, none), (⟨7⟩, some goodRecord)] }
private def shadowCtx : EvalContext := actualContext shadowed

theorem unsupported_first_record_stays_missing : shadowCtx.records ⟨7⟩ = none := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem unsupported_first_record_keys_agree : RecordKeysAgree shadowed := by
  intro id definition member
  change (id, some definition) ∈ [(⟨7⟩, none), (⟨7⟩, some goodRecord)] at member
  cases member with
  | tail _ member =>
      cases member with
      | head => rfl
      | tail _ impossible => cases impossible

theorem unsupported_first_record_associated :
    CaptureSource (decodedCaptureSource shadowed shadowCtx.byteModel) shadowCtx :=
  contextOf_capture_source shadowed 0 shadowCtx rfl unsupported_first_record_keys_agree

end CaptureSoundControls

end TrustIr.SourceLayout
