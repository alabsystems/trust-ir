-- Copyright 2026 Andrew Yates | Apache-2.0
-- Decoder-boundary proofs. JSON remains outside the pure TrustIr formal root.
import TrustIrEval.Decode
import TrustIr.Proofs.SourceInhabitSound
import TrustIr.Proofs.AxiomAuditCompat

namespace TrustIrEval
open Lean (Json)
open TrustIr
open TrustIr.SourceLayout

private def Results {ε α : Type} (property : α → Prop) (action : Except ε α) : Prop :=
  ∀ value, action = .ok value → property value

private theorem results_bind {ε α β : Type} (property : β → Prop) (action : Except ε α)
    (next : α → Except ε β)
    (preserved : ∀ value, action = .ok value → Results property (next value)) :
    Results property (action >>= next) := by
  intro result success
  cases outcome : action with
  | error error => simp [outcome, Except.bind, Bind.bind] at success
  | ok value =>
      apply preserved value outcome result
      simpa [outcome, Except.bind, Bind.bind] using success

private theorem results_pure {ε α : Type} (property : α → Prop) (value : α)
    (valid : property value) : Results property (Except.ok value : Except ε α) := by
  intro result same
  cases same
  exact valid

/-- The actual definition decoder reads its retained inner ID from the same
    JSON accessor used for the outer record-table key. Field/name failures
    retain their original order; no decoder is replaced. -/
theorem recordDef_retains_id (document : Json) (definition : RecordDef)
    (decoded : recordDef document = .ok definition) :
    natField document "id" = .ok definition.id.index := by
  have all : Results (fun result : RecordDef => natField document "id" = .ok result.id.index)
      (recordDef document) := by
    unfold recordDef
    apply results_bind
    intro fieldRows _rowsDecoded
    apply results_bind
    intro fields _fieldsDecoded
    apply results_bind
    intro id parsedId
    apply results_bind
    intro name _nameDecoded
    apply results_pure
    exact parsedId
  exact all definition decoded

private theorem record_row_keys (document : Json) :
    Results (fun row : RecordId × Option RecordDef =>
      ∀ definition, row.2 = some definition → definition.id = row.1)
      (do
        let id : RecordId := ⟨← natField document "id"⟩
        match recordDef document with
        | .ok definition => pure (id, some definition)
        | .error (.unsupported _) => pure (id, none)
        | .error error => throw error) := by
  apply results_bind
  intro id parsedId
  cases parsed : recordDef document with
  | ok definition =>
      apply results_pure
      intro retained same
      cases same
      have inner := recordDef_retains_id document definition parsed
      have identity := Except.ok.inj (parsedId.symm.trans inner)
      exact congrArg RecordId.mk identity.symm
  | error error =>
      cases error with
      | unsupported feature =>
          apply results_pure
          intro definition impossible
          cases impossible
      | malformed message => intro result success; cases success

private theorem mapM_results {α β ε : Type} (rows : List α) (action : α → Except ε β)
    (property : β → Prop) (valid : ∀ row ∈ rows, Results property (action row)) :
    Results (fun values => ∀ value ∈ values, property value) (rows.mapM action) := by
  induction rows with
  | nil =>
      apply results_pure
      intro value impossible
      cases impossible
  | cons first rest ih =>
      rw [List.mapM_cons]
      apply results_bind
      intro firstValue firstDecoded
      have firstValid := valid first (trustIrListMemConsSelf _ _) firstValue firstDecoded
      apply results_bind
      intro restValues restDecoded
      have later := ih (fun row member => valid row (List.mem_cons_of_mem first member)) restValues restDecoded
      apply results_pure
      intro value member
      cases member with
      | head => exact firstValid
      | tail _ member => exact later value member

private theorem records_field_keys (document : Json) :
    Results (fun rows : List (RecordId × Option RecordDef) =>
      ∀ id definition, (id, some definition) ∈ rows → definition.id = id)
      (match document.getObjVal? "records" with
      | .error _ => pure []
      | .ok rows => do
          (← arr "records" rows).mapM (fun row => do
            let id : RecordId := ⟨← natField row "id"⟩
            match recordDef row with
            | .ok definition => pure (id, some definition)
            | .error (.unsupported _) => pure (id, none)
            | .error error => throw error)) := by
  cases _present : document.getObjVal? "records" with
  | error error =>
      apply results_pure
      intro id definition impossible
      cases impossible
  | ok rows =>
      apply results_bind
      intro entries _parsed
      intro values decoded id definition member
      have every := mapM_results entries _ _ (fun row _member => record_row_keys row) values decoded
      exact every (id, some definition) member definition rfl

/-- Every successfully decoded actual module has coherent retained record
    keys, including sparse/duplicate IDs and unsupported `none` payloads. -/
theorem module_record_keys (document : Json) (decoded : Module)
    (success : module document = .ok decoded) : RecordKeysAgree decoded := by
  have all : Results RecordKeysAgree (module document) := by
    unfold module
    apply results_bind
    intro functionDocuments _functionDocuments
    apply results_bind
    intro functionRows _functions
    apply results_bind
    intro signatureDocuments _signatureDocuments
    apply results_bind
    intro signatures _signatures
    apply results_bind
    intro closureRows _closures
    apply results_bind
    intro globalDocuments _globalDocuments
    apply results_bind
    intro globals _globals
    apply results_bind
    intro enumDocuments _enumDocuments
    apply results_bind
    intro enums _enums
    apply results_bind
    intro structDocuments _structDocuments
    apply results_bind
    intro structs _structs
    apply results_bind
    intro tuples _tuples
    apply results_bind
    intro closures _closureLayouts
    apply results_bind
    intro records recordsDecoded
    apply results_bind
    intro types _types
    apply results_bind
    intro glue _glue
    apply results_pure
    exact records_field_keys document records recordsDecoded
  exact all decoded success

/-- The coherence premise is discharged for the actual wire decoder, then
    actual context construction supplies source association. -/
theorem decoded_context_capture_source (document : Json) (decoded : Module)
    (parsed : module document = .ok decoded) (maxDepth : Nat) (ctx : EvalContext)
    (prepared : contextOf decoded maxDepth = .ok ctx) :
    CaptureSource (decodedCaptureSource decoded ctx.byteModel) ctx :=
  contextOf_capture_source decoded maxDepth ctx prepared (module_record_keys document decoded parsed)

theorem decoded_uninhabited_capture_empty (document : Json) (decoded : Module)
    (parsed : module document = .ok decoded) (maxDepth : Nat) (ctx : EvalContext)
    (prepared : contextOf decoded maxDepth = .ok ctx) (ty : Ty)
    (flag : (inhabitFormula (Index.ofEnvironment (decodedCaptureSource decoded ctx.byteModel)) ty).holds
      (uninhabitedFacts (Index.ofEnvironment (decodedCaptureSource decoded ctx.byteModel))) = true) :
    SourceValueMembership.NoInitializedCapture ctx ty :=
  contextOf_uninhabited_capture_empty decoded maxDepth ctx prepared (module_record_keys document decoded parsed) ty flag

theorem decoded_variant_no_initialized_payload (document : Json) (decoded : Module)
    (parsed : module document = .ok decoded) (maxDepth : Nat) (ctx : EvalContext)
    (prepared : contextOf decoded maxDepth = .ok ctx) (fields : List Ty)
    (flag : variantUninhabited (Index.ofEnvironment (decodedCaptureSource decoded ctx.byteModel))
      (uninhabitedFacts (Index.ofEnvironment (decodedCaptureSource decoded ctx.byteModel))) fields = true)
    (values : List Value) (length : fields.length = values.length)
    (initialized : (Value.aggregate values).Initialized) (fuel : Nat)
    (checked : (fields.zip values).forM (fun (ty, value) => checkClosureValueAt ctx fuel ty value) = .ok ()) : False :=
  variant_uninhabited_no_initialized_payload _ ctx
    (decoded_context_capture_source document decoded parsed maxDepth ctx prepared)
    fields flag values length initialized fuel checked


-- Pure Box wire decoder controls; reserved evidence is not validator admission.
private def boxMalformed {α : Type} : D α → Bool
  | .error (.malformed _) => true
  | _ => false

private def boxFactJson (ordinal : Nat) : Json :=
  Json.mkObj [
    ("site", Json.mkObj [("item", Lean.toJson (List.replicate 16 (0 : Nat))),
      ("ordinal", Lean.toJson ordinal)]),
    ("session", Json.mkObj [("judged", .str "VerificationSnapshot"),
      ("producing", .str "ProofSession")]),
    ("evidence", .arr #[]), ("not_claimed", .arr #[])]

private def boxInstJson (operand : Nat) : Json :=
  Json.mkObj [("BoxDeref", Json.mkObj [("ptr_ty", .str "Ptr"),
    ("pointee", Json.mkObj [("Sized", Json.mkObj [("ty", .str "I64")])]),
    ("operand", Lean.toJson operand), ("fact", boxFactJson 0)])]

-- Kernel-checked pure parser regressions: compiling this existing module checks
-- these propositions using only logical imports and kernel-checked reduction.
-- Reserved evidence remains parser-only and is not validator admission.
example :
    validityEvidence (Json.mkObj [("DominatingCheck", Json.mkObj [])]) = .ok (.dominatingCheck none) := by
  trustIrReduce

example :
    validityEvidence (Json.mkObj [("DominatingCheck", Json.mkObj [("align", .null)])]) = .ok (.dominatingCheck none) := by
  trustIrReduce

example :
    validityEvidence (Json.mkObj [("DominatingCheck", Json.mkObj [("align", Lean.toJson (0 : Nat))])]) = .ok (.dominatingCheck (some 0)) := by
  trustIrReduce

example :
    validityEvidence (Json.mkObj [("DominatingCheck", Json.mkObj [("align", Lean.toJson (18446744073709551615 : Nat))])]) = .ok (.dominatingCheck (some 18446744073709551615)) := by
  trustIrReduce

example :
    ([Json.str "8", Json.bool true, Json.arr #[], Lean.toJson (-1 : Int),
      Lean.toJson (18446744073709551616 : Nat)].all (fun bad =>
        boxMalformed (validityEvidence (Json.mkObj [("DominatingCheck", Json.mkObj [("align", bad)])])))) = true := by
  trustIrReduce

example :
    ([Json.null, Json.arr #[], Json.str "not a record"].all (fun bad =>
      boxMalformed (validityEvidence (Json.mkObj [("DominatingCheck", bad)])))) = true := by
  trustIrReduce

example :
    validityEvidence (Json.mkObj [("Obligation",
      Json.mkObj [("obligation", Lean.toJson (0 : Nat))])]) = .ok (.obligation ⟨0⟩) := by
  trustIrReduce

example :
    (match boxValidityFact (boxFactJson 0) with
     | .ok fact => fact.siteOrdinal == 0
     | _ => false) = true := by
  trustIrReduce

example :
    (match inst (boxInstJson 0) with
     | .ok (.BoxDeref _ _ id _) => id.index == 0
     | _ => false) = true := by
  trustIrReduce

example :
    validityEvidence (Json.mkObj [("Obligation",
      Json.mkObj [("obligation", Lean.toJson (4294967295 : Nat))])]) = .ok (.obligation ⟨4294967295⟩) := by
  trustIrReduce

example :
    (match boxValidityFact (boxFactJson 4294967295) with
     | .ok fact => fact.siteOrdinal == 4294967295
     | _ => false) = true := by
  trustIrReduce

example :
    (match inst (boxInstJson 4294967295) with
     | .ok (.BoxDeref _ _ id _) => id.index == 4294967295
     | _ => false) = true := by
  trustIrReduce

example :
    boxMalformed (validityEvidence (Json.mkObj [("Obligation",
      Json.mkObj [("obligation", Lean.toJson (4294967296 : Nat))])])) = true := by
  trustIrReduce

example :
    boxMalformed (boxValidityFact (boxFactJson 4294967296)) = true := by
  trustIrReduce

example :
    boxMalformed (inst (boxInstJson 4294967296)) = true := by
  trustIrReduce

end TrustIrEval

/- Historical legacy printer record, preserved verbatim:
/-- info: 'TrustIrEval.recordDef_retains_id' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIrEval.recordDef_retains_id
-/
#trustIrAxiomsByCompiler TrustIrEval.recordDef_retains_id == [propext] modern [propext, Classical.choice, Quot.sound]

/- Historical legacy printer record, preserved verbatim:
/-- info: 'TrustIrEval.module_record_keys' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIrEval.module_record_keys
-/
#trustIrAxiomsByCompiler TrustIrEval.module_record_keys == [propext, Quot.sound] modern [propext, Classical.choice, Quot.sound]

/- Original printer record, preserved verbatim:
/-- info: 'TrustIrEval.decoded_context_capture_source' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIrEval.decoded_context_capture_source
-/
#trustIrAxiomsExact TrustIrEval.decoded_context_capture_source == [propext, Quot.sound, Classical.choice]

/- Original printer record, preserved verbatim:
/-- info: 'TrustIrEval.decoded_uninhabited_capture_empty' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIrEval.decoded_uninhabited_capture_empty
-/
#trustIrAxiomsExact TrustIrEval.decoded_uninhabited_capture_empty == [propext, Quot.sound, Classical.choice]

/- Original printer record, preserved verbatim:
/-- info: 'TrustIrEval.decoded_variant_no_initialized_payload' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIrEval.decoded_variant_no_initialized_payload
-/
#trustIrAxiomsExact TrustIrEval.decoded_variant_no_initialized_payload == [propext, Quot.sound, Classical.choice]
