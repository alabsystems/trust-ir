-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.DecodedClosureStorage
import TrustIr.Proofs.ClosureQueryProof

trustIrRegisterClosureQueryEquations

namespace TrustIrEval.ClosureStorage.Checks
open TrustIr

private def block (body : List Inst) : List (BlockId × BasicBlock) :=
  [(⟨0⟩, { params := [], body, terminator := .Return [] })]

private def row (id ty : Nat) (body : List Inst) : Function :=
  { id := ⟨id⟩, name := "original-storage-control", ty := ⟨ty⟩, entry := ⟨0⟩,
    isDeclaration := false, blocks := .ok (block body) }

private def apparent : FuncTyDef := { params := [.U64], returns := [.U64], isVararg := false }
private def producer : FuncTyDef := { params := [], returns := [], isVararg := false }
private def physical : FuncTyDef := { params := [.U64, .U64], returns := [.U64], isVararg := false }

/-- These are actual original decoded rows, not an executable/ABI validity
claim. The storage query must keep their constructor, target and layout roles
separate; the existing interpreter/call/byte-codec guards are unchanged. -/
private def original : Module :=
  { hasTargetInfo := true
    functions := [row 7 0 [], row 9 1 [.MakeClosure ⟨0⟩ ⟨7⟩ []]]
    funcTys := [apparent, producer]
    closureTys := [{func := ⟨0⟩, captures := []}]
    closureLayouts := [{closure := ⟨0⟩, size := 0, align := 1, captureOffsets := []}]
    globals := [], enums := [], structs := [], types := [] }

private def observed (source : Module) (closure : ClosureTyId := ⟨0⟩) :=
  (bindingOf source closure).map (fun binding =>
    (binding.target.value.index, binding.shape.size, binding.shape.align,
      binding.nominal.captures.length))

-- Standalone signature facts never rewrite a Boolean under its dependent continuation.
private theorem original_signature_true : physicalMatches [] apparent apparent = true := by
  unfold physicalMatches
  erw [closureTyListEq_refl]
  all_goals rfl

private theorem captured_signature_true : physicalMatches [.U64] apparent physical = true := by
  unfold physicalMatches
  change (closureTyListEq [.U64, .U64] [.U64, .U64] && closureTyListEq [.U64] [.U64] &&
    !false && (none : Option SignatureAbi).isNone) = true
  simp only [closureTyListEq_refl]
  all_goals rfl

private theorem parameter_signature_false :
    physicalMatches [] apparent {params := [.U32], returns := [.U64], isVararg := false} = false := by
  have different : ([.U32] : List Ty) ≠ [.U64] := by intro same; cases same
  have mismatch := TrustIr.ClosureQueryProof.list_ne_false _ _ different
  unfold physicalMatches
  change (closureTyListEq [.U32] [.U64] && closureTyListEq [.U64] [.U64] &&
    !false && (none : Option SignatureAbi).isNone) = false
  simp only [mismatch, closureTyListEq_refl]
  all_goals rfl

private theorem return_signature_false :
    physicalMatches [] apparent {params := [.U64], returns := [.I64], isVararg := false} = false := by
  have different : ([.I64] : List Ty) ≠ [.U64] := by intro same; cases same
  have mismatch := TrustIr.ClosureQueryProof.list_ne_false _ _ different
  unfold physicalMatches
  change (closureTyListEq [.U64] [.U64] && closureTyListEq [.I64] [.U64] &&
    !false && (none : Option SignatureAbi).isNone) = false
  simp only [mismatch, closureTyListEq_refl]
  all_goals rfl

private theorem prefix_signature_false : physicalMatches [.U64] apparent apparent = false := by
  have different : ([.U64] : List Ty) ≠ [.U64, .U64] := by
    intro same
    have lengths := congrArg List.length same
    cases lengths
  have mismatch := TrustIr.ClosureQueryProof.list_ne_false _ _ different
  unfold physicalMatches
  change (closureTyListEq [.U64] [.U64, .U64] && closureTyListEq [.U64] [.U64] &&
    !false && (none : Option SignatureAbi).isNone) = false
  simp only [mismatch, closureTyListEq_refl]
  all_goals rfl

private theorem vararg_signature_false :
    physicalMatches [] apparent {apparent with isVararg := true} = false := by
  unfold physicalMatches
  change (closureTyListEq [.U64] [.U64] && closureTyListEq [.U64] [.U64] &&
    !true && (none : Option SignatureAbi).isNone) = false
  simp only [closureTyListEq_refl]
  all_goals rfl

private theorem abi_signature_false (abi : SignatureAbi) :
    physicalMatches [] apparent {apparent with abi := some abi} = false := by
  unfold physicalMatches
  change (closureTyListEq [.U64] [.U64] && closureTyListEq [.U64] [.U64] &&
    !false && (some abi : Option SignatureAbi).isNone) = false
  simp only [closureTyListEq_refl]
  all_goals rfl

private theorem apparent_abi_false (abi : SignatureAbi) :
    ({apparent with abi := some abi} : FuncTyDef).abi.isNone = false := by rfl

theorem original_make_closure_binds_exact_target :
    observed original = .ok (7, 0, some 1, 0) := by
  trustIrCompilerProof { rfl } {
    have querySummary :
        ((SourceLayout.prepare (layoutSourceOf (original) ByteModel.le64)).query SourceLayout.Mode.shape (Ty.Closure ⟨0⟩)).map Prod.fst =
          .ok ({ size := 0, align := some 1 } : SourceLayout.Summary) := by
      trustIrReduce
    obtain ⟨after, queryEq⟩ := TrustIr.ClosureQueryProof.map_fst_ok_exists _ _ querySummary
    dsimp only [original, row, block, apparent, producer, physical] at queryEq
    trustIrReduce
    all_goals trustIrSplitClosureQuery queryEq allowing []
    all_goals simp_all only [TrustIr.ClosureQueryProof.error_ne_ok,
      TrustIr.ClosureQueryProof.ok_ne_error, Except.ok.injEq, Except.error.injEq, Prod.mk.injEq]
    all_goals rcases queryEq with ⟨rfl, rfl⟩
    all_goals subst_vars
    all_goals simp [physicalMatches, closureTyListEq_refl]
    all_goals first | rfl | trustIrReduce
    all_goals have signatureCheck := (TrustIrEval.ClosureStorage.requireTrue_eq_ok (physicalMatches [] apparent apparent) "closure storage target signature mismatch" original_signature_true)
    all_goals trustIrRetypeClosureCheck signatureCheck allowing []
    all_goals erw [signatureCheck]
    all_goals first | rfl | trustIrReduce
  }

private def captured : Module :=
  { original with
    functions := [row 7 2 [], row 9 1 [.MakeClosure ⟨0⟩ ⟨7⟩ [⟨5⟩]]]
    funcTys := [apparent, producer, physical]
    closureTys := [{func := ⟨0⟩, captures := [.U64]}]
    closureLayouts := [{closure := ⟨0⟩, size := 8, align := 8, captureOffsets := [0]}] }

theorem captured_signature_uses_capture_prefix_and_actual_shape :
    observed captured = .ok (7, 8, some 8, 1) := by
  trustIrCompilerProof { rfl } {
    have querySummary :
        ((SourceLayout.prepare (layoutSourceOf (captured) ByteModel.le64)).query SourceLayout.Mode.shape (Ty.Closure ⟨0⟩)).map Prod.fst =
          .ok ({ size := 8, align := some 8, fields := [{ty := .U64, offset := 0, size := 8, align := 8}] } : SourceLayout.Summary) := by
      trustIrReduce
    obtain ⟨after, queryEq⟩ := TrustIr.ClosureQueryProof.map_fst_ok_exists _ _ querySummary
    dsimp only [original, captured, row, block, apparent, producer, physical] at queryEq
    trustIrReduce
    all_goals trustIrSplitClosureQuery queryEq allowing []
    all_goals simp_all only [TrustIr.ClosureQueryProof.error_ne_ok,
      TrustIr.ClosureQueryProof.ok_ne_error, Except.ok.injEq, Except.error.injEq, Prod.mk.injEq]
    all_goals rcases queryEq with ⟨rfl, rfl⟩
    all_goals subst_vars
    all_goals simp [physicalMatches, closureTyListEq_refl]
    all_goals first | rfl | trustIrReduce
    all_goals have signatureCheck := (TrustIrEval.ClosureStorage.requireTrue_eq_ok (physicalMatches [.U64] apparent physical) "closure storage target signature mismatch" captured_signature_true)
    all_goals trustIrRetypeClosureCheck signatureCheck allowing []
    all_goals erw [signatureCheck]
    all_goals first | rfl | trustIrReduce
  }

theorem geometry_without_actual_constructor_cannot_supply_target :
    observed { original with functions := [row 7 0 [], row 9 1 []] } =
      .error (.malformed "missing closure storage target") := by
  trustIrCompilerProof { rfl } {
    have querySummary :
        ((SourceLayout.prepare (layoutSourceOf ({ original with functions := [row 7 0 [], row 9 1 []] }) ByteModel.le64)).query SourceLayout.Mode.shape (Ty.Closure ⟨0⟩)).map Prod.fst =
          .ok ({ size := 0, align := some 1 } : SourceLayout.Summary) := by
      trustIrReduce
    obtain ⟨after, queryEq⟩ := TrustIr.ClosureQueryProof.map_fst_ok_exists _ _ querySummary
    dsimp only [original, captured, row, block, apparent, producer, physical] at queryEq
    trustIrReduce
    all_goals trustIrSplitClosureQuery queryEq allowing []
    all_goals simp_all only [TrustIr.ClosureQueryProof.error_ne_ok,
      TrustIr.ClosureQueryProof.ok_ne_error, Except.ok.injEq, Except.error.injEq, Prod.mk.injEq]
    all_goals rcases queryEq with ⟨rfl, rfl⟩
    all_goals subst_vars
    all_goals simp [physicalMatches, closureTyListEq_refl]
    all_goals first | rfl | trustIrReduce
  }

theorem typed_instruction_constant_is_an_original_constructor :
    observed { original with functions := [row 7 0 [],
      row 9 1 [.Const (.Closure ⟨0⟩) (.closure ⟨7⟩ [])]] } =
      .ok (7, 0, some 1, 0) := by
  trustIrCompilerProof { rfl } {
    have querySummary :
        ((SourceLayout.prepare (layoutSourceOf ({ original with functions := [row 7 0 [],
      row 9 1 [.Const (.Closure ⟨0⟩) (.closure ⟨7⟩ [])]] }) ByteModel.le64)).query SourceLayout.Mode.shape (Ty.Closure ⟨0⟩)).map Prod.fst =
          .ok ({ size := 0, align := some 1 } : SourceLayout.Summary) := by
      trustIrReduce
    obtain ⟨after, queryEq⟩ := TrustIr.ClosureQueryProof.map_fst_ok_exists _ _ querySummary
    dsimp only [original, captured, row, block, apparent, producer, physical] at queryEq
    trustIrReduce
    all_goals trustIrSplitClosureQuery queryEq allowing []
    all_goals simp_all only [TrustIr.ClosureQueryProof.error_ne_ok,
      TrustIr.ClosureQueryProof.ok_ne_error, Except.ok.injEq, Except.error.injEq, Prod.mk.injEq]
    all_goals rcases queryEq with ⟨rfl, rfl⟩
    all_goals subst_vars
    all_goals simp [physicalMatches, closureTyListEq_refl]
    all_goals first | rfl | trustIrReduce
    all_goals have signatureCheck := (TrustIrEval.ClosureStorage.requireTrue_eq_ok (physicalMatches [] apparent apparent) "closure storage target signature mismatch" original_signature_true)
    all_goals trustIrRetypeClosureCheck signatureCheck allowing []
    all_goals erw [signatureCheck]
    all_goals first | rfl | trustIrReduce
  }

theorem typed_global_initializer_is_an_original_constructor :
    observed { original with
      functions := [row 7 0 []]
      globals := [{ty := .Closure ⟨0⟩, initializer := some (.closure ⟨7⟩ [])}] } =
      .ok (7, 0, some 1, 0) := by
  trustIrCompilerProof { rfl } {
    have querySummary :
        ((SourceLayout.prepare (layoutSourceOf ({ original with
      functions := [row 7 0 []]
      globals := [{ty := .Closure ⟨0⟩, initializer := some (.closure ⟨7⟩ [])}] }) ByteModel.le64)).query SourceLayout.Mode.shape (Ty.Closure ⟨0⟩)).map Prod.fst =
          .ok ({ size := 0, align := some 1 } : SourceLayout.Summary) := by
      trustIrReduce
    obtain ⟨after, queryEq⟩ := TrustIr.ClosureQueryProof.map_fst_ok_exists _ _ querySummary
    dsimp only [original, captured, row, block, apparent, producer, physical] at queryEq
    trustIrReduce
    all_goals trustIrSplitClosureQuery queryEq allowing []
    all_goals simp_all only [TrustIr.ClosureQueryProof.error_ne_ok,
      TrustIr.ClosureQueryProof.ok_ne_error, Except.ok.injEq, Except.error.injEq, Prod.mk.injEq]
    all_goals rcases queryEq with ⟨rfl, rfl⟩
    all_goals subst_vars
    all_goals simp [physicalMatches, closureTyListEq_refl]
    all_goals first | rfl | trustIrReduce
    all_goals have signatureCheck := (TrustIrEval.ClosureStorage.requireTrue_eq_ok (physicalMatches [] apparent apparent) "closure storage target signature mismatch" original_signature_true)
    all_goals trustIrRetypeClosureCheck signatureCheck allowing []
    all_goals erw [signatureCheck]
    all_goals first | rfl | trustIrReduce
  }

theorem global_conflict_cannot_be_hidden_by_instruction_order :
    observed { original with globals :=
      [{ty := .Closure ⟨0⟩, initializer := some (.closure ⟨8⟩ [])}] } =
      .error (.malformed "conflicting closure storage targets") := by
  trustIrCompilerProof { rfl } {
    have querySummary :
        ((SourceLayout.prepare (layoutSourceOf ({ original with globals :=
      [{ty := .Closure ⟨0⟩, initializer := some (.closure ⟨8⟩ [])}] }) ByteModel.le64)).query SourceLayout.Mode.shape (Ty.Closure ⟨0⟩)).map Prod.fst =
          .ok ({ size := 0, align := some 1 } : SourceLayout.Summary) := by
      trustIrReduce
    obtain ⟨after, queryEq⟩ := TrustIr.ClosureQueryProof.map_fst_ok_exists _ _ querySummary
    dsimp only [original, captured, row, block, apparent, producer, physical] at queryEq
    trustIrReduce
    all_goals trustIrSplitClosureQuery queryEq allowing []
    all_goals simp_all only [TrustIr.ClosureQueryProof.error_ne_ok,
      TrustIr.ClosureQueryProof.ok_ne_error, Except.ok.injEq, Except.error.injEq, Prod.mk.injEq]
    all_goals rcases queryEq with ⟨rfl, rfl⟩
    all_goals subst_vars
    all_goals simp [physicalMatches, closureTyListEq_refl]
    all_goals first | rfl | trustIrReduce
  }

theorem unreachable_function_still_constrains_storage_identity :
    observed { original with functions := original.functions ++
      [row 99 1 [.MakeClosure ⟨0⟩ ⟨8⟩ []]] } =
      .error (.malformed "conflicting closure storage targets") := by
  trustIrCompilerProof { rfl } {
    have querySummary :
        ((SourceLayout.prepare (layoutSourceOf ({ original with functions := original.functions ++
      [row 99 1 [.MakeClosure ⟨0⟩ ⟨8⟩ []]] }) ByteModel.le64)).query SourceLayout.Mode.shape (Ty.Closure ⟨0⟩)).map Prod.fst =
          .ok ({ size := 0, align := some 1 } : SourceLayout.Summary) := by
      trustIrReduce
    obtain ⟨after, queryEq⟩ := TrustIr.ClosureQueryProof.map_fst_ok_exists _ _ querySummary
    dsimp only [original, captured, row, block, apparent, producer, physical] at queryEq
    trustIrReduce
    all_goals trustIrSplitClosureQuery queryEq allowing []
    all_goals simp_all only [TrustIr.ClosureQueryProof.error_ne_ok,
      TrustIr.ClosureQueryProof.ok_ne_error, Except.ok.injEq, Except.error.injEq, Prod.mk.injEq]
    all_goals rcases queryEq with ⟨rfl, rfl⟩
    all_goals subst_vars
    all_goals simp [physicalMatches, closureTyListEq_refl]
    all_goals first | rfl | trustIrReduce
  }

theorem unreachable_block_still_constrains_storage_identity :
    observed { original with
      functions := [row 7 0 [],
        { (row 9 1 [.MakeClosure ⟨0⟩ ⟨7⟩ []]) with
          blocks := .ok (block [.MakeClosure ⟨0⟩ ⟨7⟩ []] ++
            [(⟨99⟩, {params := [], body := [.MakeClosure ⟨0⟩ ⟨8⟩ []], terminator := .Return []})]) }] } =
      .error (.malformed "conflicting closure storage targets") := by
  trustIrCompilerProof { rfl } {
    have querySummary :
        ((SourceLayout.prepare (layoutSourceOf ({ original with
      functions := [row 7 0 [],
        { (row 9 1 [.MakeClosure ⟨0⟩ ⟨7⟩ []]) with
          blocks := .ok (block [.MakeClosure ⟨0⟩ ⟨7⟩ []] ++
            [(⟨99⟩, {params := [], body := [.MakeClosure ⟨0⟩ ⟨8⟩ []], terminator := .Return []})]) }] }) ByteModel.le64)).query SourceLayout.Mode.shape (Ty.Closure ⟨0⟩)).map Prod.fst =
          .ok ({ size := 0, align := some 1 } : SourceLayout.Summary) := by
      trustIrReduce
    obtain ⟨after, queryEq⟩ := TrustIr.ClosureQueryProof.map_fst_ok_exists _ _ querySummary
    dsimp only [original, captured, row, block, apparent, producer, physical] at queryEq
    trustIrReduce
    all_goals trustIrSplitClosureQuery queryEq allowing []
    all_goals simp_all only [TrustIr.ClosureQueryProof.error_ne_ok,
      TrustIr.ClosureQueryProof.ok_ne_error, Except.ok.injEq, Except.error.injEq, Prod.mk.injEq]
    all_goals rcases queryEq with ⟨rfl, rfl⟩
    all_goals subst_vars
    all_goals simp [physicalMatches, closureTyListEq_refl]
    all_goals first | rfl | trustIrReduce
  }

theorem undecodable_unreachable_body_cannot_be_treated_as_empty :
    observed { original with functions := original.functions ++
      [{ row 99 1 [] with blocks := .error (.unsupported "original future body") }] } =
      .error (.unsupported "original future body") := by
  trustIrCompilerProof { rfl } {
    have querySummary :
        ((SourceLayout.prepare (layoutSourceOf ({ original with functions := original.functions ++
      [{ row 99 1 [] with blocks := .error (.unsupported "original future body") }] }) ByteModel.le64)).query SourceLayout.Mode.shape (Ty.Closure ⟨0⟩)).map Prod.fst =
          .ok ({ size := 0, align := some 1 } : SourceLayout.Summary) := by
      trustIrReduce
    obtain ⟨after, queryEq⟩ := TrustIr.ClosureQueryProof.map_fst_ok_exists _ _ querySummary
    dsimp only [original, captured, row, block, apparent, producer, physical] at queryEq
    trustIrReduce
    all_goals trustIrSplitClosureQuery queryEq allowing []
    all_goals simp_all only [TrustIr.ClosureQueryProof.error_ne_ok,
      TrustIr.ClosureQueryProof.ok_ne_error, Except.ok.injEq, Except.error.injEq, Prod.mk.injEq]
    all_goals rcases queryEq with ⟨rfl, rfl⟩
    all_goals subst_vars
    all_goals simp [physicalMatches, closureTyListEq_refl]
    all_goals first | rfl | trustIrReduce
  }

theorem malformed_body_error_is_preserved :
    observed { original with functions := original.functions ++
      [{ row 99 1 [] with blocks := .error (.malformed "original malformed body") }] } =
      .error (.malformed "original malformed body") := by
  trustIrCompilerProof { rfl } {
    have querySummary :
        ((SourceLayout.prepare (layoutSourceOf ({ original with functions := original.functions ++
      [{ row 99 1 [] with blocks := .error (.malformed "original malformed body") }] }) ByteModel.le64)).query SourceLayout.Mode.shape (Ty.Closure ⟨0⟩)).map Prod.fst =
          .ok ({ size := 0, align := some 1 } : SourceLayout.Summary) := by
      trustIrReduce
    obtain ⟨after, queryEq⟩ := TrustIr.ClosureQueryProof.map_fst_ok_exists _ _ querySummary
    dsimp only [original, captured, row, block, apparent, producer, physical] at queryEq
    trustIrReduce
    all_goals trustIrSplitClosureQuery queryEq allowing []
    all_goals simp_all only [TrustIr.ClosureQueryProof.error_ne_ok,
      TrustIr.ClosureQueryProof.ok_ne_error, Except.ok.injEq, Except.error.injEq, Prod.mk.injEq]
    all_goals rcases queryEq with ⟨rfl, rfl⟩
    all_goals subst_vars
    all_goals simp [physicalMatches, closureTyListEq_refl]
    all_goals first | rfl | trustIrReduce
  }

theorem repeated_same_target_is_not_an_ambiguity :
    observed { original with globals :=
      [{ty := .Closure ⟨0⟩, initializer := some (.closure ⟨7⟩ [])}] } =
      .ok (7, 0, some 1, 0) := by
  trustIrCompilerProof { rfl } {
    have querySummary :
        ((SourceLayout.prepare (layoutSourceOf ({ original with globals :=
      [{ty := .Closure ⟨0⟩, initializer := some (.closure ⟨7⟩ [])}] }) ByteModel.le64)).query SourceLayout.Mode.shape (Ty.Closure ⟨0⟩)).map Prod.fst =
          .ok ({ size := 0, align := some 1 } : SourceLayout.Summary) := by
      trustIrReduce
    obtain ⟨after, queryEq⟩ := TrustIr.ClosureQueryProof.map_fst_ok_exists _ _ querySummary
    dsimp only [original, captured, row, block, apparent, producer, physical] at queryEq
    trustIrReduce
    all_goals trustIrSplitClosureQuery queryEq allowing []
    all_goals simp_all only [TrustIr.ClosureQueryProof.error_ne_ok,
      TrustIr.ClosureQueryProof.ok_ne_error, Except.ok.injEq, Except.error.injEq, Prod.mk.injEq]
    all_goals rcases queryEq with ⟨rfl, rfl⟩
    all_goals subst_vars
    all_goals simp [physicalMatches, closureTyListEq_refl]
    all_goals first | rfl | trustIrReduce
    all_goals have signatureCheck := (TrustIrEval.ClosureStorage.requireTrue_eq_ok (physicalMatches [] apparent apparent) "closure storage target signature mismatch" original_signature_true)
    all_goals trustIrRetypeClosureCheck signatureCheck allowing []
    all_goals erw [signatureCheck]
    all_goals first | rfl | trustIrReduce
  }

theorem different_nominal_cannot_supply_missing_target :
    observed { original with functions := [row 7 0 [],
      row 9 1 [.MakeClosure ⟨1⟩ ⟨7⟩ []]] } =
      .error (.malformed "missing closure storage target") := by
  trustIrCompilerProof { rfl } {
    have querySummary :
        ((SourceLayout.prepare (layoutSourceOf ({ original with functions := [row 7 0 [],
      row 9 1 [.MakeClosure ⟨1⟩ ⟨7⟩ []]] }) ByteModel.le64)).query SourceLayout.Mode.shape (Ty.Closure ⟨0⟩)).map Prod.fst =
          .ok ({ size := 0, align := some 1 } : SourceLayout.Summary) := by
      trustIrReduce
    obtain ⟨after, queryEq⟩ := TrustIr.ClosureQueryProof.map_fst_ok_exists _ _ querySummary
    dsimp only [original, captured, row, block, apparent, producer, physical] at queryEq
    trustIrReduce
    all_goals trustIrSplitClosureQuery queryEq allowing []
    all_goals simp_all only [TrustIr.ClosureQueryProof.error_ne_ok,
      TrustIr.ClosureQueryProof.ok_ne_error, Except.ok.injEq, Except.error.injEq, Prod.mk.injEq]
    all_goals rcases queryEq with ⟨rfl, rfl⟩
    all_goals subst_vars
    all_goals simp [physicalMatches, closureTyListEq_refl]
    all_goals first | rfl | trustIrReduce
  }

theorem untyped_nested_closure_constant_refuses :
    observed { original with globals := [{
      ty := .Tuple [.Closure ⟨0⟩]
      initializer := some (.aggregate [.closure ⟨7⟩ []])}] } =
      .error (.unsupported "untyped constant closure storage") := by
  trustIrCompilerProof { rfl } {
    have querySummary :
        ((SourceLayout.prepare (layoutSourceOf ({ original with globals := [{
      ty := .Tuple [.Closure ⟨0⟩]
      initializer := some (.aggregate [.closure ⟨7⟩ []])}] }) ByteModel.le64)).query SourceLayout.Mode.shape (Ty.Closure ⟨0⟩)).map Prod.fst =
          .ok ({ size := 0, align := some 1 } : SourceLayout.Summary) := by
      trustIrReduce
    obtain ⟨after, queryEq⟩ := TrustIr.ClosureQueryProof.map_fst_ok_exists _ _ querySummary
    dsimp only [original, captured, row, block, apparent, producer, physical] at queryEq
    trustIrReduce
    all_goals trustIrSplitClosureQuery queryEq allowing []
    all_goals simp_all only [TrustIr.ClosureQueryProof.error_ne_ok,
      TrustIr.ClosureQueryProof.ok_ne_error, Except.ok.injEq, Except.error.injEq, Prod.mk.injEq]
    all_goals rcases queryEq with ⟨rfl, rfl⟩
    all_goals subst_vars
    all_goals simp [physicalMatches, closureTyListEq_refl]
    all_goals first | rfl | trustIrReduce
  }

theorem typed_closure_with_nested_capture_refuses :
    observed { original with globals := [{
      ty := .Closure ⟨0⟩
      initializer := some (.closure ⟨7⟩ [.closure ⟨8⟩ []])}] } =
      .error (.unsupported "nested constant closure storage") := by
  trustIrCompilerProof { rfl } {
    have querySummary :
        ((SourceLayout.prepare (layoutSourceOf ({ original with globals := [{
      ty := .Closure ⟨0⟩
      initializer := some (.closure ⟨7⟩ [.closure ⟨8⟩ []])}] }) ByteModel.le64)).query SourceLayout.Mode.shape (Ty.Closure ⟨0⟩)).map Prod.fst =
          .ok ({ size := 0, align := some 1 } : SourceLayout.Summary) := by
      trustIrReduce
    obtain ⟨after, queryEq⟩ := TrustIr.ClosureQueryProof.map_fst_ok_exists _ _ querySummary
    dsimp only [original, captured, row, block, apparent, producer, physical] at queryEq
    trustIrReduce
    all_goals trustIrSplitClosureQuery queryEq allowing []
    all_goals simp_all only [TrustIr.ClosureQueryProof.error_ne_ok,
      TrustIr.ClosureQueryProof.ok_ne_error, Except.ok.injEq, Except.error.injEq, Prod.mk.injEq]
    all_goals rcases queryEq with ⟨rfl, rfl⟩
    all_goals subst_vars
    all_goals simp [physicalMatches, closureTyListEq_refl]
    all_goals first | rfl | trustIrReduce
  }

theorem deeply_nested_constant_is_not_ignored :
    containsClosure (.record [("field", .splat (.array [.sequence
      [.set [.vector [.closure ⟨7⟩ []]]]]) 18446744073709551615)]) = true := by
  trustIrCompilerProof { simp [containsClosure, fieldsContainClosure, listContainsClosure] } { trustIrReduce }

theorem missing_original_function_refuses :
    observed { original with functions := [row 9 1 [.MakeClosure ⟨0⟩ ⟨7⟩ []]] } =
      .error (.malformed "missing or ambiguous closure target") := by
  trustIrCompilerProof { rfl } {
    have querySummary :
        ((SourceLayout.prepare (layoutSourceOf ({ original with functions := [row 9 1 [.MakeClosure ⟨0⟩ ⟨7⟩ []]] }) ByteModel.le64)).query SourceLayout.Mode.shape (Ty.Closure ⟨0⟩)).map Prod.fst =
          .ok ({ size := 0, align := some 1 } : SourceLayout.Summary) := by
      trustIrReduce
    obtain ⟨after, queryEq⟩ := TrustIr.ClosureQueryProof.map_fst_ok_exists _ _ querySummary
    dsimp only [original, captured, row, block, apparent, producer, physical] at queryEq
    trustIrReduce
    all_goals trustIrSplitClosureQuery queryEq allowing []
    all_goals simp_all only [TrustIr.ClosureQueryProof.error_ne_ok,
      TrustIr.ClosureQueryProof.ok_ne_error, Except.ok.injEq, Except.error.injEq, Prod.mk.injEq]
    all_goals rcases queryEq with ⟨rfl, rfl⟩
    all_goals subst_vars
    all_goals simp [physicalMatches, closureTyListEq_refl]
    all_goals first | rfl | trustIrReduce
  }

theorem duplicate_original_function_id_refuses :
    observed { original with functions := original.functions ++ [row 7 0 []] } =
      .error (.malformed "missing or ambiguous closure target") := by
  trustIrCompilerProof { rfl } {
    have querySummary :
        ((SourceLayout.prepare (layoutSourceOf ({ original with functions := original.functions ++ [row 7 0 []] }) ByteModel.le64)).query SourceLayout.Mode.shape (Ty.Closure ⟨0⟩)).map Prod.fst =
          .ok ({ size := 0, align := some 1 } : SourceLayout.Summary) := by
      trustIrReduce
    obtain ⟨after, queryEq⟩ := TrustIr.ClosureQueryProof.map_fst_ok_exists _ _ querySummary
    dsimp only [original, captured, row, block, apparent, producer, physical] at queryEq
    trustIrReduce
    all_goals trustIrSplitClosureQuery queryEq allowing []
    all_goals simp_all only [TrustIr.ClosureQueryProof.error_ne_ok,
      TrustIr.ClosureQueryProof.ok_ne_error, Except.ok.injEq, Except.error.injEq, Prod.mk.injEq]
    all_goals rcases queryEq with ⟨rfl, rfl⟩
    all_goals subst_vars
    all_goals simp [physicalMatches, closureTyListEq_refl]
    all_goals first | rfl | trustIrReduce
  }

theorem bodyless_declaration_refuses :
    observed { original with functions := [{row 7 0 [] with isDeclaration := true, blocks := .ok []},
      row 9 1 [.MakeClosure ⟨0⟩ ⟨7⟩ []]] } =
      .error (.malformed "closure storage target has no body") := by
  trustIrCompilerProof { rfl } {
    have querySummary :
        ((SourceLayout.prepare (layoutSourceOf ({ original with functions := [{row 7 0 [] with isDeclaration := true, blocks := .ok []},
      row 9 1 [.MakeClosure ⟨0⟩ ⟨7⟩ []]] }) ByteModel.le64)).query SourceLayout.Mode.shape (Ty.Closure ⟨0⟩)).map Prod.fst =
          .ok ({ size := 0, align := some 1 } : SourceLayout.Summary) := by
      trustIrReduce
    obtain ⟨after, queryEq⟩ := TrustIr.ClosureQueryProof.map_fst_ok_exists _ _ querySummary
    dsimp only [original, captured, row, block, apparent, producer, physical] at queryEq
    trustIrReduce
    all_goals trustIrSplitClosureQuery queryEq allowing []
    all_goals simp_all only [TrustIr.ClosureQueryProof.error_ne_ok,
      TrustIr.ClosureQueryProof.ok_ne_error, Except.ok.injEq, Except.error.injEq, Prod.mk.injEq]
    all_goals rcases queryEq with ⟨rfl, rfl⟩
    all_goals subst_vars
    all_goals simp [physicalMatches, closureTyListEq_refl]
    all_goals first | rfl | trustIrReduce
  }

theorem empty_body_with_false_declaration_bit_refuses :
    observed { original with functions := [{row 7 0 [] with blocks := .ok []},
      row 9 1 [.MakeClosure ⟨0⟩ ⟨7⟩ []]] } =
      .error (.malformed "closure storage target has no body") := by
  trustIrCompilerProof { rfl } {
    have querySummary :
        ((SourceLayout.prepare (layoutSourceOf ({ original with functions := [{row 7 0 [] with blocks := .ok []},
      row 9 1 [.MakeClosure ⟨0⟩ ⟨7⟩ []]] }) ByteModel.le64)).query SourceLayout.Mode.shape (Ty.Closure ⟨0⟩)).map Prod.fst =
          .ok ({ size := 0, align := some 1 } : SourceLayout.Summary) := by
      trustIrReduce
    obtain ⟨after, queryEq⟩ := TrustIr.ClosureQueryProof.map_fst_ok_exists _ _ querySummary
    dsimp only [original, captured, row, block, apparent, producer, physical] at queryEq
    trustIrReduce
    all_goals trustIrSplitClosureQuery queryEq allowing []
    all_goals simp_all only [TrustIr.ClosureQueryProof.error_ne_ok,
      TrustIr.ClosureQueryProof.ok_ne_error, Except.ok.injEq, Except.error.injEq, Prod.mk.injEq]
    all_goals rcases queryEq with ⟨rfl, rfl⟩
    all_goals subst_vars
    all_goals simp [physicalMatches, closureTyListEq_refl]
    all_goals first | rfl | trustIrReduce
  }

theorem physical_parameter_kind_and_width_are_exact :
    observed { original with
      funcTys := [apparent, producer,
        {params := [.U32], returns := [.U64], isVararg := false}]
      functions := [row 7 2 [], row 9 1 [.MakeClosure ⟨0⟩ ⟨7⟩ []]] } =
      .error (.malformed "closure storage target signature mismatch") := by
  trustIrCompilerProof { rfl } {
    have querySummary :
        ((SourceLayout.prepare (layoutSourceOf ({ original with
      funcTys := [apparent, producer,
        {params := [.U32], returns := [.U64], isVararg := false}]
      functions := [row 7 2 [], row 9 1 [.MakeClosure ⟨0⟩ ⟨7⟩ []]] }) ByteModel.le64)).query SourceLayout.Mode.shape (Ty.Closure ⟨0⟩)).map Prod.fst =
          .ok ({ size := 0, align := some 1 } : SourceLayout.Summary) := by
      trustIrReduce
    obtain ⟨after, queryEq⟩ := TrustIr.ClosureQueryProof.map_fst_ok_exists _ _ querySummary
    dsimp only [original, captured, row, block, apparent, producer, physical] at queryEq
    trustIrReduce
    all_goals trustIrSplitClosureQuery queryEq allowing []
    all_goals simp_all only [TrustIr.ClosureQueryProof.error_ne_ok,
      TrustIr.ClosureQueryProof.ok_ne_error, Except.ok.injEq, Except.error.injEq, Prod.mk.injEq]
    all_goals rcases queryEq with ⟨rfl, rfl⟩
    all_goals subst_vars
    all_goals simp [physicalMatches, closureTyListEq_refl]
    all_goals first | rfl | trustIrReduce
    all_goals have signatureCheck := (TrustIrEval.ClosureStorage.requireTrue_eq_error (physicalMatches [] apparent {params := [.U32], returns := [.U64], isVararg := false}) "closure storage target signature mismatch" parameter_signature_false)
    all_goals trustIrRetypeClosureCheck signatureCheck allowing []
    all_goals erw [signatureCheck]
    all_goals first | rfl | trustIrReduce
  }

theorem physical_returns_are_exact :
    observed { original with
      funcTys := [apparent, producer,
        {params := [.U64], returns := [.I64], isVararg := false}]
      functions := [row 7 2 [], row 9 1 [.MakeClosure ⟨0⟩ ⟨7⟩ []]] } =
      .error (.malformed "closure storage target signature mismatch") := by
  trustIrCompilerProof { rfl } {
    have querySummary :
        ((SourceLayout.prepare (layoutSourceOf ({ original with
      funcTys := [apparent, producer,
        {params := [.U64], returns := [.I64], isVararg := false}]
      functions := [row 7 2 [], row 9 1 [.MakeClosure ⟨0⟩ ⟨7⟩ []]] }) ByteModel.le64)).query SourceLayout.Mode.shape (Ty.Closure ⟨0⟩)).map Prod.fst =
          .ok ({ size := 0, align := some 1 } : SourceLayout.Summary) := by
      trustIrReduce
    obtain ⟨after, queryEq⟩ := TrustIr.ClosureQueryProof.map_fst_ok_exists _ _ querySummary
    dsimp only [original, captured, row, block, apparent, producer, physical] at queryEq
    trustIrReduce
    all_goals trustIrSplitClosureQuery queryEq allowing []
    all_goals simp_all only [TrustIr.ClosureQueryProof.error_ne_ok,
      TrustIr.ClosureQueryProof.ok_ne_error, Except.ok.injEq, Except.error.injEq, Prod.mk.injEq]
    all_goals rcases queryEq with ⟨rfl, rfl⟩
    all_goals subst_vars
    all_goals simp [physicalMatches, closureTyListEq_refl]
    all_goals first | rfl | trustIrReduce
    all_goals have signatureCheck := (TrustIrEval.ClosureStorage.requireTrue_eq_error (physicalMatches [] apparent {params := [.U64], returns := [.I64], isVararg := false}) "closure storage target signature mismatch" return_signature_false)
    all_goals trustIrRetypeClosureCheck signatureCheck allowing []
    all_goals erw [signatureCheck]
    all_goals first | rfl | trustIrReduce
  }

theorem missing_physical_capture_prefix_refuses :
    observed { captured with functions := [row 7 0 [], row 9 1 [.MakeClosure ⟨0⟩ ⟨7⟩ [⟨5⟩]]] } =
      .error (.malformed "closure storage target signature mismatch") := by
  trustIrCompilerProof { rfl } {
    have querySummary :
        ((SourceLayout.prepare (layoutSourceOf ({ captured with functions := [row 7 0 [], row 9 1 [.MakeClosure ⟨0⟩ ⟨7⟩ [⟨5⟩]]] }) ByteModel.le64)).query SourceLayout.Mode.shape (Ty.Closure ⟨0⟩)).map Prod.fst =
          .ok ({ size := 8, align := some 8, fields := [{ty := .U64, offset := 0, size := 8, align := 8}] } : SourceLayout.Summary) := by
      trustIrReduce
    obtain ⟨after, queryEq⟩ := TrustIr.ClosureQueryProof.map_fst_ok_exists _ _ querySummary
    dsimp only [original, captured, row, block, apparent, producer, physical] at queryEq
    trustIrReduce
    all_goals trustIrSplitClosureQuery queryEq allowing []
    all_goals simp_all only [TrustIr.ClosureQueryProof.error_ne_ok,
      TrustIr.ClosureQueryProof.ok_ne_error, Except.ok.injEq, Except.error.injEq, Prod.mk.injEq]
    all_goals rcases queryEq with ⟨rfl, rfl⟩
    all_goals subst_vars
    all_goals simp [physicalMatches, closureTyListEq_refl]
    all_goals first | rfl | trustIrReduce
    all_goals have signatureCheck := (TrustIrEval.ClosureStorage.requireTrue_eq_error (physicalMatches [.U64] apparent apparent) "closure storage target signature mismatch" prefix_signature_false)
    all_goals trustIrRetypeClosureCheck signatureCheck allowing []
    all_goals erw [signatureCheck]
    all_goals first | rfl | trustIrReduce
  }

theorem physical_vararg_refuses :
    observed { original with
      funcTys := [apparent, producer, {apparent with isVararg := true}]
      functions := [row 7 2 [], row 9 1 [.MakeClosure ⟨0⟩ ⟨7⟩ []]] } =
      .error (.malformed "closure storage target signature mismatch") := by
  trustIrCompilerProof { rfl } {
    have querySummary :
        ((SourceLayout.prepare (layoutSourceOf ({ original with
      funcTys := [apparent, producer, {apparent with isVararg := true}]
      functions := [row 7 2 [], row 9 1 [.MakeClosure ⟨0⟩ ⟨7⟩ []]] }) ByteModel.le64)).query SourceLayout.Mode.shape (Ty.Closure ⟨0⟩)).map Prod.fst =
          .ok ({ size := 0, align := some 1 } : SourceLayout.Summary) := by
      trustIrReduce
    obtain ⟨after, queryEq⟩ := TrustIr.ClosureQueryProof.map_fst_ok_exists _ _ querySummary
    dsimp only [original, captured, row, block, apparent, producer, physical] at queryEq
    trustIrReduce
    all_goals trustIrSplitClosureQuery queryEq allowing []
    all_goals simp_all only [TrustIr.ClosureQueryProof.error_ne_ok,
      TrustIr.ClosureQueryProof.ok_ne_error, Except.ok.injEq, Except.error.injEq, Prod.mk.injEq]
    all_goals rcases queryEq with ⟨rfl, rfl⟩
    all_goals subst_vars
    all_goals simp [physicalMatches, closureTyListEq_refl]
    all_goals first | rfl | trustIrReduce
    all_goals have signatureCheck := (TrustIrEval.ClosureStorage.requireTrue_eq_error (physicalMatches [] apparent {apparent with isVararg := true}) "closure storage target signature mismatch" vararg_signature_false)
    all_goals trustIrRetypeClosureCheck signatureCheck allowing []
    all_goals erw [signatureCheck]
    all_goals first | rfl | trustIrReduce
  }

theorem apparent_vararg_refuses :
    observed { original with funcTys := [{apparent with isVararg := true}, producer] } =
      .error (.malformed "closure storage requires an unadapted signature") := by
  trustIrCompilerProof { rfl } {
    have querySummary :
        ((SourceLayout.prepare (layoutSourceOf ({ original with funcTys := [{apparent with isVararg := true}, producer] }) ByteModel.le64)).query SourceLayout.Mode.shape (Ty.Closure ⟨0⟩)).map Prod.fst =
          .ok ({ size := 0, align := some 1 } : SourceLayout.Summary) := by
      trustIrReduce
    obtain ⟨after, queryEq⟩ := TrustIr.ClosureQueryProof.map_fst_ok_exists _ _ querySummary
    dsimp only [original, captured, row, block, apparent, producer, physical] at queryEq
    trustIrReduce
    all_goals trustIrSplitClosureQuery queryEq allowing []
    all_goals simp_all only [TrustIr.ClosureQueryProof.error_ne_ok,
      TrustIr.ClosureQueryProof.ok_ne_error, Except.ok.injEq, Except.error.injEq, Prod.mk.injEq]
    all_goals rcases queryEq with ⟨rfl, rfl⟩
    all_goals subst_vars
    all_goals simp [physicalMatches, closureTyListEq_refl]
    all_goals first | rfl | trustIrReduce
  }

theorem apparent_abi_metadata_is_not_transport_permission (abi : SignatureAbi) :
    observed { original with funcTys := [{apparent with abi := some abi}, producer] } =
      .error (.malformed "closure storage requires an unadapted signature") := by
  trustIrCompilerProof { rfl } {
    have querySummary :
        ((SourceLayout.prepare (layoutSourceOf ({ original with funcTys := [{apparent with abi := some abi}, producer] }) ByteModel.le64)).query SourceLayout.Mode.shape (Ty.Closure ⟨0⟩)).map Prod.fst =
          .ok ({ size := 0, align := some 1 } : SourceLayout.Summary) := by
      trustIrReduce
    obtain ⟨after, queryEq⟩ := TrustIr.ClosureQueryProof.map_fst_ok_exists _ _ querySummary
    dsimp only [original, captured, row, block, apparent, producer, physical] at queryEq
    trustIrReduce
    all_goals trustIrSplitClosureQuery queryEq allowing [abi]
    all_goals simp_all only [TrustIr.ClosureQueryProof.error_ne_ok,
      TrustIr.ClosureQueryProof.ok_ne_error, Except.ok.injEq, Except.error.injEq, Prod.mk.injEq]
    all_goals rcases queryEq with ⟨rfl, rfl⟩
    all_goals subst_vars
    all_goals simp [physicalMatches, closureTyListEq_refl]
    all_goals first | rfl | trustIrReduce
    all_goals have signatureCheck := (TrustIrEval.ClosureStorage.requireTrue_eq_error (({apparent with abi := some abi} : FuncTyDef).abi.isNone) "closure storage requires an unadapted signature" (apparent_abi_false abi))
    all_goals trustIrRetypeClosureCheck signatureCheck allowing [abi]
    all_goals erw [signatureCheck]
    all_goals first | rfl | trustIrReduce
  }

theorem physical_abi_metadata_is_not_transport_permission (abi : SignatureAbi) :
    observed { original with
      funcTys := [apparent, producer, {apparent with abi := some abi}]
      functions := [row 7 2 [], row 9 1 [.MakeClosure ⟨0⟩ ⟨7⟩ []]] } =
      .error (.malformed "closure storage target signature mismatch") := by
  trustIrCompilerProof { rfl } {
    have querySummary :
        ((SourceLayout.prepare (layoutSourceOf ({ original with
      funcTys := [apparent, producer, {apparent with abi := some abi}]
      functions := [row 7 2 [], row 9 1 [.MakeClosure ⟨0⟩ ⟨7⟩ []]] }) ByteModel.le64)).query SourceLayout.Mode.shape (Ty.Closure ⟨0⟩)).map Prod.fst =
          .ok ({ size := 0, align := some 1 } : SourceLayout.Summary) := by
      trustIrReduce
    obtain ⟨after, queryEq⟩ := TrustIr.ClosureQueryProof.map_fst_ok_exists _ _ querySummary
    dsimp only [original, captured, row, block, apparent, producer, physical] at queryEq
    trustIrReduce
    all_goals trustIrSplitClosureQuery queryEq allowing [abi]
    all_goals simp_all only [TrustIr.ClosureQueryProof.error_ne_ok,
      TrustIr.ClosureQueryProof.ok_ne_error, Except.ok.injEq, Except.error.injEq, Prod.mk.injEq]
    all_goals rcases queryEq with ⟨rfl, rfl⟩
    all_goals subst_vars
    all_goals simp [physicalMatches, closureTyListEq_refl]
    all_goals first | rfl | trustIrReduce
    all_goals have signatureCheck := (TrustIrEval.ClosureStorage.requireTrue_eq_error (physicalMatches [] apparent {apparent with abi := some abi}) "closure storage target signature mismatch" (abi_signature_false abi))
    all_goals trustIrRetypeClosureCheck signatureCheck allowing [abi]
    all_goals erw [signatureCheck]
    all_goals first | rfl | trustIrReduce
  }

theorem function_item_cannot_impersonate_nominal_closure_constructor :
    observed { original with functions := [row 7 0 [],
      row 9 1 [.Const (.Closure ⟨0⟩) (.fnDef ⟨7⟩)]] } =
      .error (.malformed "missing closure storage target") := by
  trustIrCompilerProof { rfl } {
    have querySummary :
        ((SourceLayout.prepare (layoutSourceOf ({ original with functions := [row 7 0 [],
      row 9 1 [.Const (.Closure ⟨0⟩) (.fnDef ⟨7⟩)]] }) ByteModel.le64)).query SourceLayout.Mode.shape (Ty.Closure ⟨0⟩)).map Prod.fst =
          .ok ({ size := 0, align := some 1 } : SourceLayout.Summary) := by
      trustIrReduce
    obtain ⟨after, queryEq⟩ := TrustIr.ClosureQueryProof.map_fst_ok_exists _ _ querySummary
    dsimp only [original, captured, row, block, apparent, producer, physical] at queryEq
    trustIrReduce
    all_goals trustIrSplitClosureQuery queryEq allowing []
    all_goals simp_all only [TrustIr.ClosureQueryProof.error_ne_ok,
      TrustIr.ClosureQueryProof.ok_ne_error, Except.ok.injEq, Except.error.injEq, Prod.mk.injEq]
    all_goals rcases queryEq with ⟨rfl, rfl⟩
    all_goals subst_vars
    all_goals simp [physicalMatches, closureTyListEq_refl]
    all_goals first | rfl | trustIrReduce
  }

theorem invalid_capture_offset_still_refuses_before_target :
    observed { captured with closureLayouts :=
      [{closure := ⟨0⟩, size := 8, align := 8, captureOffsets := [1]}] } =
      .error (.malformed s!"closure layout: {repr (SourceLayout.Error.incoherent "closure" 0)}") := by
  trustIrCompilerProof { rfl } {
    have querySummary :
        ((SourceLayout.prepare (layoutSourceOf ({ captured with closureLayouts :=
      [{closure := ⟨0⟩, size := 8, align := 8, captureOffsets := [1]}] }) ByteModel.le64)).query SourceLayout.Mode.shape (Ty.Closure ⟨0⟩)).map Prod.fst =
          .error (SourceLayout.Error.incoherent "closure" 0) := by
      trustIrReduce
    have queryEq := TrustIr.ClosureQueryProof.map_fst_error _ _ querySummary
    dsimp only [original, captured, row, block, apparent, producer, physical] at queryEq
    trustIrReduce
    all_goals trustIrSplitClosureQuery queryEq allowing []
    all_goals simp_all only [TrustIr.ClosureQueryProof.error_ne_ok,
      TrustIr.ClosureQueryProof.ok_ne_error, Except.ok.injEq, Except.error.injEq, Prod.mk.injEq]
    all_goals subst_vars
    all_goals simp [physicalMatches, closureTyListEq_refl]
    all_goals first | rfl | trustIrReduce
  }

theorem byte_model_error_is_preserved_before_binding :
    observed { original with byteModel := .error (.unsupported "original target") } =
      .error (.unsupported "original target") := rfl

/-- False statements are exported solely for the hostile fresh-kernel
substitution controls; no proof or decision procedure is attached. -/
def WrongOriginalTarget : Prop := observed original = .ok (8, 0, some 1, 0)
def WrongGeometryTarget : Prop :=
  observed { original with functions := [row 7 0 [], row 9 1 []] } = .ok (7, 0, some 1, 0)
def WrongPhysicalTarget : Prop :=
  observed { original with
    funcTys := [apparent, producer, {params := [.U32], returns := [.U64], isVararg := false}]
    functions := [row 7 2 [], row 9 1 [.MakeClosure ⟨0⟩ ⟨7⟩ []]] } = .ok (7, 0, some 1, 0)

end TrustIrEval.ClosureStorage.Checks
