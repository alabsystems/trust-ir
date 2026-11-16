-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.AYCastReplay

namespace TrustIr.TrustIrExpr.TypedBindingControls

private def mixed : Except String (SMTTypedRequest (.bv 8)) := do
  let word ← SMTCheckedTerm.nativeVar 8 "_0"
  let path ← SMTCheckedTerm.boolVar "pc$0"
  let zero ← SMTCheckedTerm.bvConst 8 0
  (SMTCheckedTerm.ite path word zero).toTypedRequest

private def observe {sort : SMTSort} (built : Except String (SMTTypedRequest sort)) :=
  built.map (fun request =>
    (request.script, request.bindings, request.boolBindings, request.typedBindings))

/-- Native-style names remain exact; the complete declarations have their sorts. -/
theorem mixed_declarations : observe mixed = .ok (
    "(set-logic QF_BV)\n(declare-fun _0 () (_ BitVec 8))\n(declare-fun pc$0 () Bool)\n" ++
      "(assert (distinct (ite pc$0 _0 (_ bv0 8)) (_ bv0 8)))\n(check-sat)\n",
    [(8,"_0")], ["pc$0"], [(.bv 8,"_0"),(.bool,"pc$0")]) := by rfl

private def collision : Except String (SMTTypedRequest (.bv 8)) := do
  let word ← SMTCheckedTerm.nativeVar 8 "x"
  let boolean ← SMTCheckedTerm.boolVar "x"
  let zero ← SMTCheckedTerm.bvConst 8 0
  (SMTCheckedTerm.ite boolean word zero).toTypedRequest

theorem cross_sort_refused : observe collision = .error "SMT symbol used at conflicting sorts" := by rfl

private def widths : Except String (SMTTypedRequest (.bv 24)) := do
  let high ← SMTCheckedTerm.nativeVar 8 "x"
  let low ← SMTCheckedTerm.nativeVar 16 "x"
  (SMTCheckedTerm.concat high low).toTypedRequest

theorem conflicting_widths_refused : observe widths = .error "SMT symbol used at conflicting widths" := by rfl

private def boolean : Except String (SMTTypedRequest .bool) := do
  let path ← SMTCheckedTerm.boolVar "flag$0"
  (SMTCheckedTerm.binary .boolAnd path path).toTypedRequest

theorem bool_duplicates_exact : observe boolean = .ok (
    "(set-logic QF_BV)\n(declare-fun flag$0 () Bool)\n(assert (and flag$0 flag$0))\n(check-sat)\n",
    [], ["flag$0"], [(.bool,"flag$0")]) := by rfl

theorem original_encoded_identifier : SMTTerm.checkIdentifier "v_120_" = true := by decide

theorem raw_names : ["x", "_0", "_1", "pc$0", "flag$0", "v$0", "v$1"].all SMTTerm.checkNativeIdentifier = true := by decide

theorem unsafe_names : ["", "true", "let", "x|", "x\n(assert false)", "0x", "λ"].all
    (fun name => !SMTTerm.checkNativeIdentifier name) = true := by decide

private def legacyRaw := (SMTCheckedTerm.var 8 "x").map (fun checked => checked.bindings)
private def legacyEncoded : Except String (SMTTypedRequest (.bv 8)) := do
  let word ← SMTCheckedTerm.var 8 "v_120_"
  word.toTypedRequest

theorem legacy_raw_name_refused : legacyRaw = .error "unsafe SMT identifier" := by rfl

theorem legacy_bv_script_unchanged : observe legacyEncoded = .ok (
    "(set-logic QF_BV)\n(declare-fun v_120_ () (_ BitVec 8))\n" ++
    "(assert (distinct v_120_ (_ bv0 8)))\n(check-sat)\n",
    [(8,"v_120_")], [], [(.bv 8,"v_120_")]) := by rfl

/-- Bool reads use the same numeric environment and complete Bool carrier. -/
theorem bool_variable_value (env : SMTEnv) :
    (SMTTerm.boolVar "pc$0").eval env = (env "pc$0" != 0) := rfl

/-- The unchanged cast theorem now accepts a real Bool variable, for ALL envs. -/
theorem full_bool_zext (arg : SMTCheckedTerm .bool) (env : SMTEnv) :
    ((IntegerCastTarget.zextBool 128 (by decide)).emit arg).term.eval env =
      BitVec.ofInt 128 (if arg.term.eval env then 1 else 0) :=
  IntegerCastTarget.emit_eval _ arg env

private def capturedBoolArgument : SMTCheckedTerm .bool :=
  ⟨.boolVar "flag$0", [], Or.inr (by decide), rfl, ["flag$0"], rfl⟩

/-- Exact bytes observed in the native cast capture's passing encoder control.
This is a local term/cast link; transport/source provenance remains separate. -/
theorem captured_bool_target_prints :
    (((IntegerCastTarget.zextBool 16 (by decide)).emit capturedBoolArgument).term).Prints
      "(ite flag$0 #x0001 #x0000)" :=
  .ite (.boolVar "flag$0")
    (.bvHex 16 1 [0,0,0,1] (by decide) (by decide) (by decide) (by decide))
    (.bvHex 16 0 [0,0,0,0] (by decide) (by decide) (by decide) (by decide))

/-- Exact hex bytes witness the SAME original BV literal, including full U64. -/
theorem full_u64_hex : (SMTTerm.bvConst 64 (-1)).Prints "#xffffffffffffffff" :=
  .bvHex 64 (-1) [15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15]
    (by decide) (by decide) (by decide) (by decide)

theorem full_u128_hex : (SMTTerm.bvConst 128 (-1)).Prints "#xffffffffffffffffffffffffffffffff" :=
  .bvHex 128 (-1) (List.replicate 32 15)
    (by decide) (by decide) (by
      intro digit member
      have same : digit = 15 := by simpa using member
      subst digit
      decide) (by rfl)

theorem binary_literal : (SMTTerm.bvConst 3 3).Prints "#b011" :=
  .bvBinary 3 3 [0,1,1] (by decide) (by decide) (by decide) (by decide)

/-- Wrong magnitude, width and digit cannot satisfy literal witness premises. -/
theorem wrong_literal_value : SMTTerm.literalValue 16 [15,15] ≠ (1 % (2 : Int)^8).toNat := by decide

theorem wrong_literal_width : [15,15].length * 4 ≠ 16 := by decide

theorem out_of_range_digit : ¬ (∀ digit ∈ [16], digit < 16) := by decide

end TrustIr.TrustIrExpr.TypedBindingControls

#trustIrAxioms TrustIr.TrustIrExpr.TypedBindingControls.mixed_declarations <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.TrustIrExpr.TypedBindingControls.cross_sort_refused <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.TrustIrExpr.TypedBindingControls.conflicting_widths_refused <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.TrustIrExpr.TypedBindingControls.bool_duplicates_exact <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.TrustIrExpr.TypedBindingControls.original_encoded_identifier <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.TrustIrExpr.TypedBindingControls.raw_names <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.TrustIrExpr.TypedBindingControls.unsafe_names <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.TrustIrExpr.TypedBindingControls.legacy_raw_name_refused <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.TrustIrExpr.TypedBindingControls.legacy_bv_script_unchanged <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.TrustIrExpr.TypedBindingControls.bool_variable_value <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.TrustIrExpr.TypedBindingControls.full_bool_zext <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.TrustIrExpr.TypedBindingControls.captured_bool_target_prints <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.TrustIrExpr.TypedBindingControls.full_u64_hex <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.TrustIrExpr.TypedBindingControls.full_u128_hex <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.TrustIrExpr.TypedBindingControls.binary_literal <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.TrustIrExpr.TypedBindingControls.wrong_literal_value <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.TrustIrExpr.TypedBindingControls.wrong_literal_width <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.TrustIrExpr.TypedBindingControls.out_of_range_digit <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.AYCastReplay.body_request <= [propext, Classical.choice, Quot.sound]
