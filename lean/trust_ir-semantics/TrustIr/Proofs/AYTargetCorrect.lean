-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYCoreValue
import TrustIr.Proofs.AYBitVecBitwise
import TrustIr.Proofs.AYSymbolProps

namespace TrustIr.TrustIrExpr

private theorem native_of_numeric (sort : SMTSort) (value : sort.CoreValue) (number : Int)
    (same : sort.fromCore value = number) : value = sort.toCore number := by
  calc
    value = sort.toCore (sort.fromCore value) := (sort.toCore_fromCore value).symm
    _ = sort.toCore number := congrArg sort.toCore same

private theorem ofInt_nat (width value : Nat) :
    BitVec.ofInt width (Int.ofNat value) = BitVec.ofNat width value := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt]
  change ((value : Int) % ((2 ^ width : Nat) : Int)).toNat = value % 2 ^ width
  trustIrCompilerProof { rw [← Int.ofNat_emod]; rfl } { rfl }

private theorem constant_value (width : Nat) (value : Int) (env : SMTEnv) :
    Int.ofNat (BitVec.ofInt width value).toNat = (.bvConst width value : TrustIrExpr).evalAt env width := by
  change Int.ofNat (value % Int.ofNat (2 ^ width)).toNat =
    ((value % (2 : Int) ^ width) + (2 : Int) ^ width) % (2 : Int) ^ width
  have power : Int.ofNat (2 ^ width) = (2 : Int) ^ width := Int.natCast_pow 2 width
  rw [power]
  simp only [Int.add_emod, Int.emod_emod, Int.emod_self, Int.add_zero]
  have positive : (0 : Int) < 2 ^ width := by
    rw [← power]
    trustIrCompilerProof { exact Int.ofNat_pos.mpr (Nat.two_pow_pos width) }
      { exact Int.natCast_pos.mpr (Nat.two_pow_pos width) }
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))

/-- The interpreter's guarded left shift retains the exact standard core result. -/
theorem SMTBinary.shiftLeft_eq {bits : Nat} (word amount : BitVec bits) :
    SMTBinary.shiftLeft word amount = word <<< amount := by
  change (if amount.toNat < bits then word <<< amount.toNat else 0) = word <<< amount.toNat
  by_cases small : amount.toNat < bits
  · rw [if_pos small]
  · rw [if_neg small]
    exact (bitvec_shiftLeft_large word amount.toNat (by omega)).symm

/-- The complete structural translation preserves actual evaluation through
independent native target operations, for every admitted constructor and environment. -/
theorem SMTTranslated.eval_correct {width : Nat} {expr : TrustIrExpr} {sort : SMTSort}
    {term : SMTTerm sort} (translated : SMTTranslated width expr term) (positive : 0 < width)
    (source target : SMTEnv) (agree : ∀ name, target (smtVariableSymbol name) = source name) :
    sort.fromCore (term.eval target) = expr.evalAt source width := by
  induction translated with
  | bvConst value _ => exact constant_value width value source
  | var name _ =>
    dsimp only [SMTTerm.eval]
    rw [agree name]
    exact constant_value width (source name) source
  | boolConst value => rfl
  | bvNeg input ih =>
    dsimp only [SMTTerm.eval, SMTUnary.eval]
    rw [native_of_numeric _ _ _ ih]
    have result := (SMTSorted.bvNeg input.sorted).bitvec_ofInt_exact source
    rw [bvNeg_bitvec] at result
    exact result
  | bvNot input ih =>
    dsimp only [SMTTerm.eval, SMTUnary.eval]
    rw [native_of_numeric _ _ _ ih]
    exact bvNot_bitvec_value width _ input.sorted source
  | boolNot input ih =>
    dsimp only [SMTTerm.eval, SMTUnary.eval]
    rw [native_of_numeric _ _ _ ih]
    exact (boolNot_core_value _ width source).symm
  | bvAdd left right leftIH rightIH =>
    dsimp only [SMTTerm.eval, SMTBinary.eval]
    rw [native_of_numeric _ _ _ leftIH, native_of_numeric _ _ _ rightIH]
    have result := (SMTSorted.bvAdd left.sorted right.sorted).bitvec_ofInt_exact source
    rw [bvAdd_bitvec width _ _ source] at result
    exact result
  | bvSub left right leftIH rightIH =>
    dsimp only [SMTTerm.eval, SMTBinary.eval]
    rw [native_of_numeric _ _ _ leftIH, native_of_numeric _ _ _ rightIH]
    have result := (SMTSorted.bvSub left.sorted right.sorted).bitvec_ofInt_exact source
    rw [bvSub_bitvec width _ _ source] at result
    exact result
  | bvMul left right leftIH rightIH =>
    dsimp only [SMTTerm.eval, SMTBinary.eval]
    rw [native_of_numeric _ _ _ leftIH, native_of_numeric _ _ _ rightIH]
    have result := (SMTSorted.bvMul left.sorted right.sorted).bitvec_ofInt_exact source
    rw [bvMul_bitvec width _ _ source] at result
    exact result
  | bvUDiv left right leftIH rightIH =>
    dsimp only [SMTTerm.eval, SMTBinary.eval]
    rw [native_of_numeric _ _ _ leftIH, native_of_numeric _ _ _ rightIH]
    exact bvUDiv_bitvec_value width _ _ left.sorted right.sorted source
  | bvSDiv left right leftIH rightIH =>
    dsimp only [SMTTerm.eval, SMTBinary.eval]
    rw [native_of_numeric _ _ _ leftIH, native_of_numeric _ _ _ rightIH]
    have result := (SMTSorted.bvSDiv left.sorted right.sorted).bitvec_ofInt_exact source
    rw [bvSDiv_bitvec width positive _ _ left.sorted right.sorted source] at result
    exact result
  | bvURem left right leftIH rightIH =>
    dsimp only [SMTTerm.eval, SMTBinary.eval]
    rw [native_of_numeric _ _ _ leftIH, native_of_numeric _ _ _ rightIH]
    exact bvURem_bitvec_value width _ _ left.sorted right.sorted source
  | bvSRem left right leftIH rightIH =>
    dsimp only [SMTTerm.eval, SMTBinary.eval]
    rw [native_of_numeric _ _ _ leftIH, native_of_numeric _ _ _ rightIH]
    have result := (SMTSorted.bvSRem left.sorted right.sorted).bitvec_ofInt_exact source
    rw [bvSRem_bitvec width positive _ _ left.sorted right.sorted source] at result
    exact result
  | bvAnd left right leftIH rightIH =>
    dsimp only [SMTTerm.eval, SMTBinary.eval]
    rw [native_of_numeric _ _ _ leftIH, native_of_numeric _ _ _ rightIH]
    exact bvAnd_bitvec_value width _ _ left.sorted right.sorted source
  | bvOr left right leftIH rightIH =>
    dsimp only [SMTTerm.eval, SMTBinary.eval]
    rw [native_of_numeric _ _ _ leftIH, native_of_numeric _ _ _ rightIH]
    exact bvOr_bitvec_value width _ _ left.sorted right.sorted source
  | bvXor left right leftIH rightIH =>
    dsimp only [SMTTerm.eval, SMTBinary.eval]
    rw [native_of_numeric _ _ _ leftIH, native_of_numeric _ _ _ rightIH]
    exact bvXor_bitvec_value width _ _ left.sorted right.sorted source
  | bvShl left right leftIH rightIH =>
    dsimp only [SMTTerm.eval, SMTBinary.eval]
    rw [SMTBinary.shiftLeft_eq]
    rw [native_of_numeric _ _ _ leftIH, native_of_numeric _ _ _ rightIH]
    have result := (SMTSorted.bvShl left.sorted right.sorted).bitvec_ofInt_exact source
    rw [bvShl_bitvec width _ _ left.sorted right.sorted source] at result
    exact result
  | bvLShr left right leftIH rightIH =>
    dsimp only [SMTTerm.eval, SMTBinary.eval]
    rw [native_of_numeric _ _ _ leftIH, native_of_numeric _ _ _ rightIH]
    have result := (SMTSorted.bvLShr left.sorted right.sorted).bitvec_ofInt_exact source
    rw [bvLShr_bitvec width _ _ left.sorted right.sorted source] at result
    exact result
  | bvAShr left right leftIH rightIH =>
    dsimp only [SMTTerm.eval, SMTBinary.eval]
    rw [native_of_numeric _ _ _ leftIH, native_of_numeric _ _ _ rightIH]
    have result := (SMTSorted.bvAShr left.sorted right.sorted).bitvec_ofInt_exact source
    rw [bvAShr_bitvec width positive _ _ left.sorted right.sorted source] at result
    exact result
  | boolAnd left right leftIH rightIH =>
    dsimp only [SMTTerm.eval, SMTBinary.eval]
    rw [native_of_numeric _ _ _ leftIH, native_of_numeric _ _ _ rightIH]
    exact (boolAnd_core_value _ _ width source).symm
  | boolOr left right leftIH rightIH =>
    dsimp only [SMTTerm.eval, SMTBinary.eval]
    rw [native_of_numeric _ _ _ leftIH, native_of_numeric _ _ _ rightIH]
    exact (boolOr_core_value _ _ width source).symm
  | boolImpl left right leftIH rightIH =>
    dsimp only [SMTTerm.eval, SMTBinary.eval]
    rw [native_of_numeric _ _ _ leftIH, native_of_numeric _ _ _ rightIH]
    exact (boolImpl_core_value _ _ width source).symm
  | bvUlt left right leftIH rightIH =>
    dsimp only [SMTTerm.eval, SMTBinary.eval]
    rw [native_of_numeric _ _ _ leftIH, native_of_numeric _ _ _ rightIH]
    exact (icmp_encoding_bitvec .Ult width positive _ _ left.sorted right.sorted source).symm
  | bvUle left right leftIH rightIH =>
    dsimp only [SMTTerm.eval, SMTBinary.eval]
    rw [native_of_numeric _ _ _ leftIH, native_of_numeric _ _ _ rightIH]
    exact (icmp_encoding_bitvec .Ule width positive _ _ left.sorted right.sorted source).symm
  | bvSlt left right leftIH rightIH =>
    dsimp only [SMTTerm.eval, SMTBinary.eval]
    rw [native_of_numeric _ _ _ leftIH, native_of_numeric _ _ _ rightIH]
    exact (icmp_encoding_bitvec .Slt width positive _ _ left.sorted right.sorted source).symm
  | bvSle left right leftIH rightIH =>
    dsimp only [SMTTerm.eval, SMTBinary.eval]
    rw [native_of_numeric _ _ _ leftIH, native_of_numeric _ _ _ rightIH]
    exact (icmp_encoding_bitvec .Sle width positive _ _ left.sorted right.sorted source).symm
  | eq left right leftIH rightIH =>
    dsimp only [SMTTerm.eval, SMTBinary.eval]
    rw [native_of_numeric _ _ _ leftIH, native_of_numeric _ _ _ rightIH]
    exact (eq_core_value width _ _ _ left.sorted right.sorted source).symm
  | bvRotL left right leftIH rightIH =>
    simp only [SMTTerm.rotate, SMTTerm.eval, SMTBinary.eval, SMTBinary.shiftLeft_eq, if_true, Bool.false_eq_true, if_false]
    rw [native_of_numeric _ _ _ leftIH, native_of_numeric _ _ _ rightIH, ofInt_nat]
    rw [← bitvec_rotateLeft_expansion positive]
    exact bvRotL_bitvec_value width positive _ _ left.sorted right.sorted source
  | bvRotR left right leftIH rightIH =>
    simp only [SMTTerm.rotate, SMTTerm.eval, SMTBinary.eval, SMTBinary.shiftLeft_eq, if_true, Bool.false_eq_true, if_false]
    rw [native_of_numeric _ _ _ leftIH, native_of_numeric _ _ _ rightIH, ofInt_nat]
    rw [← bitvec_rotateRight_expansion positive]
    exact bvRotR_bitvec_value width positive _ _ left.sorted right.sorted source
  | ite condition yes no condIH yesIH noIH =>
    dsimp only [SMTTerm.eval]
    rw [native_of_numeric _ _ _ condIH, native_of_numeric _ _ _ yesIH, native_of_numeric _ _ _ noIH]
    exact (ite_core_value width _ _ _ _ yes.sorted no.sorted source).symm

/-- Actual translation supplies positive widths and encoded identifier safety. -/
theorem SMTTranslated.wellFormed {width : Nat} {expr : TrustIrExpr} {sort : SMTSort}
    {term : SMTTerm sort} (translated : SMTTranslated width expr term) (positive : 0 < width) :
    term.WellFormed := by
  induction translated with
  | var name leafPositive =>
    refine ⟨leafPositive, ?_⟩
    apply Or.inl
    rw [SMTTerm.Identifier_function_eq_standard]
    exact smtVariableSymbol_alphabet name
  | _ => simp_all [SMTTerm.WellFormed, SMTTerm.rotate]

/-- Every actual returned target has a safe typed printing derivation. -/
theorem toSMTRequest_target_wellFormed (expr : TrustIrExpr) (width : Nat) (request : SMTRequest)
    (built : expr.toSMTRequest width = .ok request) : request.target.WellFormed :=
  (toSMTRequest_translated expr width request built).wellFormed
    (toSMTRequest_metadata expr width request built).2.1

theorem toSMTRequest_assertion_wellFormed (expr : TrustIrExpr) (width : Nat) (request : SMTRequest)
    (built : expr.toSMTRequest width = .ok request) : request.assertion.WellFormed := by
  rcases request with ⟨requestWidth, names, script, sort, term⟩
  have wellFormed := toSMTRequest_target_wellFormed expr width _ built
  have typed := toSMTRequest_sorted expr width _ built
  have metadata := toSMTRequest_metadata expr width _ built
  cases sort with
  | bool => exact wellFormed
  | bv bits =>
    change term.WellFormed ∧ 0 < bits
    refine ⟨wellFormed, ?_⟩
    cases typed.sort_cases with
    | inl impossible => cases impossible
    | inr same =>
      have bitsWidth := SMTSort.bv.inj same
      rw [bitsWidth]
      exact metadata.2.1

/-- Actual scripts have a typed fixed-token printing derivation, positive word
widths and safe declarations, all tied to the returned assertion term. -/
theorem toSMTRequest_script_derivation (expr : TrustIrExpr) (width : Nat) (request : SMTRequest)
    (built : expr.toSMTRequest width = .ok request) :
    ∃ printed : String, request.assertion.Prints printed ∧ request.assertion.WellFormed ∧
      0 < request.width ∧ (∀ name ∈ request.bindings, SMTTerm.Identifier (smtVariableSymbol name)) ∧
      request.script = "(set-logic QF_BV)\n" ++ String.join (request.bindings.map (fun name =>
        "(declare-fun " ++ smtVariableSymbol name ++ " () (_ BitVec " ++ toString request.width ++ "))\n")) ++
        "(assert " ++ printed ++ ")\n(check-sat)\n" := by
  have metadata := toSMTRequest_metadata expr width request built
  refine ⟨request.assertion.toText, request.assertion.toText_prints,
    toSMTRequest_assertion_wellFormed expr width request built, ?_, ?_,
    toSMTRequest_target_script expr width request built⟩
  · rw [metadata.1]
    exact metadata.2.1
  · intro name _member
    rw [SMTTerm.Identifier_function_eq_standard]
    exact smtVariableSymbol_alphabet name

/-- Every actual request's returned target computes its complete source value. -/
theorem toSMTRequest_target_value (expr : TrustIrExpr) (width : Nat) (request : SMTRequest)
    (built : expr.toSMTRequest width = .ok request) (source target : SMTEnv)
    (agree : ∀ name, target (smtVariableSymbol name) = source name) :
    request.sort.fromCore (request.target.eval target) = expr.evalAt source request.width := by
  have metadata := toSMTRequest_metadata expr width request built
  rw [metadata.1]
  exact (toSMTRequest_translated expr width request built).eval_correct metadata.2.1 source target agree

/-- The target assertion is true exactly when its native result is nonzero,
for both Bool roots and word roots wrapped in the emitted distinct-from-zero node. -/
theorem SMTTerm.asFormula_truth {sort : SMTSort} (term : SMTTerm sort) (env : SMTEnv) :
    term.asFormula.eval env = true ↔ sort.fromCore (term.eval env) ≠ 0 := by
  cases sort with
  | bool =>
    change term.eval env = true ↔ (if term.eval env then (1 : Int) else 0) ≠ 0
    cases term.eval env <;> decide
  | bv bits =>
    change (!(decide (term.eval env = BitVec.ofInt bits 0))) = true ↔
      ((term.eval env).toNat : Int) ≠ 0
    have zeroNat : (BitVec.ofInt bits 0).toNat = 0 := by
      rw [BitVec.toNat_ofInt]
      rfl
    have rejected : (!(decide (term.eval env = BitVec.ofInt bits 0))) = true ↔
        term.eval env ≠ BitVec.ofInt bits 0 := by
      by_cases same : term.eval env = BitVec.ofInt bits 0 <;> simp [same]
    rw [rejected, Int.ofNat_ne_zero]
    constructor
    · intro nonzero zero
      apply nonzero
      apply BitVec.eq_of_toNat_eq
      exact zero.trans zeroNat.symm
    · intro nonzero zero
      apply nonzero
      exact (congrArg BitVec.toNat zero).trans zeroNat

/-- Actual emitted assertion truth preserves the source formula's nonzero test. -/
theorem toSMTRequest_target_truth (expr : TrustIrExpr) (width : Nat) (request : SMTRequest)
    (built : expr.toSMTRequest width = .ok request) (source target : SMTEnv)
    (agree : ∀ name, target (smtVariableSymbol name) = source name) :
    request.assertion.eval target = true ↔ expr.evalAt source request.width ≠ 0 := by
  change request.target.asFormula.eval target = true ↔ _
  rw [SMTTerm.asFormula_truth, toSMTRequest_target_value expr width request built source target agree]

/-- Full source unsatisfiability and native target assertion refutation coincide.
This theorem uses no AY oracle axiom or trusted blaster topology. -/
theorem toSMTRequest_unsat_iff_target (expr : TrustIrExpr) (width : Nat) (request : SMTRequest)
    (built : expr.toSMTRequest width = .ok request) :
    formula_unsat request.width expr ↔ ∀ target : SMTEnv, request.assertion.eval target = false := by
  constructor
  · intro sourceZero target
    let source : SMTEnv := fun name => target (smtVariableSymbol name)
    have agree : ∀ name, target (smtVariableSymbol name) = source name := fun _ => rfl
    apply Bool.eq_false_iff.mpr
    intro accepted
    have nonzero := (toSMTRequest_target_truth expr width request built source target agree).mp accepted
    exact nonzero (sourceZero source)
  · intro targets source
    obtain ⟨target, agree⟩ := smtVariableSymbol_environment source
    by_cases zero : expr.evalAt source request.width = 0
    · exact zero
    · have accepted := (toSMTRequest_target_truth expr width request built source target agree).mpr zero
      rw [targets target] at accepted
      cases accepted

/-- Source countermodels and native target assertion models transfer both ways,
with actual encoded variable assignments rather than assumed model answers. -/
theorem toSMTRequest_sat_iff_target (expr : TrustIrExpr) (width : Nat) (request : SMTRequest)
    (built : expr.toSMTRequest width = .ok request) :
    (∃ source : SMTEnv, expr.evalAt source request.width ≠ 0) ↔
      ∃ target : SMTEnv, request.assertion.eval target = true := by
  constructor
  · rintro ⟨source, nonzero⟩
    obtain ⟨target, agree⟩ := smtVariableSymbol_environment source
    exact ⟨target, (toSMTRequest_target_truth expr width request built source target agree).mpr nonzero⟩
  · rintro ⟨target, accepted⟩
    let source : SMTEnv := fun name => target (smtVariableSymbol name)
    have agree : ∀ name, target (smtVariableSymbol name) = source name := fun _ => rfl
    exact ⟨source, (toSMTRequest_target_truth expr width request built source target agree).mp accepted⟩

end TrustIr.TrustIrExpr

#trustIrAxiomsPinned TrustIr.TrustIrExpr.SMTBinary.shiftLeft_eq == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.TrustIrExpr.SMTTranslated.eval_correct == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.TrustIrExpr.SMTTranslated.wellFormed == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.TrustIrExpr.toSMTRequest_target_wellFormed == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.TrustIrExpr.toSMTRequest_assertion_wellFormed == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.TrustIrExpr.toSMTRequest_script_derivation == [Classical.choice, propext, Quot.sound]

#trustIrAxiomsExact TrustIr.TrustIrExpr.toSMTRequest_target_value == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.TrustIrExpr.SMTTerm.asFormula_truth == [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.TrustIrExpr.toSMTRequest_target_truth == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.TrustIrExpr.toSMTRequest_unsat_iff_target == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.TrustIrExpr.toSMTRequest_sat_iff_target == [propext, Quot.sound, Classical.choice]
