-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYBitVecRotations

namespace TrustIr.TrustIrExpr

/-- Conversion loses no value on the actual sort carrier. -/
theorem SMTSort.fromCore_toCore (sort : SMTSort) (value : Int)
    (valid : sort.ValueValid value) : sort.fromCore (sort.toCore value) = value := by
  cases sort with
  | bool =>
    cases valid with
    | inl zero => simp [SMTSort.toCore, SMTSort.fromCore, zero]
    | inr one => simp [SMTSort.toCore, SMTSort.fromCore, one]
  | bv bits => exact bitvec_ofInt_toNat bits value valid.1 valid.2

/-- Every native core value supplies a valid numeric sort carrier. -/
theorem SMTSort.fromCore_valid (sort : SMTSort) (value : sort.CoreValue) :
    sort.ValueValid (sort.fromCore value) := by
  cases sort with
  | bool => cases value <;> simp [SMTSort.ValueValid, SMTSort.fromCore]
  | bv bits =>
    constructor
    · exact Int.ofNat_nonneg _
    · have cast := Int.ofNat_lt.mpr value.isLt
      simpa only [SMTSort.fromCore, Int.natCast_pow] using cast

/-- Both directions of the core/numeric representation preserve the whole value. -/
theorem SMTSort.toCore_fromCore (sort : SMTSort) (value : sort.CoreValue) :
    sort.toCore (sort.fromCore value) = value := by
  cases sort with
  | bool => cases value <;> rfl
  | bv bits =>
    change BitVec.ofInt bits (Int.ofNat value.toNat) = value
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofInt]
    change ((value.toNat : Int) % ((2 ^ bits : Nat) : Int)).toNat = value.toNat
    trustIrCompilerProof
      { rw [← Int.ofNat_emod, Nat.mod_eq_of_lt value.isLt] }
      { rw [← Int.natCast_emod, Nat.mod_eq_of_lt value.isLt] }
    rfl

/-- Core conversion is injective on a sort's actual carrier. -/
theorem SMTSort.toCore_eq_iff (sort : SMTSort) (left right : Int)
    (leftValid : sort.ValueValid left) (rightValid : sort.ValueValid right) :
    sort.toCore left = sort.toCore right ↔ left = right := by
  constructor
  · intro same
    have observed := congrArg sort.fromCore same
    rw [sort.fromCore_toCore left leftValid, sort.fromCore_toCore right rightValid] at observed
    exact observed
  · intro same
    rw [same]

theorem SMTSort.coreEq_true_iff (sort : SMTSort) (left right : sort.CoreValue) :
    sort.coreEq left right = true ↔ left = right := by
  cases sort <;> simp [SMTSort.coreEq, beq_iff_eq]

/-- Actual successful requests retain their complete value in their returned
core sort, uniformly for Bool and bitvector roots. -/
theorem toSMTRequest_core_exact (expr : TrustIrExpr) (width : Nat) (request : SMTRequest)
    (built : expr.toSMTRequest width = .ok request) (env : SMTEnv) :
    request.sort.fromCore (request.sort.toCore (expr.evalAt env request.width)) =
      expr.evalAt env request.width :=
  request.sort.fromCore_toCore _ (toSMTRequest_value_valid expr width request built env)

/-- Boolean literals directly use core Bool. -/
theorem boolConst_core_value (value : Bool) (width : Nat) (env : SMTEnv) :
    (.boolConst value : TrustIrExpr).evalAt env width = SMTSort.bool.fromCore value := rfl

/-- Boolean negation agrees with native Bool negation. -/
theorem boolNot_core_value (arg : TrustIrExpr) (width : Nat) (env : SMTEnv) :
    (.boolNot arg : TrustIrExpr).evalAt env width =
      SMTSort.bool.fromCore (!(SMTSort.bool.toCore (arg.evalAt env width))) := by
  simp [TrustIrExpr.evalAt, SMTSort.toCore, SMTSort.fromCore]

/-- Boolean conjunction agrees with native Bool conjunction. -/
theorem boolAnd_core_value (left right : TrustIrExpr) (width : Nat) (env : SMTEnv) :
    (.boolAnd left right : TrustIrExpr).evalAt env width =
      SMTSort.bool.fromCore ((SMTSort.bool.toCore (left.evalAt env width)) &&
        (SMTSort.bool.toCore (right.evalAt env width))) := rfl

/-- Boolean disjunction agrees with native Bool disjunction. -/
theorem boolOr_core_value (left right : TrustIrExpr) (width : Nat) (env : SMTEnv) :
    (.boolOr left right : TrustIrExpr).evalAt env width =
      SMTSort.bool.fromCore ((SMTSort.bool.toCore (left.evalAt env width)) ||
        (SMTSort.bool.toCore (right.evalAt env width))) := rfl

/-- Boolean implication agrees with native Bool implication. -/
theorem boolImpl_core_value (left right : TrustIrExpr) (width : Nat) (env : SMTEnv) :
    (.boolImpl left right : TrustIrExpr).evalAt env width =
      SMTSort.bool.fromCore ((!(SMTSort.bool.toCore (left.evalAt env width))) ||
        (SMTSort.bool.toCore (right.evalAt env width))) := by
  simp [TrustIrExpr.evalAt, SMTSort.toCore, SMTSort.fromCore]

/-- Same-sort equality retains the complete Boolean result for both carriers;
operand validity follows from typing, rather than assuming an equality answer. -/
theorem eq_core_value (width : Nat) (sort : SMTSort) (left right : TrustIrExpr)
    (leftTyped : SMTSorted width left sort) (rightTyped : SMTSorted width right sort) (env : SMTEnv) :
    (.eq left right : TrustIrExpr).evalAt env width =
      SMTSort.bool.fromCore (sort.coreEq (sort.toCore (left.evalAt env width))
        (sort.toCore (right.evalAt env width))) := by
  have equality : sort.coreEq (sort.toCore (left.evalAt env width)) (sort.toCore (right.evalAt env width)) =
      (left.evalAt env width == right.evalAt env width) := by
    apply Bool.eq_iff_iff.mpr
    simp only [SMTSort.coreEq_true_iff, beq_iff_eq]
    exact sort.toCore_eq_iff _ _ (SMTSorted.eval_value_valid width left sort leftTyped env) (SMTSorted.eval_value_valid width right sort rightTyped env)
  rw [equality]
  rfl

/-- Conditional selection preserves the exact core branch value at either sort.
No branch answer or condition truth value is a premise. -/
theorem ite_core_value (width : Nat) (sort : SMTSort) (cond yes no : TrustIrExpr)
    (yesTyped : SMTSorted width yes sort) (noTyped : SMTSorted width no sort) (env : SMTEnv) :
    (.ite cond yes no : TrustIrExpr).evalAt env width =
      sort.fromCore (if SMTSort.bool.toCore (cond.evalAt env width) then
        sort.toCore (yes.evalAt env width) else sort.toCore (no.evalAt env width)) := by
  change (if cond.evalAt env width != 0 then yes.evalAt env width else no.evalAt env width) =
    sort.fromCore (if cond.evalAt env width != 0 then sort.toCore (yes.evalAt env width)
      else sort.toCore (no.evalAt env width))
  by_cases choose : (cond.evalAt env width != 0) = true
  · rw [if_pos choose, if_pos choose]
    exact (sort.fromCore_toCore _ (SMTSorted.eval_value_valid width yes sort yesTyped env)).symm
  · rw [if_neg choose, if_neg choose]
    exact (sort.fromCore_toCore _ (SMTSorted.eval_value_valid width no sort noTyped env)).symm

/-- Actual successful equality requests supply their shared operand sort and
preserve core equality at the emitted request width. -/
theorem toSMTRequest_eq_core_value (width : Nat) (left right : TrustIrExpr)
    (request : SMTRequest) (built : (.eq left right : TrustIrExpr).toSMTRequest width = .ok request)
    (env : SMTEnv) :
    ∃ sort, SMTSorted request.width left sort ∧ SMTSorted request.width right sort ∧
      (.eq left right : TrustIrExpr).evalAt env request.width =
        SMTSort.bool.fromCore (sort.coreEq (sort.toCore (left.evalAt env request.width))
          (sort.toCore (right.evalAt env request.width))) := by
  have metadata := toSMTRequest_metadata (.eq left right) width request built
  rw [metadata.1]
  have typed := toSMTRequest_sorted (.eq left right) width request built
  generalize request.sort = sort at typed
  cases typed with
  | eq leftTyped rightTyped => exact ⟨_, leftTyped, rightTyped, eq_core_value width _ left right leftTyped rightTyped env⟩

/-- Actual successful conditionals retain the exact selected core value at the
returned sort and width, with the condition's Bool typing derived by admission. -/
theorem toSMTRequest_ite_core_value (width : Nat) (cond yes no : TrustIrExpr)
    (request : SMTRequest) (built : (.ite cond yes no : TrustIrExpr).toSMTRequest width = .ok request)
    (env : SMTEnv) :
    (.ite cond yes no : TrustIrExpr).evalAt env request.width =
      request.sort.fromCore (if SMTSort.bool.toCore (cond.evalAt env request.width) then
        request.sort.toCore (yes.evalAt env request.width) else request.sort.toCore (no.evalAt env request.width)) := by
  have metadata := toSMTRequest_metadata (.ite cond yes no) width request built
  rw [metadata.1]
  have typed := toSMTRequest_sorted (.ite cond yes no) width request built
  generalize request.sort = sort at typed ⊢
  cases typed with
  | ite _condition yesTyped noTyped => exact ite_core_value width _ cond yes no yesTyped noTyped env

end TrustIr.TrustIrExpr

/-- info: 'TrustIr.TrustIrExpr.SMTSort.fromCore_toCore' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.SMTSort.fromCore_toCore

/-- info: 'TrustIr.TrustIrExpr.SMTSort.fromCore_valid' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.SMTSort.fromCore_valid

/-- info: 'TrustIr.TrustIrExpr.SMTSort.toCore_fromCore' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.SMTSort.toCore_fromCore

/-- info: 'TrustIr.TrustIrExpr.SMTSort.toCore_eq_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.SMTSort.toCore_eq_iff

/-- info: 'TrustIr.TrustIrExpr.SMTSort.coreEq_true_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.SMTSort.coreEq_true_iff

#trustIrAxiomsPinned TrustIr.TrustIrExpr.toSMTRequest_core_exact == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

/-- info: 'TrustIr.TrustIrExpr.boolConst_core_value' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.boolConst_core_value

/-- info: 'TrustIr.TrustIrExpr.boolNot_core_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.boolNot_core_value

/-- info: 'TrustIr.TrustIrExpr.boolAnd_core_value' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.boolAnd_core_value

/-- info: 'TrustIr.TrustIrExpr.boolOr_core_value' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.boolOr_core_value

/-- info: 'TrustIr.TrustIrExpr.boolImpl_core_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.boolImpl_core_value

#trustIrAxiomsPinned TrustIr.TrustIrExpr.eq_core_value == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.ite_core_value == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.toSMTRequest_eq_core_value == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.toSMTRequest_ite_core_value == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
