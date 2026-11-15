-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYSMTLib
import Init.Data.Nat.Mod
import Init.Data.BitVec.Basic

namespace TrustIr.TrustIrExpr

/-- Semantic carriers of the admitted SMT sorts. -/
def SMTSort.ValueValid : SMTSort → Int → Prop
  | .bool, value => value = 0 ∨ value = 1
  | .bv width, value => 0 ≤ value ∧ value < (2 : Int) ^ width

private theorem int_pow_positive (width : Nat) : (0 : Int) < 2 ^ width := by
  have power : (2 : Int) ^ width = ((2 ^ width : Nat) : Int) := (Int.natCast_pow 2 width).symm
  rw [power]
  trustIrCompilerProof
    { exact Int.ofNat_pos.mpr (Nat.two_pow_pos width) }
    { exact Int.natCast_pos.mpr (Nat.two_pow_pos width) }

private theorem zero_range (width : Nat) : 0 ≤ (0 : Int) ∧ 0 < (2 : Int) ^ width :=
  ⟨Int.le_refl _, int_pow_positive width⟩

private theorem modular_range (width : Nat) (value : Int) :
    0 ≤ (TrustIrExpr.bvConst width value).evalAt SMTEnv.default width ∧
    (TrustIrExpr.bvConst width value).evalAt SMTEnv.default width < (2 : Int) ^ width :=
  variable_encoding_range (fun _ => value) width width ""

private theorem toNat_bound (width : Nat) (value : Int)
    (nonnegative : 0 ≤ value) (bound : value < (2 : Int) ^ width) :
    value.toNat < 2 ^ width := by
  have cast := Int.toNat_of_nonneg nonnegative
  have power : (2 : Int) ^ width = ((2 ^ width : Nat) : Int) := (Int.natCast_pow 2 width).symm
  rw [← cast, power] at bound
  exact Int.ofNat_lt.mp bound

private theorem ofNat_range (width value : Nat) (bound : value < 2 ^ width) :
    0 ≤ (value : Int) ∧ (value : Int) < (2 : Int) ^ width := by
  constructor
  · omega
  · have cast := Int.ofNat_lt.mpr bound
    simpa only [Int.natCast_pow] using cast

private theorem land_range (width : Nat) (left right : Int)
    (leftNonnegative : 0 ≤ left) (_leftBound : left < (2 : Int) ^ width)
    (rightNonnegative : 0 ≤ right) (rightBound : right < (2 : Int) ^ width) :
    0 ≤ Int.land left right ∧ Int.land left right < (2 : Int) ^ width := by
  cases left with
  | negSucc n => simp only [Int.negSucc_not_nonneg] at leftNonnegative
  | ofNat a =>
    cases right with
    | negSucc n => simp only [Int.negSucc_not_nonneg] at rightNonnegative
    | ofNat b =>
      exact ofNat_range width (Nat.land a b)
        (Nat.and_lt_two_pow a (toNat_bound width (.ofNat b) rightNonnegative rightBound))

private theorem lor_range (width : Nat) (left right : Int)
    (leftNonnegative : 0 ≤ left) (leftBound : left < (2 : Int) ^ width)
    (rightNonnegative : 0 ≤ right) (rightBound : right < (2 : Int) ^ width) :
    0 ≤ Int.lor left right ∧ Int.lor left right < (2 : Int) ^ width := by
  cases left with
  | negSucc n => simp only [Int.negSucc_not_nonneg] at leftNonnegative
  | ofNat a =>
    cases right with
    | negSucc n => simp only [Int.negSucc_not_nonneg] at rightNonnegative
    | ofNat b =>
      exact ofNat_range width (Nat.lor a b)
        (Nat.or_lt_two_pow (toNat_bound width (.ofNat a) leftNonnegative leftBound)
          (toNat_bound width (.ofNat b) rightNonnegative rightBound))

private theorem xor_range (width : Nat) (left right : Int)
    (leftNonnegative : 0 ≤ left) (leftBound : left < (2 : Int) ^ width)
    (rightNonnegative : 0 ≤ right) (rightBound : right < (2 : Int) ^ width) :
    0 ≤ Int.xor left right ∧ Int.xor left right < (2 : Int) ^ width := by
  cases left with
  | negSucc n => simp only [Int.negSucc_not_nonneg] at leftNonnegative
  | ofNat a =>
    cases right with
    | negSucc n => simp only [Int.negSucc_not_nonneg] at rightNonnegative
    | ofNat b =>
      exact ofNat_range width (Nat.xor a b)
        (Nat.xor_lt_two_pow (toNat_bound width (.ofNat a) leftNonnegative leftBound)
          (toNat_bound width (.ofNat b) rightNonnegative rightBound))

private theorem rotate_parts_bound (high low value : Nat) (lowPositive : 0 < low)
    (bound : value < low * high) :
    (value * high) % (low * high) + value / low < low * high := by
  rw [Nat.mul_mod_mul_right]
  have quotient : value / low < high :=
    (Nat.div_lt_iff_lt_mul lowPositive).mpr (by simpa [Nat.mul_comm] using bound)
  have remainder : value % low + 1 ≤ low := by have := Nat.mod_lt value lowPositive; omega
  have gap : value % low * high + high ≤ low * high := by
    simpa [Nat.add_mul] using Nat.mul_le_mul_right high remainder
  omega

/-- The existing left rotation retains only bits within the positive width. -/
theorem rotlWidth_bound (width value amount : Nat) (positive : 0 < width)
    (bound : value < 2 ^ width) : rotlWidth value width amount < 2 ^ width := by
  let shift := amount % width
  have small : shift < width := Nat.mod_lt _ positive
  have factor : (2 : Nat) ^ width = 2 ^ (width - shift) * 2 ^ shift := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have result := rotate_parts_bound (2 ^ shift) (2 ^ (width - shift)) value
    (Nat.two_pow_pos _) (by simpa only [factor] using bound)
  simpa only [rotlWidth, factor] using result

/-- The existing right rotation retains only bits within the positive width. -/
theorem rotrWidth_bound (width value amount : Nat) (positive : 0 < width)
    (bound : value < 2 ^ width) : rotrWidth value width amount < 2 ^ width := by
  let shift := amount % width
  have small : shift < width := Nat.mod_lt _ positive
  have factor : (2 : Nat) ^ width = 2 ^ shift * 2 ^ (width - shift) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have result := rotate_parts_bound (2 ^ (width - shift)) (2 ^ shift) value
    (Nat.two_pow_pos _) (by simpa only [factor] using bound)
  simpa only [rotrWidth, factor, Nat.add_comm] using result

private theorem sorted_bv_positive (width : Nat) (expr : TrustIrExpr) (sort : SMTSort)
    (typed : SMTSorted width expr sort) : sort = .bv width → 0 < width := by
  induction typed <;> intro kind <;> cases kind <;> simp_all

/-- Every well-sorted expression evaluates in its exact semantic carrier.
    Arbitrary integer environments are normalized by the actual variable
    evaluator; no operand-range or result premise is assumed. -/
theorem SMTSorted.eval_value_valid (width : Nat) (expr : TrustIrExpr) (sort : SMTSort)
    (typed : SMTSorted width expr sort) (env : SMTEnv) :
    sort.ValueValid (expr.evalAt env width) := by
  induction typed with
  | bvConst value _positive => exact modular_range width value
  | var name _positive => exact variable_encoding_range env width width name
  | boolConst value => cases value <;> first | exact Or.inl rfl | exact Or.inr rfl
  | bvAdd _lhs _rhs _leftIH _rightIH => exact modular_range width _
  | bvSub _lhs _rhs _leftIH _rightIH => exact modular_range width _
  | bvMul _lhs _rhs _leftIH _rightIH => exact modular_range width _
  | bvUDiv _lhs _rhs _leftIH _rightIH =>
    simp only [SMTSort.ValueValid, TrustIrExpr.evalAt]
    split <;> exact modular_range width _
  | bvSDiv _lhs _rhs _leftIH _rightIH =>
    simp only [SMTSort.ValueValid, TrustIrExpr.evalAt]
    split <;> exact modular_range width _
  | bvURem _lhs _rhs _leftIH _rightIH =>
    simp only [SMTSort.ValueValid, TrustIrExpr.evalAt]
    split <;> exact modular_range width _
  | bvSRem _lhs _rhs _leftIH _rightIH =>
    simp only [SMTSort.ValueValid, TrustIrExpr.evalAt]
    split <;> exact modular_range width _
  | bvAnd _lhs _rhs leftIH rightIH =>
    exact land_range width _ _ leftIH.1 leftIH.2 rightIH.1 rightIH.2
  | bvOr _lhs _rhs leftIH rightIH =>
    exact lor_range width _ _ leftIH.1 leftIH.2 rightIH.1 rightIH.2
  | bvXor _lhs _rhs leftIH rightIH =>
    exact xor_range width _ _ leftIH.1 leftIH.2 rightIH.1 rightIH.2
  | bvShl _lhs _rhs _leftIH _rightIH =>
    simp only [SMTSort.ValueValid, TrustIrExpr.evalAt]
    split
    · exact modular_range width _
    · exact zero_range width
  | bvLShr _lhs _rhs _leftIH _rightIH =>
    simp only [SMTSort.ValueValid, TrustIrExpr.evalAt]
    split
    · exact modular_range width _
    · exact zero_range width
  | bvAShr _lhs _rhs _leftIH _rightIH =>
    simp only [SMTSort.ValueValid, TrustIrExpr.evalAt]
    split
    · exact modular_range width _
    · split
      · exact modular_range width _
      · exact zero_range width
  | bvRotL lhs _rhs leftIH _rightIH =>
    apply ofNat_range width
    apply rotlWidth_bound width
    · exact sorted_bv_positive width _ _ lhs rfl
    · exact toNat_bound width _ leftIH.1 leftIH.2
  | bvRotR lhs _rhs leftIH _rightIH =>
    apply ofNat_range width
    apply rotrWidth_bound width
    · exact sorted_bv_positive width _ _ lhs rfl
    · exact toNat_bound width _ leftIH.1 leftIH.2
  | boolAnd _lhs _rhs _leftIH _rightIH =>
    simp only [SMTSort.ValueValid, TrustIrExpr.evalAt]
    split <;> first | exact Or.inl rfl | exact Or.inr rfl
  | boolOr _lhs _rhs _leftIH _rightIH =>
    simp only [SMTSort.ValueValid, TrustIrExpr.evalAt]
    split <;> first | exact Or.inl rfl | exact Or.inr rfl
  | boolImpl _lhs _rhs _leftIH _rightIH =>
    simp only [SMTSort.ValueValid, TrustIrExpr.evalAt]
    split <;> first | exact Or.inl rfl | exact Or.inr rfl
  | bvUlt _lhs _rhs _leftIH _rightIH =>
    simp only [SMTSort.ValueValid, TrustIrExpr.evalAt]
    split <;> first | exact Or.inl rfl | exact Or.inr rfl
  | bvUle _lhs _rhs _leftIH _rightIH =>
    simp only [SMTSort.ValueValid, TrustIrExpr.evalAt]
    split <;> first | exact Or.inl rfl | exact Or.inr rfl
  | bvSlt _lhs _rhs _leftIH _rightIH =>
    simp only [SMTSort.ValueValid, TrustIrExpr.evalAt]
    split <;> first | exact Or.inl rfl | exact Or.inr rfl
  | bvSle _lhs _rhs _leftIH _rightIH =>
    simp only [SMTSort.ValueValid, TrustIrExpr.evalAt]
    split <;> first | exact Or.inl rfl | exact Or.inr rfl
  | eq _lhs _rhs _leftIH _rightIH =>
    simp only [SMTSort.ValueValid, TrustIrExpr.evalAt]
    split <;> first | exact Or.inl rfl | exact Or.inr rfl
  | bvNeg _input _ih => exact modular_range width _
  | bvNot _input ih =>
    have positive := int_pow_positive width
    exact xor_range width _ ((2 : Int) ^ width - 1) ih.1 ih.2 (by omega) (by omega)
  | boolNot _input _ih =>
    simp only [SMTSort.ValueValid, TrustIrExpr.evalAt]
    split <;> first | exact Or.inl rfl | exact Or.inr rfl
  | ite _condition _thenBranch _elseBranch _condIH thenIH elseIH =>
    simp only [TrustIrExpr.evalAt]
    split
    · exact thenIH
    · exact elseIH

/-- Every actual successful request evaluates in the carrier of its returned
    root sort at the request's own operation width. -/
theorem toSMTRequest_value_valid (expr : TrustIrExpr) (width : Nat) (request : SMTRequest)
    (built : expr.toSMTRequest width = .ok request) (env : SMTEnv) :
    request.sort.ValueValid (expr.evalAt env request.width) := by
  rw [(toSMTRequest_metadata expr width request built).1]
  exact SMTSorted.eval_value_valid width expr request.sort
    (toSMTRequest_sorted expr width request built) env

/-- Exact unsigned range of an actual bitvector-root request. -/
theorem toSMTRequest_bv_range (expr : TrustIrExpr) (width : Nat) (request : SMTRequest)
    (built : expr.toSMTRequest width = .ok request) (bits : Nat)
    (bitvector : request.sort = .bv bits) (env : SMTEnv) :
    0 ≤ expr.evalAt env request.width ∧ expr.evalAt env request.width < (2 : Int) ^ bits := by
  have valid := toSMTRequest_value_valid expr width request built env
  simpa only [bitvector, SMTSort.ValueValid] using valid

/-- Embedding the actual result in its declared BitVec carrier loses no value.
    This derives the bound from successful serialization, rather than assuming
    that modular conversion preserves an arbitrary integer result. -/
theorem toSMTRequest_bitvec_exact (expr : TrustIrExpr) (width : Nat) (request : SMTRequest)
    (built : expr.toSMTRequest width = .ok request) (bits : Nat)
    (bitvector : request.sort = .bv bits) (env : SMTEnv) :
    Int.ofNat (BitVec.ofNat bits (expr.evalAt env request.width).toNat).toNat =
      expr.evalAt env request.width := by
  have range := toSMTRequest_bv_range expr width request built bits bitvector env
  have bounded := toNat_bound bits _ range.1 range.2
  change Int.ofNat ((expr.evalAt env request.width).toNat % 2 ^ bits) = _
  rw [Nat.mod_eq_of_lt bounded]
  exact Int.toNat_of_nonneg range.1

-- All admitted value carriers and the exact BitVec embedding use only core axioms.

#trustIrAxiomsPinned TrustIr.TrustIrExpr.rotlWidth_bound == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.rotrWidth_bound == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.SMTSorted.eval_value_valid == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.toSMTRequest_value_valid == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.toSMTRequest_bv_range == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.toSMTRequest_bitvec_exact == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

end TrustIr.TrustIrExpr
