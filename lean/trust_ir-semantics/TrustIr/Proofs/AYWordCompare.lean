-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYWordMul

namespace TrustIr.AYGateCNF
open TrustIrExpr

/-- (~left)+right with zero carry overflows exactly when left < right. -/
def Code.wordUlt {width : Nat} (left right : Fin width → Nat) (next : Nat) : Code :=
  let inverted := WordCode.bitNot left next
  inverted.appendBool (Code.addCarryOut false inverted.bits right (next + inverted.gates.length))

theorem Code.wordUlt_check {width : Nat} (left right : Fin width → Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) :
    (Code.wordUlt left right next).check next = true := by
  have inverted := WordCode.bitNot_check left next leftBound
  apply WordCode.appendBool_check _ _ next inverted
  apply Code.addCarryOut_check
  · exact ((WordCode.check_iff _ _).mp inverted).2
  · intro i; have before := rightBound i; omega

theorem Code.wordUlt_eval {width : Nat} (left right : Fin width → Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) (env : Assignment) :
    (Code.wordUlt left right next).eval env = (wordValue left env).ult (wordValue right env) := by
  have checked := WordCode.bitNot_check left next leftBound
  obtain ⟨valid, bounds⟩ := (WordCode.check_iff _ _).mp checked
  have rightLater : ∀ i, right i < next + (WordCode.bitNot left next).gates.length := by
    intro i; have before := rightBound i; omega
  have rightSame : wordValue right (run (WordCode.bitNot left next).gates env) = wordValue right env := by
    apply wordValue_congr
    intro i
    exact (valid.run_correct env).1 (right i) (rightBound i)
  have leftDecode : wordValue (WordCode.bitNot left next).bits (run (WordCode.bitNot left next).gates env) =
      ~~~(wordValue left env) := WordCode.bitNot_value left next leftBound env
  have numeric := Code.addCarryOut_numeric false (WordCode.bitNot left next).bits right _ bounds rightLater
    (run (WordCode.bitNot left next).gates env)
  rw [leftDecode, rightSame] at numeric
  simp only [BitVec.toNat_not, Bool.toNat_false, Nat.add_zero] at numeric
  have sumBound := ((WordCode.addCarry false (WordCode.bitNot left next).bits right
    (next + (WordCode.bitNot left next).gates.length)).value (run (WordCode.bitNot left next).gates env)).isLt
  have leftSize := (wordValue left env).isLt
  rw [Code.wordUlt, WordCode.appendBool_eval]
  cases carry : (Code.addCarryOut false (WordCode.bitNot left next).bits right
      (next + (WordCode.bitNot left next).gates.length)).eval (run (WordCode.bitNot left next).gates env) with
  | false =>
    rw [carry] at numeric
    simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at numeric
    have noLess : ¬ (wordValue left env).toNat < (wordValue right env).toNat := by omega
    simp [BitVec.ult, noLess]
  | true =>
    rw [carry] at numeric
    simp only [Bool.toNat_true, Nat.mul_one] at numeric
    have less : (wordValue left env).toNat < (wordValue right env).toNat := by omega
    simp [BitVec.ult, less]

def Code.wordUle {width : Nat} (left right : Fin width → Nat) (next : Nat) : Code :=
  Code.composeUnary .boolNot next (Code.wordUlt right left next)

theorem Code.wordUle_check {width : Nat} (left right : Fin width → Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) :
    (Code.wordUle left right next).check next = true :=
  Code.composeUnary_check _ _ _ (Code.wordUlt_check right left next rightBound leftBound)

theorem Code.wordUle_eval {width : Nat} (left right : Fin width → Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) (env : Assignment) :
    (Code.wordUle left right next).eval env = (wordValue left env).ule (wordValue right env) := by
  rw [Code.wordUle, Code.composeUnary_eval,
    Code.wordUlt_eval right left next rightBound leftBound]
  simp only [SMTUnary.eval, BitVec.ult, BitVec.ule, ← decide_not]
  congr 1
  apply propext
  omega

theorem word_toInt_sign {width : Nat} (word : BitVec width) :
    word.toInt = if word.msb then (word.toNat : Int) - (2 ^ width : Nat) else (word.toNat : Int) := by
  cases width with
  | zero => rw [BitVec.of_length_zero (x := word)]; decide
  | succ width =>
    rw [BitVec.toInt_eq_toNat_cond, BitVec.msb_eq_decide]
    simp only [Nat.add_sub_cancel, decide_eq_true_eq]
    have _power : 2 ^ (width + 1) = 2 ^ width * 2 := Nat.pow_succ _ _
    split <;> split <;> first | rfl | omega

theorem word_slt_sign {width : Nat} (left right : BitVec width) :
    left.slt right = if left.msb == right.msb then left.ult right else left.msb := by
  have leftBound := left.isLt
  have rightBound := right.isLt
  simp only [BitVec.slt, word_toInt_sign]
  cases hl : left.msb <;> cases hr : right.msb
  all_goals apply Bool.eq_iff_iff.mpr
  trustIrCompilerProof {
    all_goals simp [hl, hr, BitVec.ult]
  } {
    all_goals simp [hl, hr, BitVec.ult, ← Int.natCast_pow]
  }
  all_goals omega

def Code.wordSlt : {width : Nat} → (Fin width → Nat) → (Fin width → Nat) → Nat → Code
  | 0, _, _, next => Code.constant false next
  | width + 1, left, right, next =>
    let sign := (⟨width, Nat.lt_succ_self width⟩ : Fin (width + 1))
    Code.composeIte next (Code.binary (.eq .bool) (left sign) (right sign) next)
      (Code.wordUlt left right (next + 1)) ⟨[], left sign⟩

theorem Code.wordSlt_check {width : Nat} (left right : Fin width → Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) :
    (Code.wordSlt left right next).check next = true := by
  cases width with
  | zero => exact Code.constant_check _ _
  | succ width =>
    let sign := (⟨width, Nat.lt_succ_self width⟩ : Fin (width + 1))
    have yesCheck := Code.wordUlt_check left right (next + 1)
      (by intro i; have h := leftBound i; omega) (by intro i; have h := rightBound i; omega)
    apply Code.composeIte_check _ _ _ _
      (Code.binary_check (.eq .bool) _ _ next (leftBound sign) (rightBound sign)) yesCheck
    apply (Code.check_iff _ _).mpr
    constructor
    · exact .nil _
    · change left sign < _
      have before := leftBound sign
      simp only [Code.append, List.length_append]
      omega

theorem Code.wordSlt_eval {width : Nat} (left right : Fin width → Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) (env : Assignment) :
    (Code.wordSlt left right next).eval env = (wordValue left env).slt (wordValue right env) := by
  cases width with
  | zero =>
    rw [word_slt_sign]
    trustIrCompilerProof {
      simp [Code.wordSlt, Code.constant_eval, BitVec.ult]
    } {
      simp [Code.wordSlt, Code.constant_eval, BitVec.ult,
        BitVec.of_length_zero (x := wordValue left env),
        BitVec.of_length_zero (x := wordValue right env)]
    }
  | succ width =>
    let sign := (⟨width, Nat.lt_succ_self width⟩ : Fin (width + 1))
    let cond := Code.binary (.eq .bool) (left sign) (right sign) next
    let yes := Code.wordUlt left right (next + 1)
    let no : Code := ⟨[], left sign⟩
    have condCheck : cond.check next = true := Code.binary_check _ _ _ _ (leftBound sign) (rightBound sign)
    have leftLater : ∀ i, left i < next + 1 := by intro i; have h := leftBound i; omega
    have rightLater : ∀ i, right i < next + 1 := by intro i; have h := rightBound i; omega
    have yesCheck : yes.check (next + cond.gates.length) = true := Code.wordUlt_check _ _ _ leftLater rightLater
    have noCheck : no.check (next + (Code.append cond yes).gates.length) = true := by
      apply (Code.check_iff _ _).mpr
      constructor
      · exact .nil _
      · change left sign < _
        have before := leftBound sign
        simp only [Code.append, List.length_append]
        omega
    have condValid := ((cond.check_iff next).mp condCheck).1
    have prefixValid := ((Code.check_iff _ _).mp (Code.append_check cond yes next condCheck yesCheck)).1
    have leftSame : wordValue left (run cond.gates env) = wordValue left env := by
      apply wordValue_congr
      intro i
      exact (condValid.run_correct env).1 _ (leftBound i)
    have rightSame : wordValue right (run cond.gates env) = wordValue right env := by
      apply wordValue_congr
      intro i
      exact (condValid.run_correct env).1 _ (rightBound i)
    have noSame : no.eval (run (Code.append cond yes).gates env) = env (left sign) :=
      (prefixValid.run_correct env).1 _ (leftBound sign)
    have leftSign : (wordValue left env).msb = env (left sign) := by
      trustIrCompilerProof { rw [BitVec.msb_eq_getLsb_last] } {
        rw [BitVec.msb_eq_getLsbD_last]
      }
      simpa using wordValue_bit left env sign
    have rightSign : (wordValue right env).msb = env (right sign) := by
      trustIrCompilerProof { rw [BitVec.msb_eq_getLsb_last] } {
        rw [BitVec.msb_eq_getLsbD_last]
      }
      simpa using wordValue_bit right env sign
    change (Code.composeIte next cond yes no).eval env = _
    rw [Code.composeIte_eval _ _ _ _ condCheck yesCheck noCheck, noSame]
    change (if cond.eval env then (Code.wordUlt left right (next + 1)).eval (run cond.gates env)
      else env (left sign)) = _
    rw [Code.wordUlt_eval left right (next + 1) leftLater rightLater, leftSame, rightSame]
    rw [show cond.eval env = (env (left sign) == env (right sign)) from
      Code.binary_eval (.eq .bool) _ _ next (leftBound sign) (rightBound sign) env]
    rw [← leftSign, ← rightSign, word_slt_sign]

def Code.wordSle {width : Nat} (left right : Fin width → Nat) (next : Nat) : Code :=
  Code.composeUnary .boolNot next (Code.wordSlt right left next)

theorem Code.wordSle_check {width : Nat} (left right : Fin width → Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) :
    (Code.wordSle left right next).check next = true :=
  Code.composeUnary_check _ _ _ (Code.wordSlt_check right left next rightBound leftBound)

theorem Code.wordSle_eval {width : Nat} (left right : Fin width → Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) (env : Assignment) :
    (Code.wordSle left right next).eval env = (wordValue left env).sle (wordValue right env) := by
  rw [Code.wordSle, Code.composeUnary_eval, Code.wordSlt_eval right left next rightBound leftBound]
  simp only [SMTUnary.eval, BitVec.slt, BitVec.sle, ← decide_not]
  congr 1
  apply propext
  omega

/-- One XNOR and one AND per actual input pair, with a true empty seed. -/
def Code.equalRows (pairs : List (Nat × Nat)) (next : Nat) : Code :=
  pairs.foldr (fun pair rest next =>
    let prior := rest next
    Code.composeBinary .boolAnd next prior
      (Code.binary (.eq .bool) pair.1 pair.2 (next + prior.gates.length)))
    (fun next => Code.constant true next) next

theorem Code.equalRows_check (pairs : List (Nat × Nat)) (next : Nat)
    (bounds : ∀ pair ∈ pairs, pair.1 < next ∧ pair.2 < next) :
    (Code.equalRows pairs next).check next = true := by
  induction pairs generalizing next with
  | nil => exact Code.constant_check _ _
  | cons pair rest ih =>
    have restBounds := fun item member => bounds item (List.Mem.tail pair member)
    have checked := ih next restBounds
    obtain ⟨leftBound, rightBound⟩ := bounds pair (List.Mem.head _)
    have leftLater : pair.1 < next + (Code.equalRows rest next).gates.length := by omega
    have rightLater : pair.2 < next + (Code.equalRows rest next).gates.length := by omega
    exact Code.composeBinary_check _ _ _ _ checked
      (Code.binary_check (.eq .bool) pair.1 pair.2 _ leftLater rightLater)

theorem Code.equalRows_eval (pairs : List (Nat × Nat)) (next : Nat)
    (bounds : ∀ pair ∈ pairs, pair.1 < next ∧ pair.2 < next) (env : Assignment) :
    (Code.equalRows pairs next).eval env = pairs.all (fun pair => env pair.1 == env pair.2) := by
  induction pairs generalizing next env with
  | nil => exact Code.constant_eval true next env
  | cons pair rest ih =>
    have restBounds := fun item member => bounds item (List.Mem.tail pair member)
    have checked := Code.equalRows_check rest next restBounds
    obtain ⟨leftBound, rightBound⟩ := bounds pair (List.Mem.head _)
    have leftLater : pair.1 < next + (Code.equalRows rest next).gates.length := by omega
    have rightLater : pair.2 < next + (Code.equalRows rest next).gates.length := by omega
    have compared := Code.binary_check (.eq .bool) pair.1 pair.2 _ leftLater rightLater
    have valid := ((Code.check_iff _ _).mp checked).1
    have leftSame := (valid.run_correct env).1 pair.1 leftBound
    have rightSame := (valid.run_correct env).1 pair.2 rightBound
    change (Code.composeBinary .boolAnd next (Code.equalRows rest next)
      (Code.binary (.eq .bool) pair.1 pair.2 (next + (Code.equalRows rest next).gates.length))).eval env = _
    rw [Code.composeBinary_eval _ _ _ _ checked compared,
      Code.binary_eval (.eq .bool) _ _ _ leftLater rightLater, leftSame, rightSame,
      ih next restBounds env]
    simp only [SMTBinary.eval, SMTSort.coreEq, List.all]
    exact Bool.and_comm _ _

private theorem pair_bounds {width : Nat} (left right : Fin width → Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) :
    ∀ pair ∈ tabulate (fun i => (left i, right i)), pair.1 < next ∧ pair.2 < next := by
  intro pair member
  obtain ⟨i, same⟩ := tabulate_cases (fun i => (left i, right i)) pair member
  rw [← same]
  exact ⟨leftBound i, rightBound i⟩

def Code.wordEq {width : Nat} (left right : Fin width → Nat) (next : Nat) : Code :=
  Code.equalRows (tabulate (fun i => (left i, right i))) next

theorem Code.wordEq_check {width : Nat} (left right : Fin width → Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) :
    (Code.wordEq left right next).check next = true :=
  Code.equalRows_check _ _ (pair_bounds left right next leftBound rightBound)

theorem Code.wordEq_eval {width : Nat} (left right : Fin width → Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) (env : Assignment) :
    (Code.wordEq left right next).eval env = decide (wordValue left env = wordValue right env) := by
  rw [Code.wordEq, Code.equalRows_eval _ _ (pair_bounds left right next leftBound rightBound)]
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro same
    apply trustIrWordExt
    intro i
    rw [wordValue_bit, wordValue_bit]
    exact same _ (tabulate_mem (fun i => (left i, right i)) i)
  · intro same pair member
    obtain ⟨i, source⟩ := tabulate_cases (fun i => (left i, right i)) pair member
    rw [← source]
    simpa only [wordValue_bit] using congrArg (fun word => (trustIrWordBit word) i.val) same

def Code.wordDistinct {width : Nat} (left right : Fin width → Nat) (next : Nat) : Code :=
  Code.composeUnary .boolNot next (Code.wordEq left right next)

theorem Code.wordDistinct_check {width : Nat} (left right : Fin width → Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) :
    (Code.wordDistinct left right next).check next = true :=
  Code.composeUnary_check _ _ _ (Code.wordEq_check left right next leftBound rightBound)

theorem Code.wordDistinct_eval {width : Nat} (left right : Fin width → Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) (env : Assignment) :
    (Code.wordDistinct left right next).eval env = !(decide (wordValue left env = wordValue right env)) := by
  rw [Code.wordDistinct, Code.composeUnary_eval, Code.wordEq_eval left right next leftBound rightBound]
  rfl

inductive WordCompareOp where
  | eq | distinct | ult | ule | slt | sle
  deriving Repr

def WordCompareOp.target (op : WordCompareOp) (width : Nat) : SMTBinary (.bv width) .bool :=
  match op with
  | .eq => .eq (.bv width)
  | .distinct => .distinct (.bv width)
  | .ult => .bvUlt width
  | .ule => .bvUle width
  | .slt => .bvSlt width
  | .sle => .bvSle width

def Code.wordCompare {width : Nat} (op : WordCompareOp) (left right : Fin width → Nat) (next : Nat) : Code :=
  match op with
  | .eq => Code.wordEq left right next
  | .distinct => Code.wordDistinct left right next
  | .ult => Code.wordUlt left right next
  | .ule => Code.wordUle left right next
  | .slt => Code.wordSlt left right next
  | .sle => Code.wordSle left right next

theorem Code.wordCompare_check {width : Nat} (op : WordCompareOp) (left right : Fin width → Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) :
    (Code.wordCompare op left right next).check next = true := by
  cases op
  · exact Code.wordEq_check _ _ _ leftBound rightBound
  · exact Code.wordDistinct_check _ _ _ leftBound rightBound
  · exact Code.wordUlt_check _ _ _ leftBound rightBound
  · exact Code.wordUle_check _ _ _ leftBound rightBound
  · exact Code.wordSlt_check _ _ _ leftBound rightBound
  · exact Code.wordSle_check _ _ _ leftBound rightBound

theorem Code.wordCompare_eval {width : Nat} (op : WordCompareOp) (left right : Fin width → Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) (env : Assignment) :
    (Code.wordCompare op left right next).eval env =
      (op.target width).eval (wordValue left env) (wordValue right env) := by
  cases op
  · exact Code.wordEq_eval _ _ _ leftBound rightBound env
  · exact Code.wordDistinct_eval _ _ _ leftBound rightBound env
  · exact Code.wordUlt_eval _ _ _ leftBound rightBound env
  · exact Code.wordUle_eval _ _ _ leftBound rightBound env
  · exact Code.wordSlt_eval _ _ _ leftBound rightBound env
  · exact Code.wordSle_eval _ _ _ leftBound rightBound env

def Code.composeWordCompare {width : Nat} (op : WordCompareOp) (next : Nat)
    (left right : WordCode width) : Code :=
  let both := WordCode.append left right
  both.appendBool (Code.wordCompare op left.bits right.bits (next + both.gates.length))

theorem Code.composeWordCompare_check {width : Nat} (op : WordCompareOp) (next : Nat)
    (left right : WordCode width) (leftCheck : left.check next = true)
    (rightCheck : right.check (next + left.gates.length) = true) :
    (Code.composeWordCompare op next left right).check next = true := by
  obtain ⟨leftBounds, rightBounds⟩ := WordCode.append_operand_bounds next left right leftCheck rightCheck
  apply WordCode.appendBool_check _ _ next (WordCode.append_check left right next leftCheck rightCheck)
  exact Code.wordCompare_check op _ _ _ leftBounds rightBounds

theorem Code.composeWordCompare_eval {width : Nat} (op : WordCompareOp) (next : Nat)
    (left right : WordCode width) (leftCheck : left.check next = true)
    (rightCheck : right.check (next + left.gates.length) = true) (env : Assignment) :
    (Code.composeWordCompare op next left right).eval env =
      (op.target width).eval (left.value env) (right.value (run left.gates env)) := by
  obtain ⟨leftBounds, rightBounds⟩ := WordCode.append_operand_bounds next left right leftCheck rightCheck
  have rightValid := ((right.check_iff _).mp rightCheck).1
  have leftValue : wordValue left.bits (run (WordCode.append left right).gates env) = left.value env := by
    apply wordValue_congr
    intro i
    exact rightValid.append_preserves (next := next) (first := left.gates) env (left.bits i)
      (((left.check_iff next).mp leftCheck).2 i)
  have rightValue : wordValue right.bits (run (WordCode.append left right).gates env) =
      right.value (run left.gates env) := by rw [WordCode.append, run_append]; rfl
  rw [Code.composeWordCompare, WordCode.appendBool_eval,
    Code.wordCompare_eval _ _ _ _ leftBounds rightBounds, leftValue, rightValue]

theorem Code.wordCompare_target {width : Nat} (op : WordCompareOp) (left right : Fin width → Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) (env : Assignment)
    (leftTerm rightTerm : SMTTerm (.bv width)) (target : SMTEnv)
    (leftValue : wordValue left env = leftTerm.eval target)
    (rightValue : wordValue right env = rightTerm.eval target) :
    (Code.wordCompare op left right next).eval env =
      (SMTTerm.binary (op.target width) leftTerm rightTerm).eval target := by
  rw [Code.wordCompare_eval op left right next leftBound rightBound env, leftValue, rightValue]
  rfl

theorem Code.composeWordCompare_target {width : Nat} (op : WordCompareOp) (next : Nat)
    (left right : WordCode width) (leftCheck : left.check next = true)
    (rightCheck : right.check (next + left.gates.length) = true) (env : Assignment)
    (leftTerm rightTerm : SMTTerm (.bv width)) (target : SMTEnv)
    (leftValue : left.value env = leftTerm.eval target)
    (rightValue : right.value (run left.gates env) = rightTerm.eval target) :
    (Code.composeWordCompare op next left right).eval env =
      (SMTTerm.binary (op.target width) leftTerm rightTerm).eval target := by
  rw [Code.composeWordCompare_eval op next left right leftCheck rightCheck env, leftValue, rightValue]
  rfl

end TrustIr.AYGateCNF









#trustIrAxiomsExact TrustIr.AYGateCNF.Code.wordUlt_check == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.wordUlt_eval == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.wordUle_check == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.wordUle_eval == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.word_toInt_sign == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.word_slt_sign == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.wordSlt_check == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.wordSlt_eval == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.wordSle_check == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.wordSle_eval == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.equalRows_check == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.equalRows_eval == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.wordEq_check == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.wordEq_eval == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.wordDistinct_check == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.wordDistinct_eval == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.wordCompare_check == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.wordCompare_eval == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.composeWordCompare_check == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.composeWordCompare_eval == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.wordCompare_target == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.composeWordCompare_target == [propext, Classical.choice, Quot.sound]
