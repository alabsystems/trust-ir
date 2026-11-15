-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYWordWires

namespace TrustIr.AYGateCNF

/-- The single-gate assignment retains its original defining equation. -/
theorem Gate.apply_eq (gate : Gate) (env : Assignment) :
    gate.apply env = (fun id => if id = gate.output then gate.eval env else env id) := rfl

/-- Every declared output lies in the allocated range. -/
theorem Valid.output_bound {next : Nat} {gates : List Gate} (valid : Valid next gates)
    (gate : Gate) (member : gate ∈ gates) : gate.output < next + gates.length := by
  induction valid with
  | nil next => cases member
  | @cons next head tail output _inputs _rest ih =>
    cases member with
    | head => simp only [List.length_cons]; omega
    | tail _ member => have bound := ih member; simp only [List.length_cons]; omega

/-- Interpret any recorded cell field as a native little-endian word. -/
def Adder.word (adder : Adder) (field : AdderCell → Nat) (env : Assignment) : BitVec adder.width :=
  (BitVec.ofBoolListLE (adder.cells.map (fun cell => env (field cell)))).cast (by simp [Adder.width])

theorem Adder.word_bit (adder : Adder) (field : AdderCell → Nat) (env : Assignment) (i : Fin adder.width) :
    (trustIrWordBit (adder.word field env)) i.val = env (field (adder.cells.get i)) := by
  trustIrCompilerProof {
    simp only [Adder.word, BitVec.getLsb_cast, BitVec.getLsb_ofBoolListLE,
      List.getD_eq_get?, List.get?_map]
    rw [List.get?_eq_get i.isLt]
  } {
    simp only [Adder.word, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
      List.getD_eq_getElem?_getD, List.getElem?_map]
    rw [List.getElem?_eq_getElem i.isLt]
  }
  rfl

theorem Adder.word_toNat (adder : Adder) (field : AdderCell → Nat) (env : Assignment) :
    (adder.word field env).toNat =
      adder.cells.foldr (fun cell rest => (env (field cell)).toNat + 2 * rest) 0 := by
  simp only [Adder.word, BitVec.toNat_cast]
  induction adder.cells with
  | nil => rfl
  | cons cell tail ih =>
    simp only [List.map, BitVec.ofBoolListLE, BitVec.toNat_concat, List.foldr]
    rw [ih]
    omega

theorem Adder.word_wires (adder : Adder) (field : AdderCell → Nat) (env : Assignment) :
    wordValue (fun i : Fin adder.width => field (adder.cells.get i)) env = adder.word field env := by
  apply trustIrWordExt
  intro i
  rw [wordValue_bit, Adder.word_bit]

/-- Result wires are read from the actual cells, not inferred from a guessed
stride or reconstructed arithmetic result. -/
def Adder.code (adder : Adder) : WordCode adder.width :=
  ⟨adder.gates, fun i => (adder.cells.get i).sum⟩

private theorem Adder.sum_gate (adder : Adder) (cell : AdderCell) (member : cell ∈ adder.cells) :
    ∃ gate ∈ adder.gates, gate.output = cell.sum := by
  induction adder using Adder.induction with
  | nil carry => cases member
  | cons left right sum carry tail ih =>
    change cell ∈ AdderCell.mk left right sum tail.inputCarry :: tail.cells at member
    cases member with
    | head => exact ⟨.xor3 sum left right carry, List.Mem.head _, rfl⟩
    | tail _ member =>
      obtain ⟨gate, present, output⟩ := ih member
      exact ⟨gate, List.Mem.tail _ (List.Mem.tail _ present), output⟩

theorem Adder.code_check (adder : Adder) (next : Nat)
    (checked : checkProgram next adder.gates = true) : adder.code.check next = true := by
  have valid := (checkProgram_iff next adder.gates).mp checked
  apply (WordCode.check_iff _ _).mpr
  refine ⟨valid, ?_⟩
  intro i
  trustIrCompilerProof {
    obtain ⟨gate, member, output⟩ := adder.sum_gate (adder.cells.get i) (List.get_mem _ _ _)
  } {
    obtain ⟨gate, member, output⟩ := adder.sum_gate (adder.cells.get i) (List.get_mem _ _)
  }
  have bound := valid.output_bound gate member
  rw [output] at bound
  exact bound

private theorem word_roundtrip {width : Nat} (word : BitVec width) : BitVec.ofNat width word.toNat = word := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt word.isLt]

/-- The existing carry theorem reaches the actual typed result-vector decoder. -/
theorem Adder.code_value (adder : Adder) (next : Nat)
    (checked : checkProgram next adder.gates = true) (inputCheck : adder.checkInputs next = true)
    (env : Assignment) : adder.code.value env =
      adder.word AdderCell.left env + adder.word AdderCell.right env +
        BitVec.ofNat adder.width (env adder.inputCarry).toNat := by
  have left : BitVec.ofNat adder.width (adder.leftValue env) = adder.word AdderCell.left env := by
    simpa only [Adder.word_toNat, Adder.leftValue] using word_roundtrip (adder.word AdderCell.left env)
  have right : BitVec.ofNat adder.width (adder.rightValue env) = adder.word AdderCell.right env := by
    simpa only [Adder.word_toNat, Adder.rightValue] using word_roundtrip (adder.word AdderCell.right env)
  have result : BitVec.ofNat adder.width (adder.sumValue (run adder.gates env)) = adder.code.value env := by
    have decoded : adder.code.value env = adder.word AdderCell.sum (run adder.gates env) :=
      Adder.word_wires adder AdderCell.sum (run adder.gates env)
    have round : BitVec.ofNat adder.width (adder.sumValue (run adder.gates env)) =
        adder.word AdderCell.sum (run adder.gates env) := by
      simpa only [Adder.word_toNat, Adder.sumValue] using
        word_roundtrip (adder.word AdderCell.sum (run adder.gates env))
    exact round.trans decoded.symm
  have addition := adder.run_native_add next checked inputCheck env
  rw [left, right, result] at addition
  exact addition.symm

/-- Width transport changes no gates or data; only the static vector index. -/
def WordCode.castWidth {a b : Nat} (same : a = b) (code : WordCode a) : WordCode b := same ▸ code

theorem WordCode.castWidth_check {a b : Nat} (same : a = b) (code : WordCode a) (next : Nat) :
    (code.castWidth same).check next = code.check next := by cases same; rfl

theorem WordCode.castWidth_value {a b : Nat} (same : a = b) (code : WordCode a) (env : Assignment) :
    (code.castWidth same).value env = (code.value env).cast same := by cases same; rfl

def wordAdder {width : Nat} (left right : Fin width → Nat) (next carry : Nat) : Adder :=
  buildAdder (tabulate (fun i => (left i, right i))) next carry

theorem wordAdder_width {width : Nat} (left right : Fin width → Nat) (next carry : Nat) :
    (wordAdder left right next carry).width = width := by rw [wordAdder, buildAdder_width, tabulate_length]

private theorem builder_pairs (inputs : List (Nat × Nat)) (next carry : Nat) :
    (buildAdder inputs next carry).cells.map (fun cell => (cell.left, cell.right)) = inputs := by
  induction inputs generalizing next carry with
  | nil => rfl
  | cons pair tail ih =>
    change pair :: (buildAdder tail (next + 2) (next + 1)).cells.map _ = pair :: tail
    rw [ih]

private theorem wordAdder_cell {width : Nat} (left right : Fin width → Nat) (next carry : Nat) (i : Fin width) :
    let adder := wordAdder left right next carry
    let j : Fin adder.width := ⟨i.val, by rw [wordAdder_width]; exact i.isLt⟩
    ((adder.cells.get j).left, (adder.cells.get j).right) = (left i, right i) := by
  let adder := wordAdder left right next carry
  let j : Fin adder.width := ⟨i.val, by rw [wordAdder_width]; exact i.isLt⟩
  have lookup : (adder.cells.map (fun cell => (cell.left, cell.right))).getD i.val (0,0) = (left i, right i) := by
    rw [show adder.cells.map (fun cell => (cell.left, cell.right)) = tabulate (fun i => (left i, right i))
      from builder_pairs _ next carry]
    exact tabulate_getD _ i _
  trustIrCompilerProof {
    rw [List.getD_eq_get?, List.get?_map, List.get?_eq_get j.isLt] at lookup
  } {
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem j.isLt] at lookup
  }
  exact lookup

theorem wordAdder_left {width : Nat} (left right : Fin width → Nat) (next carry : Nat) (env : Assignment) :
    ((wordAdder left right next carry).word AdderCell.left env).cast (wordAdder_width left right next carry) =
      wordValue left env := by
  apply trustIrWordExt
  intro i
  let j : Fin (wordAdder left right next carry).width := ⟨i.val, by rw [wordAdder_width]; exact i.isLt⟩
  trustIrCompilerProof {
    rw [BitVec.getLsb_cast, Adder.word_bit _ _ _ j, wordValue_bit]
  } {
    rw [BitVec.getLsbD_cast, Adder.word_bit _ _ _ j, wordValue_bit]
  }
  exact congrArg env (congrArg Prod.fst (wordAdder_cell left right next carry i))

theorem wordAdder_right {width : Nat} (left right : Fin width → Nat) (next carry : Nat) (env : Assignment) :
    ((wordAdder left right next carry).word AdderCell.right env).cast (wordAdder_width left right next carry) =
      wordValue right env := by
  apply trustIrWordExt
  intro i
  let j : Fin (wordAdder left right next carry).width := ⟨i.val, by rw [wordAdder_width]; exact i.isLt⟩
  trustIrCompilerProof {
    rw [BitVec.getLsb_cast, Adder.word_bit _ _ _ j, wordValue_bit]
  } {
    rw [BitVec.getLsbD_cast, Adder.word_bit _ _ _ j, wordValue_bit]
  }
  exact congrArg env (congrArg Prod.snd (wordAdder_cell left right next carry i))

theorem wordAdder_checks {width : Nat} (left right : Fin width → Nat) (next carry : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) (carryBound : carry < next) :
    checkProgram next (wordAdder left right next carry).gates = true ∧
      (wordAdder left right next carry).checkInputs next = true := by
  apply buildAdder_checks
  · intro pair member
    obtain ⟨i, same⟩ := tabulate_cases (fun i => (left i, right i)) pair member
    rw [← same]
    exact ⟨leftBound i, rightBound i⟩
  · exact carryBound

/-- Reuse the existing ripple topology with a typed word result. -/
def WordCode.ripple {width : Nat} (left right : Fin width → Nat) (next carry : Nat) : WordCode width :=
  (wordAdder left right next carry).code.castWidth (wordAdder_width left right next carry)

theorem WordCode.ripple_check {width : Nat} (left right : Fin width → Nat) (next carry : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) (carryBound : carry < next) :
    (WordCode.ripple left right next carry).check next = true := by
  rw [WordCode.ripple, WordCode.castWidth_check]
  exact Adder.code_check _ next (wordAdder_checks left right next carry leftBound rightBound carryBound).1

private theorem cast_add {a b : Nat} (same : a = b) (x y : BitVec a) :
    (x + y).cast same = x.cast same + y.cast same := by cases same; rfl

theorem WordCode.ripple_value {width : Nat} (left right : Fin width → Nat) (next carry : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) (carryBound : carry < next)
    (env : Assignment) : (WordCode.ripple left right next carry).value env =
      wordValue left env + wordValue right env + BitVec.ofNat width (env carry).toNat := by
  obtain ⟨checked, inputCheck⟩ := wordAdder_checks left right next carry leftBound rightBound carryBound
  have carryEq : (wordAdder left right next carry).inputCarry = carry := buildAdder_inputCarry _ next carry
  rw [WordCode.ripple, WordCode.castWidth_value, Adder.code_value _ next checked inputCheck env]
  rw [cast_add, cast_add, BitVec.cast_ofNat, carryEq, wordAdder_left, wordAdder_right]

/-- Allocate a fixed carry before the ripple block. Operand wires predate it. -/
def WordCode.addCarry {width : Nat} (carry : Bool) (left right : Fin width → Nat) (next : Nat) : WordCode width :=
  let result := WordCode.ripple left right (next + 1) next
  ⟨(if carry then Gate.constTrue next else Gate.constFalse next) :: result.gates, result.bits⟩

theorem WordCode.addCarry_check {width : Nat} (carry : Bool) (left right : Fin width → Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) :
    (WordCode.addCarry carry left right next).check next = true := by
  have leftLater : ∀ i, left i < next + 1 := by intro i; have h := leftBound i; omega
  have rightLater : ∀ i, right i < next + 1 := by intro i; have h := rightBound i; omega
  obtain ⟨valid, bounds⟩ := (WordCode.check_iff _ _).mp
    (WordCode.ripple_check left right (next + 1) next leftLater rightLater (by omega))
  apply (WordCode.check_iff _ _).mpr
  constructor
  · cases carry <;> exact Valid.cons (next := next) rfl (by simp [Gate.inputs]) valid
  · intro i
    have bound := bounds i
    change (WordCode.ripple left right (next + 1) next).bits i <
      next + ((WordCode.ripple left right (next + 1) next).gates.length + 1)
    omega

theorem WordCode.addCarry_value {width : Nat} (carry : Bool) (left right : Fin width → Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) (env : Assignment) :
    (WordCode.addCarry carry left right next).value env = wordValue left env + wordValue right env + BitVec.ofNat width carry.toNat := by
  let after := Gate.apply (if carry then Gate.constTrue next else Gate.constFalse next) env
  have leftLater : ∀ i, left i < next + 1 := by intro i; have h := leftBound i; omega
  have rightLater : ∀ i, right i < next + 1 := by intro i; have h := rightBound i; omega
  have leftSame : wordValue left after = wordValue left env := by
    apply wordValue_congr
    intro i
    cases carry <;> simp [after, Gate.apply, Gate.output, show left i ≠ next by have h := leftBound i; omega]
  have rightSame : wordValue right after = wordValue right env := by
    apply wordValue_congr
    intro i
    cases carry <;> simp [after, Gate.apply, Gate.output, show right i ≠ next by have h := rightBound i; omega]
  change (WordCode.ripple left right (next + 1) next).value after = _
  have result := WordCode.ripple_value left right (next + 1) next leftLater rightLater (by omega) after
  rw [leftSame, rightSame] at result
  cases carry <;> simpa [after, Gate.apply, Gate.output, Gate.eval] using result

/-- Plain modular addition is the fixed-zero-carry specialization. -/
def WordCode.add {width : Nat} (left right : Fin width → Nat) (next : Nat) : WordCode width :=
  WordCode.addCarry false left right next

theorem WordCode.add_check {width : Nat} (left right : Fin width → Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) :
    (WordCode.add left right next).check next = true :=
  WordCode.addCarry_check false left right next leftBound rightBound

theorem WordCode.add_value {width : Nat} (left right : Fin width → Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) (env : Assignment) :
    (WordCode.add left right next).value env = wordValue left env + wordValue right env := by
  simpa [WordCode.add] using WordCode.addCarry_value false left right next leftBound rightBound env

theorem WordCode.add_target {width : Nat} (left right : Fin width → Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) (env : Assignment)
    (leftTerm rightTerm : TrustIrExpr.SMTTerm (.bv width)) (target : SMTEnv)
    (leftValue : wordValue left env = leftTerm.eval target)
    (rightValue : wordValue right env = rightTerm.eval target) :
    (WordCode.add left right next).value env =
      (TrustIrExpr.SMTTerm.binary (.bvAdd width) leftTerm rightTerm).eval target := by
  rw [WordCode.add_value left right next leftBound rightBound env, leftValue, rightValue]
  rfl

def WordCode.composeAdd {width : Nat} (next : Nat) (left right : WordCode width) : WordCode width :=
  let both := WordCode.append left right
  WordCode.append both (WordCode.add left.bits right.bits (next + both.gates.length))

theorem WordCode.composeAdd_check {width : Nat} (next : Nat) (left right : WordCode width)
    (leftCheck : left.check next = true)
    (rightCheck : right.check (next + left.gates.length) = true) :
    (WordCode.composeAdd next left right).check next = true := by
  obtain ⟨leftBounds, rightBounds⟩ := WordCode.append_operand_bounds next left right leftCheck rightCheck
  apply WordCode.append_check _ _ next (WordCode.append_check left right next leftCheck rightCheck)
  exact WordCode.add_check _ _ _ leftBounds rightBounds

theorem WordCode.composeAdd_value {width : Nat} (next : Nat) (left right : WordCode width)
    (leftCheck : left.check next = true)
    (rightCheck : right.check (next + left.gates.length) = true) (env : Assignment) :
    (WordCode.composeAdd next left right).value env = left.value env + right.value (run left.gates env) := by
  obtain ⟨leftBounds, rightBounds⟩ := WordCode.append_operand_bounds next left right leftCheck rightCheck
  have rightValid := ((right.check_iff _).mp rightCheck).1
  have leftValue : wordValue left.bits (run (WordCode.append left right).gates env) = left.value env := by
    apply wordValue_congr
    intro i
    exact rightValid.append_preserves (next := next) (first := left.gates) env (left.bits i)
      (((left.check_iff next).mp leftCheck).2 i)
  have rightValue : wordValue right.bits (run (WordCode.append left right).gates env) =
      right.value (run left.gates env) := by rw [WordCode.append, run_append]; rfl
  rw [WordCode.composeAdd, WordCode.append_value, WordCode.add_value _ _ _ leftBounds rightBounds,
    leftValue, rightValue]

theorem WordCode.composeAdd_target {width : Nat} (next : Nat) (left right : WordCode width)
    (leftCheck : left.check next = true)
    (rightCheck : right.check (next + left.gates.length) = true) (env : Assignment)
    (leftTerm rightTerm : TrustIrExpr.SMTTerm (.bv width)) (target : SMTEnv)
    (leftValue : left.value env = leftTerm.eval target)
    (rightValue : right.value (run left.gates env) = rightTerm.eval target) :
    (WordCode.composeAdd next left right).value env =
      (TrustIrExpr.SMTTerm.binary (.bvAdd width) leftTerm rightTerm).eval target := by
  rw [WordCode.composeAdd_value next left right leftCheck rightCheck env, leftValue, rightValue]
  rfl

theorem Adder.outputCarry_cases (adder : Adder) :
    adder.outputCarry = adder.inputCarry ∨ ∃ gate ∈ adder.gates, gate.output = adder.outputCarry := by
  induction adder using Adder.induction with
  | nil carry => exact Or.inl rfl
  | cons left right sum carry tail ih =>
    cases ih with
    | inl same =>
      exact Or.inr ⟨.fullAdderCarry tail.inputCarry left right carry,
        List.Mem.tail _ (List.Mem.head _), same.symm⟩
    | inr present =>
      obtain ⟨gate, member, output⟩ := present
      exact Or.inr ⟨gate, List.Mem.tail _ (List.Mem.tail _ member), output⟩

/-- Boolean result is the actual recorded outgoing carry, including empty adders. -/
def Adder.carryCode (adder : Adder) : Code := ⟨adder.gates, adder.outputCarry⟩

theorem Adder.carryCode_check (adder : Adder) (next : Nat)
    (checked : checkProgram next adder.gates = true) (carryBound : adder.inputCarry < next) :
    adder.carryCode.check next = true := by
  have valid := (checkProgram_iff next adder.gates).mp checked
  apply (Code.check_iff _ _).mpr
  refine ⟨valid, ?_⟩
  change adder.outputCarry < next + adder.gates.length
  cases adder.outputCarry_cases with
  | inl same => rw [same]; omega
  | inr present =>
    obtain ⟨gate, member, output⟩ := present
    have bound := valid.output_bound gate member
    rw [output] at bound
    exact bound

def Code.addCarryOut {width : Nat} (carry : Bool) (left right : Fin width → Nat) (next : Nat) : Code :=
  Code.append (Code.constant carry next) (wordAdder left right (next + 1) next).carryCode

theorem Code.addCarryOut_check {width : Nat} (carry : Bool) (left right : Fin width → Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) :
    (Code.addCarryOut carry left right next).check next = true := by
  apply Code.append_check _ _ next (Code.constant_check carry next)
  have leftLater : ∀ i, left i < next + 1 := by intro i; have h := leftBound i; omega
  have rightLater : ∀ i, right i < next + 1 := by intro i; have h := rightBound i; omega
  exact Adder.carryCode_check _ _
    (wordAdder_checks left right (next + 1) next leftLater rightLater (by omega)).1 (by
      change (wordAdder left right (next + 1) next).inputCarry < next + 1
      rw [show (wordAdder left right (next + 1) next).inputCarry = next from buildAdder_inputCarry _ _ _]
      omega)

/-- The carry decoder and sum decoder use exactly the same emitted program. -/
theorem Code.addCarryOut_numeric {width : Nat} (carry : Bool) (left right : Fin width → Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) (env : Assignment) :
    (wordValue left env).toNat + (wordValue right env).toNat + carry.toNat =
      ((WordCode.addCarry carry left right next).value env).toNat +
        2 ^ width * ((Code.addCarryOut carry left right next).eval env).toNat := by
  let block := wordAdder left right (next + 1) next
  let after := Gate.apply (if carry then Gate.constTrue next else Gate.constFalse next) env
  have leftLater : ∀ i, left i < next + 1 := by intro i; have h := leftBound i; omega
  have rightLater : ∀ i, right i < next + 1 := by intro i; have h := rightBound i; omega
  obtain ⟨checked, inputs⟩ := wordAdder_checks left right (next + 1) next leftLater rightLater (by omega)
  have numeric := block.run_numeric (next + 1) checked inputs after
  have leftSame : wordValue left after = wordValue left env := by
    apply wordValue_congr
    intro i
    cases carry <;> simp [after, Gate.apply, Gate.output, show left i ≠ next by have h := leftBound i; omega]
  have rightSame : wordValue right after = wordValue right env := by
    apply wordValue_congr
    intro i
    cases carry <;> simp [after, Gate.apply, Gate.output, show right i ≠ next by have h := rightBound i; omega]
  have leftDecode : block.leftValue after = (wordValue left env).toNat := by
    have decoded := congrArg BitVec.toNat (wordAdder_left left right (next + 1) next after)
    simpa only [BitVec.toNat_cast, Adder.word_toNat, Adder.leftValue, leftSame] using decoded
  have rightDecode : block.rightValue after = (wordValue right env).toNat := by
    have decoded := congrArg BitVec.toNat (wordAdder_right left right (next + 1) next after)
    simpa only [BitVec.toNat_cast, Adder.word_toNat, Adder.rightValue, rightSame] using decoded
  have sumDecode : ((WordCode.addCarry carry left right next).value env).toNat =
      block.sumValue (run block.gates after) := by
    change ((WordCode.ripple left right (next + 1) next).value after).toNat = _
    rw [WordCode.ripple, WordCode.castWidth_value, BitVec.toNat_cast]
    change (wordValue (fun i => (block.cells.get i).sum) (run block.gates after)).toNat = _
    simpa only [Adder.word_toNat, Adder.sumValue] using
      congrArg BitVec.toNat (Adder.word_wires block AdderCell.sum (run block.gates after))
  have carryDecode : (Code.addCarryOut carry left right next).eval env = run block.gates after block.outputCarry := rfl
  have inputCarry : block.inputCarry = next := buildAdder_inputCarry _ (next + 1) next
  have carrySame : after next = carry := by cases carry <;> simp [after, Gate.apply, Gate.output, Gate.eval]
  have widthSame : block.width = width := wordAdder_width left right (next + 1) next
  rw [leftDecode, rightDecode, inputCarry, carrySame, widthSame] at numeric
  rw [sumDecode, carryDecode]
  exact numeric

end TrustIr.AYGateCNF

/-- info: 'TrustIr.AYGateCNF.Gate.apply_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.Gate.apply_eq

#trustIrAxiomsPinned TrustIr.AYGateCNF.Valid.output_bound == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.Adder.word_bit == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.Adder.word_toNat == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.Adder.word_wires == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.Adder.code_check == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.Adder.code_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.castWidth_check == [propext]

#trustIrAxiomsPinned TrustIr.AYGateCNF.WordCode.castWidth_value == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.wordAdder_width == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsExact TrustIr.AYGateCNF.wordAdder_left == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.wordAdder_right == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.wordAdder_checks == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.ripple_check == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.ripple_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.add_check == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.add_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.add_target == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.composeAdd_check == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.composeAdd_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.composeAdd_target == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.addCarry_check == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.addCarry_value == [propext, Classical.choice, Quot.sound]

/-- info: 'TrustIr.AYGateCNF.Adder.outputCarry_cases' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.Adder.outputCarry_cases

#trustIrAxiomsPinned TrustIr.AYGateCNF.Adder.carryCode_check == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.addCarryOut_check == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.addCarryOut_numeric == [propext, Classical.choice, Quot.sound]
