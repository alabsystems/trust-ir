-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYWordSignedValue

/-- Select the actual proof lemma before elaborating either compiler API. -/
macro "trustIrWidthLemma " oldName:ident newName:ident : term => do
  if Lean.versionString == "4.8.0" then pure oldName
  else if Lean.versionString == "4.30.0-rc2" then pure newName
  else Lean.Macro.throwError "unsupported compiler for native width lemmas"

namespace TrustIr.AYGateCNF

/-- Rewire any output width through original input positions, sharing one
fresh zero for every absent position. No input wire is reallocated. -/
def WordCode.route {source target : Nat} (input : Fin source → Nat)
    (positions : Fin target → Option (Fin source)) (next : Nat) : WordCode target :=
  ⟨[.constFalse next], fun i => (positions i).elim next input⟩

theorem WordCode.route_check {source target : Nat} (input : Fin source → Nat)
    (positions : Fin target → Option (Fin source)) (next : Nat) (bound : ∀ i, input i < next) :
    (WordCode.route input positions next).check next = true := by
  apply (WordCode.check_iff _ _).mpr
  refine ⟨Valid.cons rfl (by simp [Gate.inputs]) (.nil _), ?_⟩
  intro i
  change (positions i).elim next input < next + 1
  cases positions i with
  | none => simp
  | some position => simp; have before := bound position; omega

theorem WordCode.route_value_bit {source target : Nat} (input : Fin source → Nat)
    (positions : Fin target → Option (Fin source)) (next : Nat) (bound : ∀ i, input i < next)
    (env : Assignment) (i : Fin target) :
    (trustIrWordBit ((WordCode.route input positions next).value env)) i.val =
      (positions i).elim false (fun position => env (input position)) := by
  have valid := ((WordCode.check_iff _ _).mp (WordCode.route_check input positions next bound)).1
  change (trustIrWordBit (wordValue _ (run [.constFalse next] env))) i.val = _
  rw [wordValue_bit]
  cases h : positions i with
  | none => simp [WordCode.route, h, run, Gate.apply, Gate.eval, Gate.output]
  | some position =>
    simp only [WordCode.route, h, Option.elim]
    exact (valid.run_correct env).1 _ (bound position)

def resizePositions (source target : Nat) (i : Fin target) : Option (Fin source) :=
  if h : i.val < source then some ⟨i.val, h⟩ else none

/-- Native zero extension when wider and truncation when narrower. -/
def WordCode.resize {source : Nat} (target : Nat) (input : Fin source → Nat) (next : Nat) : WordCode target :=
  WordCode.route input (resizePositions source target) next

theorem WordCode.resize_check {source : Nat} (target : Nat) (input : Fin source → Nat) (next : Nat)
    (bound : ∀ i, input i < next) : (WordCode.resize target input next).check next = true :=
  WordCode.route_check _ _ _ bound

theorem WordCode.resize_value {source : Nat} (target : Nat) (input : Fin source → Nat) (next : Nat)
    (bound : ∀ i, input i < next) (env : Assignment) :
    (WordCode.resize target input next).value env = (wordValue input env).zeroExtend target := by
  apply trustIrWordExt
  intro i
  rw [WordCode.resize, WordCode.route_value_bit _ _ _ bound]
  by_cases h : i.val < source
  · simp only [resizePositions, dif_pos h, Option.elim]
    simpa [trustIrWidthLemma BitVec.getLsb_zeroExtend BitVec.getLsbD_setWidth, i.isLt] using (wordValue_bit input env ⟨i.val, h⟩).symm
  · simp [resizePositions, h, trustIrWidthLemma BitVec.getLsb_zeroExtend BitVec.getLsbD_setWidth, trustIrWidthLemma BitVec.getLsb_ge BitVec.getLsbD_of_ge, show source ≤ i.val by omega]

def extractPositions (source target start : Nat) (i : Fin target) : Option (Fin source) :=
  if h : start + i.val < source then some ⟨start + i.val, h⟩ else none

/-- Extract exactly target low-to-high bits starting at start; outside the
original word is zero, and the empty result is represented without fake bits. -/
def WordCode.extract {source : Nat} (target start : Nat) (input : Fin source → Nat) (next : Nat) : WordCode target :=
  WordCode.route input (extractPositions source target start) next

theorem WordCode.extract_check {source : Nat} (target start : Nat) (input : Fin source → Nat) (next : Nat)
    (bound : ∀ i, input i < next) : (WordCode.extract target start input next).check next = true :=
  WordCode.route_check _ _ _ bound

theorem WordCode.extract_value {source : Nat} (target start : Nat) (input : Fin source → Nat) (next : Nat)
    (bound : ∀ i, input i < next) (env : Assignment) :
    (WordCode.extract target start input next).value env =
      BitVec.extractLsb' start target (wordValue input env) := by
  apply trustIrWordExt
  intro i
  rw [WordCode.extract, WordCode.route_value_bit _ _ _ bound]
  have bit : (trustIrWordBit (BitVec.extractLsb' start target (wordValue input env))) i.val =
      (trustIrWordBit (wordValue input env)) (start + i.val) := by
    trustIrCompilerProof {
      simp [BitVec.extractLsb', BitVec.getLsb, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, i.isLt]
    } {
      simp [BitVec.extractLsb', BitVec.getLsbD, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, i.isLt]
    }
  rw [bit]
  by_cases h : start + i.val < source
  · simp only [extractPositions, dif_pos h, Option.elim]
    exact (wordValue_bit input env ⟨start + i.val, h⟩).symm
  · simp [extractPositions, h, trustIrWidthLemma BitVec.getLsb_ge BitVec.getLsbD_of_ge, show source ≤ start + i.val by omega]

def signPositions (source target : Nat) (i : Fin target) : Option (Fin source) :=
  if h : i.val < source then some ⟨i.val, h⟩
  else if positive : 0 < source then some ⟨source-1, by omega⟩ else none

def WordCode.signExtend {source : Nat} (target : Nat) (input : Fin source → Nat) (next : Nat) : WordCode target :=
  WordCode.route input (signPositions source target) next

theorem WordCode.signExtend_check {source : Nat} (target : Nat) (input : Fin source → Nat) (next : Nat)
    (bound : ∀ i, input i < next) : (WordCode.signExtend target input next).check next = true :=
  WordCode.route_check _ _ _ bound

theorem WordCode.signExtend_value {source : Nat} (target : Nat) (input : Fin source → Nat) (next : Nat)
    (wide : source ≤ target) (bound : ∀ i, input i < next) (env : Assignment) :
    (WordCode.signExtend target input next).value env = (wordValue input env).signExtend target := by
  rw [word_signExtend target _ wide]
  apply trustIrWordExt
  intro i
  rw [WordCode.signExtend, WordCode.route_value_bit _ _ _ bound]
  cases source with
  | zero =>
    simp [signPositions, Nat.not_lt_zero, BitVec.msb, BitVec.getMsb, trustIrWidthLemma BitVec.getLsb_zeroExtend BitVec.getLsbD_setWidth,
      trustIrWidthLemma BitVec.getLsb_ge BitVec.getLsbD_of_ge, i.isLt]
  | succ source =>
    have sign : env (input ⟨source, by omega⟩) = (wordValue input env).msb := by
      rw [trustIrWidthLemma BitVec.msb_eq_getLsb_last BitVec.msb_eq_getLsbD_last]
      simpa using (wordValue_bit input env ⟨source, by omega⟩).symm
    by_cases h : i.val < source+1
    · simp only [signPositions, dif_pos h, Option.elim]
      rw [← wordValue_bit input env ⟨i.val, h⟩]
      cases s : (wordValue input env).msb <;>
        simp [s, trustIrWidthLemma BitVec.getLsb_zeroExtend BitVec.getLsbD_setWidth, trustIrWidthLemma BitVec.getLsb_not BitVec.getLsbD_not, i.isLt, h]
    · have outside : source+1 ≤ i.val := by omega
      simp only [signPositions, dif_neg h, show 0 < source+1 by omega, dite_true,
        Nat.add_sub_cancel, Option.elim]
      rw [sign]
      cases s : (wordValue input env).msb <;>
        simp [s, trustIrWidthLemma BitVec.getLsb_zeroExtend BitVec.getLsbD_setWidth, trustIrWidthLemma BitVec.getLsb_not BitVec.getLsbD_not, trustIrWidthLemma BitVec.getLsb_ge BitVec.getLsbD_of_ge, outside, i.isLt]

/-- Concatenation preserves actual low/high references and allocates no gates. -/
def WordCode.concat {highWidth lowWidth : Nat} (high : Fin highWidth → Nat) (low : Fin lowWidth → Nat) :
    WordCode (highWidth + lowWidth) :=
  ⟨[], fun i => if h : i.val < lowWidth then low ⟨i.val, h⟩ else high ⟨i.val-lowWidth, by omega⟩⟩

theorem WordCode.concat_check {highWidth lowWidth : Nat} (high : Fin highWidth → Nat)
    (low : Fin lowWidth → Nat) (next : Nat) (highBound : ∀ i, high i < next) (lowBound : ∀ i, low i < next) :
    (WordCode.concat high low).check next = true := by
  apply (WordCode.check_iff _ _).mpr
  refine ⟨.nil next, ?_⟩
  intro i
  change (if h : i.val < lowWidth then low ⟨i.val,h⟩ else high ⟨i.val-lowWidth, by omega⟩) < next+0
  split
  · exact lowBound _
  · exact highBound _

theorem WordCode.concat_value {highWidth lowWidth : Nat} (high : Fin highWidth → Nat)
    (low : Fin lowWidth → Nat) (env : Assignment) :
    (WordCode.concat high low).value env = wordValue high env ++ wordValue low env := by
  apply trustIrWordExt
  intro i
  change (trustIrWordBit (wordValue _ env)) i.val = _
  rw [wordValue_bit, trustIrWidthLemma BitVec.getLsb_append BitVec.getLsbD_append]
  by_cases h : i.val < lowWidth
  · simp only [WordCode.concat, dif_pos h, h, trustIrWidthLemma decide_True decide_true, cond_true]
    exact (wordValue_bit low env ⟨i.val,h⟩).symm
  · simp only [WordCode.concat, dif_neg h, h, trustIrWidthLemma decide_False decide_false, cond_false]
    exact (wordValue_bit high env ⟨i.val-lowWidth, by omega⟩).symm

/-- Width-indexed native operations. Sign extension carries its actual widening
constraint; resize separately handles shrinking. This is not target syntax. -/
inductive WidthOp (source target : Nat) where
  | resize : WidthOp source target
  | extract (start : Nat) : WidthOp source target
  | signExtend (wide : source ≤ target) : WidthOp source target

def WidthOp.emit {source target : Nat} (op : WidthOp source target) (input : Fin source → Nat)
    (next : Nat) : WordCode target :=
  match op with
  | .resize => WordCode.resize target input next
  | .extract start => WordCode.extract target start input next
  | .signExtend _ => WordCode.signExtend target input next

def WidthOp.eval {source target : Nat} (op : WidthOp source target) (word : BitVec source) : BitVec target :=
  match op with
  | .resize => word.zeroExtend target
  | .extract start => word.extractLsb' start target
  | .signExtend _ => word.signExtend target

theorem WidthOp.emit_check {source target : Nat} (op : WidthOp source target) (input : Fin source → Nat)
    (next : Nat) (bound : ∀ i, input i < next) : (op.emit input next).check next = true := by
  cases op with
  | resize => exact WordCode.resize_check _ _ _ bound
  | extract start => exact WordCode.extract_check _ _ _ _ bound
  | signExtend wide => exact WordCode.signExtend_check _ _ _ bound

theorem WidthOp.emit_value {source target : Nat} (op : WidthOp source target) (input : Fin source → Nat)
    (next : Nat) (bound : ∀ i, input i < next) (env : Assignment) :
    (op.emit input next).value env = op.eval (wordValue input env) := by
  cases op with
  | resize => exact WordCode.resize_value _ _ _ bound env
  | extract start => exact WordCode.extract_value _ _ _ _ bound env
  | signExtend wide => exact WordCode.signExtend_value _ _ _ wide bound env

theorem WidthOp.emit_length {source target : Nat} (op : WidthOp source target) (input : Fin source → Nat)
    (next : Nat) : (op.emit input next).gates.length = 1 := by cases op <;> rfl

def WordCode.composeWidth {source target : Nat} (op : WidthOp source target) (next : Nat)
    (child : WordCode source) : WordCode target :=
  WordCode.append child (op.emit child.bits (next + child.gates.length))

theorem WordCode.composeWidth_check {source target : Nat} (op : WidthOp source target) (next : Nat)
    (child : WordCode source) (checked : child.check next = true) :
    (WordCode.composeWidth op next child).check next = true := by
  apply WordCode.append_check _ _ _ checked
  exact op.emit_check _ _ ((WordCode.check_iff _ _).mp checked).2

theorem WordCode.composeWidth_value {source target : Nat} (op : WidthOp source target) (next : Nat)
    (child : WordCode source) (checked : child.check next = true) (env : Assignment) :
    (WordCode.composeWidth op next child).value env = op.eval (child.value env) := by
  rw [WordCode.composeWidth, WordCode.append_value, WidthOp.emit_value _ _ _ ((WordCode.check_iff _ _).mp checked).2]
  rfl

def WordCode.composeConcat {highWidth lowWidth : Nat} (_next : Nat) (high : WordCode highWidth)
    (low : WordCode lowWidth) : WordCode (highWidth+lowWidth) :=
  WordCode.append (WordCode.append high low) (WordCode.concat high.bits low.bits)

theorem WordCode.composeConcat_check {highWidth lowWidth : Nat} (next : Nat) (high : WordCode highWidth)
    (low : WordCode lowWidth) (highCheck : high.check next = true)
    (lowCheck : low.check (next + high.gates.length) = true) :
    (WordCode.composeConcat next high low).check next = true := by
  apply WordCode.append_check _ _ _ (WordCode.append_check _ _ _ highCheck lowCheck)
  apply WordCode.concat_check
  · intro i
    have before := ((WordCode.check_iff _ _).mp highCheck).2 i
    simp only [WordCode.append, List.length_append]
    omega
  · simpa [WordCode.append, Nat.add_assoc] using ((WordCode.check_iff _ _).mp lowCheck).2

theorem WordCode.composeConcat_value {highWidth lowWidth : Nat} (next : Nat) (high : WordCode highWidth)
    (low : WordCode lowWidth) (highCheck : high.check next = true)
    (lowCheck : low.check (next + high.gates.length) = true) (env : Assignment) :
    (WordCode.composeConcat next high low).value env = high.value env ++ low.value (run high.gates env) := by
  have lowValid := ((WordCode.check_iff _ _).mp lowCheck).1
  have highSame : wordValue high.bits (run (WordCode.append high low).gates env) = high.value env := by
    apply wordValue_congr
    intro i
    exact lowValid.append_preserves (next := next) (first := high.gates) env (high.bits i)
      (((WordCode.check_iff _ _).mp highCheck).2 i)
  have lowSame : wordValue low.bits (run (WordCode.append high low).gates env) = low.value (run high.gates env) := by
    rw [WordCode.append, run_append]; rfl
  rw [WordCode.composeConcat, WordCode.append_value, WordCode.concat_value, highSame, lowSame]

end TrustIr.AYGateCNF

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.route_check == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.route_value_bit == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.resize_check == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.resize_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.extract_check == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.extract_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.signExtend_check == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.signExtend_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.concat_check == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.concat_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WidthOp.emit_check == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WidthOp.emit_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.WidthOp.emit_length == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.composeWidth_check == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.composeWidth_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.composeConcat_check == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.composeConcat_value == [propext, Classical.choice, Quot.sound]
