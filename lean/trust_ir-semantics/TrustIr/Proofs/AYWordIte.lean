-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYWordWires

namespace TrustIr.AYGateCNF
open TrustIrExpr

theorem word_mask_select {width : Nat} (cond : Bool) (yes no : BitVec width) :
    (if cond then yes else BitVec.ofNat width 0) |||
      (if !cond then no else BitVec.ofNat width 0) = (if cond then yes else no) := by
  cases cond <;> apply trustIrWordExt <;> intro i <;> simp

/-- One shared condition inversion, two masked words and their disjunction. -/
def WordCode.ite {width : Nat} (cond : Nat) (yes no : Fin width → Nat) (next : Nat) : WordCode width :=
  let inverse := Code.unary .boolNot cond next
  let yesMask := WordCode.bitwise .band yes (fun _ => cond) (next + inverse.gates.length)
  let noMask := WordCode.bitwise .band no (fun _ => inverse.output)
    (next + inverse.gates.length + yesMask.gates.length)
  inverse.appendWord (WordCode.composeBitwise .bor (next + inverse.gates.length) yesMask noMask)

theorem WordCode.ite_check {width : Nat} (cond : Nat) (yes no : Fin width → Nat) (next : Nat)
    (condBound : cond < next) (yesBound : ∀ i, yes i < next) (noBound : ∀ i, no i < next) :
    (WordCode.ite cond yes no next).check next = true := by
  have inverse := Code.unary_check .boolNot cond next condBound
  apply Code.appendWord_check _ _ next inverse
  apply WordCode.composeBitwise_check
  · apply WordCode.bitwise_check
    · intro i; have before := yesBound i; change yes i < next + 1; omega
    · intro _i; change cond < next + 1; omega
  · apply WordCode.bitwise_check
    · intro i; have before := noBound i
      change no i < next + 1 + (WordCode.bitwise .band yes (fun _ => cond) (next + 1)).gates.length
      omega
    · intro _i
      change next < next + 1 + (WordCode.bitwise .band yes (fun _ => cond) (next + 1)).gates.length
      omega

theorem WordCode.ite_value {width : Nat} (cond : Nat) (yes no : Fin width → Nat) (next : Nat)
    (condBound : cond < next) (yesBound : ∀ i, yes i < next) (noBound : ∀ i, no i < next)
    (env : Assignment) : (WordCode.ite cond yes no next).value env =
      if env cond then wordValue yes env else wordValue no env := by
  let inverse := Code.unary .boolNot cond next
  let yesMask := WordCode.bitwise .band yes (fun _ => cond) (next + 1)
  let noMask := WordCode.bitwise .band no (fun _ => next) (next + 1 + yesMask.gates.length)
  have inverseCheck : inverse.check next = true := Code.unary_check .boolNot cond next condBound
  have yesLater : ∀ i, yes i < next + 1 := by intro i; have before := yesBound i; omega
  have condLater : cond < next + 1 := by omega
  have yesCheck : yesMask.check (next + 1) = true :=
    WordCode.bitwise_check .band _ _ _ yesLater (fun _ => condLater)
  have noLater : ∀ i, no i < next + 1 + yesMask.gates.length := by
    intro i; have before := noBound i; omega
  have inverseLater : next < next + 1 + yesMask.gates.length := by omega
  have noCheck : noMask.check (next + 1 + yesMask.gates.length) = true :=
    WordCode.bitwise_check .band _ _ _ noLater (fun _ => inverseLater)
  have inverseValid := ((inverse.check_iff next).mp inverseCheck).1
  have yesValid := ((yesMask.check_iff (next + 1)).mp yesCheck).1
  have bothCheck := Code.appendWord_check inverse yesMask next inverseCheck yesCheck
  have bothValid := ((WordCode.check_iff _ _).mp bothCheck).1
  have yesSame : wordValue yes (run inverse.gates env) = wordValue yes env := by
    apply wordValue_congr
    intro i
    exact (inverseValid.run_correct env).1 _ (yesBound i)
  have condSame := (inverseValid.run_correct env).1 cond condBound
  have noSame : wordValue no (run yesMask.gates (run inverse.gates env)) = wordValue no env := by
    rw [← run_append]
    apply wordValue_congr
    intro i
    exact (bothValid.run_correct env).1 _ (noBound i)
  have inverseSame : run yesMask.gates (run inverse.gates env) next = !(env cond) := by
    rw [(yesValid.run_correct (run inverse.gates env)).1 next (by omega)]
    exact Code.unary_eval .boolNot cond next env
  change (inverse.appendWord (WordCode.composeBitwise .bor (next + 1) yesMask noMask)).value env = _
  rw [Code.appendWord_value, WordCode.composeBitwise_value _ _ _ _ yesCheck noCheck,
    WordCode.mask_value yes cond (next + 1) yesLater condLater,
    WordCode.mask_value no next _ noLater inverseLater, yesSame, condSame, noSame, inverseSame]
  exact word_mask_select _ _ _

theorem WordCode.ite_length {width : Nat} (cond : Nat) (yes no : Fin width → Nat) (next : Nat) :
    (WordCode.ite cond yes no next).gates.length = 3 * width + 1 := by
  simp only [WordCode.ite, Code.appendWord, Code.unary, WordCode.composeBitwise, WordCode.append,
    WordCode.bitwise, List.length_append, tabulate_length, List.length_cons, List.length_nil]
  omega

theorem WordCode.ite_bits {width : Nat} (cond : Nat) (yes no : Fin width → Nat) (next : Nat) (i : Fin width) :
    (WordCode.ite cond yes no next).bits i = next + 1 + 2 * width + i.val := by
  simp only [WordCode.ite, Code.appendWord, Code.unary, WordCode.composeBitwise, WordCode.append,
    WordCode.bitwise, List.length_append, tabulate_length, List.length_cons, List.length_nil]
  omega

/-- Preserve the actual condition and both branch programs, then select their
recorded result wires. Child programs are not re-emitted inside the selector. -/
def WordCode.composeIte {width : Nat} (next : Nat) (cond : Code) (yes no : WordCode width) : WordCode width :=
  let prior := cond.appendWord (WordCode.append yes no)
  WordCode.append prior (WordCode.ite cond.output yes.bits no.bits (next + prior.gates.length))

private theorem ite_bounds {width : Nat} (next : Nat) (cond : Code) (yes no : WordCode width)
    (condCheck : cond.check next = true)
    (yesCheck : yes.check (next + cond.gates.length) = true)
    (noCheck : no.check (next + cond.gates.length + yes.gates.length) = true) :
    let prior := cond.appendWord (WordCode.append yes no)
    cond.output < next + prior.gates.length ∧
      (∀ i, yes.bits i < next + prior.gates.length) ∧
      (∀ i, no.bits i < next + prior.gates.length) := by
  have condBound := ((cond.check_iff next).mp condCheck).2
  obtain ⟨yesBounds, noBounds⟩ := WordCode.append_operand_bounds (next + cond.gates.length) yes no yesCheck noCheck
  simp only [Code.appendWord, WordCode.append, List.length_append] at *
  exact ⟨by omega, by intro i; have h := yesBounds i; omega,
    by intro i; have h := noBounds i; omega⟩

theorem WordCode.composeIte_check {width : Nat} (next : Nat) (cond : Code) (yes no : WordCode width)
    (condCheck : cond.check next = true)
    (yesCheck : yes.check (next + cond.gates.length) = true)
    (noCheck : no.check (next + cond.gates.length + yes.gates.length) = true) :
    (WordCode.composeIte next cond yes no).check next = true := by
  have branches := WordCode.append_check yes no (next + cond.gates.length) yesCheck noCheck
  have prior := Code.appendWord_check cond _ next condCheck branches
  obtain ⟨condBound, yesBounds, noBounds⟩ := ite_bounds next cond yes no condCheck yesCheck noCheck
  apply WordCode.append_check _ _ next prior
  exact WordCode.ite_check _ _ _ _ condBound yesBounds noBounds

theorem WordCode.composeIte_value {width : Nat} (next : Nat) (cond : Code) (yes no : WordCode width)
    (condCheck : cond.check next = true)
    (yesCheck : yes.check (next + cond.gates.length) = true)
    (noCheck : no.check (next + cond.gates.length + yes.gates.length) = true) (env : Assignment) :
    (WordCode.composeIte next cond yes no).value env =
      if cond.eval env then yes.value (run cond.gates env)
      else no.value (run (cond.appendWord yes).gates env) := by
  let prior := cond.appendWord (WordCode.append yes no)
  have branchesCheck := WordCode.append_check yes no (next + cond.gates.length) yesCheck noCheck
  have branchesValid := ((WordCode.check_iff _ _).mp branchesCheck).1
  have noValid := ((no.check_iff _).mp noCheck).1
  have condBound := ((cond.check_iff next).mp condCheck).2
  have condSame : run prior.gates env cond.output = cond.eval env :=
    branchesValid.append_preserves (next := next) (first := cond.gates) env cond.output condBound
  have yesSame : wordValue yes.bits (run prior.gates env) = yes.value (run cond.gates env) := by
    apply wordValue_congr
    intro i
    change run (cond.gates ++ (yes.gates ++ no.gates)) env (yes.bits i) = _
    rw [run_append]
    exact noValid.append_preserves (next := next + cond.gates.length) (first := yes.gates)
      (run cond.gates env) (yes.bits i) (((yes.check_iff _).mp yesCheck).2 i)
  have noSame : wordValue no.bits (run prior.gates env) = no.value (run (cond.appendWord yes).gates env) := by
    simp only [prior, Code.appendWord, WordCode.append, WordCode.value, run_append]
  obtain ⟨condLater, yesBounds, noBounds⟩ := ite_bounds next cond yes no condCheck yesCheck noCheck
  rw [WordCode.composeIte, WordCode.append_value,
    WordCode.ite_value _ _ _ _ condLater yesBounds noBounds, condSame, yesSame, noSame]

theorem WordCode.ite_target {width : Nat} (cond : Nat) (yes no : Fin width → Nat) (next : Nat)
    (condBound : cond < next) (yesBound : ∀ i, yes i < next) (noBound : ∀ i, no i < next)
    (env : Assignment) (condition : SMTTerm .bool) (yesTerm noTerm : SMTTerm (.bv width)) (target : SMTEnv)
    (condValue : env cond = condition.eval target)
    (yesValue : wordValue yes env = yesTerm.eval target) (noValue : wordValue no env = noTerm.eval target) :
    (WordCode.ite cond yes no next).value env = (SMTTerm.ite condition yesTerm noTerm).eval target := by
  rw [WordCode.ite_value cond yes no next condBound yesBound noBound env, condValue, yesValue, noValue]
  rfl

theorem WordCode.composeIte_target {width : Nat} (next : Nat) (cond : Code) (yes no : WordCode width)
    (condCheck : cond.check next = true)
    (yesCheck : yes.check (next + cond.gates.length) = true)
    (noCheck : no.check (next + cond.gates.length + yes.gates.length) = true) (env : Assignment)
    (condition : SMTTerm .bool) (yesTerm noTerm : SMTTerm (.bv width)) (target : SMTEnv)
    (condValue : cond.eval env = condition.eval target)
    (yesValue : yes.value (run cond.gates env) = yesTerm.eval target)
    (noValue : no.value (run (cond.appendWord yes).gates env) = noTerm.eval target) :
    (WordCode.composeIte next cond yes no).value env = (SMTTerm.ite condition yesTerm noTerm).eval target := by
  rw [WordCode.composeIte_value next cond yes no condCheck yesCheck noCheck env, condValue, yesValue, noValue]
  rfl

end TrustIr.AYGateCNF

#trustIrAxiomsPinned TrustIr.AYGateCNF.word_mask_select == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.ite_check == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.ite_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.WordCode.ite_length == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.WordCode.ite_bits == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.composeIte_check == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.composeIte_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.ite_target == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.composeIte_target == [propext, Quot.sound, Classical.choice]
