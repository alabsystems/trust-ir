-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYFreshGates
import TrustIr.Proofs.AYBufferedGates

namespace TrustIr.AYGateCNF
open TrustIrExpr

/-- Concatenation preserves exact fresh allocation, with the suffix starting
at the prefix's actual allocation frontier. -/
theorem Valid.append {next : Nat} {first second : List Gate} (firstValid : Valid next first)
    (suffix : Valid (next + first.length) second) : Valid next (first ++ second) := by
  induction firstValid with
  | nil next => simpa using suffix
  | @cons next gate tail output inputs _rest ih =>
    apply Valid.cons output inputs
    apply ih
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using suffix

theorem run_append (first second : List Gate) (env : Assignment) :
    run (first ++ second) env = run second (run first env) := by
  induction first generalizing env with
  | nil => rfl
  | cons head _tail ih => exact ih (head.apply env)

/-- A fresh suffix cannot alter any already allocated wire. -/
theorem Valid.append_preserves {next : Nat} {first second : List Gate}
    (suffix : Valid (next + first.length) second) (env : Assignment)
    (id : Nat) (bound : id < next + first.length) :
    run (first ++ second) env id = run first env id := by
  rw [run_append]
  exact (suffix.run_correct (run first env)).1 id bound

/-- A compiled fragment records its actual gates and result wire. -/
structure Code where
  gates : List Gate
  output : Nat
  deriving Repr

def Code.check (code : Code) (next : Nat) : Bool :=
  checkProgram next code.gates && decide (code.output < next + code.gates.length)

def Code.eval (code : Code) (env : Assignment) : Bool := run code.gates env code.output

theorem Code.check_iff (code : Code) (next : Nat) :
    code.check next = true ↔ Valid next code.gates ∧ code.output < next + code.gates.length := by
  simp [Code.check, checkProgram_iff]

def Code.constant (value : Bool) (next : Nat) : Code :=
  ⟨[if value then .constTrue next else .constFalse next], next⟩

def Code.unary : SMTUnary .bool .bool → Nat → Nat → Code
  | .boolNot, input, next => ⟨[.not next input], next⟩

def Code.binary : SMTBinary .bool .bool → Nat → Nat → Nat → Code
  | .boolAnd, left, right, next => ⟨[.and2 next left right], next⟩
  | .boolOr, left, right, next => ⟨[.or2 next left right], next⟩
  | .boolImpl, left, right, next => ⟨[.not next left, .or2 (next + 1) next right], next + 1⟩
  | .eq .bool, left, right, next => ⟨[.xnorEq next left right], next⟩
  | .distinct .bool, left, right, next => ⟨[.xor2 next left right], next⟩

def Code.ite (cond yes no next : Nat) : Code :=
  ⟨[.not next cond, .and2 (next + 1) cond yes,
    .and2 (next + 2) next no, .or2 (next + 3) (next + 1) (next + 2)], next + 3⟩

theorem Code.constant_check (value : Bool) (next : Nat) :
    (Code.constant value next).check next = true := by
  trustIrCompilerProof {
    cases value <;> simp [Code.constant, Code.check, checkProgram, List.foldr,
      Gate.output, Gate.inputs, List.all]
  } {
    cases value <;> apply (Code.check_iff _ _).mpr
    all_goals refine ⟨Valid.cons rfl ?_ (Valid.nil _), Nat.lt_succ_self next⟩
    all_goals intro id member; cases member
  }

theorem Code.unary_check (op : SMTUnary .bool .bool) (input next : Nat) (bound : input < next) :
    (Code.unary op input next).check next = true := by
  trustIrCompilerProof {
    cases op <;> simp [Code.unary, Code.check, checkProgram, List.foldr,
      Gate.output, Gate.inputs, List.all, bound]
  } {
    cases op
    apply (Code.check_iff _ _).mpr
    refine ⟨Valid.cons rfl ?_ (Valid.nil _), Nat.lt_succ_self next⟩
    intro id member
    cases member with
    | head => exact bound
    | tail _ member => cases member
  }

theorem Code.binary_check (op : SMTBinary .bool .bool) (left right next : Nat)
    (leftBound : left < next) (rightBound : right < next) :
    (Code.binary op left right next).check next = true := by
  cases op <;> simp [Code.binary, Code.check, checkProgram, List.foldr,
    Gate.output, Gate.inputs, List.all, leftBound, rightBound]
  omega

theorem Code.ite_check (cond yes no next : Nat)
    (condBound : cond < next) (yesBound : yes < next) (noBound : no < next) :
    (Code.ite cond yes no next).check next = true := by
  simp [Code.ite, Code.check, checkProgram, List.foldr, Gate.output, Gate.inputs,
    List.all, condBound, yesBound, noBound]
  constructor <;> omega

theorem Code.constant_eval (value : Bool) (next : Nat) (env : Assignment) :
    (Code.constant value next).eval env = value := by
  cases value with
  | false => change (if next = next then false else env next) = false; exact if_pos rfl
  | true => change (if next = next then true else env next) = true; exact if_pos rfl

theorem Code.unary_eval (op : SMTUnary .bool .bool) (input next : Nat) (env : Assignment) :
    (Code.unary op input next).eval env = op.eval (env input) := by
  cases op
  change (if next = next then !(env input) else env next) = !(env input)
  exact if_pos rfl

theorem Code.binary_eval (op : SMTBinary .bool .bool) (left right next : Nat)
    (leftBound : left < next) (rightBound : right < next) (env : Assignment) :
    (Code.binary op left right next).eval env = op.eval (env left) (env right) := by
  have leftFresh : left ≠ next := by omega
  have rightFresh : right ≠ next := by omega
  cases op <;> cases hleft : env left <;> cases hright : env right <;>
    simp [Code.binary, Code.eval, run, List.foldl, Gate.apply, Gate.output,
      Gate.eval, SMTBinary.eval, SMTSort.coreEq, leftFresh, rightFresh, hleft, hright]

theorem Code.ite_eval (cond yes no next : Nat)
    (condBound : cond < next) (yesBound : yes < next) (noBound : no < next) (env : Assignment) :
    (Code.ite cond yes no next).eval env = if env cond then env yes else env no := by
  have condFresh : cond ≠ next := by omega
  have yesFresh : yes ≠ next := by omega
  have noFresh : no ≠ next := by omega
  have noNext : no ≠ next + 1 := by omega
  have nextNe : next + 1 ≠ next := by omega
  have zeroOne : next ≠ next + 1 := Ne.symm nextNe
  have twoNe : next + 2 ≠ next := by omega
  have twoOne : next + 2 ≠ next + 1 := by omega
  cases hc : env cond <;> cases hy : env yes <;> cases hn : env no <;>
    simp [Code.ite, Code.eval, run, List.foldl, Gate.apply, Gate.output, Gate.eval,
      condFresh, yesFresh, noFresh, noNext, nextNe, zeroOne, twoNe, twoOne, hc, hy, hn]

def Code.append (first second : Code) : Code := ⟨first.gates ++ second.gates, second.output⟩

theorem Code.append_check (first second : Code) (next : Nat)
    (firstCheck : first.check next = true)
    (secondCheck : second.check (next + first.gates.length) = true) :
    (Code.append first second).check next = true := by
  obtain ⟨firstValid, _firstBound⟩ := (first.check_iff next).mp firstCheck
  obtain ⟨secondValid, secondBound⟩ := (second.check_iff _).mp secondCheck
  apply (Code.check_iff _ _).mpr
  refine ⟨firstValid.append secondValid, ?_⟩
  simpa [Code.append, Nat.add_assoc] using secondBound

theorem Code.append_eval (first second : Code) (env : Assignment) :
    (Code.append first second).eval env = second.eval (run first.gates env) :=
  congrFun (run_append first.gates second.gates env) second.output

def Code.composeUnary (op : SMTUnary .bool .bool) (next : Nat) (child : Code) : Code :=
  Code.append child (Code.unary op child.output (next + child.gates.length))

theorem Code.composeUnary_check (op : SMTUnary .bool .bool) (next : Nat) (child : Code)
    (checked : child.check next = true) : (Code.composeUnary op next child).check next = true := by
  apply Code.append_check child _ next checked
  exact Code.unary_check op child.output _ ((child.check_iff next).mp checked).2

theorem Code.composeUnary_eval (op : SMTUnary .bool .bool) (next : Nat) (child : Code)
    (env : Assignment) : (Code.composeUnary op next child).eval env = op.eval (child.eval env) := by
  rw [Code.composeUnary, Code.append_eval, Code.unary_eval]
  rfl

def Code.composeBinary (op : SMTBinary .bool .bool) (next : Nat) (left right : Code) : Code :=
  let both := Code.append left right
  Code.append both (Code.binary op left.output right.output (next + both.gates.length))

private theorem binary_bounds (next : Nat) (left right : Code)
    (leftCheck : left.check next = true)
    (rightCheck : right.check (next + left.gates.length) = true) :
    left.output < next + (Code.append left right).gates.length ∧
      right.output < next + (Code.append left right).gates.length := by
  have leftBound := ((left.check_iff next).mp leftCheck).2
  have rightBound := ((right.check_iff _).mp rightCheck).2
  simp only [Code.append, List.length_append]
  constructor <;> omega

theorem Code.composeBinary_check (op : SMTBinary .bool .bool) (next : Nat) (left right : Code)
    (leftCheck : left.check next = true)
    (rightCheck : right.check (next + left.gates.length) = true) :
    (Code.composeBinary op next left right).check next = true := by
  obtain ⟨leftBound, rightBound⟩ := binary_bounds next left right leftCheck rightCheck
  apply Code.append_check _ _ next (Code.append_check left right next leftCheck rightCheck)
  exact Code.binary_check op left.output right.output _ leftBound rightBound

/-- Child results retain their exact meanings through later allocations. -/
theorem Code.composeBinary_eval (op : SMTBinary .bool .bool) (next : Nat) (left right : Code)
    (leftCheck : left.check next = true)
    (rightCheck : right.check (next + left.gates.length) = true) (env : Assignment) :
    (Code.composeBinary op next left right).eval env =
      op.eval (left.eval env) (right.eval (run left.gates env)) := by
  obtain ⟨leftBound, rightBound⟩ := binary_bounds next left right leftCheck rightCheck
  have rightValid := ((right.check_iff _).mp rightCheck).1
  have preserved := rightValid.append_preserves (next := next) (first := left.gates)
    env left.output ((left.check_iff next).mp leftCheck).2
  have rightValue := congrFun (run_append left.gates right.gates env) right.output
  rw [Code.composeBinary, Code.append_eval,
    Code.binary_eval op left.output right.output _ leftBound rightBound]
  change op.eval (run (left.gates ++ right.gates) env left.output)
    (run (left.gates ++ right.gates) env right.output) = _
  rw [preserved, rightValue]
  rfl

/-- Compositional refinement reaches the actual typed target constructor.
Only child refinements are premises; the composed gate result is proved. -/
theorem Code.composeBinary_target (op : SMTBinary .bool .bool) (next : Nat) (left right : Code)
    (leftCheck : left.check next = true)
    (rightCheck : right.check (next + left.gates.length) = true)
    (env : Assignment) (leftTerm rightTerm : SMTTerm .bool) (target : SMTEnv)
    (leftValue : left.eval env = leftTerm.eval target)
    (rightValue : right.eval (run left.gates env) = rightTerm.eval target) :
    (Code.composeBinary op next left right).eval env =
      (SMTTerm.binary op leftTerm rightTerm).eval target := by
  rw [Code.composeBinary_eval op next left right leftCheck rightCheck env, leftValue, rightValue]
  rfl

def Code.composeIte (next : Nat) (cond yes no : Code) : Code :=
  let first := Code.append cond yes
  let all := Code.append first no
  Code.append all (Code.ite cond.output yes.output no.output (next + all.gates.length))

private theorem ite_bounds (next : Nat) (cond yes no : Code)
    (condCheck : cond.check next = true)
    (yesCheck : yes.check (next + cond.gates.length) = true)
    (noCheck : no.check (next + (Code.append cond yes).gates.length) = true) :
    let all := Code.append (Code.append cond yes) no
    cond.output < next + all.gates.length ∧ yes.output < next + all.gates.length ∧
      no.output < next + all.gates.length := by
  have condBound := ((cond.check_iff next).mp condCheck).2
  have yesBound := ((yes.check_iff _).mp yesCheck).2
  have noBound := ((no.check_iff _).mp noCheck).2
  simp only [Code.append, List.length_append] at *
  exact ⟨by omega, by omega, by omega⟩

theorem Code.composeIte_check (next : Nat) (cond yes no : Code)
    (condCheck : cond.check next = true)
    (yesCheck : yes.check (next + cond.gates.length) = true)
    (noCheck : no.check (next + (Code.append cond yes).gates.length) = true) :
    (Code.composeIte next cond yes no).check next = true := by
  obtain ⟨condBound, yesBound, noBound⟩ := ite_bounds next cond yes no condCheck yesCheck noCheck
  apply Code.append_check _ _ next
    (Code.append_check _ _ next (Code.append_check _ _ next condCheck yesCheck) noCheck)
  exact Code.ite_check _ _ _ _ condBound yesBound noBound

theorem Code.composeIte_eval (next : Nat) (cond yes no : Code)
    (condCheck : cond.check next = true)
    (yesCheck : yes.check (next + cond.gates.length) = true)
    (noCheck : no.check (next + (Code.append cond yes).gates.length) = true) (env : Assignment) :
    (Code.composeIte next cond yes no).eval env =
      if cond.eval env then yes.eval (run cond.gates env)
      else no.eval (run (Code.append cond yes).gates env) := by
  obtain ⟨condBound, yesBound, noBound⟩ := ite_bounds next cond yes no condCheck yesCheck noCheck
  obtain ⟨condMiddle, yesMiddle⟩ := binary_bounds next cond yes condCheck yesCheck
  have yesValid := ((yes.check_iff _).mp yesCheck).1
  have noValid := ((no.check_iff _).mp noCheck).1
  have condPrior := yesValid.append_preserves (next := next) (first := cond.gates)
    env cond.output ((cond.check_iff next).mp condCheck).2
  have condLater := noValid.append_preserves (next := next) (first := (Code.append cond yes).gates)
    env cond.output condMiddle
  have yesLater := noValid.append_preserves (next := next) (first := (Code.append cond yes).gates)
    env yes.output yesMiddle
  have yesValue := congrFun (run_append cond.gates yes.gates env) yes.output
  have noValue := congrFun (run_append (Code.append cond yes).gates no.gates env) no.output
  rw [Code.composeIte, Code.append_eval, Code.ite_eval _ _ _ _ condBound yesBound noBound]
  change (if run ((Code.append cond yes).gates ++ no.gates) env cond.output then
    run ((Code.append cond yes).gates ++ no.gates) env yes.output else
    run ((Code.append cond yes).gates ++ no.gates) env no.output) = _
  change run (Code.append cond yes).gates env cond.output = cond.eval env at condPrior
  change run (Code.append cond yes).gates env yes.output = yes.eval (run cond.gates env) at yesValue
  rw [condLater, condPrior, yesLater, yesValue, noValue]
  rfl

theorem Code.composeIte_target (next : Nat) (cond yes no : Code)
    (condCheck : cond.check next = true)
    (yesCheck : yes.check (next + cond.gates.length) = true)
    (noCheck : no.check (next + (Code.append cond yes).gates.length) = true)
    (env : Assignment) (condTerm yesTerm noTerm : SMTTerm .bool) (target : SMTEnv)
    (condValue : cond.eval env = condTerm.eval target)
    (yesValue : yes.eval (run cond.gates env) = yesTerm.eval target)
    (noValue : no.eval (run (Code.append cond yes).gates env) = noTerm.eval target) :
    (Code.composeIte next cond yes no).eval env = (SMTTerm.ite condTerm yesTerm noTerm).eval target := by
  rw [Code.composeIte_eval next cond yes no condCheck yesCheck noCheck env,
    condValue, yesValue, noValue]
  rfl

/-- Every checked fragment has exact asserted-CNF model semantics. -/
theorem Code.asserted_iff (code : Code) (next : Nat) (checked : code.check next = true)
    (env : Assignment) :
    (∃ model : Assignment, (∀ id, id < next → model id = env id) ∧
      CNF.eval model (assertOutput code.gates code.output) = true) ↔ code.eval env = true := by
  obtain ⟨valid, bound⟩ := (code.check_iff next).mp checked
  exact valid.asserted_iff env code.output bound

/-- A refutation of this exact emitted CNF is equivalent to universal fragment
refutation; model existence is provided by fresh construction. -/
theorem Code.unsat_iff (code : Code) (next : Nat) (checked : code.check next = true) :
    (∀ model : Assignment, CNF.eval model (assertOutput code.gates code.output) = false) ↔
      ∀ env : Assignment, code.eval env = false := by
  constructor
  · intro refuted env
    apply Bool.eq_false_iff.mpr
    intro accepted
    obtain ⟨model, _agree, clauses⟩ := (code.asserted_iff next checked env).mpr accepted
    rw [refuted model] at clauses
    cases clauses
  · intro refuted model
    apply Bool.eq_false_iff.mpr
    intro clauses
    have accepted := (code.asserted_iff next checked model).mp ⟨model, fun _ _ => rfl, clauses⟩
    rw [refuted model] at accepted
    cases accepted

/-- Reference an existing wire without allocating or copying it. -/
def Code.wire (id : Nat) : Code := ⟨[], id⟩

theorem Code.wire_check (id next : Nat) : (Code.wire id).check next = true ↔ id < next := by
  simp [Code.wire, Code.check, checkProgram, List.foldr]

theorem Code.wire_eval (id : Nat) (env : Assignment) : (Code.wire id).eval env = env id := rfl

theorem Code.constant_target (value : Bool) (next : Nat) (env : Assignment) (target : SMTEnv) :
    (Code.constant value next).eval env = (SMTTerm.boolConst value).eval target :=
  Code.constant_eval value next env

theorem Code.composeUnary_target (op : SMTUnary .bool .bool) (next : Nat) (child : Code)
    (env : Assignment) (term : SMTTerm .bool) (target : SMTEnv)
    (childValue : child.eval env = term.eval target) :
    (Code.composeUnary op next child).eval env = (SMTTerm.unary op term).eval target := by
  rw [Code.composeUnary_eval, childValue]
  rfl

/-- Boolean checked evaluation uses the same proved buffered execution as words. -/
def Code.checkedEval (code : Code) (next : Nat) (env : Assignment) : Option Bool :=
  if code.check next then some (runBuffered next code.gates env code.output) else none

theorem Code.checkedEval_eq_some (code : Code) (next : Nat) (env : Assignment) (result : Bool) :
    code.checkedEval next env = some result ↔ code.check next = true ∧ code.eval env = result := by
  by_cases checked : code.check next = true
  · have program := (checkProgram_iff next code.gates).mpr ((code.check_iff next).mp checked).1
    have same : runBuffered next code.gates env code.output = code.eval env := by
      rw [runBuffered_eq_run next code.gates program]
      rfl
    simp [Code.checkedEval, checked, same]
  · simp [Code.checkedEval, checked]

theorem Code.checkedEval_asserted_iff (code : Code) (next : Nat) (checked : code.check next = true)
    (env : Assignment) : code.checkedEval next env = some true ↔
      ∃ model : Assignment, (∀ id, id < next → model id = env id) ∧
        CNF.eval model (assertOutput code.gates code.output) = true := by
  have accepted : code.checkedEval next env = some true ↔ code.eval env = true := by
    rw [Code.checkedEval_eq_some]
    simp only [checked, true_and]
  exact accepted.trans (code.asserted_iff next checked env).symm

theorem Code.checkedEval_unsat_iff (code : Code) (next : Nat) (checked : code.check next = true) :
    (∀ model : Assignment, CNF.eval model (assertOutput code.gates code.output) = false) ↔
      ∀ env : Assignment, code.checkedEval next env = some false := by
  rw [code.unsat_iff next checked]
  constructor
  · intro refuted env
    exact (code.checkedEval_eq_some next env false).mpr ⟨checked, refuted env⟩
  · intro refuted env
    exact ((code.checkedEval_eq_some next env false).mp (refuted env)).2

end TrustIr.AYGateCNF

/-- info: 'TrustIr.AYGateCNF.Valid.append' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.Valid.append

/-- info: 'TrustIr.AYGateCNF.run_append' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.run_append

#trustIrAxiomsPinned TrustIr.AYGateCNF.Valid.append_preserves == [Quot.sound, propext, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.check_iff == [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.constant_check == [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.unary_check == [Quot.sound, propext]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.binary_check == [Quot.sound, propext, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.ite_check == [Quot.sound, propext, Classical.choice]

/-- info: 'TrustIr.AYGateCNF.Code.constant_eval' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.Code.constant_eval

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.unary_eval == [propext]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.binary_eval == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.ite_eval == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.append_check == [propext, Quot.sound]

/-- info: 'TrustIr.AYGateCNF.Code.append_eval' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.Code.append_eval

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.composeUnary_check == [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.composeUnary_eval == [propext]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.composeBinary_check == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.composeBinary_eval == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.composeBinary_target == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.composeIte_check == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.composeIte_eval == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.composeIte_target == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsPinned TrustIr.AYGateCNF.Code.asserted_iff == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.Code.unsat_iff == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.wire_check == [propext]

/-- info: 'TrustIr.AYGateCNF.Code.wire_eval' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.Code.wire_eval

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.constant_target == [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.composeUnary_target == [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.checkedEval_eq_some == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.checkedEval_asserted_iff == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.checkedEval_unsat_iff == [propext, Quot.sound, Classical.choice]
