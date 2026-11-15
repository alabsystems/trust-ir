-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYTargetCorrect

namespace TrustIr.AYGateCNF

/-- Same zero-based variable/negation carrier as the SAT-resolution payload. -/
abbrev Lit := Nat × Bool
abbrev Clause := List Lit
abbrev CNF := List Clause
abbrev Assignment := Nat → Bool

def Lit.eval (env : Assignment) (literal : Lit) : Bool :=
  if literal.2 then !(env literal.1) else env literal.1

def Clause.eval (env : Assignment) (clause : Clause) : Bool :=
  clause.any (Lit.eval env)

def CNF.eval (env : Assignment) (clauses : CNF) : Bool :=
  clauses.all (Clause.eval env)

/-- All nine definitional bit gates in the pinned AY proof carrier. Arity is
structural; malformed input counts cannot construct a gate. -/
inductive Gate where
  | xor2 (out a b : Nat)
  | and2 (out a b : Nat)
  | or2 (out a b : Nat)
  | xor3 (out a b c : Nat)
  | fullAdderCarry (out a b c : Nat)
  | not (out a : Nat)
  | constTrue (out : Nat)
  | constFalse (out : Nat)
  | xnorEq (out a b : Nat)
  deriving Repr

def Gate.output : Gate → Nat
  | .xor2 out _ _ => out
  | .and2 out _ _ => out
  | .or2 out _ _ => out
  | .xor3 out _ _ _ => out
  | .fullAdderCarry out _ _ _ => out
  | .not out _ => out
  | .constTrue out => out
  | .constFalse out => out
  | .xnorEq out _ _ => out

def Gate.eval (env : Assignment) : Gate → Bool
  | .xor2 _ a b => xor (env a) (env b)
  | .and2 _ a b => env a && env b
  | .or2 _ a b => env a || env b
  | .xor3 _ a b c => xor (xor (env a) (env b)) (env c)
  | .fullAdderCarry _ a b c => (env a && env b) || (env c && xor (env a) (env b))
  | .not _ a => !(env a)
  | .constTrue _ => true
  | .constFalse _ => false
  | .xnorEq _ a b => !(xor (env a) (env b))

/-- Canonical positional row-blocking clauses: each clause forbids one row
violating the gate equation. Repeated variable ids are retained, so aliases need
no freshness assumption. These clauses are independent of Gate.eval. -/
def Gate.clauses : Gate → CNF
  | .xor2 out a b =>
    [[(out, false), (a, false), (b, true)],
     [(out, false), (a, true), (b, false)],
     [(out, true), (a, false), (b, false)],
     [(out, true), (a, true), (b, true)]]
  | .and2 out a b =>
    [[(out, false), (a, true), (b, true)],
     [(out, true), (a, false), (b, false)],
     [(out, true), (a, false), (b, true)],
     [(out, true), (a, true), (b, false)]]
  | .or2 out a b =>
    [[(out, false), (a, false), (b, true)],
     [(out, false), (a, true), (b, false)],
     [(out, false), (a, true), (b, true)],
     [(out, true), (a, false), (b, false)]]
  | .xor3 out a b c =>
    [[(out, false), (a, false), (b, false), (c, true)],
     [(out, false), (a, false), (b, true), (c, false)],
     [(out, false), (a, true), (b, false), (c, false)],
     [(out, false), (a, true), (b, true), (c, true)],
     [(out, true), (a, false), (b, false), (c, false)],
     [(out, true), (a, false), (b, true), (c, true)],
     [(out, true), (a, true), (b, false), (c, true)],
     [(out, true), (a, true), (b, true), (c, false)]]
  | .fullAdderCarry out a b c =>
    [[(out, false), (a, false), (b, true), (c, true)],
     [(out, false), (a, true), (b, false), (c, true)],
     [(out, false), (a, true), (b, true), (c, false)],
     [(out, false), (a, true), (b, true), (c, true)],
     [(out, true), (a, false), (b, false), (c, false)],
     [(out, true), (a, false), (b, false), (c, true)],
     [(out, true), (a, false), (b, true), (c, false)],
     [(out, true), (a, true), (b, false), (c, false)]]
  | .not out a =>
    [[(out, false), (a, false)],
     [(out, true), (a, true)]]
  | .constTrue out =>
    [[(out, false)]]
  | .constFalse out =>
    [[(out, true)]]
  | .xnorEq out a b =>
    [[(out, false), (a, false), (b, false)],
     [(out, false), (a, true), (b, true)],
     [(out, true), (a, false), (b, true)],
     [(out, true), (a, true), (b, false)]]

/-- Exact gate equivalence for every assignment, including aliased input/output
ids. No solver answer, gate provenance or CNF claim is assumed. -/
theorem Gate.clauses_correct (gate : Gate) (env : Assignment) :
    CNF.eval env gate.clauses = true ↔ env gate.output = gate.eval env := by
  cases gate with
  | xor2 out a b =>
    cases hout : env out <;> cases ha : env a <;> cases hb : env b <;>
      simp [Gate.clauses, Gate.output, Gate.eval, CNF.eval, Clause.eval, Lit.eval,
        hout, ha, hb, List.all, List.any]
  | and2 out a b =>
    cases hout : env out <;> cases ha : env a <;> cases hb : env b <;>
      simp [Gate.clauses, Gate.output, Gate.eval, CNF.eval, Clause.eval, Lit.eval,
        hout, ha, hb, List.all, List.any]
  | or2 out a b =>
    cases hout : env out <;> cases ha : env a <;> cases hb : env b <;>
      simp [Gate.clauses, Gate.output, Gate.eval, CNF.eval, Clause.eval, Lit.eval,
        hout, ha, hb, List.all, List.any]
  | xor3 out a b c =>
    cases hout : env out <;> cases ha : env a <;> cases hb : env b <;> cases hc : env c <;>
      simp [Gate.clauses, Gate.output, Gate.eval, CNF.eval, Clause.eval, Lit.eval,
        hout, ha, hb, hc, List.all, List.any]
  | fullAdderCarry out a b c =>
    cases hout : env out <;> cases ha : env a <;> cases hb : env b <;> cases hc : env c <;>
      simp [Gate.clauses, Gate.output, Gate.eval, CNF.eval, Clause.eval, Lit.eval,
        hout, ha, hb, hc, List.all, List.any]
  | not out a =>
    cases hout : env out <;> cases ha : env a <;>
      simp [Gate.clauses, Gate.output, Gate.eval, CNF.eval, Clause.eval, Lit.eval,
        hout, ha, List.all, List.any]
  | constTrue out =>
    cases hout : env out <;>
      simp [Gate.clauses, Gate.output, Gate.eval, CNF.eval, Clause.eval, Lit.eval,
        hout, List.all, List.any]
  | constFalse out =>
    cases hout : env out <;>
      simp [Gate.clauses, Gate.output, Gate.eval, CNF.eval, Clause.eval, Lit.eval,
        hout, List.all, List.any]
  | xnorEq out a b =>
    cases hout : env out <;> cases ha : env a <;> cases hb : env b <;>
      simp [Gate.clauses, Gate.output, Gate.eval, CNF.eval, Clause.eval, Lit.eval,
        hout, ha, hb, List.all, List.any]

theorem CNF.eval_append (env : Assignment) (left right : CNF) :
    CNF.eval env (left ++ right) = (CNF.eval env left && CNF.eval env right) := by
  induction left with
  | nil => rfl
  | cons head tail ih => simp_all [CNF.eval, List.all, Bool.and_assoc]

/-- Composition retains exactly all gate equations. A topology proof must still
establish which word operation these gates implement. -/
def encode (gates : List Gate) : CNF :=
  gates.foldr (fun head rest => head.clauses ++ rest) []

theorem encode_correct (gates : List Gate) (env : Assignment) :
    CNF.eval env (encode gates) = true ↔
      ∀ gate ∈ gates, env gate.output = gate.eval env := by
  induction gates with
  | nil => simp [encode, CNF.eval, List.all]
  | cons head tail ih =>
    change CNF.eval env (head.clauses ++ encode tail) = true ↔ _
    rw [CNF.eval_append, Bool.and_eq_true, Gate.clauses_correct, ih]
    constructor
    · rintro ⟨first, rest⟩ gate member
      cases member with
      | head => exact first
      | tail _ member => exact rest gate member
    · intro all
      exact ⟨all head (List.Mem.head _), fun gate member => all gate (List.Mem.tail _ member)⟩

/-- The asserted CNF includes the actual output literal as a unit clause. -/
def assertOutput (gates : List Gate) (output : Nat) : CNF :=
  encode gates ++ [[(output, false)]]

theorem assertOutput_correct (gates : List Gate) (output : Nat) (env : Assignment) :
    CNF.eval env (assertOutput gates output) = true ↔
      (∀ gate ∈ gates, env gate.output = gate.eval env) ∧ env output = true := by
  rw [assertOutput, CNF.eval_append, Bool.and_eq_true, encode_correct]
  simp [CNF.eval, Clause.eval, Lit.eval, List.all, List.any]

/-- The two full-adder gates encode exact one-bit addition with carry. -/
theorem fullAdder_numeric (a b c : Bool) :
    a.toNat + b.toNat + c.toNat =
      (xor (xor a b) c).toNat + 2 * ((a && b) || (c && xor a b)).toNat := by
  cases a <;> cases b <;> cases c <;> decide

end TrustIr.AYGateCNF

/-- info: 'TrustIr.AYGateCNF.Gate.clauses_correct' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.Gate.clauses_correct

/-- info: 'TrustIr.AYGateCNF.CNF.eval_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.CNF.eval_append

/-- info: 'TrustIr.AYGateCNF.encode_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.encode_correct

/-- info: 'TrustIr.AYGateCNF.assertOutput_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.assertOutput_correct

/-- info: 'TrustIr.AYGateCNF.fullAdder_numeric' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.fullAdder_numeric
