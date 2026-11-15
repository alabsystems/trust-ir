-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYSMTTarget

namespace TrustIr.TrustIrExpr

def SMTTerm.checkIdentifier (symbol : String) : Bool :=
  match StringCompat.toList symbol with
  | first :: second :: payload => decide (first = 'v') && decide (second = '_') &&
      payload.all (fun c => decide (c = '_' ∨ (48 ≤ c.toNat ∧ c.toNat ≤ 57)))
  | _ => false

/-- The complete executable checker accepts exactly the original character grammar. -/
theorem SMTTerm.checkIdentifier_function_eq_standard : SMTTerm.checkIdentifier =
    fun symbol => match symbol.data with
      | first :: second :: payload => decide (first = 'v') && decide (second = '_') &&
          payload.all (fun c => decide (c = '_' ∨ (48 ≤ c.toNat ∧ c.toNat ≤ 57)))
      | _ => false := by
  trustIrCompilerProof { rfl } {
    funext symbol
    unfold SMTTerm.checkIdentifier
    rw [StringCompat.toList_eq_standard]
    rfl
  }
trustIrString48 #trustIrAxiomsExact SMTTerm.checkIdentifier_function_eq_standard == []
trustIrString430 #trustIrAxiomsExact SMTTerm.checkIdentifier_function_eq_standard == [propext, Classical.choice, Quot.sound]

theorem SMTTerm.checkIdentifier_iff (symbol : String) :
    checkIdentifier symbol = true ↔ Identifier symbol := by
  trustIrCompilerProof {
    unfold Identifier checkIdentifier
    simp only [StringCompat.toList, String.toList]
    cases symbol.data with
    | nil => simp
    | cons first rest =>
      cases rest with
      | nil => simp
      | cons second payload => simp [List.all_eq_true, List.cons.injEq, and_assoc]
  } {
    unfold Identifier checkIdentifier
    cases StringCompat.toList symbol with
    | nil => simp
    | cons first rest =>
      cases rest with
      | nil => simp
      | cons second payload => simp [List.all_eq_true, List.cons.injEq, and_assoc]
  }

def SMTSort.Positive : SMTSort → Prop
  | .bool => True
  | .bv bits => 0 < bits

theorem SMTUnary.output_positive {input output : SMTSort} (op : SMTUnary input output)
    (positive : input.Positive) : output.Positive := by
  cases op <;> simp_all [SMTSort.Positive] <;> omega

theorem SMTBinary.output_positive {input output : SMTSort} (op : SMTBinary input output)
    (positive : input.Positive) : output.Positive := by
  cases op <;> simp_all [SMTSort.Positive]

theorem SMTTerm.wellFormed_positive {sort : SMTSort} (term : SMTTerm sort) (wellFormed : term.WellFormed) :
    sort.Positive := by
  induction term with
  | bvConst bits value => exact wellFormed
  | boolConst value => trivial
  | var bits symbol => exact wellFormed.1
  | unary op arg ih => exact op.output_positive (ih wellFormed)
  | binary op left right leftIH _ => exact op.output_positive (leftIH wellFormed.1)
  | ite cond yes no _ yesIH _ => exact yesIH wellFormed.2.1
  | concat high low highIH _ =>
    have positive := highIH wellFormed.1
    simp only [SMTSort.Positive] at *
    omega

theorem SMTTerm.asFormula_wellFormed {sort : SMTSort} (term : SMTTerm sort) (wellFormed : term.WellFormed) :
    term.asFormula.WellFormed := by
  cases sort with
  | bool => exact wellFormed
  | bv bits => exact ⟨wellFormed, term.wellFormed_positive wellFormed⟩

/-- Typed variable occurrences, before duplicate elimination. -/
noncomputable def SMTTerm.bindings {sort : SMTSort} (term : SMTTerm sort) : List (Nat × String) :=
  SMTTerm.rec (motive := fun _ _ => List (Nat × String))
    (fun _ _ => []) (fun _ => []) (fun bits symbol => [(bits,symbol)])
    (fun _ _ arg => arg) (fun _ _ _ left right => left ++ right)
    (fun _ _ _ cond yes no => cond ++ yes ++ no) (fun _ _ high low => high ++ low) term

private theorem mem_append_iff {α : Type} (name : α) (a b : List α) :
    name ∈ a ++ b ↔ name ∈ a ∨ name ∈ b := by
  constructor
  · induction a with
    | nil => exact fun h => Or.inr h
    | cons head tail ih =>
      intro h
      cases h with
      | head => exact Or.inl (List.Mem.head _)
      | tail _ h =>
        cases ih h with
        | inl h => exact Or.inl (List.Mem.tail _ h)
        | inr h => exact Or.inr h
  · intro h
    cases h with
    | inl h => exact trustIrListMemAppendLeft b h
    | inr h => exact trustIrListMemAppendRight a h

theorem SMTTerm.bindings_wellFormed {sort : SMTSort} (term : SMTTerm sort) (wellFormed : term.WellFormed) :
    ∀ binding ∈ term.bindings, 0 < binding.1 ∧ Identifier binding.2 := by
  trustIrCompilerProof {
    induction term with
    | bvConst bits value => simp [bindings]
    | boolConst value => simp [bindings]
    | var bits symbol => simpa [bindings] using wellFormed
    | unary op arg ih => exact ih wellFormed
    | binary op left right leftIH rightIH =>
      simpa only [bindings, mem_append_iff, or_imp, forall_and] using
        And.intro (leftIH wellFormed.1) (rightIH wellFormed.2)
    | ite cond yes no condIH yesIH noIH =>
      simpa only [bindings, mem_append_iff, or_imp, forall_and, and_assoc] using
        And.intro (condIH wellFormed.1) (And.intro (yesIH wellFormed.2.1) (noIH wellFormed.2.2))
    | concat high low highIH lowIH =>
      simpa only [bindings, mem_append_iff, or_imp, forall_and] using
        And.intro (highIH wellFormed.1) (lowIH wellFormed.2)
  } {
    induction term with
    | bvConst bits value => simp [bindings]
    | boolConst value => simp [bindings]
    | var bits symbol => simpa [bindings] using wellFormed
    | unary op arg ih => exact ih wellFormed
    | binary op left right leftIH rightIH =>
      intro binding member
      change binding ∈ left.bindings ++ right.bindings at member
      cases (mem_append_iff binding _ _).mp member with
      | inl h => exact leftIH wellFormed.1 binding h
      | inr h => exact rightIH wellFormed.2 binding h
    | ite cond yes no condIH yesIH noIH =>
      intro binding member
      change binding ∈ (cond.bindings ++ yes.bindings) ++ no.bindings at member
      cases (mem_append_iff binding _ _).mp member with
      | inl h =>
        cases (mem_append_iff binding _ _).mp h with
        | inl h => exact condIH wellFormed.1 binding h
        | inr h => exact yesIH wellFormed.2.1 binding h
      | inr h => exact noIH wellFormed.2.2 binding h
    | concat high low highIH lowIH =>
      intro binding member
      change binding ∈ high.bindings ++ low.bindings at member
      cases (mem_append_iff binding _ _).mp member with
      | inl h => exact highIH wellFormed.1 binding h
      | inr h => exact lowIH wellFormed.2 binding h
  }

trustIrString48 private theorem mem_reverseAux (name : Nat × String) (a b : List (Nat × String)) :
    name ∈ a.reverseAux b ↔ name ∈ a ∨ name ∈ b := by
  induction a generalizing b with
  | nil => simp [List.reverseAux]
  | cons head tail ih =>
    simp [List.reverseAux, ih, List.mem_cons, or_assoc, or_left_comm]

trustIrString48 private theorem mem_eraseDups_loop (name : Nat × String) (input seen : List (Nat × String)) :
    name ∈ List.eraseDups.loop input seen ↔ name ∈ input ∨ name ∈ seen := by
  induction input generalizing seen with
  | nil => simp [List.eraseDups.loop, List.reverse, mem_reverseAux]
  | cons head tail ih =>
    simp only [List.eraseDups.loop]
    split
    · rename_i found
      have present : head ∈ seen := List.mem_of_elem_eq_true found
      by_cases same : name = head
      · subst name
        simp [ih, present]
      · simp [ih, List.mem_cons, same]
    · simp [ih, List.mem_cons, or_assoc, or_left_comm]

private theorem mem_eraseDups (name : Nat × String) (input : List (Nat × String)) :
    name ∈ input.eraseDups ↔ name ∈ input := by
  trustIrCompilerProof { simp [List.eraseDups, mem_eraseDups_loop] } { exact List.mem_eraseDups }

def typedBindingsConsistent (bindings : List (Nat × String)) : Prop :=
  ∀ a ∈ bindings, ∀ b ∈ bindings, a.2 = b.2 → a.1 = b.1

def checkTypedBindings (bindings : List (Nat × String)) : Bool :=
  bindings.all (fun a => bindings.all (fun b => decide (a.2 = b.2 → a.1 = b.1)))

theorem checkTypedBindings_iff (bindings : List (Nat × String)) :
    checkTypedBindings bindings = true ↔ typedBindingsConsistent bindings := by
  simp only [checkTypedBindings, typedBindingsConsistent, List.all_eq_true, decide_eq_true_eq]

def SMTTerm.typedScript {sort : SMTSort} (term : SMTTerm sort) (bindings : List (Nat × String)) : String :=
  "(set-logic QF_BV)\n" ++ String.join (bindings.map (fun binding =>
    "(declare-fun " ++ binding.2 ++ " () (_ BitVec " ++ toString binding.1 ++ "))\n")) ++
    "(assert " ++ term.asFormula.toText ++ ")\n(check-sat)\n"

/-- A serialized request, not execution, certificate or proof authority. The
typed target is retained; variable declarations carry their actual widths. -/
structure SMTTypedRequest (sort : SMTSort) where
  target : SMTTerm sort
  bindings : List (Nat × String)
  script : String

/-- Verified construction data. Proof fields erase; the exact binding inventory
is computed while building nodes, not by an additional indexed AST traversal. -/
structure SMTCheckedTerm (sort : SMTSort) where
  term : SMTTerm sort
  bindings : List (Nat × String)
  wellFormed : term.WellFormed
  inventory : bindings = term.bindings

def SMTCheckedTerm.bvConst (bits : Nat) (value : Int) : Except String (SMTCheckedTerm (.bv bits)) :=
  if positive : 0 < bits then .ok ⟨.bvConst bits value, [], positive, rfl⟩
  else .error "SMT bitvector width must be positive"

def SMTCheckedTerm.boolConst (value : Bool) : SMTCheckedTerm .bool :=
  ⟨.boolConst value, [], True.intro, rfl⟩

def SMTCheckedTerm.var (bits : Nat) (symbol : String) : Except String (SMTCheckedTerm (.bv bits)) :=
  if positive : 0 < bits then
    if safe : SMTTerm.checkIdentifier symbol = true then
      .ok ⟨.var bits symbol, [(bits,symbol)], ⟨positive, SMTTerm.checkIdentifier_iff symbol |>.mp safe⟩, rfl⟩
    else .error "unsafe SMT identifier"
  else .error "SMT bitvector width must be positive"

def SMTCheckedTerm.unary {input output : SMTSort} (op : SMTUnary input output) (arg : SMTCheckedTerm input) :
    SMTCheckedTerm output :=
  ⟨.unary op arg.term, arg.bindings, arg.wellFormed, by rw [arg.inventory]; rfl⟩

def SMTCheckedTerm.binary {input output : SMTSort} (op : SMTBinary input output)
    (left right : SMTCheckedTerm input) : SMTCheckedTerm output :=
  ⟨.binary op left.term right.term, left.bindings ++ right.bindings,
    ⟨left.wellFormed,right.wellFormed⟩, by rw [left.inventory,right.inventory]; rfl⟩

def SMTCheckedTerm.ite {sort : SMTSort} (cond : SMTCheckedTerm .bool) (yes no : SMTCheckedTerm sort) :
    SMTCheckedTerm sort :=
  ⟨.ite cond.term yes.term no.term, cond.bindings ++ yes.bindings ++ no.bindings,
    ⟨cond.wellFormed,yes.wellFormed,no.wellFormed⟩, by rw [cond.inventory,yes.inventory,no.inventory]; rfl⟩

def SMTCheckedTerm.concat {highWidth lowWidth : Nat} (high : SMTCheckedTerm (.bv highWidth))
    (low : SMTCheckedTerm (.bv lowWidth)) : SMTCheckedTerm (.bv (highWidth+lowWidth)) :=
  ⟨.concat high.term low.term, high.bindings ++ low.bindings,
    ⟨high.wellFormed,low.wellFormed⟩, by rw [high.inventory,low.inventory]; rfl⟩

/-- The typed target and certified inventory are retained. Same-symbol width
conflicts refuse before any script is returned. No solver is run here. -/
def SMTCheckedTerm.toTypedRequest {sort : SMTSort} (checked : SMTCheckedTerm sort) :
    Except String (SMTTypedRequest sort) :=
  let bindings := checked.bindings.eraseDups
  if checkTypedBindings bindings then .ok ⟨checked.term,bindings,checked.term.typedScript bindings⟩
  else .error "SMT symbol used at conflicting widths"

theorem SMTCheckedTerm.toTypedRequest_admitted {sort : SMTSort} (checked : SMTCheckedTerm sort)
    (request : SMTTypedRequest sort) (built : checked.toTypedRequest = .ok request) :
    request.target = checked.term ∧ request.target.WellFormed ∧
      request.bindings = checked.term.bindings.eraseDups ∧ typedBindingsConsistent request.bindings ∧
      request.script = checked.term.typedScript request.bindings := by
  unfold toTypedRequest at built
  dsimp only at built
  split at built
  · rename_i consistent
    cases built
    exact ⟨rfl, checked.wellFormed, congrArg List.eraseDups checked.inventory,
      (checkTypedBindings_iff _).mp consistent, rfl⟩
  · cases built

theorem SMTCheckedTerm.toTypedRequest_exists_iff {sort : SMTSort} (checked : SMTCheckedTerm sort) :
    (∃ request, checked.toTypedRequest = .ok request) ↔ typedBindingsConsistent checked.bindings.eraseDups := by
  unfold toTypedRequest
  by_cases consistent : checkTypedBindings checked.bindings.eraseDups = true <;>
    simp [consistent, ← checkTypedBindings_iff]

theorem SMTCheckedTerm.toTypedRequest_prints {sort : SMTSort} (checked : SMTCheckedTerm sort)
    (request : SMTTypedRequest sort) (built : checked.toTypedRequest = .ok request) :
    request.target.asFormula.Prints request.target.asFormula.toText ∧ request.target.asFormula.WellFormed := by
  have admitted := checked.toTypedRequest_admitted request built
  exact ⟨SMTTerm.toText_prints _, request.target.asFormula_wellFormed admitted.2.1⟩

theorem SMTCheckedTerm.toTypedRequest_bindings_wellFormed {sort : SMTSort} (checked : SMTCheckedTerm sort)
    (request : SMTTypedRequest sort) (built : checked.toTypedRequest = .ok request) :
    ∀ binding ∈ request.bindings, 0 < binding.1 ∧ SMTTerm.Identifier binding.2 := by
  have admitted := checked.toTypedRequest_admitted request built
  intro binding member
  rw [admitted.2.2.1] at member
  exact checked.term.bindings_wellFormed checked.wellFormed binding ((mem_eraseDups _ _).mp member)

end TrustIr.TrustIrExpr

#trustIrAxiomsExact TrustIr.TrustIrExpr.SMTTerm.checkIdentifier_iff == [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.SMTUnary.output_positive == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.SMTBinary.output_positive == [propext] modern []

#trustIrAxiomsPinned TrustIr.TrustIrExpr.SMTTerm.wellFormed_positive == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.SMTTerm.asFormula_wellFormed == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.TrustIrExpr.SMTTerm.bindings_wellFormed == [Quot.sound, propext]

#trustIrAxiomsExact TrustIr.TrustIrExpr.checkTypedBindings_iff == [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.SMTCheckedTerm.toTypedRequest_admitted == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.TrustIrExpr.SMTCheckedTerm.toTypedRequest_exists_iff == [Quot.sound, propext]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.SMTCheckedTerm.toTypedRequest_prints == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.SMTCheckedTerm.toTypedRequest_bindings_wellFormed == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]
