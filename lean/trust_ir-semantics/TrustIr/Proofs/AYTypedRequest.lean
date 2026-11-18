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
  | boolVar symbol => trivial
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
    (fun _ _ => []) (fun _ => []) (fun bits symbol => [(bits,symbol)]) (fun _ => [])
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

theorem SMTTerm.variableBindings_wellFormed {sort : SMTSort} (term : SMTTerm sort) (wellFormed : term.WellFormed) :
    ∀ binding ∈ term.bindings, 0 < binding.1 ∧ VariableIdentifier binding.2 := by
  trustIrCompilerProof {
    induction term with
    | bvConst bits value => simp [bindings]
    | boolConst value => simp [bindings]
    | var bits symbol => simpa [bindings] using wellFormed
    | boolVar symbol => simp [bindings]
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
    | boolVar symbol => simp [bindings]
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

/-- Bool occurrences complement the existing BV projection. No variable is
invented and no symbol is rewritten. The public BV bindings API stays intact. -/
noncomputable def SMTTerm.boolBindings {sort : SMTSort} (term : SMTTerm sort) : List String :=
  SMTTerm.rec (motive := fun _ _ => List String)
    (fun _ _ => []) (fun _ => []) (fun _ _ => []) (fun symbol => [symbol])
    (fun _ _ arg => arg) (fun _ _ _ left right => left ++ right)
    (fun _ _ _ cond yes no => cond ++ yes ++ no) (fun _ _ high low => high ++ low) term

theorem SMTTerm.boolBindings_wellFormed {sort : SMTSort} (term : SMTTerm sort) (wellFormed : term.WellFormed) :
    ∀ binding ∈ term.boolBindings, VariableIdentifier binding := by
  trustIrCompilerProof {
    induction term with
    | bvConst bits value => simp [boolBindings]
    | boolConst value => simp [boolBindings]
    | var bits symbol => simp [boolBindings]
    | boolVar symbol => simpa [boolBindings] using wellFormed
    | unary op arg ih => exact ih wellFormed
    | binary op left right leftIH rightIH =>
      simpa only [boolBindings, mem_append_iff, or_imp, forall_and] using
        And.intro (leftIH wellFormed.1) (rightIH wellFormed.2)
    | ite cond yes no condIH yesIH noIH =>
      simpa only [boolBindings, mem_append_iff, or_imp, forall_and, and_assoc] using
        And.intro (condIH wellFormed.1) (And.intro (yesIH wellFormed.2.1) (noIH wellFormed.2.2))
    | concat high low highIH lowIH =>
      simpa only [boolBindings, mem_append_iff, or_imp, forall_and] using
        And.intro (highIH wellFormed.1) (lowIH wellFormed.2)
  } {
    induction term with
    | bvConst bits value => simp [boolBindings]
    | boolConst value => simp [boolBindings]
    | var bits symbol => simp [boolBindings]
    | boolVar symbol => simpa [boolBindings] using wellFormed
    | unary op arg ih => exact ih wellFormed
    | binary op left right leftIH rightIH =>
      intro binding member
      change binding ∈ left.boolBindings ++ right.boolBindings at member
      cases (mem_append_iff binding _ _).mp member with
      | inl h => exact leftIH wellFormed.1 binding h
      | inr h => exact rightIH wellFormed.2 binding h
    | ite cond yes no condIH yesIH noIH =>
      intro binding member
      change binding ∈ (cond.boolBindings ++ yes.boolBindings) ++ no.boolBindings at member
      cases (mem_append_iff binding _ _).mp member with
      | inl h =>
        cases (mem_append_iff binding _ _).mp h with
        | inl h => exact condIH wellFormed.1 binding h
        | inr h => exact yesIH wellFormed.2.1 binding h
      | inr h => exact noIH wellFormed.2.2 binding h
    | concat high low highIH lowIH =>
      intro binding member
      change binding ∈ high.boolBindings ++ low.boolBindings at member
      cases (mem_append_iff binding _ _).mp member with
      | inl h => exact highIH wellFormed.1 binding h
      | inr h => exact lowIH wellFormed.2 binding h
  }

/-- Complete typed inventory, grouped as the existing BV projection then Bool.
Repeated occurrences remain until request construction removes exact duplicates. -/
noncomputable def SMTTerm.typedBindings {sort : SMTSort} (term : SMTTerm sort) : List (SMTSort × String) :=
  term.bindings.map (fun (bits, name) => (.bv bits, name)) ++
    term.boolBindings.map (fun name => (.bool, name))

def sortedBindingsConsistent (bindings : List (SMTSort × String)) : Prop :=
  ∀ a ∈ bindings, ∀ b ∈ bindings, a.2 = b.2 → a.1 = b.1

def checkSortedBindings (bindings : List (SMTSort × String)) : Bool :=
  bindings.all (fun a => bindings.all (fun b => decide (a.2 = b.2 → a.1 = b.1)))

theorem checkSortedBindings_iff (bindings : List (SMTSort × String)) :
    checkSortedBindings bindings = true ↔ sortedBindingsConsistent bindings := by
  simp only [checkSortedBindings, sortedBindingsConsistent, List.all_eq_true, decide_eq_true_eq]

def SMTSort.toText : SMTSort → String
  | .bool => "Bool"
  | .bv bits => "(_ BitVec " ++ toString bits ++ ")"

def typedBindingsConsistent (bindings : List (Nat × String)) : Prop :=
  ∀ a ∈ bindings, ∀ b ∈ bindings, a.2 = b.2 → a.1 = b.1

theorem typedBindingsConsistent_eraseDups_iff (bindings : List (Nat × String)) :
    typedBindingsConsistent bindings.eraseDups ↔ typedBindingsConsistent bindings := by
  constructor
  · intro consistent a ha b hb same
    exact consistent a ((mem_eraseDups _ _).mpr ha) b ((mem_eraseDups _ _).mpr hb) same
  · intro consistent a ha b hb same
    exact consistent a ((mem_eraseDups _ _).mp ha) b ((mem_eraseDups _ _).mp hb) same

def checkTypedBindings (bindings : List (Nat × String)) : Bool :=
  bindings.all (fun a => bindings.all (fun b => decide (a.2 = b.2 → a.1 = b.1)))

theorem checkTypedBindings_iff (bindings : List (Nat × String)) :
    checkTypedBindings bindings = true ↔ typedBindingsConsistent bindings := by
  simp only [checkTypedBindings, typedBindingsConsistent, List.all_eq_true, decide_eq_true_eq]

/-- The complete typed rule restricts to the original width rule on BV-only
inventories. This keeps all legacy BV admission facts, not just examples. -/
theorem sortedBindingsConsistent_bv_iff (bindings : List (Nat × String)) :
    sortedBindingsConsistent (bindings.map (fun (bits, name) => (SMTSort.bv bits, name))) ↔
      typedBindingsConsistent bindings := by
  trustIrCompilerProof {
    simp [sortedBindingsConsistent, typedBindingsConsistent]
  } {
    constructor
    · rintro consistent ⟨leftWidth, leftName⟩ leftMember
        ⟨rightWidth, rightName⟩ rightMember sameName
      apply SMTSort.bv.inj
      exact consistent (.bv leftWidth, leftName)
        (List.mem_map.mpr ⟨(leftWidth, leftName), leftMember, rfl⟩)
        (.bv rightWidth, rightName)
        (List.mem_map.mpr ⟨(rightWidth, rightName), rightMember, rfl⟩) sameName
    · intro consistent left leftMember right rightMember sameName
      rcases List.mem_map.mp leftMember with ⟨⟨leftWidth, leftName⟩, leftOriginal, leftEq⟩
      rcases List.mem_map.mp rightMember with ⟨⟨rightWidth, rightName⟩, rightOriginal, rightEq⟩
      cases leftEq
      cases rightEq
      exact congrArg SMTSort.bv
        (consistent (leftWidth, leftName) leftOriginal
          (rightWidth, rightName) rightOriginal sameName)
  }

def SMTTerm.typedScript {sort : SMTSort} (term : SMTTerm sort) (bindings : List (Nat × String))
    (boolBindings : List String := []) : String :=
  let typed := bindings.map (fun (bits, name) => (SMTSort.bv bits, name)) ++
    boolBindings.map (fun name => (SMTSort.bool, name))
  "(set-logic QF_BV)\n" ++ String.join (typed.map (fun binding =>
    "(declare-fun " ++ binding.2 ++ " () " ++ binding.1.toText ++ ")\n")) ++
    "(assert " ++ term.asFormula.toText ++ ")\n(check-sat)\n"

/-- A serialized request, not execution, certificate or proof authority. The
typed target is retained; variable declarations carry their actual widths. -/
structure SMTTypedRequest (sort : SMTSort) where
  target : SMTTerm sort
  bindings : List (Nat × String)
  script : String
  boolBindings : List String

/-- Complete declarations carried by this request, including Bool variables.
The legacy `bindings` field is exactly its BV projection. -/
def SMTTypedRequest.typedBindings {sort : SMTSort} (request : SMTTypedRequest sort) :
    List (SMTSort × String) :=
  request.bindings.map (fun (bits, name) => (.bv bits, name)) ++
    request.boolBindings.map (fun name => (.bool, name))

/-- Verified construction data. Proof fields erase; the exact binding inventory
is computed while building nodes, not by an additional indexed AST traversal. -/
structure SMTCheckedTerm (sort : SMTSort) where
  term : SMTTerm sort
  bindings : List (Nat × String)
  wellFormed : term.WellFormed
  inventory : bindings = term.bindings
  boolBindings : List String
  boolInventory : boolBindings = term.boolBindings

def SMTCheckedTerm.typedBindings {sort : SMTSort} (checked : SMTCheckedTerm sort) :
    List (SMTSort × String) :=
  checked.bindings.map (fun (bits, name) => (.bv bits, name)) ++
    checked.boolBindings.map (fun name => (.bool, name))

theorem SMTCheckedTerm.typedInventory {sort : SMTSort} (checked : SMTCheckedTerm sort) :
    checked.typedBindings = checked.term.typedBindings := by
  simp only [typedBindings, SMTTerm.typedBindings, checked.inventory, checked.boolInventory]

def SMTCheckedTerm.bvConst (bits : Nat) (value : Int) : Except String (SMTCheckedTerm (.bv bits)) :=
  if positive : 0 < bits then .ok ⟨.bvConst bits value, [], positive, rfl, [], rfl⟩
  else .error "SMT bitvector width must be positive"

def SMTCheckedTerm.boolConst (value : Bool) : SMTCheckedTerm .bool :=
  ⟨.boolConst value, [], True.intro, rfl, [], rfl⟩

def SMTCheckedTerm.var (bits : Nat) (symbol : String) : Except String (SMTCheckedTerm (.bv bits)) :=
  if positive : 0 < bits then
    if safe : SMTTerm.checkIdentifier symbol = true then
      .ok ⟨.var bits symbol, [(bits,symbol)], ⟨positive, Or.inl (SMTTerm.checkIdentifier_iff symbol |>.mp safe)⟩, rfl, [], rfl⟩
    else .error "unsafe SMT identifier"
  else .error "SMT bitvector width must be positive"

/-- Explicit native-name entrypoint over the SAME variable constructor. The
legacy `var` checker remains restricted to its original encoded alphabet. -/
def SMTCheckedTerm.nativeVar (bits : Nat) (symbol : String) : Except String (SMTCheckedTerm (.bv bits)) :=
  if positive : 0 < bits then
    if native : SMTTerm.checkNativeIdentifier symbol = true then
      .ok ⟨.var bits symbol, [(bits,symbol)], ⟨positive, Or.inr native⟩, rfl, [], rfl⟩
    else .error "unsafe SMT identifier"
  else .error "SMT bitvector width must be positive"

theorem SMTCheckedTerm.var_legacy_bindings (bits : Nat) (symbol : String)
    (checked : SMTCheckedTerm (.bv bits)) (built : SMTCheckedTerm.var bits symbol = .ok checked) :
    ∀ binding ∈ checked.bindings, SMTTerm.Identifier binding.2 := by
  unfold var at built
  split at built
  · split at built
    · rename_i safe
      cases built
      simpa using ((SMTTerm.checkIdentifier_iff symbol).mp safe)
    · cases built
  · cases built

def SMTCheckedTerm.boolVar (symbol : String) : Except String (SMTCheckedTerm .bool) :=
  if safe : SMTTerm.checkIdentifier symbol = true then
    .ok ⟨.boolVar symbol, [], Or.inl ((SMTTerm.checkIdentifier_iff symbol).mp safe), rfl, [symbol], rfl⟩
  else if native : SMTTerm.checkNativeIdentifier symbol = true then
    .ok ⟨.boolVar symbol, [], Or.inr native, rfl, [symbol], rfl⟩
  else .error "unsafe SMT identifier"

def SMTCheckedTerm.unary {input output : SMTSort} (op : SMTUnary input output) (arg : SMTCheckedTerm input) :
    SMTCheckedTerm output :=
  ⟨.unary op arg.term, arg.bindings, arg.wellFormed, by rw [arg.inventory]; rfl,
    arg.boolBindings, by rw [arg.boolInventory]; rfl⟩

def SMTCheckedTerm.binary {input output : SMTSort} (op : SMTBinary input output)
    (left right : SMTCheckedTerm input) : SMTCheckedTerm output :=
  ⟨.binary op left.term right.term, left.bindings ++ right.bindings,
    ⟨left.wellFormed,right.wellFormed⟩, by rw [left.inventory,right.inventory]; rfl,
    left.boolBindings ++ right.boolBindings, by rw [left.boolInventory,right.boolInventory]; rfl⟩

def SMTCheckedTerm.ite {sort : SMTSort} (cond : SMTCheckedTerm .bool) (yes no : SMTCheckedTerm sort) :
    SMTCheckedTerm sort :=
  ⟨.ite cond.term yes.term no.term, cond.bindings ++ yes.bindings ++ no.bindings,
    ⟨cond.wellFormed,yes.wellFormed,no.wellFormed⟩, by rw [cond.inventory,yes.inventory,no.inventory]; rfl,
    cond.boolBindings ++ yes.boolBindings ++ no.boolBindings,
    by rw [cond.boolInventory,yes.boolInventory,no.boolInventory]; rfl⟩

def SMTCheckedTerm.concat {highWidth lowWidth : Nat} (high : SMTCheckedTerm (.bv highWidth))
    (low : SMTCheckedTerm (.bv lowWidth)) : SMTCheckedTerm (.bv (highWidth+lowWidth)) :=
  ⟨.concat high.term low.term, high.bindings ++ low.bindings,
    ⟨high.wellFormed,low.wellFormed⟩, by rw [high.inventory,low.inventory]; rfl,
    high.boolBindings ++ low.boolBindings, by rw [high.boolInventory,low.boolInventory]; rfl⟩

/-- The typed target and complete certified inventory are retained. Width or
Bool/BV sort aliases refuse before any script is returned. No solver runs here. -/
def SMTCheckedTerm.toTypedRequest {sort : SMTSort} (checked : SMTCheckedTerm sort) :
    Except String (SMTTypedRequest sort) :=
  let bindings := checked.bindings.eraseDups
  if checkTypedBindings bindings then
    if checkSortedBindings checked.typedBindings then
      let boolBindings := checked.boolBindings.eraseDups
      .ok ⟨checked.term,bindings,checked.term.typedScript bindings boolBindings,boolBindings⟩
    else .error "SMT symbol used at conflicting sorts"
  else .error "SMT symbol used at conflicting widths"

theorem SMTCheckedTerm.toTypedRequest_admitted {sort : SMTSort} (checked : SMTCheckedTerm sort)
    (request : SMTTypedRequest sort) (built : checked.toTypedRequest = .ok request) :
    request.target = checked.term ∧ request.target.WellFormed ∧
      request.bindings = checked.term.bindings.eraseDups ∧ typedBindingsConsistent request.bindings ∧
      request.script = checked.term.typedScript request.bindings request.boolBindings := by
  unfold toTypedRequest at built
  dsimp only at built
  split at built
  · rename_i consistent
    split at built
    · cases built
      exact ⟨rfl, checked.wellFormed, congrArg List.eraseDups checked.inventory,
        (checkTypedBindings_iff _).mp consistent, rfl⟩
    · cases built
  · cases built

/-- The successful request retains every Bool occurrence (up to exact duplicate
removal), and the SAME original full typed inventory has no cross-sort aliases. -/
theorem SMTCheckedTerm.toTypedRequest_typed_inventory {sort : SMTSort} (checked : SMTCheckedTerm sort)
    (request : SMTTypedRequest sort) (built : checked.toTypedRequest = .ok request) :
    request.boolBindings = checked.term.boolBindings.eraseDups ∧
      sortedBindingsConsistent checked.term.typedBindings := by
  unfold toTypedRequest at built
  dsimp only at built
  split at built
  · split at built
    · rename_i sorted
      cases built
      constructor
      · exact congrArg List.eraseDups checked.boolInventory
      · rw [← checked.typedInventory]
        exact (checkSortedBindings_iff _).mp sorted
    · cases built
  · cases built

theorem SMTCheckedTerm.toTypedRequest_exists_iff {sort : SMTSort} (checked : SMTCheckedTerm sort) :
    (∃ request, checked.toTypedRequest = .ok request) ↔
      typedBindingsConsistent checked.bindings.eraseDups ∧
      sortedBindingsConsistent checked.typedBindings := by
  unfold toTypedRequest
  by_cases consistent : checkTypedBindings checked.bindings.eraseDups = true <;>
    by_cases sorted : checkSortedBindings checked.typedBindings = true <;>
      simp [consistent, sorted, ← checkTypedBindings_iff, ← checkSortedBindings_iff]

/-- Exact original BV-only request existence criterion, retained as a
corollary of the combined typed inventory rather than a weakened conclusion. -/
theorem SMTCheckedTerm.toTypedRequest_exists_bv_iff {sort : SMTSort} (checked : SMTCheckedTerm sort)
    (noBool : checked.boolBindings = []) :
    (∃ request, checked.toTypedRequest = .ok request) ↔
      typedBindingsConsistent checked.bindings.eraseDups := by
  rw [checked.toTypedRequest_exists_iff]
  simp only [SMTCheckedTerm.typedBindings, noBool, List.map_nil, List.append_nil,
    sortedBindingsConsistent_bv_iff]
  constructor
  · exact fun both => both.1
  · intro consistent
    exact ⟨consistent, (typedBindingsConsistent_eraseDups_iff _).mp consistent⟩

theorem SMTCheckedTerm.toTypedRequest_prints {sort : SMTSort} (checked : SMTCheckedTerm sort)
    (request : SMTTypedRequest sort) (built : checked.toTypedRequest = .ok request) :
    request.target.asFormula.Prints request.target.asFormula.toText ∧ request.target.asFormula.WellFormed := by
  have admitted := checked.toTypedRequest_admitted request built
  exact ⟨SMTTerm.toText_prints _, request.target.asFormula_wellFormed admitted.2.1⟩

theorem SMTCheckedTerm.toTypedRequest_variable_bindings_wellFormed {sort : SMTSort} (checked : SMTCheckedTerm sort)
    (request : SMTTypedRequest sort) (built : checked.toTypedRequest = .ok request) :
    ∀ binding ∈ request.bindings, 0 < binding.1 ∧ SMTTerm.VariableIdentifier binding.2 := by
  have admitted := checked.toTypedRequest_admitted request built
  intro binding member
  rw [admitted.2.2.1] at member
  exact checked.term.variableBindings_wellFormed checked.wellFormed binding ((mem_eraseDups _ _).mp member)

/-- Original encoded-name conclusion retained explicitly for the legacy BV
constructor grammar. Native names cannot supply this premise by fiat. -/
theorem SMTTerm.bindings_wellFormed {sort : SMTSort} (term : SMTTerm sort)
    (wellFormed : term.WellFormed) (legacy : ∀ binding ∈ term.bindings, Identifier binding.2) :
    ∀ binding ∈ term.bindings, 0 < binding.1 ∧ Identifier binding.2 := by
  intro binding member
  exact ⟨(term.variableBindings_wellFormed wellFormed binding member).1, legacy binding member⟩

/-- Legacy request clients retain the original Identifier postcondition; the
complete combined API uses the separately named VariableIdentifier theorem. -/
theorem SMTCheckedTerm.toTypedRequest_bindings_wellFormed {sort : SMTSort} (checked : SMTCheckedTerm sort)
    (request : SMTTypedRequest sort) (built : checked.toTypedRequest = .ok request)
    (legacy : ∀ binding ∈ checked.bindings, SMTTerm.Identifier binding.2) :
    ∀ binding ∈ request.bindings, 0 < binding.1 ∧ SMTTerm.Identifier binding.2 := by
  have admitted := checked.toTypedRequest_admitted request built
  intro binding member
  refine ⟨(checked.toTypedRequest_variable_bindings_wellFormed request built binding member).1, ?_⟩
  rw [admitted.2.2.1, ← checked.inventory] at member
  exact legacy binding ((mem_eraseDups _ _).mp member)

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

#trustIrAxioms TrustIr.TrustIrExpr.SMTTerm.boolBindings_wellFormed <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.TrustIrExpr.SMTTerm.variableBindings_wellFormed <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.TrustIrExpr.SMTCheckedTerm.typedInventory <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.TrustIrExpr.SMTCheckedTerm.var_legacy_bindings <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.TrustIrExpr.SMTCheckedTerm.toTypedRequest_typed_inventory <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.TrustIrExpr.SMTCheckedTerm.toTypedRequest_variable_bindings_wellFormed <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.TrustIrExpr.SMTCheckedTerm.toTypedRequest_exists_bv_iff <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.TrustIrExpr.sortedBindingsConsistent_bv_iff <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.TrustIrExpr.typedBindingsConsistent_eraseDups_iff <= [propext, Classical.choice, Quot.sound]
