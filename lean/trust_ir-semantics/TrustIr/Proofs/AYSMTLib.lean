-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYSMTTarget
import TrustIr.StringUnicode

namespace TrustIr
namespace TrustIrExpr

local instance : Append String := ⟨StringCompat.append⟩

/-- Declarative typing for the complete homogeneous BV/Bool request language. -/
inductive SMTSorted (width : Nat) : TrustIrExpr → SMTSort → Prop where
  | bvConst (value : Int) (positive : 0 < width) :
      SMTSorted width (.bvConst width value) (.bv width)
  | var (name : String) (positive : 0 < width) :
      SMTSorted width (.var name width) (.bv width)
  | boolConst (value : Bool) : SMTSorted width (.boolConst value) .bool
  | bvAdd {left right : TrustIrExpr}
      (lhs : SMTSorted width left (.bv width)) (rhs : SMTSorted width right (.bv width)) :
      SMTSorted width (.bvAdd left right) (.bv width)
  | bvSub {left right : TrustIrExpr}
      (lhs : SMTSorted width left (.bv width)) (rhs : SMTSorted width right (.bv width)) :
      SMTSorted width (.bvSub left right) (.bv width)
  | bvMul {left right : TrustIrExpr}
      (lhs : SMTSorted width left (.bv width)) (rhs : SMTSorted width right (.bv width)) :
      SMTSorted width (.bvMul left right) (.bv width)
  | bvUDiv {left right : TrustIrExpr}
      (lhs : SMTSorted width left (.bv width)) (rhs : SMTSorted width right (.bv width)) :
      SMTSorted width (.bvUDiv left right) (.bv width)
  | bvSDiv {left right : TrustIrExpr}
      (lhs : SMTSorted width left (.bv width)) (rhs : SMTSorted width right (.bv width)) :
      SMTSorted width (.bvSDiv left right) (.bv width)
  | bvURem {left right : TrustIrExpr}
      (lhs : SMTSorted width left (.bv width)) (rhs : SMTSorted width right (.bv width)) :
      SMTSorted width (.bvURem left right) (.bv width)
  | bvSRem {left right : TrustIrExpr}
      (lhs : SMTSorted width left (.bv width)) (rhs : SMTSorted width right (.bv width)) :
      SMTSorted width (.bvSRem left right) (.bv width)
  | bvAnd {left right : TrustIrExpr}
      (lhs : SMTSorted width left (.bv width)) (rhs : SMTSorted width right (.bv width)) :
      SMTSorted width (.bvAnd left right) (.bv width)
  | bvOr {left right : TrustIrExpr}
      (lhs : SMTSorted width left (.bv width)) (rhs : SMTSorted width right (.bv width)) :
      SMTSorted width (.bvOr left right) (.bv width)
  | bvXor {left right : TrustIrExpr}
      (lhs : SMTSorted width left (.bv width)) (rhs : SMTSorted width right (.bv width)) :
      SMTSorted width (.bvXor left right) (.bv width)
  | bvShl {left right : TrustIrExpr}
      (lhs : SMTSorted width left (.bv width)) (rhs : SMTSorted width right (.bv width)) :
      SMTSorted width (.bvShl left right) (.bv width)
  | bvLShr {left right : TrustIrExpr}
      (lhs : SMTSorted width left (.bv width)) (rhs : SMTSorted width right (.bv width)) :
      SMTSorted width (.bvLShr left right) (.bv width)
  | bvAShr {left right : TrustIrExpr}
      (lhs : SMTSorted width left (.bv width)) (rhs : SMTSorted width right (.bv width)) :
      SMTSorted width (.bvAShr left right) (.bv width)
  | bvRotL {left right : TrustIrExpr}
      (lhs : SMTSorted width left (.bv width)) (rhs : SMTSorted width right (.bv width)) :
      SMTSorted width (.bvRotL left right) (.bv width)
  | bvRotR {left right : TrustIrExpr}
      (lhs : SMTSorted width left (.bv width)) (rhs : SMTSorted width right (.bv width)) :
      SMTSorted width (.bvRotR left right) (.bv width)
  | boolAnd {left right : TrustIrExpr}
      (lhs : SMTSorted width left (.bool)) (rhs : SMTSorted width right (.bool)) :
      SMTSorted width (.boolAnd left right) (.bool)
  | boolOr {left right : TrustIrExpr}
      (lhs : SMTSorted width left (.bool)) (rhs : SMTSorted width right (.bool)) :
      SMTSorted width (.boolOr left right) (.bool)
  | boolImpl {left right : TrustIrExpr}
      (lhs : SMTSorted width left (.bool)) (rhs : SMTSorted width right (.bool)) :
      SMTSorted width (.boolImpl left right) (.bool)
  | bvUlt {left right : TrustIrExpr}
      (lhs : SMTSorted width left (.bv width)) (rhs : SMTSorted width right (.bv width)) :
      SMTSorted width (.bvUlt left right) .bool
  | bvUle {left right : TrustIrExpr}
      (lhs : SMTSorted width left (.bv width)) (rhs : SMTSorted width right (.bv width)) :
      SMTSorted width (.bvUle left right) .bool
  | bvSlt {left right : TrustIrExpr}
      (lhs : SMTSorted width left (.bv width)) (rhs : SMTSorted width right (.bv width)) :
      SMTSorted width (.bvSlt left right) .bool
  | bvSle {left right : TrustIrExpr}
      (lhs : SMTSorted width left (.bv width)) (rhs : SMTSorted width right (.bv width)) :
      SMTSorted width (.bvSle left right) .bool
  | bvNeg {arg : TrustIrExpr} (input : SMTSorted width arg (.bv width)) :
      SMTSorted width (.bvNeg arg) (.bv width)
  | bvNot {arg : TrustIrExpr} (input : SMTSorted width arg (.bv width)) :
      SMTSorted width (.bvNot arg) (.bv width)
  | boolNot {arg : TrustIrExpr} (input : SMTSorted width arg (.bool)) :
      SMTSorted width (.boolNot arg) (.bool)
  | eq {left right : TrustIrExpr} {sort : SMTSort}
      (lhs : SMTSorted width left sort) (rhs : SMTSorted width right sort) :
      SMTSorted width (.eq left right) .bool
  | ite {cond yes no : TrustIrExpr} {sort : SMTSort}
      (condition : SMTSorted width cond .bool)
      (thenBranch : SMTSorted width yes sort) (elseBranch : SMTSorted width no sort) :
      SMTSorted width (.ite cond yes no) sort

private structure Rendered where
  kind : SMTSort
  term : SMTTerm kind
  variables : List String := []

private def Rendered.text (result : Rendered) : String := result.term.toText

-- Encode code points, rather than quoting user text into SMT syntax. Separators
-- distinguish every sequence, including the empty name and Unicode names.
def smtVariableSymbol (name : String) : String :=
  "v_" ++ StringCompat.intercalate "_" ((StringCompat.toList name).map (fun c => toString c.toNat))

/-- Variable mangling preserves the original Unicode code-point encoding. -/
theorem smtVariableSymbol_eq_standard (name : String) :
    smtVariableSymbol name = String.append "v_"
      (String.intercalate "_" (name.toList.map (fun c => toString c.toNat))) := by
  trustIrCompilerProof
    { rfl }
    { unfold smtVariableSymbol
      rw [StringCompat.toList_eq_standard, StringCompat.intercalate_eq_standard]
      rfl }

/-- Structural translation evidence for the actual target syntax returned by
serialization. The rotation nodes contain the emitted primitive expansion. -/
inductive SMTTranslated (width : Nat) : TrustIrExpr → {sort : SMTSort} → SMTTerm sort → Prop where
  | bvConst (value : Int) (positive : 0 < width) :
      SMTTranslated width (.bvConst width value) (.bvConst width value)
  | var (name : String) (positive : 0 < width) :
      SMTTranslated width (.var name width) (.var width (smtVariableSymbol name))
  | boolConst (value : Bool) : SMTTranslated width (.boolConst value) (.boolConst value)
  | bvNeg {arg : TrustIrExpr} {term : SMTTerm (.bv width)}
      (input : SMTTranslated width arg term) :
      SMTTranslated width (.bvNeg arg) (.unary (.bvNeg width) term)
  | bvNot {arg : TrustIrExpr} {term : SMTTerm (.bv width)}
      (input : SMTTranslated width arg term) :
      SMTTranslated width (.bvNot arg) (.unary (.bvNot width) term)
  | boolNot {arg : TrustIrExpr} {term : SMTTerm .bool}
      (input : SMTTranslated width arg term) :
      SMTTranslated width (.boolNot arg) (.unary (.boolNot) term)
  | bvAdd {left right : TrustIrExpr} {lhs rhs : SMTTerm (.bv width)}
      (leftInput : SMTTranslated width left lhs) (rightInput : SMTTranslated width right rhs) :
      SMTTranslated width (.bvAdd left right) (.binary (.bvAdd width) lhs rhs)
  | bvSub {left right : TrustIrExpr} {lhs rhs : SMTTerm (.bv width)}
      (leftInput : SMTTranslated width left lhs) (rightInput : SMTTranslated width right rhs) :
      SMTTranslated width (.bvSub left right) (.binary (.bvSub width) lhs rhs)
  | bvMul {left right : TrustIrExpr} {lhs rhs : SMTTerm (.bv width)}
      (leftInput : SMTTranslated width left lhs) (rightInput : SMTTranslated width right rhs) :
      SMTTranslated width (.bvMul left right) (.binary (.bvMul width) lhs rhs)
  | bvUDiv {left right : TrustIrExpr} {lhs rhs : SMTTerm (.bv width)}
      (leftInput : SMTTranslated width left lhs) (rightInput : SMTTranslated width right rhs) :
      SMTTranslated width (.bvUDiv left right) (.binary (.bvUDiv width) lhs rhs)
  | bvSDiv {left right : TrustIrExpr} {lhs rhs : SMTTerm (.bv width)}
      (leftInput : SMTTranslated width left lhs) (rightInput : SMTTranslated width right rhs) :
      SMTTranslated width (.bvSDiv left right) (.binary (.bvSDiv width) lhs rhs)
  | bvURem {left right : TrustIrExpr} {lhs rhs : SMTTerm (.bv width)}
      (leftInput : SMTTranslated width left lhs) (rightInput : SMTTranslated width right rhs) :
      SMTTranslated width (.bvURem left right) (.binary (.bvURem width) lhs rhs)
  | bvSRem {left right : TrustIrExpr} {lhs rhs : SMTTerm (.bv width)}
      (leftInput : SMTTranslated width left lhs) (rightInput : SMTTranslated width right rhs) :
      SMTTranslated width (.bvSRem left right) (.binary (.bvSRem width) lhs rhs)
  | bvAnd {left right : TrustIrExpr} {lhs rhs : SMTTerm (.bv width)}
      (leftInput : SMTTranslated width left lhs) (rightInput : SMTTranslated width right rhs) :
      SMTTranslated width (.bvAnd left right) (.binary (.bvAnd width) lhs rhs)
  | bvOr {left right : TrustIrExpr} {lhs rhs : SMTTerm (.bv width)}
      (leftInput : SMTTranslated width left lhs) (rightInput : SMTTranslated width right rhs) :
      SMTTranslated width (.bvOr left right) (.binary (.bvOr width) lhs rhs)
  | bvXor {left right : TrustIrExpr} {lhs rhs : SMTTerm (.bv width)}
      (leftInput : SMTTranslated width left lhs) (rightInput : SMTTranslated width right rhs) :
      SMTTranslated width (.bvXor left right) (.binary (.bvXor width) lhs rhs)
  | bvShl {left right : TrustIrExpr} {lhs rhs : SMTTerm (.bv width)}
      (leftInput : SMTTranslated width left lhs) (rightInput : SMTTranslated width right rhs) :
      SMTTranslated width (.bvShl left right) (.binary (.bvShl width) lhs rhs)
  | bvLShr {left right : TrustIrExpr} {lhs rhs : SMTTerm (.bv width)}
      (leftInput : SMTTranslated width left lhs) (rightInput : SMTTranslated width right rhs) :
      SMTTranslated width (.bvLShr left right) (.binary (.bvLShr width) lhs rhs)
  | bvAShr {left right : TrustIrExpr} {lhs rhs : SMTTerm (.bv width)}
      (leftInput : SMTTranslated width left lhs) (rightInput : SMTTranslated width right rhs) :
      SMTTranslated width (.bvAShr left right) (.binary (.bvAShr width) lhs rhs)
  | boolAnd {left right : TrustIrExpr} {lhs rhs : SMTTerm .bool}
      (leftInput : SMTTranslated width left lhs) (rightInput : SMTTranslated width right rhs) :
      SMTTranslated width (.boolAnd left right) (.binary (.boolAnd) lhs rhs)
  | boolOr {left right : TrustIrExpr} {lhs rhs : SMTTerm .bool}
      (leftInput : SMTTranslated width left lhs) (rightInput : SMTTranslated width right rhs) :
      SMTTranslated width (.boolOr left right) (.binary (.boolOr) lhs rhs)
  | boolImpl {left right : TrustIrExpr} {lhs rhs : SMTTerm .bool}
      (leftInput : SMTTranslated width left lhs) (rightInput : SMTTranslated width right rhs) :
      SMTTranslated width (.boolImpl left right) (.binary (.boolImpl) lhs rhs)
  | bvUlt {left right : TrustIrExpr} {lhs rhs : SMTTerm (.bv width)}
      (leftInput : SMTTranslated width left lhs) (rightInput : SMTTranslated width right rhs) :
      SMTTranslated width (.bvUlt left right) (.binary (.bvUlt width) lhs rhs)
  | bvUle {left right : TrustIrExpr} {lhs rhs : SMTTerm (.bv width)}
      (leftInput : SMTTranslated width left lhs) (rightInput : SMTTranslated width right rhs) :
      SMTTranslated width (.bvUle left right) (.binary (.bvUle width) lhs rhs)
  | bvSlt {left right : TrustIrExpr} {lhs rhs : SMTTerm (.bv width)}
      (leftInput : SMTTranslated width left lhs) (rightInput : SMTTranslated width right rhs) :
      SMTTranslated width (.bvSlt left right) (.binary (.bvSlt width) lhs rhs)
  | bvSle {left right : TrustIrExpr} {lhs rhs : SMTTerm (.bv width)}
      (leftInput : SMTTranslated width left lhs) (rightInput : SMTTranslated width right rhs) :
      SMTTranslated width (.bvSle left right) (.binary (.bvSle width) lhs rhs)
  | bvRotL {left right : TrustIrExpr} {lhs rhs : SMTTerm (.bv width)}
      (leftInput : SMTTranslated width left lhs) (rightInput : SMTTranslated width right rhs) :
      SMTTranslated width (.bvRotL left right) (SMTTerm.rotate true width lhs rhs)
  | bvRotR {left right : TrustIrExpr} {lhs rhs : SMTTerm (.bv width)}
      (leftInput : SMTTranslated width left lhs) (rightInput : SMTTranslated width right rhs) :
      SMTTranslated width (.bvRotR left right) (SMTTerm.rotate false width lhs rhs)
  | eq {left right : TrustIrExpr} {sort : SMTSort} {lhs rhs : SMTTerm sort}
      (leftInput : SMTTranslated width left lhs) (rightInput : SMTTranslated width right rhs) :
      SMTTranslated width (.eq left right) (.binary (.eq sort) lhs rhs)
  | ite {cond yes no : TrustIrExpr} {sort : SMTSort}
      {condition : SMTTerm .bool} {thenTerm elseTerm : SMTTerm sort}
      (condInput : SMTTranslated width cond condition)
      (yesInput : SMTTranslated width yes thenTerm) (noInput : SMTTranslated width no elseTerm) :
      SMTTranslated width (.ite cond yes no) (.ite condition thenTerm elseTerm)

theorem SMTTranslated.sorted {width : Nat} {expr : TrustIrExpr} {sort : SMTSort} {term : SMTTerm sort}
    (translated : SMTTranslated width expr term) : SMTSorted width expr sort := by
  induction translated <;> constructor <;> assumption

/-- Source variable occurrences in traversal order, before declaration deduplication. -/
def variables : TrustIrExpr → List String
  | .var name _ => [name]
  | .bvConst _ _ | .boolConst _ => []
  | .bvNeg a | .bvNot a | .boolNot a => variables a
  | .bvAdd a b | .bvSub a b | .bvMul a b | .bvUDiv a b | .bvSDiv a b
  | .bvURem a b | .bvSRem a b | .bvAnd a b | .bvOr a b | .bvXor a b
  | .bvShl a b | .bvLShr a b | .bvAShr a b | .bvRotL a b | .bvRotR a b
  | .boolAnd a b | .boolOr a b | .boolImpl a b
  | .eq a b | .bvUlt a b | .bvUle a b | .bvSlt a b | .bvSle a b =>
    variables a ++ variables b
  | .ite c t e => variables c ++ variables t ++ variables e

private theorem mem_append_iff (name : String) (a b : List String) :
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

private theorem mem_singleton_iff (name value : String) : name ∈ [value] ↔ name = value := by
  constructor
  · intro h
    cases h with
    | head => rfl
    | tail _ h => cases h
  · intro h
    subst name
    exact List.Mem.head _

private theorem mem_reverseAux (name : String) (a b : List String) :
    name ∈ a.reverseAux b ↔ name ∈ a ∨ name ∈ b := by
  induction a generalizing b with
  | nil => simp [List.reverseAux]
  | cons head tail ih =>
    simp [List.reverseAux, ih, List.mem_cons, or_assoc, or_left_comm]

trustIrString48 private theorem mem_eraseDups_loop (name : String) (input seen : List String) :
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

private theorem mem_eraseDups (name : String) (input : List String) :
    name ∈ input.eraseDups ↔ name ∈ input := by
  trustIrCompilerProof
    { simp [List.eraseDups, mem_eraseDups_loop] }
    { exact List.mem_eraseDups }

/-- Evaluation depends only on the expression's actual source variables. -/
theorem evalAt_variables_congr (expr : TrustIrExpr) (left right : SMTEnv) (width : Nat) :
    (∀ name ∈ expr.variables, left name = right name) →
    expr.evalAt left width = expr.evalAt right width := by
  induction expr <;> intro agree <;>
    simp_all [variables, TrustIrExpr.evalAt, mem_append_iff, mem_singleton_iff,
      or_imp, forall_and]

private def unary (input output : SMTSort) (op : SMTUnary input output) (a : Rendered) :
    Except String Rendered :=
  if equal : a.kind = input then
    .ok ⟨output, .unary op (equal ▸ a.term), a.variables⟩
  else .error ("wrong operand sort for " ++ op.name)

private def binary (input output : SMTSort) (op : SMTBinary input output) (a b : Rendered) :
    Except String Rendered :=
  if equal : a.kind = input ∧ b.kind = input then
    .ok ⟨output, .binary op (equal.1 ▸ a.term) (equal.2 ▸ b.term), a.variables ++ b.variables⟩
  else .error ("wrong operand sort for " ++ op.name)

private def rotate (left : Bool) (width : Nat) (a b : Rendered) :
    Except String Rendered := do
  if wrong : a.kind ≠ .bv width ∨ b.kind ≠ .bv width then
    throw "wrong operand sort for rotation"
  else
    have lhs : a.kind = .bv width := by
      by_cases equal : a.kind = .bv width
      · exact equal
      · exact False.elim (wrong (Or.inl equal))
    have rhs : b.kind = .bv width := by
      by_cases equal : b.kind = .bv width
      · exact equal
      · exact False.elim (wrong (Or.inr equal))
    pure ⟨.bv width, SMTTerm.rotate left width (lhs ▸ a.term) (rhs ▸ b.term), a.variables ++ b.variables⟩

private def render (width : Nat) : TrustIrExpr → Except String Rendered
  | .bvConst w value =>
    if w = width ∧ w > 0 then .ok ⟨.bv w, SMTTerm.bvConst w value, []⟩
    else .error "bitvector constant width differs from the operation width"
  | .var name w =>
    if w = width ∧ w > 0 then .ok ⟨.bv w, SMTTerm.var w (smtVariableSymbol name), [name]⟩
    else .error "bitvector variable width differs from the operation width"
  | .boolConst b => .ok ⟨.bool, SMTTerm.boolConst b, []⟩
  | .bvAdd a b => do binary (.bv width) (.bv width) (.bvAdd width) (← render width a) (← render width b)
  | .bvSub a b => do binary (.bv width) (.bv width) (.bvSub width) (← render width a) (← render width b)
  | .bvMul a b => do binary (.bv width) (.bv width) (.bvMul width) (← render width a) (← render width b)
  | .bvUDiv a b => do binary (.bv width) (.bv width) (.bvUDiv width) (← render width a) (← render width b)
  | .bvSDiv a b => do binary (.bv width) (.bv width) (.bvSDiv width) (← render width a) (← render width b)
  | .bvURem a b => do binary (.bv width) (.bv width) (.bvURem width) (← render width a) (← render width b)
  | .bvSRem a b => do binary (.bv width) (.bv width) (.bvSRem width) (← render width a) (← render width b)
  | .bvAnd a b => do binary (.bv width) (.bv width) (.bvAnd width) (← render width a) (← render width b)
  | .bvOr a b => do binary (.bv width) (.bv width) (.bvOr width) (← render width a) (← render width b)
  | .bvXor a b => do binary (.bv width) (.bv width) (.bvXor width) (← render width a) (← render width b)
  | .bvNeg a => do unary (.bv width) (.bv width) (.bvNeg width) (← render width a)
  | .bvNot a => do unary (.bv width) (.bv width) (.bvNot width) (← render width a)
  | .bvShl a b => do binary (.bv width) (.bv width) (.bvShl width) (← render width a) (← render width b)
  | .bvLShr a b => do binary (.bv width) (.bv width) (.bvLShr width) (← render width a) (← render width b)
  | .bvAShr a b => do binary (.bv width) (.bv width) (.bvAShr width) (← render width a) (← render width b)
  | .bvRotL a b => do rotate true width (← render width a) (← render width b)
  | .bvRotR a b => do rotate false width (← render width a) (← render width b)
  | .boolNot a => do unary .bool .bool (.boolNot) (← render width a)
  | .boolAnd a b => do binary .bool .bool (.boolAnd) (← render width a) (← render width b)
  | .boolOr a b => do binary .bool .bool (.boolOr) (← render width a) (← render width b)
  | .boolImpl a b => do binary .bool .bool (.boolImpl) (← render width a) (← render width b)
  | .bvUlt a b => do binary (.bv width) .bool (.bvUlt width) (← render width a) (← render width b)
  | .bvUle a b => do binary (.bv width) .bool (.bvUle width) (← render width a) (← render width b)
  | .bvSlt a b => do binary (.bv width) .bool (.bvSlt width) (← render width a) (← render width b)
  | .bvSle a b => do binary (.bv width) .bool (.bvSle width) (← render width a) (← render width b)
  | .eq a b => do
    let lhs ← render width a
    let rhs ← render width b
    binary lhs.kind .bool (.eq lhs.kind) lhs rhs
  | .ite c t e => do
    let cond ← render width c
    let yes ← render width t
    let no ← render width e
    if wrong : cond.kind ≠ .bool ∨ yes.kind ≠ no.kind then throw "wrong operand sorts for ite"
    else
      have condition : cond.kind = .bool := by
        by_cases equal : cond.kind = .bool
        · exact equal
        · exact False.elim (wrong (Or.inl equal))
      have branches : no.kind = yes.kind := by
        by_cases equal : yes.kind = no.kind
        · exact equal.symm
        · exact False.elim (wrong (Or.inr equal))
      pure ⟨yes.kind, .ite (condition ▸ cond.term) yes.term (branches ▸ no.term),
        cond.variables ++ yes.variables ++ no.variables⟩

private theorem render_variables (width : Nat) (expr : TrustIrExpr) (result : Rendered)
    (rendered : render width expr = .ok result) : result.variables = expr.variables := by
  induction expr generalizing result <;> simp only [render] at rendered
  all_goals try simp only [bind, Except.bind, pure, Except.pure] at rendered
  all_goals simp_all [unary, binary, rotate, variables, bind, Except.bind, pure, Except.pure]
  all_goals repeat (split at rendered <;>
    simp_all [unary, binary, rotate, variables, bind, Except.bind, pure, Except.pure])
  all_goals cases rendered; rfl

private theorem render_sorted (width : Nat) (expr : TrustIrExpr) (term : Rendered)
    (rendered : render width expr = .ok term) : SMTSorted width expr term.kind := by
  induction expr generalizing term <;> simp only [render] at rendered
  all_goals try simp only [bind, Except.bind, pure, Except.pure] at rendered
  all_goals simp_all [unary, binary, rotate, bind, Except.bind, pure, Except.pure]
  all_goals repeat (split at rendered <;>
    simp_all [unary, binary, rotate, bind, Except.bind, pure, Except.pure])
  all_goals cases rendered
  all_goals dsimp only at *
  all_goals try simp_all [not_or, Decidable.not_not]
  all_goals constructor <;> first | assumption | omega

private theorem translated_complete (width : Nat) (expr : TrustIrExpr) (sort : SMTSort)
    (typed : SMTSorted width expr sort) :
    ∃ term : SMTTerm sort, ∃ names : List String,
      render width expr = .ok ⟨sort, term, names⟩ ∧ SMTTranslated width expr term := by
  induction typed with
  | bvConst value positive =>
    refine ⟨.bvConst width value, [], ?_, .bvConst value positive⟩
    simp [render, positive]
  | var name positive =>
    refine ⟨.var width (smtVariableSymbol name), [name], ?_, .var name positive⟩
    simp [render, positive]
  | boolConst value => exact ⟨.boolConst value, [], rfl, .boolConst value⟩
  | bvNeg _input ih =>
    obtain ⟨arg, names, compiled, translated⟩ := ih
    refine ⟨.unary (.bvNeg width) arg, names, ?_, .bvNeg translated⟩
    simp [render, compiled, unary, bind, Except.bind, pure, Except.pure]
  | bvNot _input ih =>
    obtain ⟨arg, names, compiled, translated⟩ := ih
    refine ⟨.unary (.bvNot width) arg, names, ?_, .bvNot translated⟩
    simp [render, compiled, unary, bind, Except.bind, pure, Except.pure]
  | boolNot _input ih =>
    obtain ⟨arg, names, compiled, translated⟩ := ih
    refine ⟨.unary (.boolNot) arg, names, ?_, .boolNot translated⟩
    simp [render, compiled, unary, bind, Except.bind, pure, Except.pure]
  | bvAdd _left _right leftIH rightIH =>
    obtain ⟨lhs, leftNames, leftCompiled, leftTranslated⟩ := leftIH
    obtain ⟨rhs, rightNames, rightCompiled, rightTranslated⟩ := rightIH
    refine ⟨.binary (.bvAdd width) lhs rhs, leftNames ++ rightNames, ?_, .bvAdd leftTranslated rightTranslated⟩
    simp [render, leftCompiled, rightCompiled, binary, rotate, bind, Except.bind, pure, Except.pure]
  | bvSub _left _right leftIH rightIH =>
    obtain ⟨lhs, leftNames, leftCompiled, leftTranslated⟩ := leftIH
    obtain ⟨rhs, rightNames, rightCompiled, rightTranslated⟩ := rightIH
    refine ⟨.binary (.bvSub width) lhs rhs, leftNames ++ rightNames, ?_, .bvSub leftTranslated rightTranslated⟩
    simp [render, leftCompiled, rightCompiled, binary, rotate, bind, Except.bind, pure, Except.pure]
  | bvMul _left _right leftIH rightIH =>
    obtain ⟨lhs, leftNames, leftCompiled, leftTranslated⟩ := leftIH
    obtain ⟨rhs, rightNames, rightCompiled, rightTranslated⟩ := rightIH
    refine ⟨.binary (.bvMul width) lhs rhs, leftNames ++ rightNames, ?_, .bvMul leftTranslated rightTranslated⟩
    simp [render, leftCompiled, rightCompiled, binary, rotate, bind, Except.bind, pure, Except.pure]
  | bvUDiv _left _right leftIH rightIH =>
    obtain ⟨lhs, leftNames, leftCompiled, leftTranslated⟩ := leftIH
    obtain ⟨rhs, rightNames, rightCompiled, rightTranslated⟩ := rightIH
    refine ⟨.binary (.bvUDiv width) lhs rhs, leftNames ++ rightNames, ?_, .bvUDiv leftTranslated rightTranslated⟩
    simp [render, leftCompiled, rightCompiled, binary, rotate, bind, Except.bind, pure, Except.pure]
  | bvSDiv _left _right leftIH rightIH =>
    obtain ⟨lhs, leftNames, leftCompiled, leftTranslated⟩ := leftIH
    obtain ⟨rhs, rightNames, rightCompiled, rightTranslated⟩ := rightIH
    refine ⟨.binary (.bvSDiv width) lhs rhs, leftNames ++ rightNames, ?_, .bvSDiv leftTranslated rightTranslated⟩
    simp [render, leftCompiled, rightCompiled, binary, rotate, bind, Except.bind, pure, Except.pure]
  | bvURem _left _right leftIH rightIH =>
    obtain ⟨lhs, leftNames, leftCompiled, leftTranslated⟩ := leftIH
    obtain ⟨rhs, rightNames, rightCompiled, rightTranslated⟩ := rightIH
    refine ⟨.binary (.bvURem width) lhs rhs, leftNames ++ rightNames, ?_, .bvURem leftTranslated rightTranslated⟩
    simp [render, leftCompiled, rightCompiled, binary, rotate, bind, Except.bind, pure, Except.pure]
  | bvSRem _left _right leftIH rightIH =>
    obtain ⟨lhs, leftNames, leftCompiled, leftTranslated⟩ := leftIH
    obtain ⟨rhs, rightNames, rightCompiled, rightTranslated⟩ := rightIH
    refine ⟨.binary (.bvSRem width) lhs rhs, leftNames ++ rightNames, ?_, .bvSRem leftTranslated rightTranslated⟩
    simp [render, leftCompiled, rightCompiled, binary, rotate, bind, Except.bind, pure, Except.pure]
  | bvAnd _left _right leftIH rightIH =>
    obtain ⟨lhs, leftNames, leftCompiled, leftTranslated⟩ := leftIH
    obtain ⟨rhs, rightNames, rightCompiled, rightTranslated⟩ := rightIH
    refine ⟨.binary (.bvAnd width) lhs rhs, leftNames ++ rightNames, ?_, .bvAnd leftTranslated rightTranslated⟩
    simp [render, leftCompiled, rightCompiled, binary, rotate, bind, Except.bind, pure, Except.pure]
  | bvOr _left _right leftIH rightIH =>
    obtain ⟨lhs, leftNames, leftCompiled, leftTranslated⟩ := leftIH
    obtain ⟨rhs, rightNames, rightCompiled, rightTranslated⟩ := rightIH
    refine ⟨.binary (.bvOr width) lhs rhs, leftNames ++ rightNames, ?_, .bvOr leftTranslated rightTranslated⟩
    simp [render, leftCompiled, rightCompiled, binary, rotate, bind, Except.bind, pure, Except.pure]
  | bvXor _left _right leftIH rightIH =>
    obtain ⟨lhs, leftNames, leftCompiled, leftTranslated⟩ := leftIH
    obtain ⟨rhs, rightNames, rightCompiled, rightTranslated⟩ := rightIH
    refine ⟨.binary (.bvXor width) lhs rhs, leftNames ++ rightNames, ?_, .bvXor leftTranslated rightTranslated⟩
    simp [render, leftCompiled, rightCompiled, binary, rotate, bind, Except.bind, pure, Except.pure]
  | bvShl _left _right leftIH rightIH =>
    obtain ⟨lhs, leftNames, leftCompiled, leftTranslated⟩ := leftIH
    obtain ⟨rhs, rightNames, rightCompiled, rightTranslated⟩ := rightIH
    refine ⟨.binary (.bvShl width) lhs rhs, leftNames ++ rightNames, ?_, .bvShl leftTranslated rightTranslated⟩
    simp [render, leftCompiled, rightCompiled, binary, rotate, bind, Except.bind, pure, Except.pure]
  | bvLShr _left _right leftIH rightIH =>
    obtain ⟨lhs, leftNames, leftCompiled, leftTranslated⟩ := leftIH
    obtain ⟨rhs, rightNames, rightCompiled, rightTranslated⟩ := rightIH
    refine ⟨.binary (.bvLShr width) lhs rhs, leftNames ++ rightNames, ?_, .bvLShr leftTranslated rightTranslated⟩
    simp [render, leftCompiled, rightCompiled, binary, rotate, bind, Except.bind, pure, Except.pure]
  | bvAShr _left _right leftIH rightIH =>
    obtain ⟨lhs, leftNames, leftCompiled, leftTranslated⟩ := leftIH
    obtain ⟨rhs, rightNames, rightCompiled, rightTranslated⟩ := rightIH
    refine ⟨.binary (.bvAShr width) lhs rhs, leftNames ++ rightNames, ?_, .bvAShr leftTranslated rightTranslated⟩
    simp [render, leftCompiled, rightCompiled, binary, rotate, bind, Except.bind, pure, Except.pure]
  | boolAnd _left _right leftIH rightIH =>
    obtain ⟨lhs, leftNames, leftCompiled, leftTranslated⟩ := leftIH
    obtain ⟨rhs, rightNames, rightCompiled, rightTranslated⟩ := rightIH
    refine ⟨.binary (.boolAnd) lhs rhs, leftNames ++ rightNames, ?_, .boolAnd leftTranslated rightTranslated⟩
    simp [render, leftCompiled, rightCompiled, binary, rotate, bind, Except.bind, pure, Except.pure]
  | boolOr _left _right leftIH rightIH =>
    obtain ⟨lhs, leftNames, leftCompiled, leftTranslated⟩ := leftIH
    obtain ⟨rhs, rightNames, rightCompiled, rightTranslated⟩ := rightIH
    refine ⟨.binary (.boolOr) lhs rhs, leftNames ++ rightNames, ?_, .boolOr leftTranslated rightTranslated⟩
    simp [render, leftCompiled, rightCompiled, binary, rotate, bind, Except.bind, pure, Except.pure]
  | boolImpl _left _right leftIH rightIH =>
    obtain ⟨lhs, leftNames, leftCompiled, leftTranslated⟩ := leftIH
    obtain ⟨rhs, rightNames, rightCompiled, rightTranslated⟩ := rightIH
    refine ⟨.binary (.boolImpl) lhs rhs, leftNames ++ rightNames, ?_, .boolImpl leftTranslated rightTranslated⟩
    simp [render, leftCompiled, rightCompiled, binary, rotate, bind, Except.bind, pure, Except.pure]
  | bvUlt _left _right leftIH rightIH =>
    obtain ⟨lhs, leftNames, leftCompiled, leftTranslated⟩ := leftIH
    obtain ⟨rhs, rightNames, rightCompiled, rightTranslated⟩ := rightIH
    refine ⟨.binary (.bvUlt width) lhs rhs, leftNames ++ rightNames, ?_, .bvUlt leftTranslated rightTranslated⟩
    simp [render, leftCompiled, rightCompiled, binary, rotate, bind, Except.bind, pure, Except.pure]
  | bvUle _left _right leftIH rightIH =>
    obtain ⟨lhs, leftNames, leftCompiled, leftTranslated⟩ := leftIH
    obtain ⟨rhs, rightNames, rightCompiled, rightTranslated⟩ := rightIH
    refine ⟨.binary (.bvUle width) lhs rhs, leftNames ++ rightNames, ?_, .bvUle leftTranslated rightTranslated⟩
    simp [render, leftCompiled, rightCompiled, binary, rotate, bind, Except.bind, pure, Except.pure]
  | bvSlt _left _right leftIH rightIH =>
    obtain ⟨lhs, leftNames, leftCompiled, leftTranslated⟩ := leftIH
    obtain ⟨rhs, rightNames, rightCompiled, rightTranslated⟩ := rightIH
    refine ⟨.binary (.bvSlt width) lhs rhs, leftNames ++ rightNames, ?_, .bvSlt leftTranslated rightTranslated⟩
    simp [render, leftCompiled, rightCompiled, binary, rotate, bind, Except.bind, pure, Except.pure]
  | bvSle _left _right leftIH rightIH =>
    obtain ⟨lhs, leftNames, leftCompiled, leftTranslated⟩ := leftIH
    obtain ⟨rhs, rightNames, rightCompiled, rightTranslated⟩ := rightIH
    refine ⟨.binary (.bvSle width) lhs rhs, leftNames ++ rightNames, ?_, .bvSle leftTranslated rightTranslated⟩
    simp [render, leftCompiled, rightCompiled, binary, rotate, bind, Except.bind, pure, Except.pure]
  | eq _left _right leftIH rightIH =>
    obtain ⟨lhs, leftNames, leftCompiled, leftTranslated⟩ := leftIH
    obtain ⟨rhs, rightNames, rightCompiled, rightTranslated⟩ := rightIH
    refine ⟨.binary (.eq _) lhs rhs, leftNames ++ rightNames, ?_, .eq leftTranslated rightTranslated⟩
    simp [render, leftCompiled, rightCompiled, binary, rotate, bind, Except.bind, pure, Except.pure]
  | bvRotL _left _right leftIH rightIH =>
    obtain ⟨lhs, leftNames, leftCompiled, leftTranslated⟩ := leftIH
    obtain ⟨rhs, rightNames, rightCompiled, rightTranslated⟩ := rightIH
    refine ⟨SMTTerm.rotate true width lhs rhs, leftNames ++ rightNames, ?_, .bvRotL leftTranslated rightTranslated⟩
    simp [render, leftCompiled, rightCompiled, binary, rotate, bind, Except.bind, pure, Except.pure]
  | bvRotR _left _right leftIH rightIH =>
    obtain ⟨lhs, leftNames, leftCompiled, leftTranslated⟩ := leftIH
    obtain ⟨rhs, rightNames, rightCompiled, rightTranslated⟩ := rightIH
    refine ⟨SMTTerm.rotate false width lhs rhs, leftNames ++ rightNames, ?_, .bvRotR leftTranslated rightTranslated⟩
    simp [render, leftCompiled, rightCompiled, binary, rotate, bind, Except.bind, pure, Except.pure]
  | ite _condition _yes _no condIH yesIH noIH =>
    obtain ⟨condition, condNames, condCompiled, condTranslated⟩ := condIH
    obtain ⟨yes, yesNames, yesCompiled, yesTranslated⟩ := yesIH
    obtain ⟨no, noNames, noCompiled, noTranslated⟩ := noIH
    refine ⟨.ite condition yes no, condNames ++ yesNames ++ noNames, ?_,
      .ite condTranslated yesTranslated noTranslated⟩
    simp [render, condCompiled, yesCompiled, noCompiled, bind, Except.bind, pure, Except.pure,
      throw, throwThe, MonadExceptOf.throw]

private theorem render_complete (width : Nat) (expr : TrustIrExpr) (sort : SMTSort)
    (typed : SMTSorted width expr sort) :
    ∃ term, render width expr = .ok term ∧ term.kind = sort := by
  obtain ⟨term, names, compiled, _translated⟩ := translated_complete width expr sort typed
  exact ⟨⟨sort, term, names⟩, compiled, rfl⟩

private theorem render_translated (width : Nat) (expr : TrustIrExpr) (result : Rendered)
    (compiled : render width expr = .ok result) : SMTTranslated width expr result.term := by
  rcases result with ⟨sort, target, names⟩
  have typed := render_sorted width expr ⟨sort, target, names⟩ compiled
  obtain ⟨term, variables, rendered, translated⟩ := translated_complete width expr sort typed
  have same : (⟨sort, term, variables⟩ : Rendered) = ⟨sort, target, names⟩ :=
    Except.ok.inj (rendered.symm.trans compiled)
  cases same
  exact translated

/-- Actual request metadata and script share one declaration inventory. -/
structure SMTRequest where
  width : Nat
  bindings : List String
  script : String
  sort : SMTSort
  target : SMTTerm sort
  deriving Repr

/-- Serialize a formula with the evaluator's single ambient operation width.
    Constants and variables must carry that same positive width. Sort errors
    refuse before a script is returned; arbitrary names never become syntax.
    A bitvector root means nonzero, exactly as `formula_valid`/`formula_unsat`.
    This produces a request only: it does not run AY or confer proof authority. -/
def toSMTRequest (expr : TrustIrExpr) (width : Nat) : Except String SMTRequest := do
  if width = 0 then throw "SMT bitvector width must be positive"
  let term ← render width expr
  let bindings := term.variables.eraseDups
  let declarations := bindings.map (fun name =>
    "(declare-fun " ++ smtVariableSymbol name ++ " () (_ BitVec " ++ toString width ++ "))\n")
  let formula := term.term.asFormula.toText
  pure ⟨width, bindings, "(set-logic QF_BV)\n" ++ String.join declarations ++
    "(assert " ++ formula ++ ")\n(check-sat)\n", term.kind, term.term⟩

/-- The assertion whose text was emitted by this request. -/
def SMTRequest.assertion (request : SMTRequest) : SMTTerm .bool := request.target.asFormula

/-- Text projection of the same actual request, with identical refusals. -/
def toSMTLib (expr : TrustIrExpr) (width : Nat) : Except String String := do
  pure (← expr.toSMTRequest width).script

/-- Every actual request carries a declarative derivation of its root sort. -/
theorem toSMTRequest_sorted (expr : TrustIrExpr) (width : Nat) (request : SMTRequest)
    (built : expr.toSMTRequest width = .ok request) : SMTSorted width expr request.sort := by
  simp only [toSMTRequest, bind, Except.bind, pure, Except.pure,
    throw, throwThe, MonadExceptOf.throw] at built
  split at built
  · cases built
  · split at built
    · cases built
    · rename_i term rendered
      cases built
      exact render_sorted width expr term rendered

/-- The actual serialized request has exactly the deduplicated source-variable
    inventory and retains the positive operation width used to render it. -/
theorem toSMTRequest_metadata (expr : TrustIrExpr) (width : Nat) (request : SMTRequest)
    (built : expr.toSMTRequest width = .ok request) :
    request.width = width ∧ 0 < width ∧ request.bindings = expr.variables.eraseDups := by
  simp only [toSMTRequest, bind, Except.bind, pure, Except.pure,
    throw, throwThe, MonadExceptOf.throw] at built
  split at built
  · cases built
  · rename_i positive
    split at built
    · cases built
    · rename_i term rendered
      have inventory := render_variables width expr term rendered
      cases built
      exact ⟨rfl, by omega, congrArg List.eraseDups inventory⟩

/-- Every actual returned target term carries a structural source-to-target
translation derivation, including the expanded rotation graph. -/
theorem toSMTRequest_translated (expr : TrustIrExpr) (width : Nat) (request : SMTRequest)
    (built : expr.toSMTRequest width = .ok request) : SMTTranslated width expr request.target := by
  simp only [toSMTRequest, bind, Except.bind, pure, Except.pure,
    throw, throwThe, MonadExceptOf.throw] at built
  split at built
  · cases built
  · split at built
    · cases built
    · rename_i term rendered
      cases built
      exact render_translated width expr term rendered

/-- Exact admission for every root sort: successful serialization is equivalent
    to a positive operation width and a derivation in the complete language. -/
theorem toSMTRequest_admitted_iff (expr : TrustIrExpr) (width : Nat) (sort : SMTSort) :
    (∃ request, expr.toSMTRequest width = .ok request ∧ request.sort = sort) ↔
      0 < width ∧ SMTSorted width expr sort := by
  constructor
  · rintro ⟨request, built, rootSort⟩
    exact ⟨(toSMTRequest_metadata expr width request built).2.1,
      rootSort ▸ toSMTRequest_sorted expr width request built⟩
  · rintro ⟨positive, typed⟩
    obtain ⟨term, rendered, kind⟩ := render_complete width expr sort typed
    have nonzero : width ≠ 0 := by omega
    simp [toSMTRequest, nonzero, rendered, kind, bind, Except.bind, pure, Except.pure]

/-- A well-sorted source expression has one root sort. -/
theorem SMTSorted.unique {width : Nat} {expr : TrustIrExpr} {left right : SMTSort}
    (leftTyped : SMTSorted width expr left) (rightTyped : SMTSorted width expr right) :
    left = right := by
  obtain ⟨a, renderedA, kindA⟩ := render_complete width expr left leftTyped
  obtain ⟨b, renderedB, kindB⟩ := render_complete width expr right rightTyped
  have same : a = b := Except.ok.inj (renderedA.symm.trans renderedB)
  exact kindA.symm.trans ((congrArg Rendered.kind same).trans kindB)

/-- Every BV sort admitted by these homogeneous rules is the operation width. -/
theorem SMTSorted.sort_cases {width : Nat} {expr : TrustIrExpr} {sort : SMTSort}
    (typed : SMTSorted width expr sort) : sort = .bool ∨ sort = .bv width := by
  induction typed <;> first | exact Or.inl rfl | exact Or.inr rfl | assumption

private theorem sorted_bool_value (width : Nat) (expr : TrustIrExpr) (sort : SMTSort)
    (typed : SMTSorted width expr sort) (env : SMTEnv) :
    sort = .bool → expr.evalAt env width = 0 ∨ expr.evalAt env width = 1 := by
  induction typed <;> intro rootSort
  all_goals cases rootSort
  all_goals simp_all only [TrustIrExpr.evalAt, true_implies]
  all_goals split <;> first | exact Or.inl rfl | exact Or.inr rfl | assumption

/-- An actual Boolean-root request evaluates to exactly zero or one, including
    conditionals whose branches were both checked by the real serializer. -/
theorem toSMTRequest_bool_value (expr : TrustIrExpr) (width : Nat) (request : SMTRequest)
    (built : expr.toSMTRequest width = .ok request) (boolean : request.sort = .bool)
    (env : SMTEnv) : expr.evalAt env width = 0 ∨ expr.evalAt env width = 1 :=
  sorted_bool_value width expr request.sort (toSMTRequest_sorted expr width request built) env boolean

/-- No emitted declaration is extraneous and no source variable is missing. -/
theorem toSMTRequest_binding_iff (expr : TrustIrExpr) (width : Nat) (request : SMTRequest)
    (built : expr.toSMTRequest width = .ok request) (name : String) :
    name ∈ request.bindings ↔ name ∈ expr.variables := by
  rw [(toSMTRequest_metadata expr width request built).2.2]
  exact mem_eraseDups name expr.variables

/-- The actual script declares exactly the source inventory in order, using
    the request's operation width and the existing encoded variable symbols. -/
theorem toSMTRequest_declarations (expr : TrustIrExpr) (width : Nat) (request : SMTRequest)
    (built : expr.toSMTRequest width = .ok request) :
    ∃ assertion : String, request.script =
      "(set-logic QF_BV)\n" ++ String.join (expr.variables.eraseDups.map (fun name =>
        "(declare-fun " ++ smtVariableSymbol name ++ " () (_ BitVec " ++ toString width ++ "))\n")) ++
      "(assert " ++ assertion ++ ")\n(check-sat)\n" := by
  simp only [toSMTRequest, bind, Except.bind, pure, Except.pure,
    throw, throwThe, MonadExceptOf.throw] at built
  split at built
  · cases built
  · split at built
    · cases built
    · rename_i term rendered
      have inventory := render_variables width expr term rendered
      cases built
      rw [inventory]
      exact ⟨_, rfl⟩

/-- Agreement on the actual emitted declaration inventory suffices for exact
    expression-result agreement at the request's own width. -/
theorem toSMTRequest_eval_congr (expr : TrustIrExpr) (width : Nat) (request : SMTRequest)
    (built : expr.toSMTRequest width = .ok request) (left right : SMTEnv)
    (agree : ∀ name ∈ request.bindings, left name = right name) :
    expr.evalAt left request.width = expr.evalAt right request.width := by
  apply evalAt_variables_congr
  intro name member
  exact agree name ((toSMTRequest_binding_iff expr width request built name).mpr member)

/-- The actual emitted assertion text is printed from the same typed target
whose core semantics can be checked independently of the source evaluator. -/
theorem toSMTRequest_target_script (expr : TrustIrExpr) (width : Nat) (request : SMTRequest)
    (built : expr.toSMTRequest width = .ok request) :
    request.script = "(set-logic QF_BV)\n" ++ String.join (request.bindings.map (fun name =>
      "(declare-fun " ++ smtVariableSymbol name ++ " () (_ BitVec " ++ toString request.width ++ "))\n")) ++
      "(assert " ++ request.assertion.toText ++ ")\n(check-sat)\n" := by
  simp only [toSMTRequest, bind, Except.bind, pure, Except.pure,
    throw, throwThe, MonadExceptOf.throw] at built
  split at built
  · cases built
  · split at built
    · cases built
    · cases built
      rfl

/-- The legacy text API is exactly the script projection of the same request. -/
theorem toSMTLib_request_script (expr : TrustIrExpr) (width : Nat) (request : SMTRequest)
    (built : expr.toSMTRequest width = .ok request) :
    expr.toSMTLib width = .ok request.script := by
  simp [toSMTLib, built, bind, Except.bind, pure, Except.pure]

example : toSMTLib (.eq (.var "x" 8) (.bvConst 8 (-1))) 8 = .ok
    "(set-logic QF_BV)\n(declare-fun v_120 () (_ BitVec 8))\n(assert (= v_120 (_ bv255 8)))\n(check-sat)\n" := by rfl
example : toSMTLib (.bvAdd (.boolConst true) (.bvConst 8 1)) 8 =
    .error "wrong operand sort for bvadd" := by rfl
example : toSMTLib (.eq (.var "x" 16) (.bvConst 8 0)) 8 =
    .error "bitvector variable width differs from the operation width" := by rfl
example : toSMTLib (.boolConst true) 0 =
    .error "SMT bitvector width must be positive" := by rfl
example : toSMTLib (.ite (.boolConst true) (.boolConst false) (.bvConst 8 1)) 8 =
    .error "wrong operand sorts for ite" := by rfl
example : smtVariableSymbol "x|)\n(check-sat)" =
    "v_120_124_41_10_40_99_104_101_99_107_45_115_97_116_41" := by rfl

example : toSMTLib (.eq (.boolConst true) (.bvConst 8 1)) 8 =
    .error "wrong operand sort for =" := by rfl
example : toSMTLib (.ite (.bvConst 8 1) (.bvConst 8 2) (.bvConst 8 3)) 8 =
    .error "wrong operand sorts for ite" := by rfl

-- Actual request inventory and semantic dependence: no solver authority.

#trustIrAxiomsExact TrustIr.TrustIrExpr.evalAt_variables_congr == [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.toSMTRequest_metadata == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.toSMTRequest_binding_iff == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.toSMTRequest_declarations == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.toSMTRequest_eval_congr == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.TrustIrExpr.toSMTLib_request_script == [propext]

-- Exact sort admission and Boolean normalization use no solver authority.

#trustIrAxiomsPinned TrustIr.TrustIrExpr.toSMTRequest_sorted == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.toSMTRequest_admitted_iff == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.TrustIrExpr.SMTSorted.unique == [propext]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.toSMTRequest_bool_value == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.TrustIrExpr.SMTSorted.sort_cases == []

end TrustIrExpr
end TrustIr

#trustIrAxiomsExact TrustIr.TrustIrExpr.SMTTranslated.sorted == []

#trustIrAxiomsPinned TrustIr.TrustIrExpr.toSMTRequest_translated == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.toSMTRequest_target_script == [Classical.choice, propext, Quot.sound] modern [propext]
