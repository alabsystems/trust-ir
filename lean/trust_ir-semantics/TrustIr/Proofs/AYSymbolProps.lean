-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYSMTLib

namespace TrustIr.TrustIrExpr

private def decimalDigit (c : Char) : Nat := c.toNat - 48

private theorem digitChar_spec (n : Nat) (bound : n < 10) :
    decimalDigit (Nat.digitChar n) = n ∧ Nat.digitChar n ≠ '_' ∧
      48 ≤ (Nat.digitChar n).toNat ∧ (Nat.digitChar n).toNat ≤ 57 := by
  have cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨
      n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private def decimalValue : List Char → Nat
  | [] => 0
  | c :: rest => decimalDigit c * 10 ^ rest.length + decimalValue rest

private theorem toDigitsCore_value (fuel n : Nat) (suffix : List Char)
    (enough : n < fuel) :
    decimalValue (Nat.toDigitsCore 10 fuel n suffix) =
      n * 10 ^ suffix.length + decimalValue suffix := by
  induction fuel generalizing n suffix with
  | zero => omega
  | succ fuel ih =>
    rw [Nat.toDigitsCore]
    trustIrCompilerProof { dsimp only } { skip }
    have digit := (digitChar_spec (n % 10) (Nat.mod_lt _ (by decide))).1
    split
    · rename_i zero
      simp only [decimalValue, digit]
      have remainder : n % 10 = n := by have := Nat.div_add_mod n 10; omega
      rw [remainder]
    · rename_i nonzero
      have smaller : n / 10 < n := Nat.div_lt_self (by omega) (by decide)
      rw [ih (n / 10) _ (by omega)]
      simp only [List.length_cons, decimalValue, digit, Nat.pow_succ]
      calc
        n / 10 * (10 ^ suffix.length * 10) +
            (n % 10 * 10 ^ suffix.length + decimalValue suffix) =
            (n / 10 * 10 + n % 10) * 10 ^ suffix.length + decimalValue suffix := by
              simp [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc]
        _ = _ := by rw [Nat.mul_comm (n / 10) 10, Nat.div_add_mod]

private theorem toDigits_value (n : Nat) : decimalValue (Nat.toDigits 10 n) = n := by
  have result := toDigitsCore_value (n + 1) n [] (by omega)
  simpa [Nat.toDigits, decimalValue] using result

private theorem toDigitsCore_all (property : Char → Prop)
    (digitProperty : ∀ n, n < 10 → property (Nat.digitChar n))
    (fuel n : Nat) (suffix : List Char) (safe : ∀ c ∈ suffix, property c) :
    ∀ c ∈ Nat.toDigitsCore 10 fuel n suffix, property c := by
  induction fuel generalizing n suffix with
  | zero => exact safe
  | succ fuel ih =>
    have digit := digitProperty (n % 10) (Nat.mod_lt _ (by decide))
    have next : ∀ c ∈ Nat.digitChar (n % 10) :: suffix, property c := by
      intro c member
      cases member with
      | head => exact digit
      | tail _ member => exact safe c member
    simp only [Nat.toDigitsCore]
    split
    · exact next
    · exact ih _ _ next

private theorem toDigitsCore_no_separator (fuel n : Nat) (suffix : List Char)
    (safe : ∀ c ∈ suffix, c ≠ '_') :
    ∀ c ∈ Nat.toDigitsCore 10 fuel n suffix, c ≠ '_' :=
  toDigitsCore_all _ (fun n bound => (digitChar_spec n bound).2.1) fuel n suffix safe

private theorem toDigits_decimal (n : Nat) :
    ∀ c ∈ Nat.toDigits 10 n, 48 ≤ c.toNat ∧ c.toNat ≤ 57 :=
  toDigitsCore_all _ (fun n bound => (digitChar_spec n bound).2.2) _ n [] (by simp)

private def readWord : List Char → Nat → List Nat
  | [], value => [value]
  | c :: rest, value =>
    if c = '_' then value :: readWord rest 0
    else readWord rest (value * 10 + decimalDigit c)

private theorem readWord_prefix (word suffix : List Char) (value : Nat)
    (safe : ∀ c ∈ word, c ≠ '_') :
    readWord (word ++ suffix) value =
      readWord suffix (value * 10 ^ word.length + decimalValue word) := by
  induction word generalizing value with
  | nil => simp [decimalValue]
  | cons head tail ih =>
    have headSafe := safe head (List.Mem.head _)
    have tailSafe : ∀ c ∈ tail, c ≠ '_' := fun c member => safe c (List.Mem.tail _ member)
    simp only [List.cons_append, readWord, if_neg headSafe]
    trustIrCompilerProof { simp only [List.append_eq] } { skip }
    rw [ih _ tailSafe]
    simp [decimalValue, Nat.pow_succ, Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm, Nat.add_assoc]

private theorem readWord_digits (n : Nat) (suffix : List Char) :
    readWord (Nat.toDigits 10 n ++ suffix) 0 = readWord suffix n := by
  have safe : ∀ c ∈ Nat.toDigits 10 n, c ≠ '_' :=
    toDigitsCore_no_separator _ _ [] (by simp)
  rw [readWord_prefix _ _ _ safe, toDigits_value]
  simp

private def codeWords : List Nat → List Char
  | [] => []
  | [n] => Nat.toDigits 10 n
  | n :: m :: rest => Nat.toDigits 10 n ++ '_' :: codeWords (m :: rest)

private theorem digits_nonempty (n : Nat) : Nat.toDigits 10 n ≠ [] := by
  by_cases zero : n = 0
  · subst n
    decide
  · intro empty
    have value := toDigits_value n
    rw [empty] at value
    simp only [decimalValue] at value
    omega

private theorem codeWords_nonempty (n : Nat) (rest : List Nat) : codeWords (n :: rest) ≠ [] := by
  cases rest with
  | nil => exact digits_nonempty n
  | cons head tail =>
    simp only [codeWords]
    cases digits : Nat.toDigits 10 n with
    | nil => exact False.elim (digits_nonempty n digits)
    | cons c cs => intro empty; cases empty

private theorem readWord_codeWords (n : Nat) (rest : List Nat) :
    readWord (codeWords (n :: rest)) 0 = n :: rest := by
  induction rest generalizing n with
  | nil =>
    have read := readWord_digits n []
    simpa [codeWords, readWord] using read
  | cons head tail ih =>
    rw [codeWords, readWord_digits]
    simp [readWord, ih]

private def readWords (chars : List Char) : List Nat :=
  if chars = [] then [] else readWord chars 0

private theorem readWords_codeWords (values : List Nat) : readWords (codeWords values) = values := by
  cases values with
  | nil => rfl
  | cons n rest => simp [readWords, codeWords_nonempty, readWord_codeWords]

trustIrString48 private theorem append_data (left right : String) :
    (left ++ right).data = left.data ++ right.data := rfl

trustIrString48 private theorem repr_data (n : Nat) : (toString n : String).data = Nat.toDigits 10 n := rfl

trustIrString48 private theorem intercalate_go_data (acc : String) (values : List Nat) :
    (String.intercalate.go acc "_" (values.map toString)).data =
      acc.data ++ (match values with | [] => [] | _ => '_' :: codeWords values) := by
  induction values generalizing acc with
  | nil => simp [String.intercalate.go]
  | cons n rest ih =>
    simp only [List.map_cons, String.intercalate.go]
    rw [ih]
    cases rest <;> simp [codeWords, append_data, repr_data, List.append_assoc]

trustIrString48 private theorem intercalate_data (values : List Nat) :
    (String.intercalate "_" (values.map toString)).data = codeWords values := by
  cases values with
  | nil => rfl
  | cons n rest =>
    simp only [List.map_cons, String.intercalate, intercalate_go_data]
    cases rest <;> simp [codeWords, repr_data]

trustIrString48 private theorem symbol_data (name : String) :
    (smtVariableSymbol name).data = ['v', '_'] ++ codeWords (name.data.map Char.toNat) := by
  have mapped : name.data.map (fun c => toString c.toNat) =
      (name.data.map Char.toNat).map toString := by
    induction name.data with
    | nil => rfl
    | cons c cs ih => simp only [List.map_cons, ih]
  rw [smtVariableSymbol_eq_standard]
  change ("v_" ++ String.intercalate "_" (name.toList.map (fun c => toString c.toNat))).data = _
  simp only [append_data, String.toList, mapped, intercalate_data]

trustIrString430 private theorem append_data (left right : String) :
    (left ++ right).toList = left.toList ++ right.toList := String.toList_append

trustIrString430 private theorem repr_data (n : Nat) : (toString n : String).toList = Nat.toDigits 10 n := by
  simpa only [Nat.toString_eq_repr] using (Nat.toList_repr (n := n))

trustIrString430 private theorem intercalate_data (values : List Nat) :
    (String.intercalate "_" (values.map toString)).toList = codeWords values := by
  induction values with
  | nil => rfl
  | cons n rest ih =>
    cases rest with
    | nil =>
      simp only [List.map_cons, List.map_nil, String.intercalate_singleton]
      exact repr_data n
    | cons head tail =>
      simp only [List.map_cons, String.intercalate_cons_cons, String.toList_append, repr_data]
      simp only [List.map_cons] at ih
      rw [ih]
      simp only [codeWords, List.append_assoc]
      rfl

trustIrString430 private theorem symbol_data (name : String) :
    (smtVariableSymbol name).toList = ['v', '_'] ++ codeWords (name.toList.map Char.toNat) := by
  rw [smtVariableSymbol_eq_standard]
  change ("v_" ++ String.intercalate "_" (name.toList.map (fun c => toString c.toNat))).toList = _
  have mapped : name.toList.map (fun c => toString c.toNat) =
      (name.toList.map Char.toNat).map toString := by
    induction name.toList with
    | nil => rfl
    | cons c cs ih => simp only [List.map_cons, ih]
  rw [append_data, mapped, intercalate_data]
  rfl

trustIrString48 private def readSymbol (symbol : String) : List Nat := readWords (symbol.data.drop 2)
trustIrString430 private def readSymbol (symbol : String) : List Nat := readWords (symbol.toList.drop 2)

private theorem readSymbol_roundtrip (name : String) :
    readSymbol (smtVariableSymbol name) = name.data.map Char.toNat := by
  unfold readSymbol
  rw [symbol_data]
  change readWords (codeWords (name.data.map Char.toNat)) = _
  exact readWords_codeWords _

trustIrString48 private theorem char_toNat_injective (left right : Char) (same : left.toNat = right.toNat) :
    left = right := by
  cases left with
  | mk left leftValid =>
    cases right with
    | mk right rightValid =>
      cases left with
      | mk left =>
        cases right with
        | mk right =>
          cases left with
          | mk left leftBound =>
            cases right with
            | mk right rightBound =>
              simp only [Char.toNat, UInt32.toNat, Fin.val_mk] at same
              subst right
              rfl

trustIrString48
/-- Distinct source names cannot alias through the actual decimal-codepoint
    encoder, including empty names and arbitrary Unicode scalar values. -/
theorem smtVariableSymbol_injective (left right : String)
    (same : smtVariableSymbol left = smtVariableSymbol right) : left = right := by
  have points := congrArg readSymbol same
  rw [readSymbol_roundtrip, readSymbol_roundtrip] at points
  clear same
  cases left with
  | mk left =>
    cases right with
    | mk right =>
      congr
      induction left generalizing right with
      | nil => cases right <;> simp_all
      | cons head tail ih =>
        cases right with
        | nil => cases points
        | cons other rest =>
          simp only [List.map_cons, List.cons.injEq] at points
          have heads := char_toNat_injective head other points.1
          cases heads
          exact congrArg (List.cons head) (ih _ points.2)

trustIrString430 private theorem char_toNat_injective (left right : Char) (same : left.toNat = right.toNat) :
    left = right := Char.toNat_inj.mp same

trustIrString430 private theorem charLists_toNat_injective (left right : List Char)
    (points : left.map Char.toNat = right.map Char.toNat) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp_all
  | cons head tail ih =>
    cases right with
    | nil => cases points
    | cons other rest =>
      simp only [List.map_cons, List.cons.injEq] at points
      have heads := char_toNat_injective head other points.1
      cases heads
      exact congrArg (List.cons head) (ih _ points.2)

trustIrString430
/-- Full Unicode symbol injection, through the actual decimal encoder. -/
theorem smtVariableSymbol_injective (left right : String)
    (same : smtVariableSymbol left = smtVariableSymbol right) : left = right := by
  have points := congrArg readSymbol same
  rw [readSymbol_roundtrip, readSymbol_roundtrip] at points
  exact String.toList_inj.mp (charLists_toNat_injective _ _ points)

theorem smtVariableSymbol_eq_iff (left right : String) :
    smtVariableSymbol left = smtVariableSymbol right ↔ left = right :=
  ⟨smtVariableSymbol_injective left right, congrArg smtVariableSymbol⟩

/-- Every source integer assignment has an assignment on encoded names that
    recovers it exactly. No distinct source bindings must share a target slot. -/
theorem smtVariableSymbol_environment (source : SMTEnv) :
    ∃ target : SMTEnv, ∀ name, target (smtVariableSymbol name) = source name := by
  let _ := Classical.propDecidable
  let target : SMTEnv := fun symbol =>
    if existsName : ∃ name, smtVariableSymbol name = symbol then
      source (Classical.choose existsName)
    else 0
  refine ⟨target, ?_⟩
  intro name
  have existsName : ∃ original, smtVariableSymbol original = smtVariableSymbol name := ⟨name, rfl⟩
  dsimp only [target]
  rw [dif_pos existsName]
  have recovered := smtVariableSymbol_injective _ _ (Classical.choose_spec existsName)
  rw [recovered]

private theorem mem_append_cases (a b : List Char) (c : Char) :
    c ∈ a ++ b → c ∈ a ∨ c ∈ b := by
  induction a with
  | nil => exact Or.inr
  | cons head tail ih =>
    intro member
    cases member with
    | head => exact Or.inl (List.Mem.head _)
    | tail _ member =>
      cases ih member with
      | inl first => exact Or.inl (List.Mem.tail _ first)
      | inr later => exact Or.inr later

private theorem codeWords_alphabet (values : List Nat) :
    ∀ c ∈ codeWords values, c = '_' ∨ (48 ≤ c.toNat ∧ c.toNat ≤ 57) := by
  induction values with
  | nil => simp [codeWords]
  | cons n rest ih =>
    cases rest with
    | nil => exact fun c member => Or.inr (toDigits_decimal n c member)
    | cons head tail =>
      intro c member
      cases mem_append_cases _ _ c member with
      | inl first => exact Or.inr (toDigits_decimal n c first)
      | inr later =>
        cases later with
        | head => exact Or.inl rfl
        | tail _ member => exact ih c member

/-- Every actual symbol starts with the fixed identifier prefix; its payload
    contains only underscores and ASCII decimal digits, regardless of input. -/
theorem smtVariableSymbol_alphabet (name : String) :
    ∃ payload : List Char, (smtVariableSymbol name).data = ['v', '_'] ++ payload ∧
      ∀ c ∈ payload, c = '_' ∨ (48 ≤ c.toNat ∧ c.toNat ≤ 57) :=
  ⟨codeWords (name.data.map Char.toNat), symbol_data name, codeWords_alphabet _⟩

-- Actual symbol identity and alphabet use no solver or native evaluator axiom.

#trustIrAxiomsExact TrustIr.TrustIrExpr.smtVariableSymbol_injective == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.TrustIrExpr.smtVariableSymbol_eq_iff == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.TrustIrExpr.smtVariableSymbol_alphabet == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.TrustIrExpr.smtVariableSymbol_environment == [Classical.choice, propext, Quot.sound]

end TrustIr.TrustIrExpr
