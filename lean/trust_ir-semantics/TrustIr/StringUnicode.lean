-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.StringAppend

namespace TrustIr.StringCompat

-- Decode only actual String bytes; malformed byte lists are not exposed.
trustIrString430 private def decode (input : List UInt8) : List Char :=
  match input with
  | [] => []
  | a :: rest =>
    if a.toNat < 128 then Char.ofNat a.toNat :: decode rest
    else if a.toNat < 224 then
      match rest with
      | b :: tail => Char.ofNat ((a.toNat % 32) * 64 + b.toNat % 64) :: decode tail
      | [] => []
    else if a.toNat < 240 then
      match rest with
      | b :: c :: tail =>
        Char.ofNat ((a.toNat % 16) * 4096 + (b.toNat % 64) * 64 + c.toNat % 64) :: decode tail
      | [] => []
      | [_] => []
    else
      match rest with
      | b :: c :: d :: tail =>
        Char.ofNat ((a.toNat % 8) * 262144 + (b.toNat % 64) * 4096 +
          (c.toNat % 64) * 64 + d.toNat % 64) :: decode tail
      | [] => []
      | [_] => []
      | [_, _] => []
termination_by structural input

trustIrString430 def toList (s : String) : List Char := decode s.toByteArray.data.toList

trustIrString430 private theorem decode_encode_char (c : Char) (tail : List UInt8) :
    decode (String.utf8EncodeChar c ++ tail) = c :: decode tail := by
  have valid := c.valid
  simp [UInt32.isValidChar, Nat.isValidChar] at valid
  unfold String.utf8EncodeChar
  dsimp only
  split <;> (try split) <;> (try split)
  all_goals simp only [Char.toNat] at valid
  all_goals simp only [List.cons_append, List.nil_append]
  all_goals rw [decode.eq_def]
  all_goals simp (disch := omega) only [
    UInt8.toNat_ofNat', Nat.mod_eq_of_lt, if_pos, if_neg]
  all_goals apply congrArg (fun d => d :: decode tail)
  all_goals exact (congrArg Char.ofNat (show _ = c.toNat from by
    change _ = c.val.toNat
    omega)).trans (Char.ofNat_toNat c)

trustIrString430 private theorem decode_flatMap (xs : List Char) :
    decode (xs.flatMap String.utf8EncodeChar) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change decode (String.utf8EncodeChar x ++ xs.flatMap String.utf8EncodeChar) = x :: xs
    rw [decode_encode_char, ih]

trustIrString430 private theorem decode_encode (xs : List Char) :
    decode xs.utf8Encode.data.toList = xs := by
  simpa only [List.utf8Encode, List.toList_data_toByteArray] using decode_flatMap xs

trustIrString430 theorem toList_eq_standard (s : String) : toList s = s.toList := by
  unfold toList
  rw [← String.utf8Encode_toList]
  exact decode_encode s.toList

trustIrString48 def toList (s : String) : List Char := s.toList

trustIrString48 theorem toList_eq_standard (s : String) : toList s = s.toList := rfl

#trustIrAxiomsExact toList == []
trustIrString430 #trustIrAxiomsExact decode == []
trustIrString430 #trustIrAxiomsExact toList_eq_standard == [propext, Classical.choice, Quot.sound]
trustIrString48 #trustIrAxiomsExact toList_eq_standard == []

trustIrString430 private def intercalateGo (acc separator : String) : List String → String
  | [] => acc
  | x :: xs => intercalateGo (append (append acc separator) x) separator xs

trustIrString430 def intercalate (separator : String) : List String → String
  | [] => ""
  | x :: xs => intercalateGo x separator xs

trustIrString48 def intercalate (separator : String) (xs : List String) : String :=
  String.intercalate separator xs

trustIrString430 private theorem intercalateGo_eq_standard (acc separator : String) (xs : List String) :
    intercalateGo acc separator xs = String.intercalate separator (acc :: xs) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    exact ih (append (append acc separator) x)

trustIrString430 theorem intercalate_eq_standard (separator : String) (xs : List String) :
    intercalate separator xs = String.intercalate separator xs := by
  cases xs with
  | nil => rfl
  | cons x xs => exact intercalateGo_eq_standard x separator xs

trustIrString48 theorem intercalate_eq_standard (separator : String) (xs : List String) :
    intercalate separator xs = String.intercalate separator xs := rfl

#trustIrAxiomsExact intercalate == []
trustIrString430 #trustIrAxiomsExact intercalate_eq_standard == [propext]
trustIrString48 #trustIrAxiomsExact intercalate_eq_standard == []

trustIrString430 def singleton (c : Char) : String := String.ofList [c]
trustIrString48 def singleton (c : Char) : String := toString c

trustIrString430 theorem singleton_bytes (c : Char) :
    (singleton c).toByteArray = [c].utf8Encode := rfl

theorem singleton_eq_standard (c : Char) : singleton c = toString c := by
  trustIrCompilerProof { rfl } { exact String.singleton_eq_ofList.symm }

#trustIrAxiomsExact singleton == []
trustIrString430 #trustIrAxiomsExact singleton_bytes == []
trustIrString48 #trustIrAxiomsExact singleton_eq_standard == []
trustIrString430 #trustIrAxiomsExact singleton_eq_standard == [propext, Quot.sound]

/-- The same complete left-fold as standard `String.join`, using the
constructive append's UTF-8 witness on the modern string representation. -/
def join (xs : List String) : String := xs.foldl append ""

private theorem joinFold_eq_standard (xs : List String) (acc : String) :
    xs.foldl append acc = xs.foldl (fun left right : String => left ++ right) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    trustIrCompilerProof { exact ih (append acc x) } {
      rw [append_eq_standard]
      exact ih (acc ++ x)
    }

/-- Preserve the original joined string for every input, including empty
and non-ASCII strings. The comparison does not enter the logical operation. -/
theorem join_eq_standard (xs : List String) : join xs = String.join xs :=
  joinFold_eq_standard xs ""

#trustIrAxiomsExact join == []
trustIrString48 #trustIrAxiomsExact join_eq_standard == []
trustIrString430 #trustIrAxiomsExact join_eq_standard == [propext]

end TrustIr.StringCompat
