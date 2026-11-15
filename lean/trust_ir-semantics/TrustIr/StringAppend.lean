-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.CompilerCompat

/-- Elaborate only the matching pinned representation of String. -/
macro "trustIrString430 " declaration:command : command => do
  if Lean.versionString == "4.30.0-rc2" then pure declaration
  else if Lean.versionString == "4.8.0" then `(command| run_cmd pure ())
  else Lean.Macro.throwError "unsupported Lean compiler for constructive String append"

macro "trustIrString48 " declaration:command : command => do
  if Lean.versionString == "4.8.0" then pure declaration
  else if Lean.versionString == "4.30.0-rc2" then `(command| run_cmd pure ())
  else Lean.Macro.throwError "unsupported Lean compiler for constructive String append"

namespace TrustIr.StringCompat

-- The modern validity witness is built from list and byte-array equality,
-- without invoking the standard UTF-8 append proof or a decoder.
trustIrString430 private theorem pairCongr {α β γ : Type} (f : α → β → γ) {a b : α} {c d : β}
    (left : a = b) (right : c = d) : f a c = f b d :=
  (congrArg (fun x => f x c) left).trans (congrArg (fun y => f b y) right)
trustIrString430 private theorem appNil {α : Type} (xs : List α) : xs ++ [] = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (List.cons x) ih
trustIrString430 private theorem appAssoc {α : Type} (xs ys zs : List α) : (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (List.cons x) ih
trustIrString430 private theorem concatAppend {α : Type} (xs : List α) (x : α) : xs.concat x = xs ++ [x] := by
  induction xs with
  | nil => rfl
  | cons y ys ih => exact congrArg (List.cons y) ih
trustIrString430 private theorem flatAppend {α β : Type} (f : α → List β) (xs ys : List α) :
    (xs ++ ys).flatMap f = xs.flatMap f ++ ys.flatMap f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    exact (congrArg (fun tail => f x ++ tail) ih).trans (appAssoc (f x) (xs.flatMap f) (ys.flatMap f)).symm
trustIrString430 private theorem pushData (a : ByteArray) (b : UInt8) :
    (a.push b).data.toList = a.data.toList ++ [b] := by
  rcases a with ⟨⟨xs⟩⟩
  exact concatAppend xs b
trustIrString430 private theorem loopData (xs : List UInt8) (a : ByteArray) :
    (List.toByteArray.loop xs a).data.toList = a.data.toList ++ xs := by
  induction xs generalizing a with
  | nil => exact (appNil a.data.toList).symm
  | cons x xs ih =>
    exact (ih (a.push x)).trans
      ((congrArg (fun initial => initial ++ xs) (pushData a x)).trans
        (appAssoc a.data.toList [x] xs))
trustIrString430 private theorem bytesData (xs : List UInt8) : xs.toByteArray.data.toList = xs :=
  loopData xs ByteArray.empty
trustIrString430 private theorem bytesExt {a b : ByteArray} (h : a.data.toList = b.data.toList) : a = b := by
  rcases a with ⟨⟨xs⟩⟩
  rcases b with ⟨⟨ys⟩⟩
  cases h
  rfl
trustIrString430 private theorem bytesAppend (xs ys : List UInt8) :
    (xs ++ ys).toByteArray = xs.toByteArray ++ ys.toByteArray := by
  apply bytesExt
  exact (bytesData (xs ++ ys)).trans
    (pairCongr (fun left right : List UInt8 => left ++ right) (bytesData xs).symm (bytesData ys).symm)
trustIrString430 private theorem utf8Append (xs ys : List Char) :
    (xs ++ ys).utf8Encode = xs.utf8Encode ++ ys.utf8Encode :=
  (congrArg List.toByteArray (flatAppend String.utf8EncodeChar xs ys)).trans
    (bytesAppend (xs.flatMap String.utf8EncodeChar) (ys.flatMap String.utf8EncodeChar))
trustIrString430 private theorem validAppend {a b : ByteArray} (ha : a.IsValidUTF8) (hb : b.IsValidUTF8) :
    (a ++ b).IsValidUTF8 := by
  cases ha with
  | intro xs hx =>
    cases hb with
    | intro ys hy =>
      exact .intro (xs ++ ys)
        ((pairCongr (fun left right : ByteArray => left ++ right) hx hy).trans (utf8Append xs ys).symm)
trustIrString430 def append (left right : String) : String :=
  ⟨left.toByteArray ++ right.toByteArray, validAppend left.isValidUTF8 right.isValidUTF8⟩

trustIrString48 def append (left right : String) : String := left ++ right

trustIrString430
/-- The modern operation preserves exactly the original appended byte array. -/
theorem append_bytes (left right : String) :
    (append left right).toByteArray = left.toByteArray ++ right.toByteArray := rfl

trustIrString430
/-- Only the standard operation in this comparison carries propext. The
constructive operation and byte identity above remain axiom-free. -/
theorem append_eq_standard (left right : String) :
    append left right = left ++ right := rfl

#trustIrAxiomsExact append == []
trustIrString430 #trustIrAxiomsExact utf8Append == []
trustIrString430 #trustIrAxiomsExact validAppend == []
trustIrString430 #trustIrAxiomsExact append_bytes == []
trustIrString430 #trustIrAxiomsExact append_eq_standard == [propext]

end TrustIr.StringCompat
