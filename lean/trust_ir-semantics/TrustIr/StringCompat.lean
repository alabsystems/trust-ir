-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.CompilerCompat

/-- Modern strings carry a UTF-8 proof. Select only declarations whose
    representation exists on the named compiler; legacy strings stay original. -/
macro "trustIrModernStringDecl " declaration:command : command => do
  if Lean.versionString == "4.8.0" then `(command| run_cmd pure ())
  else if Lean.versionString == "4.30.0-rc2" then pure declaration
  else Lean.Macro.throwError "unsupported Lean compiler for constructive strings"

namespace TrustIr.CompilerCompat.Strings
trustIrModernStringDecl
private theorem cong2C {α β γ : Type} (f : α → β → γ) {a a' : α} {b b' : β} (ha : a = a') (hb : b = b') : f a b = f a' b' := by
  cases ha
  cases hb
  rfl
trustIrModernStringDecl
private theorem append_assocC {α : Type} (a b c : List α) : (a ++ b) ++ c = a ++ (b ++ c) := by
  induction a with
  | nil => rfl
  | cons x xs ih => exact congrArg (List.cons x) ih
trustIrModernStringDecl
private theorem append_nilC {α : Type} (a : List α) : a ++ [] = a := by
  induction a with
  | nil => rfl
  | cons x xs ih => exact congrArg (List.cons x) ih
trustIrModernStringDecl
private theorem flatMap_appendModern {α β : Type} (f : α → List β) (a b : List α) :
    (a ++ b).flatMap f = a.flatMap f ++ b.flatMap f := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
    change f x ++ (xs ++ b).flatMap f = (f x ++ xs.flatMap f) ++ b.flatMap f
    exact (congrArg (fun t => f x ++ t) ih).trans (append_assocC _ _ _).symm
trustIrModernStringDecl
private theorem push_listC (a : Array UInt8) (x : UInt8) : (a.push x).toList = a.toList ++ [x] := by
  cases a with
  | mk xs =>
    change List.concat xs x = xs ++ [x]
    induction xs with
    | nil => rfl
    | cons h t ih => exact congrArg (List.cons h) ih
trustIrModernStringDecl
private theorem loop_listC (a : List UInt8) (b : ByteArray) :
    (List.toByteArray.loop a b).data.toList = b.data.toList ++ a := by
  induction a generalizing b with
  | nil => exact (append_nilC _).symm
  | cons x xs ih =>
    change (List.toByteArray.loop xs (b.push x)).data.toList = b.data.toList ++ x :: xs
    exact (ih (b.push x)).trans ((congrArg (fun t => t ++ xs) (push_listC b.data x)).trans (append_assocC _ _ _))
trustIrModernStringDecl
private theorem encode_listC (a : List UInt8) : a.toByteArray.data.toList = a :=
  loop_listC a ByteArray.empty
trustIrModernStringDecl
private theorem byte_extC {a b : ByteArray} (h : a.data.toList = b.data.toList) : a = b := by
  cases a with
  | mk a => cases b with
    | mk b => cases a; cases b; cases h; rfl
trustIrModernStringDecl
private theorem bytes_appendModern (a b : List UInt8) : (a ++ b).toByteArray = a.toByteArray ++ b.toByteArray := by
  apply byte_extC
  change (a ++ b).toByteArray.data.toList = a.toByteArray.data.toList ++ b.toByteArray.data.toList
  exact (encode_listC _).trans (cong2C (fun x y => x ++ y) (encode_listC a).symm (encode_listC b).symm)
trustIrModernStringDecl
private theorem utf8_appendModern (a b : List Char) : (a ++ b).utf8Encode = a.utf8Encode ++ b.utf8Encode :=
  (congrArg List.toByteArray (flatMap_appendModern String.utf8EncodeChar a b)).trans (bytes_appendModern _ _)
trustIrModernStringDecl
private theorem valid_appendModern {a b : ByteArray} (ha : a.IsValidUTF8) (hb : b.IsValidUTF8) :
    (a ++ b).IsValidUTF8 := by
  rcases ha with ⟨x, hx⟩
  rcases hb with ⟨y, hy⟩
  exact ⟨x ++ y, (cong2C (fun x y => x ++ y) hx hy).trans (utf8_appendModern x y).symm⟩
trustIrModernStringDecl
def appendModern (s t : String) : String :=
  ⟨s.toByteArray ++ t.toByteArray, valid_appendModern s.isValidUTF8 t.isValidUTF8⟩
trustIrModernStringDecl
@[csimp]
theorem appendModern_eq : @appendModern = @String.append := rfl
trustIrModernStringDecl
#trustIrAxiomsExact TrustIr.CompilerCompat.Strings.appendModern == []
trustIrModernStringDecl
#trustIrAxioms TrustIr.CompilerCompat.Strings.appendModern_eq <= [propext]
end TrustIr.CompilerCompat.Strings

/-- Preserve the original append bytes and native runtime entry on both pins. -/
macro "trustIrStringAppend " left:term:max right:term : term => do
  if Lean.versionString == "4.8.0" then `(String.append $left $right)
  else if Lean.versionString == "4.30.0-rc2" then
    `(TrustIr.CompilerCompat.Strings.appendModern $left $right)
  else Lean.Macro.throwError "unsupported Lean compiler for constructive string append"

/-- Build diagnostic text with the same append bytes and native entry.
    Legacy interpolation remains the original syntax; modern interpolation
    uses the constructive UTF-8 proof only within this expression. -/
macro "trustIrStringBuild " body:term : term => do
  if Lean.versionString == "4.8.0" then pure body
  else if Lean.versionString == "4.30.0-rc2" then
    `(let _ : Append String := ⟨TrustIr.CompilerCompat.Strings.appendModern⟩; $body)
  else Lean.Macro.throwError "unsupported Lean compiler for constructive string building"
