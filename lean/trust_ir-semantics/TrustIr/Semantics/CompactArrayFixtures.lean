-- Copyright 2026 Andrew Yates
-- Licensed under the Apache License, Version 2.0

import TrustIr.Semantics.Aggregate

namespace TrustIr

private def compactIntIs (expected : Nat) : Option Value → Bool
  | some (.int 64 value) => value == Int.ofNat expected
  | _ => false

/-- The actual Value constructor and element helpers, not the sample model:
    persistent updates at the largest u64 logical extent retain a bounded path. -/
def compactArrayRuntimeProbe : Bool := Id.run do
  let count := 2 ^ 64 - 1
  let original := Value.array (CompactArray.Packed.uniform count (.int 64 7))
  let mut current := original
  for value in List.range 1024 do
    match setElement current (count - 1) (.int 64 (Int.ofNat value)) with
    | none => return false
    | some updated => current := updated
  match current with
  | .array values =>
    return values.size == count && values.tree.nodes == 129 &&
      values.tree.height == 65 &&
      compactIntIs 7 (getElement original (count - 1)) &&
      compactIntIs 1023 (getElement current (count - 1)) &&
      compactIntIs 7 (getElement current (count - 2)) &&
      (getElement current count).isNone &&
      (setElement current count (.int 64 3)).isNone
  | _ => return false

/-- Dense literals straddle the leaf and branch boundaries; every output
    observation must match its source buffer. Empty trees admit no update. -/
def compactArrayDenseProbe : Bool :=
  [0, 1, 2, 15, 16, 17, 31, 32, 33, 65, 129, 1024].all (fun count =>
    let source := ((List.range count).map (fun n => Value.int 64 (Int.ofNat n))).toArray
    let value := Value.array (CompactArray.Packed.ofArray source)
    (List.range count).all (fun index => compactIntIs index (getElement value index)) &&
      (getElement value count).isNone && (setElement value count (.int 64 9)).isNone)

/-- Stored pointer provenance transports unchanged without any dereference. -/
def compactArrayPointerProbe : Bool :=
  let count := 2 ^ 64
  let pointer := Value.ptr 57 (some ⟨13⟩)
  let original := Value.array (CompactArray.Packed.uniform count pointer)
  match setElement original (count - 1) (.ptr 71 (some ⟨29⟩)) with
  | none => false
  | some updated =>
    match getElement original (count - 1), getElement updated (count - 2),
        getElement updated (count - 1) with
    | some (.ptr 57 (some ⟨13⟩)), some (.ptr 57 (some ⟨13⟩)),
        some (.ptr 71 (some ⟨29⟩)) => true
    | _, _, _ => false


end TrustIr
