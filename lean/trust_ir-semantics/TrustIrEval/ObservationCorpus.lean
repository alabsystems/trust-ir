-- Copyright 2026 Andrew Yates
-- Licensed under the Apache License, Version 2.0

import TrustIrRuntime
import TrustIrEval.Observation

open TrustIr
open TrustIrEval.Observation

/-- Actual serializer outputs for the cross-language compact graph reader.
    Huge extents and nested values stay structural throughout this corpus. -/
def main : IO Unit := do
  let count := 2^64 - 1
  let uniform := CompactArray.Packed.uniform count (Value.int 32 7)
  IO.println (renderGraph [.array uniform]).compress
  let updated ← match uniform.set? (count - 1) (.int 32 42) with
    | some values => pure values
    | none => throw (IO.userError "last-index update failed")
  IO.println (renderGraph [.array updated]).compress
  IO.println (renderGraph [
    .int 128 (-1), .bool true, .float (0.0 / 0.0), .float (-0.0),
    .ptr 0 none, .nullPtr, .fatPtr 0 none (.int 64 9),
    .aggregate [.uninit, .int 8 255], .vector [.bool false],
    .sequence [.int 16 1], .set [.int 16 2], .record [("λ", .int 32 3)],
    .closure ⟨4⟩ [.array uniform], .typedClosure ⟨5⟩ ⟨4⟩ [.array uniform],
    .fnDef ⟨6⟩ ⟨7⟩, .frame 0 [.uninit], .partial [none], .uninit,
    .array (CompactArray.Packed.uniform 0 (.int 32 99))]).compress
  let dense := CompactArray.Packed.ofArray ((List.range 65).map (fun n => Value.int 32 (Int.ofNat n))).toArray
  IO.println (renderGraph [.array dense]).compress
  let unit := CompactArray.Tree.ofArray #[Value.int 32 11, .int 32 22, .int 32 33]
  let periodic : CompactArray.Packed Value := ⟨count, .periodic unit (by decide) 1 count⟩
  IO.println (renderGraph [.array periodic]).compress
  let changed ← match periodic.set? (count - 1) (.int 32 44) with
    | some values => pure values
    | none => throw (IO.userError "periodic last-index update failed")
  IO.println (renderGraph [.array periodic, .array changed]).compress
  let clipped : CompactArray.Tree Value 5 := .periodic unit (by decide) 0 5
  let nestedCount := 5 * (2^40 + 37)
  let nested : CompactArray.Packed Value :=
    ⟨nestedCount, .periodic clipped (by decide) 1 nestedCount⟩
  IO.println (renderGraph [.array nested]).compress
  -- Width 256 is outside the Rust observation domain. Even unreachable
  -- graph nodes are validated, so exposing this retained value must fail.
  let hidden := CompactArray.Tree.ofArray #[Value.int 256 1, .int 32 8, .int 32 9]
  IO.println (renderGraph [
    .array ⟨2, .periodic hidden (by decide) 1 2⟩,
    .array ⟨0, .periodic hidden (by decide) 0 0⟩]).compress
