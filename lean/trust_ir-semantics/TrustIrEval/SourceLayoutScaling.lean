-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIrRuntime
import TrustIr.Layout.Service

namespace TrustIrEval.SourceLayoutScaling
open TrustIr TrustIr.SourceLayout

private def require (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"source-layout scaling: {label}")

private def ask (session : Session) (mode : Mode) (ty : Ty) (size align : Nat) : IO Session := do
  match session.query mode ty with
  | .error error => throw (IO.userError s!"source-layout scaling: {repr error}")
  | .ok (value, next) =>
    require "size/align" (value.size == size && value.align == some align)
    pure next

private def arrays (count : Nat) : Environment :=
  { hasTargetInfo := true
    types := (List.range count).map (fun position =>
      some (if position + 1 < count then Ty.Array ⟨position + 1⟩ 1 else .U8)) }

private def tuples (count : Nat) : Environment :=
  { hasTargetInfo := true
    types := some .U8 :: (List.range count).map (fun size => some (.Tuple [.Array ⟨0⟩ size]))
    tupleLayouts := (List.range count).map (fun size =>
      { tupleType := ⟨size + 1⟩, size, align := 1, fieldOffsets := [0] }) }

private def sparse (count : Nat) : Environment :=
  { hasTargetInfo := true
    structs := (List.range count).map (fun position =>
      { id := ⟨4294967295 - position⟩, name := "Sparse", size := some 1, align := some 1,
        fields := [{ name := "byte", ty := .U8, offset := some 0 }] }) }

def run (count : Nat) : IO Unit := do
  require "nonempty test cohort" (count > 0)
  let session := prepare (arrays count)
  let session ← ask session .shape (.Array ⟨0⟩ 1) 1 1
  let session ← ask session .execution (.Array ⟨0⟩ 1) 1 1
  let nodes := session.graph.count
  let session ← ask session .execution (.Array ⟨0⟩ 1) 1 1
  require "repeated root shares graph" (session.graph.count == nodes)
  IO.println s!"source-layout: {count} deep array entries and repeated-root sharing PASS"
  let session := prepare (tuples count)
  let session ← ask session .execution (.Tuple [.Array ⟨0⟩ (count - 1)]) (count - 1) 1
  let _ ← ask session .shape (.Tuple [.Array ⟨0⟩ (count / 2)]) (count / 2) 1
  IO.println s!"source-layout: {count} declared tuples and whole-table validation PASS"
  let session := prepare (sparse count)
  let session ← ask session .shape (.Struct ⟨4294967295⟩) 1 1
  let _ ← ask session .execution (.Struct ⟨4294967295 - (count - 1)⟩) 1 1
  IO.println s!"source-layout: {count} sparse nominal rows at u32::MAX PASS"

end TrustIrEval.SourceLayoutScaling

def main (args : List String) : IO Unit := do
  let count := (args.head?.bind String.toNat?).getD 4096
  TrustIrEval.SourceLayoutScaling.run count
