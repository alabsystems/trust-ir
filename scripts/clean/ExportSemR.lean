/- Copyright 2026 Andrew Yates | Apache-2.0
   Untrusted data exporter using the official, separately pinned lean4export.
   Visit every imported constant, including internal declarations. Stock
   dumpConstant excludes unsafe declarations and retains partial declarations;
   the independent checker must report their disposition, never hide skips.
   The sole argument is the inventory output path; NDJSON goes to stdout.
-/
import Export
open Lean

-- Display names are not an identity: dotted components, numeric components,
-- and Unicode have different display policies in Lean and Clean.
def nameComponents : Name → List Json
  | .anonymous => []
  | .str parent component =>
      nameComponents parent ++ [Json.mkObj [("str", toJson component)]]
  | .num parent component =>
      nameComponents parent ++ [Json.mkObj [("num", toJson component)]]

def main (args : List String) : IO Unit := do
  unless args.length == 1 do
    throw <| IO.userError "usage: ExportSemR.lean INVENTORY.json"
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `SemRMemory }, { module := `SemRMiniRust }] {}
  let constants := env.constants.toList
  let rows := constants.map fun (name, info) =>
    let owner := match env.getModuleIdxFor? name with
      | some index => env.header.moduleNames[index.toNat]!.toString
      | none => "<builtin>"
    Json.mkObj [
      ("name", toJson name.toString), ("module", toJson owner),
      ("components", toJson (nameComponents name)),
      ("unsafe", toJson info.isUnsafe), ("partial", toJson info.isPartial),
      ("internal", toJson name.isInternal),
      ("axiom", toJson (match info with | .axiomInfo _ => true | _ => false))]
  IO.FS.writeFile args.head! (Json.mkObj [
    ("schema", toJson (2 : Nat)),
    ("modules", toJson (env.header.moduleNames.map Name.toString)),
    ("constants", toJson rows)]).compress
  M.run env do
    initState env
    dumpMetadata
    for (name, _) in constants do
      modify fun st => { st with noMDataExprs := {} }
      dumpConstant name
