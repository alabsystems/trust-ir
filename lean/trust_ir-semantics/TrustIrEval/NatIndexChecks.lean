-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIrRuntime
import TrustIr.Proofs.NatIndexProps

/-! Executable representation controls. Timing is not a pass criterion.
    The public index work/depth is checked against the unchanged logical
    view; physical objects/visits are reported independently.
    Run: lake env lean --run TrustIrEval/NatIndexChecks.lean -/

namespace TrustIrEval.NatIndexChecks
open TrustIr

def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def sparseKeys (count : Nat) : List Nat :=
  (List.range (count + 3)).map fun index =>
    if index = 0 then 2^32 - 1 else 1000000000 + 7919 * index

def checkIndex (label : String) (keys : List Nat) : IO Unit := do
  let index := keys.foldl (fun index key => index.insert key key) (NatIndex.empty : NatIndex Nat)
  let view := index.tree
  let logical := view.nodeCount
  let physical := index.storage.nodeCount
  let visits := keys.foldl (fun sum key => sum + index.storage.lookupSteps key) 0
  let oldVisits := keys.foldl (fun sum key => sum + view.lookupSteps key) 0
  check (index.depth == view.depth) "cached depth differs from original binary view"
  check (physical ≤ logical && index.storage.depth ≤ index.depth) "physical view bounds failed"
  for key in keys do
    check (index.find? key == some key && view.find key == some key) "stored lookup differs"
  IO.println s!"case={label} declarations={keys.length} physical_nodes={physical} binary_view_nodes={logical} physical_depth={index.storage.depth} binary_view_depth={index.depth} physical_lookup_visits={visits} binary_view_lookup_visits={oldVisits}"

def snapshots : IO Unit := do
  let huge : Nat := 2^4096 + 7
  let half : Nat := 2^512 + 7
  let base := ((NatIndex.empty : NatIndex Nat).insert 0 11).insert huge 22
  let left := base.insert huge 33
  let right := base.insert half 44
  check (base.find? 0 == some 11 && base.find? huge == some 22 && base.find? half == none)
    "shared source changed after update"
  check (left.find? huge == some 33 && left.find? half == none && left.find? 0 == some 11)
    "overwrite changed another key"
  check (right.find? huge == some 22 && right.find? half == some 44 && right.find? 0 == some 11)
    "persistent branch changed another key"
  check (base.depth == 4098 && left.depth == 4098 && right.depth == 4098 &&
      base.keyBound == huge + 1 && left.keyBound == huge + 1 && right.keyBound == huge + 1)
    "unbounded key depth or bound changed"
  for query in [1, huge-1, huge+1, half-1, half+1] do
    check (base.find? query == none && left.find? query == none && right.find? query == none)
      "nearby missing key became present"
  let mut index := right
  for value in List.range 512 do index := index.insert half value
  check (index.find? half == some 511 && right.find? half == some 44 && base.find? half == none)
    "repeated update changed a retained snapshot"
  check (index.depth == right.depth && index.keyBound == right.keyBound)
    "overwrite changed exact evidence fields"
  IO.println "case=persistent-512-and-4096-bit-Nat:PASS updates=512 binary_view_depth=4098"

def arbitraryTree : IO Unit := do
  let tree : NatIndexTree Nat := .node none (.node none .empty .empty)
    (.node none (.node none .empty .empty) .empty)
  have outside : ∀ key, 100 ≤ key → tree.find key = none := by
    intro key _
    simp [tree, NatIndexTree.find]
  let original := NatIndex.ofTree tree 100 outside
  let inserted := original.insert 0 9
  check (original.depth == 3 && original.keyBound == 100 && original.find? 0 == none)
    "noncanonical tree or loose bound changed"
  check (inserted.depth == 3 && inserted.keyBound == 100 && inserted.find? 0 == some 9)
    "update changed loose bound or retained empty routing nodes"
  for key in List.range 200 do
    check (original.find? key == none && inserted.find? key == (if key == 0 then some 9 else none))
      "arbitrary routing tree adapter changed lookup"
  IO.println "case=noncanonical-empty-routes-and-loose-bound:PASS depth=3 bound=100"

def run : IO Unit := do
  snapshots
  arbitraryTree
  for count in [256, 2048, 8192, 32768] do
    checkIndex s!"dense-{count}" (List.range (count + 3))
    checkIndex s!"sparse-{count}" (sparseKeys count)

end TrustIrEval.NatIndexChecks

def main : IO Unit := TrustIrEval.NatIndexChecks.run
