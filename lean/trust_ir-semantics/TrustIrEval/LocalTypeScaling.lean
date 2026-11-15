-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIrRuntime
import TrustIr.Semantics.LocalTypes
import Init.Data.Nat.Log2

/-! Executable work/scaling controls for sparse SSA declarations and long
    Borrow chains. Timings are diagnostic; correctness, linear graph work and
    exact numeric-key binary-depth checks determine the verdict.
    Run: lake env lean --run TrustIrEval/LocalTypeScaling.lean -/

namespace TrustIrEval.LocalTypeScaling
open TrustIr

def sparseId (i : Nat) : ValueId := ⟨1000000000 + i * 7919⟩

def rowsFor (borrow reverseOrder : Bool) (n : Nat) : List (Inst × List ValueId) :=
  let rows := (List.range n).map (fun i =>
    let operand := if i == 0 then ValueId.mk 0 else sparseId (i - 1)
    (if borrow then Inst.Borrow operand else Inst.Copy .I8 operand, [sparseId i]))
  if reverseOrder then rows.reverse else rows

def benchmark (borrow reverseOrder : Bool) (n : Nat) : IO Unit := do
  let rows := rowsFor borrow reverseOrder n
  let params := [(ValueId.mk 0, if borrow then Ty.FatPtr .Str else Ty.I8)]
  let start ← IO.monoNanosNow
  let (table, work) ← match inferLocalTypesWithWork (fun _ => none) (fun _ => none) params rows with
    | .ok result => pure result
    | .error error => throw (IO.userError s!"metadata failure: {repr error}")
  let mut hits := 0
  for i in List.range n do
    let correct := match table (sparseId i) with
      | some .I8 => !borrow
      | some (.FatPtr .Str) => borrow
      | _ => false
    if correct then hits := hits + 1
  let stop ← IO.monoNanosNow
  -- Every source key is at most this actual sparse id. A radix index is
  -- bounded by key bits, independently of declaration insertion order.
  let largestId := (sparseId (n - 1)).index
  let depthBound := Nat.log2 largestId + 2
  unless work.declarationDepth ≤ depthBound && work.memoDepth ≤ depthBound do
    throw (IO.userError s!"index exceeds binary-key depth: {repr work}")
  unless hits == n && work.declarations == n + 1 && work.resolvedDeclarations == n + 1 &&
      work.declarationLookups == n + 1 && work.borrowEdges == (if borrow then n else 0) &&
      work.memoLookups == (if borrow then 2*n + 1 else n + 1) do
    throw (IO.userError s!"wrong lookup/work census: {hits}/{n} {repr work}")
  IO.println s!"kind={if borrow then "borrow" else "flat"} reverse={reverseOrder} declarations={n + 1} queries={n} elapsed_ns={stop - start} declaration_lookups={work.declarationLookups} memo_lookups={work.memoLookups} borrow_edges={work.borrowEdges} resolved={work.resolvedDeclarations} declaration_depth={work.declarationDepth} memo_depth={work.memoDepth} binary_depth_bound={depthBound}"

def extremeKeys : IO Unit := do
  let maximum : Nat := 2^32 - 1
  let huge : Nat := 2^128 + 7
  let index := ((NatIndex.empty : NatIndex Nat).insert 0 11).insert maximum 22
  unless index.find? 0 == some 11 && index.find? maximum == some 22 &&
      index.find? (maximum - 1) == none && index.depth == 33 do
    throw (IO.userError "u32 boundary index mismatch")
  let widened := index.insert huge 33
  unless widened.find? 0 == some 11 && widened.find? maximum == some 22 &&
      widened.find? huge == some 33 && widened.find? (huge + 1) == none &&
      widened.depth == 130 do
    throw (IO.userError "unbounded Nat index mismatch")
  IO.println "index=u32-max-and-128-bit-Nat:PASS depth=33/130"

def expectTypeError (label : String) (params : List (ValueId × Ty))
    (nodes : List (Inst × List ValueId)) (message : String) : IO Unit := do
  match inferLocalTypes (fun _ => none) (fun _ => none) params nodes with
  | .error (.typeError actual) =>
    unless actual == message do throw (IO.userError s!"{label}: wrong error {actual}")
  | _ => throw (IO.userError s!"{label}: missing TypeError")
  IO.println s!"refusal={label}:PASS"

def run : IO Unit := do
  for n in [256, 512, 1024, 2048, 8192, 32768] do benchmark false true n
  for n in [64, 128, 256, 512, 2048, 8192, 32768] do benchmark true true n
  benchmark true false 32768
  extremeKeys
  expectTypeError "duplicate" [(⟨0⟩,.I8),(⟨0⟩,.I8)] []
    "SSA types: duplicate value declaration"
  expectTypeError "conflict" [(⟨0⟩,.I8),(⟨0⟩,.U8)] []
    "SSA types: duplicate value declaration"
  expectTypeError "cycle" [] [(.Borrow ⟨1⟩,[⟨2⟩]),(.Borrow ⟨2⟩,[⟨1⟩])]
    "SSA types: cyclic borrow declarations"
  expectTypeError "missing" [] [(.Borrow ⟨404⟩,[⟨1⟩])]
    "SSA types: borrowed value has no declaration"
  expectTypeError "result-census" [] [(.Copy .I8 ⟨0⟩,[])]
    "SSA types: instruction result count mismatch"

end TrustIrEval.LocalTypeScaling

def main : IO Unit := TrustIrEval.LocalTypeScaling.run
