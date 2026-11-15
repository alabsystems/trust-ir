-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIrRuntime
import TrustIr

open TrustIr TrustIr.ExecutableFixtures

def expectedCmp (op : ICmpOp) (width : Nat) (a b : Int) : Bool :=
  let sign := fun n => if n < (2 : Int) ^ (width - 1) then n else n - (2 : Int) ^ width
  match op with
  | .Eq => a == b | .Ne => a != b
  | .Ult => a < b | .Ule => a ≤ b | .Ugt => a > b | .Uge => a ≥ b
  | .Slt => sign a < sign b | .Sle => sign a ≤ sign b
  | .Sgt => sign a > sign b | .Sge => sign a ≥ sign b

def check (op : ICmpOp) (ty : Ty) (lhs rhs want : Value) : IO Unit := do
  let before := stateWith [(v0, lhs), (v1, rhs)] 2
  match Sem.run (stepInst (.ICmp op ty v0 v1)) before with
  | .error e => throw (IO.userError s!"{repr ty} {repr op}: {repr e}")
  | .ok (.value (some id), after) =>
    let some got := after.lookupValue id | throw (IO.userError "missing comparison result")
    unless stableValueString got == stableValueString want do
      throw (IO.userError s!"{repr ty} {repr op}: {stableValueString got} != {stableValueString want}")
    unless id.index == 2 && after.nextValueId == 3 do
      throw (IO.userError "incorrect fresh result identity")
    unless reprStr after.memory == reprStr before.memory do
      throw (IO.userError "comparison changed memory")
    unless stableValueString (after.lookupValue v0 |>.getD .nullPtr) == stableValueString lhs &&
        stableValueString (after.lookupValue v1 |>.getD .nullPtr) == stableValueString rhs do
      throw (IO.userError "comparison overwrote an operand")
  | .ok _ => throw (IO.userError "comparison did not produce one value")

def main : IO Unit := do
  let ops := [ICmpOp.Eq, .Ne, .Ult, .Ule, .Ugt, .Uge, .Slt, .Sle, .Sgt, .Sge]
  let mut runs := 0
  for op in ops do
    for a in [false, true] do
      for b in [false, true] do
        check op .Bool (.bool a) (.bool b) (.bool (expectedCmp op 1 (if a then 1 else 0) (if b then 1 else 0)))
        runs := runs + 1
  for (elem, width) in [(Ty.Bool, 1), (.I8, 8), (.U8, 8), (.I16, 16), (.U16, 16),
      (.I32, 32), (.U32, 32), (.I64, 64), (.U64, 64)] do
    for count in [1, 2, 3, 5, 8, 16, 17] do
      let edges : List Int := [0, (2 : Int) ^ (width - 1), (2 : Int) ^ width - 1, 1]
      let lhs := (List.range count).map (fun i => edges[i % 4]!)
      let other := (List.range count).map (fun i => edges[(i + 1) % 4]!)
      let lane := fun v => if elem == .Bool then Value.bool (v != 0) else .int width v
      for op in ops do
        for rhs in [lhs, other] do
          let want := (lhs.zip rhs).map (fun (a, b) => Value.bool (expectedCmp op width a b))
          check op (.Vector count elem) (.vector (lhs.map lane)) (.vector (rhs.map lane)) (.vector want)
          runs := runs + 1
  unless runs == 1300 do throw (IO.userError s!"incorrect corpus size: {runs}")
  for (ty, lhs, rhs) in [
      (Ty.Bool, Value.undef .Bool, .bool true),
      (.Bool, .bool true, .undef .Bool),
      (.Vector 3 .Bool, .vector [.bool true, .undef .Bool, .bool false], .vector [.bool false, .bool true, .bool false]),
      (.Vector 3 .I32, .vector [.int 32 0, .undef .I32, .int 32 1], .vector [.int 32 1, .int 32 0, .int 32 1])] do
    match Sem.run (stepInst (.ICmp .Eq ty v0 v1)) (stateWith [(v0, lhs), (v1, rhs)] 2) with
    | .error (.ub _) => pure ()
    | _ => throw (IO.userError "poison comparison did not report UB")
  for (ty, lhs, rhs) in [
      (Ty.Bool, Value.int 1 1, .int 1 0),
      (.Vector 3 .Bool, .vector [.int 1 1, .int 1 0, .int 1 1], .vector [.bool false, .bool true, .bool false]),
      (.Vector 3 .I32, .vector [.int 64 0, .int 64 0, .int 64 0], .vector [.int 32 0, .int 32 0, .int 32 0]),
      (.Vector 3 .I8, .vector [.int 8 0], .vector [.int 8 0])] do
    match Sem.run (stepInst (.ICmp .Eq ty v0 v1)) (stateWith [(v0, lhs), (v1, rhs)] 2) with
    | .error (.typeError _) => pure ()
    | _ => throw (IO.userError "malformed comparison did not report a type error")
  IO.println s!"ICmp parity: {runs} positive engine runs, 4 poison and 4 malformed controls passed"
