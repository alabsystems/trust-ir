-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIrRuntime
import TrustIr.Proofs.AYSMTLib

open TrustIr

-- Produce independent solver queries using the actual serializer. The expected
-- constants come from the Lean evaluator, not a second SMT printer. Each reset
-- gives the next query its own declarations and assertion scope.
def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "usage: AYSMTLib.lean OUTPUT_DIRECTORY")
  IO.FS.createDirAll directory
  let queries ← IO.FS.Handle.mk (directory ++ "/queries.smt2") .write
  let expected ← IO.FS.Handle.mk (directory ++ "/expected.txt") .write
  let emit := fun (expr : TrustIrExpr) (width : Nat) (answer : String) => do
    match expr.toSMTLib width with
    | .error reason => throw (IO.userError reason)
    | .ok script =>
      queries.putStr (script ++ "(reset)\n")
      expected.putStr (answer ++ "\n")
  let binary : List (Bool × (TrustIrExpr → TrustIrExpr → TrustIrExpr)) := [
    (false, .bvAdd), (false, .bvSub), (false, .bvMul),
    (false, .bvUDiv), (false, .bvSDiv), (false, .bvURem), (false, .bvSRem),
    (false, .bvAnd), (false, .bvOr), (false, .bvXor),
    (false, .bvShl), (false, .bvLShr), (false, .bvAShr),
    (false, .bvRotL), (false, .bvRotR),
    (true, .bvUlt), (true, .bvUle), (true, .bvSlt), (true, .bvSle), (true, .eq)]
  let values : List Int := [0, 1, 2, 7, -1, -7, -128]
  for width in [1, 2, 3, 4, 8, 16, 32, 64, 128, 256] do
    for a in values do
      for b in values do
        for (boolean, op) in binary do
          let e := op (.bvConst width a) (.bvConst width b)
          let v := e.evalAt SMTEnv.default width
          let want := if boolean then TrustIrExpr.boolConst (v != 0) else .bvConst width v
          emit (.boolNot (.eq e want)) width "unsat"
      for op in [TrustIrExpr.bvNeg, TrustIrExpr.bvNot] do
        let e := op (.bvConst width a)
        emit (.boolNot (.eq e (.bvConst width (e.evalAt SMTEnv.default width)))) width "unsat"
    for a in [false, true] do
      for b in [false, true] do
        for op in [TrustIrExpr.boolAnd, TrustIrExpr.boolOr, TrustIrExpr.boolImpl, TrustIrExpr.eq] do
          let e := op (.boolConst a) (.boolConst b)
          emit (.boolNot (.eq e (.boolConst (e.evalAt SMTEnv.default width != 0)))) width "unsat"
        let e := TrustIrExpr.ite (.boolConst a) (.bvConst width (-1)) (.bvConst width 0)
        emit (.boolNot (.eq e (.bvConst width (e.evalAt SMTEnv.default width)))) width "unsat"
        let e := TrustIrExpr.ite (.boolConst a) (.boolConst b) (.boolConst (!b))
        emit (.boolNot (.eq e (.boolConst (e.evalAt SMTEnv.default width != 0)))) width "unsat"
  emit (.bvConst 8 0) 8 "unsat"
  emit (.bvConst 8 1) 8 "sat"
  emit (.boolConst false) 8 "unsat"
  emit (.boolConst true) 8 "sat"
  emit (.bvUlt (.var "x" 8) (.bvConst 8 0)) 8 "unsat"
  emit (.eq (.var "x|)\n(check-sat)" 8) (.bvConst 8 (-1))) 8 "sat"
  emit (.boolNot (.eq (.var "λ" 8) (.var "λ" 8))) 8 "unsat"
  emit (.boolNot (.eq (.var "" 8) (.var "x" 8))) 8 "sat"
