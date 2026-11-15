-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- `trustir_eval`: the W5b Lean-execution oracle executable (roadmap WS2.19).
--
--   trustir_eval <request.json>
--
-- reads one batch request — a serde-JSON `trust-ir` module plus a list of
-- (function, scalar arguments) runs — evaluates each run with the Lean
-- executable semantics (`evalFunctionInContext`), and prints one JSON verdict
-- per run to stdout (grammar: TrustIrEval/Run.lean). The Rust harness
-- (`crates/trust-ir-conformance/tests/lean_exec_differential.rs`) compares
-- these against the reference interpreter. Exit status 0 whenever a verdict
-- list was produced; 2 on a usage or I/O error.

import TrustIrRuntime
import TrustIrEval.Run
import TrustIrEval.RecordKeysChecks
import TrustIrEval.EnumAdmissionReplay

open TrustIrEval

def main (argv : List String) : IO UInt32 := do
  match argv with
  | [path] =>
    let text ← IO.FS.readFile path
    match Lean.Json.parse text with
    | .error e =>
      IO.println (Lean.Json.compress (obj [("error", jstr s!"request is not JSON: {e}")]))
      pure 0
    | .ok j =>
      IO.println (Lean.Json.compress (runRequest j))
      pure 0
  | _ =>
    IO.eprintln "usage: trustir_eval <request.json>"
    pure 2
