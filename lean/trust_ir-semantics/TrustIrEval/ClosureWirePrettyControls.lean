-- Copyright 2026 Andrew Yates | Apache-2.0
-- Exact serde pretty DATA spelling; no evaluator or admission authority.
import TrustIrEval.ClosureWire
namespace TrustIrEval.ClosureWirePrettyControls
open Lean ClosureWire

theorem pretty_empty_object : materializePretty 1 0 (.object []) =
    .ok ("{}", Json.mkObj []) := by rfl

theorem pretty_empty_array : materializePretty 1 0 (.array []) =
    .ok ("[]", Json.arr #[]) := by rfl

theorem pretty_nested : materializePretty 3 0 (.object [("a", .array [.nat 1])]) =
    .ok ("{\n  \"a\": [\n    1\n  ]\n}", Json.mkObj [("a", Json.arr #[toJson (1 : Nat)])]) := by rfl

theorem pretty_duplicate_refused :
    materializePretty 2 0 (.object [("a", .nat 1), ("a", .nat 2)]) =
      .error (.unsupported "closure_wire.duplicate_key") := by rfl

end TrustIrEval.ClosureWirePrettyControls
