-- Copyright 2026 Andrew Yates | Apache-2.0
-- Codec/depth/refusal controls. No synthetic program is an actual-source case.
import TrustIrEval.ClosureWire

namespace TrustIrEval.ClosureWire.Controls
open Lean TrustIr

theorem control_01 : materialize 1 (.nat 23) = .ok ("23", toJson (23 : Nat)) := rfl

theorem control_02 : materialize 4 (.object [("z", .null), ("a", .bool true)]) =
    .ok ("{\"z\":null,\"a\":true}", Json.mkObj [("z", .null), ("a", .bool true)]) := rfl

theorem array_materialization : materialize 2 (.array [.null]) =
    .ok ("[null]", Json.arr #[Json.null]) := rfl

theorem control_03 : materialize 4 (.object [("x", .nat 1), ("x", .nat 2)]) =
    .error (.unsupported "closure_wire.duplicate_key") := rfl

theorem control_04 : materialize 0 .null = .error (.unsupported "closure_wire.depth") := rfl

theorem control_05 : quotedAscii "λ" = .error (.unsupported "closure_wire.ascii_string") := rfl

theorem control_06 : quotedAscii "a\"\\\n" = .ok "\"a\\\"\\\\\\n\"" := rfl

theorem control_07 : decode 4 "{\"z\":null}" (.object [("z", .bool true)]) =
    .error (.malformed "closure_wire.bytes_mismatch") := rfl

theorem control_08 : tagged "enum" (Json.mkObj [("A", .null), ("B", .null)]) =
    .error (.malformed "enum: expected a single-variant object") := rfl

theorem control_09 : abiFields "abi" (Json.mkObj [("known", .null), ("aaa", .null), ("zzz", .null)])
    ["known"] = .error (.unsupported "abi.unknown_field.zzz") := rfl

theorem control_10 : ClosureDecode.funcTy (Json.mkObj [("abi", Json.mkObj [])]) =
    .error (.unsupported "signature_abi.transport_semantics") := rfl

theorem control_11 : ClosureDecode.requireEmpty (Json.mkObj [("globals", Json.arr #[Json.null])])
    "globals" = .error (.unsupported "closure_subset.table.globals") := rfl

theorem control_12 : ClosureDecode.tyFuel 0 (.str "U64") =
    .error (.unsupported "closure_subset.type_depth") := rfl

theorem control_13 : ClosureDecode.tyFuel 1 (.str "U64") = .ok .U64 := rfl

theorem control_14 : ClosureDecode.tyFuel 1 (Json.mkObj [("Ref", .str "U64")]) =
    .error (.unsupported "closure_subset.type_depth") := rfl

theorem control_15 : ClosureDecode.tyFuel 2 (Json.mkObj [("Ref", .str "U64")]) = .ok (.Ref .U64) := rfl

theorem control_16 : ClosureDecode.inst (Json.mkObj [("Const", .null)]) =
    .error (.unsupported "closure_subset.inst.Const") := rfl

theorem control_17 : ClosureDecode.ty (.str "Unrecognized") =
    .error (.unsupported "ty.Unrecognized") := rfl

end TrustIrEval.ClosureWire.Controls
