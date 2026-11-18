-- Copyright 2026 Andrew Yates
-- Licensed under the Apache License, Version 2.0
import TrustIrEval.Decode

namespace TrustIrEval.ConstantLayerControls
open Lean TrustIr

private def integer (value : Nat) : Json :=
  Json.mkObj [("Int", .num (JsonNumber.fromNat value))]

theorem scalar_int_is_independent_of_the_recursive_callback (recurse : Json → D Constant) :
    constantLayer recurse (integer 1) = .ok (.int 1) := by trustIrReduce

trustIrDecodeModernOnly
theorem public_scalar_int_uses_the_original_layer :
    constant (integer 1) = .ok (.int 1) := by trustIrReduce

theorem array_layer_uses_the_original_callback :
    constantLayer (fun _ => .ok (.int 7))
      (Json.mkObj [("Array", .arr #[integer 1])]) = .ok (.array [.int 7]) := by trustIrReduce

theorem recursive_child_refusal_is_not_replaced :
    constantLayer (fun _ => .error (.unsupported "original child"))
      (Json.mkObj [("Vector", .arr #[integer 1])]) =
        .error (.unsupported "original child") := by trustIrReduce

trustIrDecodeModernOnly
theorem unknown_tag_keeps_its_original_refusal :
    constant (Json.str "Unknown") = .error (.unsupported "constant.Unknown") := by trustIrReduce

trustIrDecodeModernOnly
theorem negative_unsigned_literal_keeps_its_original_refusal :
    constant (Json.mkObj [("U128", .str "-1")]) =
      .error (.malformed "U128: negative") := by trustIrReduce

trustIrDecodeModernOnly
theorem invalid_byte_keeps_its_original_refusal :
    constant (Json.mkObj [("Bytes", Json.mkObj [
      ("data", .arr #[.num (JsonNumber.fromNat 256)]), ("utf8", .bool false)])]) =
      .error (.malformed "Bytes.data: byte > 255") := by trustIrReduce

end TrustIrEval.ConstantLayerControls

-- A legacy executable artifact cannot supply the modern public parser theorem.
-- Shared-layer controls above still elaborate on both exact compiler pins.
trustIrDecodeCompilerCommand {
/-- error: unknown identifier 'TrustIrEval.constant_int' -/
#guard_msgs in
#check TrustIrEval.constant_int
} {
#check TrustIrEval.constant_int
}
