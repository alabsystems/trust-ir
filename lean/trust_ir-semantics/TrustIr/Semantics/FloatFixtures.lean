-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Float-fidelity fixtures (roadmap WS2.23, docs/ub-numerics-policy.md §7
-- item 6): float memory images and per-width float results, checked by
-- `lake build` via `native_decide`.

import TrustIr.Semantics.ExecutableFixtures

namespace TrustIr

namespace FloatFixtures

open ExecutableFixtures

/-!
# Float fidelity fixtures

Operands are written in exact dyadic form (`mkDyadic`), never as decimal
literals: Lean 4.8's decimal `Float` literals are not correctly rounded, so a
literal would put the literal parser in the trust path. Results are rendered
bit-faithfully with `floatExactString` (the `frExp` normalization, which is
independent of the float codec under test) and error outcomes with their
stable code plus detail (`SemError.stable`), so a refusal must be refused for
the NAMED reason.

The two ratchet rows this file ports (F-044), both PASS since WS2.23:

* `review/lean-float-memory-placeholder` — the float byte codec wrote eight
  zero bytes for any float and decoded every F32/F64 image as `0.0`
  (`review_lean_float_memory_placeholder_*`);
* `trust-ir-self-declared/lean-semantic-depth-ledger`, float row — `F32` was
  computed at binary64 (`lean_semantic_depth_ledger_float_*`).

The `f32_table_*` theorems are the Lean half of the cross-engine table: the
Rust half (`crates/trust-ir-build/tests/numerics_policy.rs`,
`F32_CROSS_ENGINE_TABLE`) runs the reference interpreter over the SAME
operand bits, asserts the SAME result bits, and checks that each row's
theorem and expected string appear in this file, so neither side can drift
alone. The table catches a truncating (non-RNE) rounder, double rounding
through a wider intermediate, and an encoder that ignores the width.
-/

/-- Stable rendering of a single returned value, floats bit-faithfully. -/
def exactValueString : Value → String
  | .float f => "float:" ++ floatExactString f
  | v => stableValueString v

/-- Run a straight-line instruction list from the empty state; render the
    LAST instruction's value, or the error (code AND detail) that stopped it. -/
def runExact (insts : List Inst) : String :=
  match Sem.run
      (insts.foldlM (fun _ inst => stepInst inst) (InstrResult.value none))
      MachineState.empty with
  | .ok (.value (some id), post) =>
    match post.lookupValue id with
    | some v => "ok:" ++ exactValueString v
    | none => "ok:missing"
  | .ok (.value none, _) => "ok:none"
  | .ok (.values ids, post) =>
    -- A two-result instruction (`Overflow` / `CmpXchg`, WS2.24): every
    -- destination rendered in order, floats bit-faithfully.
    "ok:values[" ++ stableJoin "," (ids.map (fun id =>
      match post.lookupValue id with
      | some v => exactValueString v
      | none => "missing")) ++ "]"
  | .ok (.terminator _, _) => "ok:terminator"
  | .error err => "error:" ++ err.stable

/-- Hex rendering of one byte, two digits. -/
def byteHex (b : UInt8) : String :=
  let digits := Nat.toDigits 16 b.toNat
  String.mk (if digits.length < 2 then '0' :: digits else digits)

/-- Run a straight-line list whose FIRST instruction allocates (so `v0` is
    the cell), then render the `n`-byte little-endian image stored there. -/
def runBytes (insts : List Inst) (n : Nat) : String :=
  match Sem.run
      (insts.foldlM (fun _ inst => stepInst inst) (InstrResult.value none))
      MachineState.empty with
  | .ok (_, post) =>
    match post.lookupValue v0 with
    | some (.ptr a _) =>
      match post.memory.readBytes a n with
      | some bs => "bytes:" ++ stableJoin "," (bs.map byteHex)
      | none => "bytes:uninit"
    | _ => "no-cell"
  | .error err => "error:" ++ err.stable

/-- Render the LAST value as its binary32 bit pattern (`encodeBits`), for the
    cross-engine table. The codec itself is anchored to the independent
    `floatExactString` rendering by the `codec_anchor_*` fixtures below. -/
def runF32Bits (insts : List Inst) : String :=
  match Sem.run
      (insts.foldlM (fun _ inst => stepInst inst) (InstrResult.value none))
      MachineState.empty with
  | .ok (.value (some id), post) =>
    match post.lookupValue id with
    | some (.float f) =>
      match encodeBits .binary32 f with
      | some bits =>
        let digits := Nat.toDigits 16 bits
        "ok:f32:0x" ++ String.mk (List.replicate (8 - digits.length) '0' ++ digits)
      | none => "ok:not-binary32:" ++ floatExactString f
    | some v => "ok:" ++ stableValueString v
    | none => "ok:missing"
  | .ok _ => "ok:none"
  | .error err => "error:" ++ err.stable

/-- `1.5` (binary64 bits 0x3ff8000000000000). -/
def f1_5 : Float := mkDyadic false 3 (-1)
/-- `0.1f32` as its exact binary64 value (binary32 bits 0x3dcccccd). -/
def f0_1f32 : Float := mkDyadic false 13421773 (-27)
/-- `0.2f32` as its exact binary64 value (binary32 bits 0x3e4ccccd). -/
def f0_2f32 : Float := mkDyadic false 13421773 (-26)
/-- `0.1` as binary64 (bits 0x3fb999999999999a) — NOT a binary32 value. -/
def f0_1 : Float := mkDyadic false 3602879701896397 (-55)
/-- `1/3` as binary64 (bits 0x3fd5555555555555). -/
def fThird : Float := mkDyadic false 6004799503160661 (-54)

/-- Store `x : ty` into a fresh cell and load it back. -/
def storeLoad (ty : Ty) (x : Float) : List Inst :=
  [.Alloca ty none none, .Const ty (.float x), .Store ty v0 v1 false none,
   .Load ty v0 false none]

/-- Store `x : ty` into a fresh cell (render the image with `runBytes`). -/
def storeOnly (ty : Ty) (x : Float) : List Inst :=
  [.Alloca ty none none, .Const ty (.float x), .Store ty v0 v1 false none]

-- =================================================================
-- Codec anchors: the IEEE codec against the independent frExp rendering
-- =================================================================

theorem codec_anchor_binary32_decode :
    floatExactString (decodeBits .binary32 0x3dcccccd) = "+7205759511166976p-56" := by
  native_decide

theorem codec_anchor_binary32_encode :
    encodeBits .binary32 f0_1f32 = some 0x3dcccccd := by
  native_decide

theorem codec_anchor_binary64_decode :
    floatExactString (decodeBits .binary64 0x3ff8000000000000) = "+6755399441055744p-52" := by
  native_decide

theorem codec_anchor_binary64_encode_subnormal :
    encodeBits .binary64 (mkDyadic false 1 (-1074)) = some 1 := by
  native_decide

/-- A binary64 value that is not a binary32 value has no binary32 image. -/
theorem codec_anchor_binary32_refuses_non_member :
    encodeBits .binary32 f0_1 = none := by
  native_decide

/-- Rounding a binary64 value to binary64 is the identity. -/
theorem codec_anchor_binary64_round_identity :
    floatExactString (roundToFormat .binary64 fThird) = floatExactString fThird := by
  native_decide

-- =================================================================
-- review/lean-float-memory-placeholder: real IEEE images (PASS)
-- =================================================================

/-- `store f64 1.5; load` gives `1.5` (it used to give `0.0`). -/
theorem review_lean_float_memory_placeholder_f64_roundtrip :
    runExact (storeLoad .F64 f1_5) = "ok:float:+6755399441055744p-52" := by
  native_decide

/-- The F64 image of `1.5` is its binary64 pattern 0x3ff8000000000000. -/
theorem review_lean_float_memory_placeholder_f64_image :
    runBytes (storeOnly .F64 f1_5) 8 = "bytes:00,00,00,00,00,00,f8,3f" := by
  native_decide

/-- `store f32 0.1f32; load` gives the f32 value 0x3dcccccd. -/
theorem review_lean_float_memory_placeholder_f32_roundtrip :
    runExact (storeLoad .F32 f0_1f32) = "ok:float:+7205759511166976p-56" := by
  native_decide

/-- The F32 image of `0.1f32` is 0x3dcccccd, four bytes. -/
theorem review_lean_float_memory_placeholder_f32_image :
    runBytes (storeOnly .F32 f0_1f32) 4 = "bytes:cd,cc,cc,3d" := by
  native_decide

/-- Width control: `1.5` at F32 is 0x3fc00000, not the F64 pattern's top half. -/
theorem review_lean_float_memory_placeholder_f32_image_width :
    runBytes (storeOnly .F32 f1_5) 4 = "bytes:00,00,c0,3f" := by
  native_decide

/-- Decode side on its own: an F64 load of the integer-written bits of `1.5`. -/
theorem review_lean_float_memory_placeholder_f64_decode :
    runExact [.Alloca .I64 none none, .Const .I64 (.int 0x3ff8000000000000),
      .Store .I64 v0 v1 false none, .Load .F64 v0 false none] =
      "ok:float:+6755399441055744p-52" := by
  native_decide

/-- Negative twin (right reason): an F32 store of a value that is not a
    binary32 value is refused as ill-typed — never silently rounded, never a
    placeholder. -/
theorem review_lean_float_memory_placeholder_f32_non_member_refused :
    runExact [.Alloca .F32 none none, .Const .F64 (.float f0_1),
      .Store .F32 v0 v1 false none] =
      "error:type_error:F32 value is not a binary32 value" := by
  native_decide

-- Edge images: ±0, ±inf, NaN, subnormals.

theorem float_image_f64_neg_zero :
    runBytes (storeOnly .F64 (-0.0)) 8 = "bytes:00,00,00,00,00,00,00,80" := by
  native_decide

theorem float_roundtrip_f64_neg_zero :
    runExact (storeLoad .F64 (-0.0)) = "ok:float:-0" := by
  native_decide

theorem float_image_f32_neg_zero :
    runBytes (storeOnly .F32 (-0.0)) 4 = "bytes:00,00,00,80" := by
  native_decide

theorem float_roundtrip_f32_neg_zero :
    runExact (storeLoad .F32 (-0.0)) = "ok:float:-0" := by
  native_decide

theorem float_image_f32_pos_inf :
    runBytes (storeOnly .F32 infF) 4 = "bytes:00,00,80,7f" := by
  native_decide

theorem float_image_f64_neg_inf :
    runBytes (storeOnly .F64 (-infF)) 8 = "bytes:00,00,00,00,00,00,f0,ff" := by
  native_decide

theorem float_roundtrip_f64_neg_inf :
    runExact (storeLoad .F64 (-infF)) = "ok:float:-inf" := by
  native_decide

/-- A NaN STORE refuses (the B3 NaN-payload residue): Lean 4.8.0 cannot
    observe a NaN's payload or sign, and the stored image IS observable —
    reload the cell at an integer type — so a canonical image would be a
    fabricated one. -/
theorem float_image_f32_nan_refused :
    runBytes (storeOnly .F32 floatNaN) 4 =
      "error:unsupported.float:NaN byte image unobservable (no Float.toBits in Lean 4.8.0)" := by
  native_decide

theorem float_roundtrip_f64_nan_refused :
    runExact (storeLoad .F64 floatNaN) =
      "error:unsupported.float:NaN byte image unobservable (no Float.toBits in Lean 4.8.0)" := by
  native_decide

/-- A NaN image the program wrote itself (an integer store) decodes to a NaN:
    the decode side needs no payload. -/
theorem float_decode_f32_nan_image :
    runExact [.Alloca .I32 none none, .Const .I32 (.int 0x7f800001),
      .Store .I32 v0 v1 false none, .Load .F32 v0 false none] = "ok:float:nan" := by
  native_decide

/-- The largest binary32 subnormal, (2^23 - 1)·2^-149 = 0x007fffff. -/
theorem float_image_f32_largest_subnormal :
    runBytes (storeOnly .F32 (mkDyadic false 8388607 (-149))) 4 = "bytes:ff,ff,7f,00" := by
  native_decide

theorem float_roundtrip_f32_largest_subnormal :
    runExact (storeLoad .F32 (mkDyadic false 8388607 (-149))) =
      "ok:float:+9007198180999168p-179" := by
  native_decide

/-- The least binary64 subnormal, 2^-1074. -/
theorem float_image_f64_least_subnormal :
    runBytes (storeOnly .F64 (mkDyadic false 1 (-1074))) 8 =
      "bytes:01,00,00,00,00,00,00,00" := by
  native_decide

theorem float_roundtrip_f64_least_subnormal :
    runExact (storeLoad .F64 (mkDyadic false 1 (-1074))) =
      "ok:float:+4503599627370496p-1126" := by
  native_decide

-- =================================================================
-- trust-ir-self-declared/lean-semantic-depth-ledger, float row (PASS)
-- =================================================================

/-- `fadd f32 0.1, 0.2` gives 0x3e99999a, not the binary64 sum. -/
theorem lean_semantic_depth_ledger_float_fadd_f32 :
    runExact [.Const .F32 (.float f0_1f32), .Const .F32 (.float f0_2f32),
      .BinOp .FAdd .F32 v0 v1] = "ok:float:+5404319767592960p-54" := by
  native_decide

/-- Control: the same operands at F64 give the binary64 sum, which differs. -/
theorem lean_semantic_depth_ledger_float_fadd_f64_control :
    runExact [.Const .F64 (.float f0_1f32), .Const .F64 (.float f0_2f32),
      .BinOp .FAdd .F64 v0 v1] = "ok:float:+5404319633375232p-54" := by
  native_decide

/-- `fptrunc f64 → f32` of `1/3` is 0x3eaaaaab (it was the identity). -/
theorem lean_semantic_depth_ledger_float_fptrunc_third :
    runExact [.Const .F64 (.float fThird), .Cast .FPTrunc .F64 .F32 v0] =
      "ok:float:+6004799682117632p-54" := by
  native_decide

/-- The proof program's `fn avg(a: f32, b: f32) -> f32 { (a + b) / 2.0 }` at
    `a = 16777216, b = 1`: in f32 the sum rounds back to 16777216 and the mean
    is 8388608; at binary64 it would be 8388608.5. -/
theorem lean_semantic_depth_ledger_float_avg_f32 :
    runExact [.Const .F32 (.float (mkDyadic false 1 24)), .Const .F32 (.float 1.0),
      .BinOp .FAdd .F32 v0 v1, .Const .F32 (.float 2.0),
      .BinOp .FDiv .F32 v2 v3] = "ok:float:+4503599627370496p-29" := by
  native_decide

/-- A `Const` of type F32 is its literal rounded to binary32 once:
    16777217 → 16777216. -/
theorem lean_semantic_depth_ledger_float_const_rounds :
    runExact [.Const .F32 (.float (mkDyadic false 16777217 0))] =
      "ok:float:+4503599627370496p-28" := by
  native_decide

/-- `uitofp u64 → f32` rounds the INTEGER once: 2^60 + 2^36 + 1 is above the
    halfway point, so it rounds up to 2^60 + 2^37. Through a binary64
    intermediate it would round to 2^60 + 2^36 first, then tie to even 2^60. -/
theorem lean_semantic_depth_ledger_float_uitofp_no_double_rounding :
    runExact [.Const .U64 (.int 1152921573326323713), .Cast .UIToFP .U64 .F32 v0] =
      "ok:float:+4503600164241408p8" := by
  native_decide

/-- The same at F64 from a 128-bit source: 2^100 + 2^47 + 1 rounds up to
    2^100 + 2^48 (the former `Float.ofNat` truncated to 64 bits first and
    answered 2^100). -/
theorem lean_semantic_depth_ledger_float_uitofp_f64_u128_rounds_once :
    runExact [.Const .U128 (.int 1267650600228229542234191560705),
      .Cast .UIToFP .U128 .F64 v0] = "ok:float:+4503599627370497p48" := by
  native_decide

/-- `sitofp i64 → f32` of the negated value rounds symmetrically. -/
theorem lean_semantic_depth_ledger_float_sitofp_negative :
    runExact [.Const .I64 (.int (-1152921573326323713)), .Cast .SIToFP .I64 .F32 v0] =
      "ok:float:-4503600164241408p8" := by
  native_decide

/-- An F32 comparison compares binary32 values. -/
theorem lean_semantic_depth_ledger_float_fcmp_f32 :
    runExact [.Const .F32 (.float f0_1f32), .Const .F32 (.float f0_2f32),
      .FCmp .OLt .F32 v0 v1] = "ok:bool:true" := by
  native_decide

/-- `bitcast i32 → f32` reinterprets the IEEE pattern (it used to mint an
    int-shaped value of type F32). -/
theorem lean_semantic_depth_ledger_float_bitcast_i32_to_f32 :
    runExact [.Const .I32 (.int 0x3fc00000), .Cast .Bitcast .I32 .F32 v0] =
      "ok:float:+6755399441055744p-52" := by
  native_decide

theorem lean_semantic_depth_ledger_float_bitcast_f32_to_i32 :
    runExact [.Const .F32 (.float f1_5), .Cast .Bitcast .F32 .I32 v0] =
      "ok:int32:1069547520" := by
  native_decide

-- Negative twins (right reason).

/-- An F32 operation on a value that is not a binary32 value is ill-typed. -/
theorem lean_semantic_depth_ledger_float_non_member_operand_refused :
    runExact [.Const .F64 (.float f0_1), .Const .F32 (.float f0_2f32),
      .BinOp .FAdd .F32 v0 v1] =
      "error:type_error:F32 value is not a binary32 value" := by
  native_decide

/-- Binary16 uses the same typed arithmetic and cast path. -/
theorem lean_semantic_depth_ledger_float_f16_add :
    runExact [.Const .F16 (.float f1_5), .Const .F16 (.float f1_5),
      .BinOp .FAdd .F16 v0 v1] =
      "ok:float:+6755399441055744p-51" := by
  native_decide

theorem lean_semantic_depth_ledger_float_fptrunc_f16 :
    runExact [.Const .F64 (.float f1_5), .Cast .FPTrunc .F64 .F16 v0] =
      "ok:float:+6755399441055744p-52" := by
  native_decide

theorem float_f16_non_member_operand_refused :
    runExact [.Const .F64 (.float f0_1), .Const .F16 (.float f1_5),
      .BinOp .FAdd .F16 v0 v1] =
      "error:type_error:F16 value is not a binary16 value" := by
  native_decide

theorem float_f16_store_load :
    runExact (storeLoad .F16 f1_5) = "ok:float:+6755399441055744p-52" := by
  native_decide

theorem float_f16_midpoint_even_down :
    runExact [.Const .F64 (.float (mkDyadic false 2049 (-11))),
      .Cast .FPTrunc .F64 .F16 v0, .Cast .Bitcast .F16 .U16 v1] =
      "ok:int16:15360" := by
  native_decide

theorem float_f16_midpoint_even_up :
    runExact [.Const .F64 (.float (mkDyadic false 2051 (-11))),
      .Cast .FPTrunc .F64 .F16 v0, .Cast .Bitcast .F16 .U16 v1] =
      "ok:int16:15362" := by
  native_decide

theorem float_f16_integer_rounding :
    runExact [.Const .U64 (.int 2049), .Cast .UIToFP .U64 .F16 v0,
      .Cast .Bitcast .F16 .U16 v1] = "ok:int16:26624" := by
  native_decide

theorem float_f16_nan_bitcast_refused :
    runExact [.Const .F16 (.float floatNaN), .Cast .Bitcast .F16 .U16 v0] =
      "error:unsupported.float:NaN payload unobservable (no Float.toBits in Lean 4.8.0)" := by
  native_decide

theorem float_f16_nan_store_refused :
    runExact (storeOnly .F16 floatNaN) =
      "error:unsupported.float:NaN byte image unobservable (no Float.toBits in Lean 4.8.0)" := by
  native_decide

/-- Reading a NaN's bits refuses: Lean 4.8.0 cannot observe its payload. -/
theorem lean_semantic_depth_ledger_float_bitcast_nan_refused :
    runExact [.Const .F32 (.float floatNaN), .Cast .Bitcast .F32 .I32 v0] =
      "error:unsupported.float:NaN payload unobservable (no Float.toBits in Lean 4.8.0)" := by
  native_decide

/-- A float BinOp at a NON-float type is a type error, not a binary64 answer. -/
theorem float_binop_at_int_type_is_type_error :
    runExact [.Const .F64 (.float f1_5), .Const .F64 (.float f1_5),
      .BinOp .FAdd .I64 v0 v1] =
      "error:type_error:float value at non-float type TrustIr.Ty.I64" := by
  native_decide

-- =================================================================
-- WS2.23 review: adversarial rows (Rust halves in numerics_policy.rs,
-- `ws2_23_review_*`)
-- =================================================================

/-- Render the LAST value; a vector or aggregate renders its float lanes
    bit-faithfully (`stableValueString` would print them at 6 decimals). -/
def runExactLanesUsing (step : Inst → Sem InstrResult) (insts : List Inst) : String :=
  match Sem.run
      (insts.foldlM (fun _ inst => step inst) (InstrResult.value none))
      MachineState.empty with
  | .ok (.value (some id), post) =>
    match post.lookupValue id with
    | some (.vector ls) => "ok:vector[" ++ stableJoin "," (ls.map exactValueString) ++ "]"
    | some (.aggregate ls) =>
      "ok:aggregate[" ++ stableJoin "," (ls.map exactValueString) ++ "]"
    | some v => "ok:" ++ exactValueString v
    | none => "ok:missing"
  | .ok (.values ids, post) =>
    -- WS2.24: `CmpXchg` / `Overflow` bind TWO destinations, rendered in order.
    "ok:values[" ++ stableJoin "," (ids.map (fun id =>
      match post.lookupValue id with
      | some v => exactValueString v
      | none => "missing")) ++ "]"
  | .ok _ => "ok:none"
  | .error err => "error:" ++ err.stable

def runExactLanes (insts : List Inst) : String :=
  runExactLanesUsing (fun inst => stepInst inst) insts

/-- (1) A signalling-NaN pattern made by `bitcast i32 → f32`, stored as F32
    and reloaded as I32. The real program (and the interpreter, which keeps
    `FloatBits`) reads back 0x7f800001; a canonical-NaN store image read back
    0x7fc00000 — a fabricated integer. The store now refuses. -/
theorem ws2_23_review_snan_store_reload_refused :
    runExact [.Alloca .F32 none none, .Const .I32 (.int 0x7f800001),
      .Cast .Bitcast .I32 .F32 v1, .Store .F32 v0 v2 false none,
      .Load .I32 v0 false none] =
      "error:unsupported.float:NaN byte image unobservable (no Float.toBits in Lean 4.8.0)" := by
  native_decide

/-- The same through `fneg` of a NaN: the real image has the sign bit SET,
    which the model cannot see (a Lean NaN's sign is unobservable). -/
theorem ws2_23_review_fneg_nan_store_refused :
    runExact [.Alloca .F32 none none, .Const .F32 (.float floatNaN), .UnOp .FNeg .F32 v1,
      .Store .F32 v0 v2 false none, .Load .I32 v0 false none] =
      "error:unsupported.float:NaN byte image unobservable (no Float.toBits in Lean 4.8.0)" := by
  native_decide

/-- (2) A TUPLE constant resolves each float field at its field type: the F32
    field of `(0.1, 0.1) : (f32, f64)` is 0x3dcccccd (the interpreter's
    `constant_to_value` recursion), the F64 field keeps binary64 0.1. It used
    to materialize the F32 field as binary64 0.1 — a value no `f32` has — and
    `ExtractField` + `Return` carried it out unchecked. -/
theorem ws2_23_review_tuple_const_f32_field_rounds :
    runExactLanes [.Const (.Tuple [.F32, .F64]) (.aggregate [.float f0_1, .float f0_1])] =
      "ok:aggregate[float:+7205759511166976p-56,float:+7205759403792794p-56]" := by
  native_decide

theorem ws2_23_review_tuple_const_extract_f32 :
    runExact [.Const (.Tuple [.F32, .F64]) (.aggregate [.float f0_1, .float f0_1]),
      .ExtractField .F32 v0 0] = "ok:float:+7205759511166976p-56" := by
  native_decide

/-- A VECTOR constant resolves each float lane at the element type. -/
theorem ws2_23_review_vector_const_f32_lanes_round :
    runExactLanes [.Const (.Vector 2 .F32) (.vector [.float f0_1, .float fThird])] =
      "ok:vector[float:+7205759511166976p-56,float:+6004799682117632p-54]" := by
  native_decide

/-- A STRUCT constant's field types are named by id, which the step rule
    cannot resolve: a float field whose value differs between F32 and F64
    refuses rather than guessing a width. -/
theorem ws2_23_review_struct_const_inexact_float_refused :
    runExact [.Const (.Struct ⟨0⟩) (.aggregate [.float f0_1])] =
      "error:unsupported.float:" ++ constWidthAmbiguousMsg := by
  native_decide

/-- The actual declaration supplies the float width and integer field type;
    an exact binary32 payload alone cannot establish a named struct's type. -/
def floatStructContext : EvalContext :=
  { EvalContext.empty with
    structs := fun id => if id.index == 0 then some
      { id := StructId.mk 0, name := "FloatStruct",
        fields := [{ name := "float", ty := .F32, offset := none },
                   { name := "integer", ty := .I64, offset := none }],
        size := none, align := none }
      else none }

/-- A binary32-exact field keeps its value under the declared F32 type. -/
theorem ws2_23_review_struct_const_exact_float_admitted :
    runExactLanesUsing (stepInstWithContext floatStructContext)
      [.Const (.Struct ⟨0⟩) (.aggregate [.float f0_1f32, .int 7])] =
      "ok:aggregate[float:+7205759511166976p-56,int64:7]" := by
  native_decide

/-- The same declaration rounds an inexact binary64 payload to F32. -/
theorem ws2_23_review_struct_const_inexact_float_with_definition_rounds :
    runExactLanesUsing (stepInstWithContext floatStructContext)
      [.Const (.Struct ⟨0⟩) (.aggregate [.float f0_1, .int 7])] =
      "ok:aggregate[float:+7205759511166976p-56,int64:7]" := by
  native_decide

/-- Even an exact payload needs the named declaration and field census. -/
theorem ws2_23_review_struct_const_exact_float_without_definition_refused :
    runExactLanes [.Const (.Struct ⟨0⟩) (.aggregate [.float f0_1f32, .int 7])] =
      "error:unsupported.enum_def_table:Const: a struct constant's fields need the module's struct table" := by
  native_decide

/-- The same guard reaches nested and sequence positions. -/
theorem ws2_23_review_sequence_const_inexact_float_refused :
    runExact [.Const (.Tuple [.Struct ⟨0⟩]) (.aggregate [.aggregate [.float f0_1]])] =
      "error:unsupported.float:" ++ constWidthAmbiguousMsg := by
  native_decide

/-- (3) `cmpxchg` at F32 compares the IEEE PATTERN: a matching expected value
    succeeds and writes the desired value (it used to report failure for
    every float and skip the write). -/
theorem ws2_23_review_cmpxchg_f32_success :
    runExactLanes [.Alloca .F32 none none, .Const .F32 (.float f1_5),
      .Store .F32 v0 v1 false none, .Const .F32 (.float 2.0),
      .CmpXchg .F32 v0 v1 v2 .SeqCst .SeqCst false] =
      "ok:values[float:+6755399441055744p-52,bool:true]" := by
  native_decide

theorem ws2_23_review_cmpxchg_f32_writes_desired :
    runExact [.Alloca .F32 none none, .Const .F32 (.float f1_5),
      .Store .F32 v0 v1 false none, .Const .F32 (.float 2.0),
      .CmpXchg .F32 v0 v1 v2 .SeqCst .SeqCst false, .Load .F32 v0 false none] =
      "ok:float:+4503599627370496p-51" := by
  native_decide

/-- Bitwise, not IEEE `==`: `-0.0` does not match a stored `+0.0`. -/
theorem ws2_23_review_cmpxchg_f32_signed_zero_differs :
    runExactLanes [.Alloca .F32 none none, .Const .F32 (.float 0.0),
      .Store .F32 v0 v1 false none, .Const .F32 (.float (-0.0)),
      .CmpXchg .F32 v0 v2 v2 .SeqCst .SeqCst false] =
      "ok:values[float:+0,bool:false]" := by
  native_decide

/-- A NaN operand refuses: its bits are unobservable. -/
theorem ws2_23_review_cmpxchg_f32_nan_refused :
    runExact [.Alloca .I32 none none, .Const .I32 (.int 0x7fc00000),
      .Store .I32 v0 v1 false none, .Const .F32 (.float f1_5),
      .CmpXchg .F32 v0 v2 v2 .SeqCst .SeqCst false] =
      "error:unsupported.float:NaN payload unobservable (no Float.toBits in Lean 4.8.0)" := by
  native_decide

-- =================================================================
-- Cross-engine table (Rust half: numerics_policy.rs F32_CROSS_ENGINE_TABLE)
-- =================================================================

/-- A binary32 constant from its bit pattern. -/
def c32 (bits : Nat) : Inst := .Const .F32 (.float (decodeBits .binary32 bits))
/-- A binary64 constant from its bit pattern. -/
def c64 (bits : Nat) : Inst := .Const .F64 (.float (decodeBits .binary64 bits))

theorem f32_table_fadd_0_1_0_2 :
    runF32Bits [c32 0x3dcccccd, c32 0x3e4ccccd, .BinOp .FAdd .F32 v0 v1] =
      "ok:f32:0x3e99999a" := by native_decide
theorem f32_table_fsub_one_minus_half_ulp :
    runF32Bits [c32 0x3f800000, c32 0x33800000, .BinOp .FSub .F32 v0 v1] =
      "ok:f32:0x3f7fffff" := by native_decide
theorem f32_table_fmul_0_1_squared :
    runF32Bits [c32 0x3dcccccd, c32 0x3dcccccd, .BinOp .FMul .F32 v0 v1] =
      "ok:f32:0x3c23d70b" := by native_decide
theorem f32_table_fdiv_one_third :
    runF32Bits [c32 0x3f800000, c32 0x40400000, .BinOp .FDiv .F32 v0 v1] =
      "ok:f32:0x3eaaaaab" := by native_decide
theorem f32_table_frem_5_25_by_2 :
    runF32Bits [c32 0x40a80000, c32 0x40000000, .BinOp .FRem .F32 v0 v1] =
      "ok:f32:0x3fa00000" := by native_decide
theorem f32_table_fmul_overflow_to_inf :
    runF32Bits [c32 0x7f7fffff, c32 0x40000000, .BinOp .FMul .F32 v0 v1] =
      "ok:f32:0x7f800000" := by native_decide
theorem f32_table_fmul_to_subnormal :
    runF32Bits [c32 0x00800000, c32 0x3f000000, .BinOp .FMul .F32 v0 v1] =
      "ok:f32:0x00400000" := by native_decide
theorem f32_table_fdiv_half_least_subnormal_ties_to_zero :
    runF32Bits [c32 0x00000001, c32 0x40000000, .BinOp .FDiv .F32 v0 v1] =
      "ok:f32:0x00000000" := by native_decide
theorem f32_table_fdiv_three_halves_least_subnormal_ties_even :
    runF32Bits [c32 0x00000003, c32 0x40000000, .BinOp .FDiv .F32 v0 v1] =
      "ok:f32:0x00000002" := by native_decide
theorem f32_table_fadd_2p24_plus_one :
    runF32Bits [c32 0x4b800000, c32 0x3f800000, .BinOp .FAdd .F32 v0 v1] =
      "ok:f32:0x4b800000" := by native_decide
theorem f32_table_fptrunc_third :
    runF32Bits [c64 0x3fd5555555555555, .Cast .FPTrunc .F64 .F32 v0] =
      "ok:f32:0x3eaaaaab" := by native_decide
theorem f32_table_fptrunc_overflow_threshold_tie :
    runF32Bits [c64 0x47effffff0000000, .Cast .FPTrunc .F64 .F32 v0] =
      "ok:f32:0x7f800000" := by native_decide
theorem f32_table_fptrunc_below_overflow_threshold :
    runF32Bits [c64 0x47efffffefffffff, .Cast .FPTrunc .F64 .F32 v0] =
      "ok:f32:0x7f7fffff" := by native_decide
theorem f32_table_fptrunc_half_least_subnormal :
    runF32Bits [c64 0x3690000000000000, .Cast .FPTrunc .F64 .F32 v0] =
      "ok:f32:0x00000000" := by native_decide
theorem f32_table_fptrunc_three_halves_least_subnormal :
    runF32Bits [c64 0x36a8000000000000, .Cast .FPTrunc .F64 .F32 v0] =
      "ok:f32:0x00000002" := by native_decide
theorem f32_table_fptrunc_one_plus_half_ulp_ties_even :
    runF32Bits [c64 0x3ff0000010000000, .Cast .FPTrunc .F64 .F32 v0] =
      "ok:f32:0x3f800000" := by native_decide
theorem f32_table_fptrunc_one_plus_half_ulp_sticky :
    runF32Bits [c64 0x3ff0000010000004, .Cast .FPTrunc .F64 .F32 v0] =
      "ok:f32:0x3f800001" := by native_decide
theorem f32_table_fptrunc_negative_underflow_keeps_sign :
    runF32Bits [c64 0xb690000000000000, .Cast .FPTrunc .F64 .F32 v0] =
      "ok:f32:0x80000000" := by native_decide
theorem f32_table_fptrunc_neg_zero :
    runF32Bits [c64 0x8000000000000000, .Cast .FPTrunc .F64 .F32 v0] =
      "ok:f32:0x80000000" := by native_decide
theorem f32_table_fptrunc_neg_inf :
    runF32Bits [c64 0xfff0000000000000, .Cast .FPTrunc .F64 .F32 v0] =
      "ok:f32:0xff800000" := by native_decide
theorem f32_table_uitofp_u64_no_double_rounding :
    runF32Bits [.Const .U64 (.int 1152921573326323713), .Cast .UIToFP .U64 .F32 v0] =
      "ok:f32:0x5d800001" := by native_decide
theorem f32_table_sitofp_i64_no_double_rounding :
    runF32Bits [.Const .I64 (.int (-1152921573326323713)), .Cast .SIToFP .I64 .F32 v0] =
      "ok:f32:0xdd800001" := by native_decide
theorem f32_table_uitofp_u32_max :
    runF32Bits [.Const .U32 (.int 4294967295), .Cast .UIToFP .U32 .F32 v0] =
      "ok:f32:0x4f800000" := by native_decide

end FloatFixtures

end TrustIr
