-- Copyright 2026 Andrew Yates
-- Licensed under the Apache License, Version 2.0
import SemRDeclaredDivisionChecks
import TrustIrEval.Decode
import TrustIrEval.ConstantLayerControls
import TrustIr.DecodedContext

/-! Exact original WP division_question packet. The full public/native packet,
result and same-derivation witness are retained in the adjacent fixture. The
byte list and JSON value below directly quote its two module carriers.
Existing decoders/context assembly own every interpretation. This is scalar
execution, not integer-text entry-codec, guarded-consumer, source/ABI or grade
 authority. -/

namespace SemR.CanonicalDeclaredDivision.Packet
set_option maxRecDepth 20000
open TrustIr

def originalBytes : List Nat := [84, 82, 85, 83, 84, 95, 73, 82, 41, 0, 0, 0, 15, 31, 116, 114, 117, 115, 116, 95, 119, 112, 95, 116, 114, 117, 115, 116, 95, 105, 114, 95, 110, 97, 116, 105, 118, 101, 95, 100, 105, 114, 101, 99, 116, 7, 80, 97, 105, 114, 73, 54, 52, 5, 118, 97, 108, 117, 101, 31, 100, 101, 109, 111, 58, 58, 118, 101, 114, 105, 102, 105, 101, 100, 95, 102, 114, 111, 109, 95, 116, 109, 105, 114, 95, 110, 97, 116, 105, 118, 101, 46, 116, 114, 117, 115, 116, 45, 119, 112, 32, 112, 114, 111, 118, 101, 115, 32, 116, 104, 101, 32, 116, 77, 73, 82, 45, 99, 97, 114, 114, 105, 101, 100, 32, 112, 111, 115, 116, 99, 111, 110, 100, 105, 116, 105, 111, 110, 21, 116, 114, 117, 115, 116, 45, 119, 112, 46, 112, 117, 114, 101, 45, 101, 120, 112, 114, 46, 118, 49, 4, 116, 114, 117, 101, 4, 112, 111, 115, 116, 20, 116, 114, 117, 115, 116, 45, 97, 115, 115, 101, 114, 116, 105, 111, 110, 58, 112, 111, 115, 116, 15, 111, 98, 108, 105, 103, 97, 116, 105, 111, 110, 58, 112, 111, 115, 116, 6, 100, 32, 33, 61, 32, 48, 1, 100, 5, 101, 110, 116, 114, 121, 21, 116, 114, 117, 115, 116, 45, 97, 115, 115, 101, 114, 116, 105, 111, 110, 58, 101, 110, 116, 114, 121, 16, 111, 98, 108, 105, 103, 97, 116, 105, 111, 110, 58, 101, 110, 116, 114, 121, 0, 1, 1, 8, 1, 8, 0, 1, 0, 1, 1, 2, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 8, 0, 0, 0, 0, 0, 0, 0, 1, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 5, 1, 0, 3, 0, 0, 1, 0, 1, 0, 8, 3, 25, 8, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 3, 8, 1, 0, 1, 2, 0, 0, 0, 0, 20, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 4, 1, 5, 6, 0, 0, 0, 1, 0, 1, 7, 8, 0, 1, 9, 0, 93, 78, 163, 5, 202, 161, 213, 50, 152, 16, 235, 102, 85, 185, 221, 136, 13, 166, 29, 89, 59, 107, 13, 66, 169, 114, 157, 59, 116, 209, 24, 10, 0, 1, 0, 0, 4, 1, 5, 10, 0, 0, 1, 11, 2, 64, 0, 0, 1, 0, 1, 12, 13, 0, 1, 14, 0, 38, 89, 219, 91, 52, 49, 219, 212, 42, 220, 204, 218, 160, 117, 22, 99, 201, 123, 204, 34, 240, 245, 187, 244, 73, 63, 193, 51, 150, 34, 167, 216, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def moduleJson : Lean.Json := Lean.Json.mkObj [("closure_layouts", Lean.Json.arr #[]), ("closure_types", Lean.Json.arr #[]), ("completeness", Lean.Json.null), ("drop_glue", Lean.Json.arr #[]), ("enums", Lean.Json.arr #[]), ("files", Lean.Json.arr #[]), ("func_types", Lean.Json.arr #[(Lean.Json.mkObj [("is_vararg", Lean.Json.bool false), ("params", Lean.Json.arr #[(Lean.Json.str "U64")]), ("returns", Lean.Json.arr #[(Lean.Json.str "U64")])])]), ("functions", Lean.Json.arr #[(Lean.Json.mkObj [("attrs", Lean.Json.mkObj [("cold", Lean.Json.bool false), ("inlinehint", Lean.Json.bool false), ("naked", Lean.Json.bool false), ("params", Lean.Json.arr #[]), ("readnone", Lean.Json.bool false), ("readonly", Lean.Json.bool false), ("target_features", Lean.Json.arr #[])]), ("blocks", Lean.Json.arr #[(Lean.Json.mkObj [("body", Lean.Json.arr #[(Lean.Json.mkObj [("inst", Lean.Json.mkObj [("Const", Lean.Json.mkObj [("ty", Lean.Json.str "U64"), ("value", Lean.Json.mkObj [("Int", Lean.Json.num (Lean.JsonNumber.fromNat 1))])])]), ("proof_context", Lean.Json.null), ("proofs", Lean.Json.arr #[]), ("results", Lean.Json.arr #[(Lean.Json.num (Lean.JsonNumber.fromNat 1))]), ("span", Lean.Json.null)]), (Lean.Json.mkObj [("inst", Lean.Json.mkObj [("BinOp", Lean.Json.mkObj [("lhs", Lean.Json.num (Lean.JsonNumber.fromNat 1)), ("op", Lean.Json.str "UDiv"), ("rhs", Lean.Json.num (Lean.JsonNumber.fromNat 0)), ("ty", Lean.Json.str "U64")])]), ("proof_context", Lean.Json.null), ("proofs", Lean.Json.arr #[]), ("results", Lean.Json.arr #[(Lean.Json.num (Lean.JsonNumber.fromNat 2))]), ("span", Lean.Json.null)]), (Lean.Json.mkObj [("inst", Lean.Json.mkObj [("Return", Lean.Json.mkObj [("values", Lean.Json.arr #[(Lean.Json.num (Lean.JsonNumber.fromNat 2))])])]), ("proof_context", Lean.Json.null), ("proofs", Lean.Json.arr #[]), ("results", Lean.Json.arr #[]), ("span", Lean.Json.null)])]), ("id", Lean.Json.num (Lean.JsonNumber.fromNat 0)), ("params", Lean.Json.arr #[(Lean.Json.arr #[(Lean.Json.num (Lean.JsonNumber.fromNat 0)), (Lean.Json.str "U64")])])])]), ("body_gate", Lean.Json.null), ("calling_conv", Lean.Json.str "C"), ("display_path", Lean.Json.null), ("entry", Lean.Json.num (Lean.JsonNumber.fromNat 0)), ("id", Lean.Json.num (Lean.JsonNumber.fromNat 0)), ("linkage", Lean.Json.str "External"), ("name", Lean.Json.str "demo::verified_from_tmir_native"), ("producer", Lean.Json.null), ("proofs", Lean.Json.arr #[]), ("scopes", Lean.Json.null), ("section", Lean.Json.null), ("source_provenance", Lean.Json.null), ("summary", Lean.Json.null), ("ty", Lean.Json.num (Lean.JsonNumber.fromNat 0)), ("value_names", Lean.Json.null), ("visibility", Lean.Json.str "Default")])]), ("global_asm", Lean.Json.arr #[]), ("globals", Lean.Json.arr #[]), ("imports", Lean.Json.arr #[]), ("name", Lean.Json.str "trust_wp_trust_ir_native_direct"), ("obligation_diagnostics", Lean.Json.arr #[]), ("predicates", Lean.Json.arr #[]), ("proof_certificates", Lean.Json.arr #[]), ("proof_obligations", Lean.Json.arr #[(Lean.Json.mkObj [("description", Lean.Json.str "trust-wp proves the tMIR-carried postcondition"), ("formula", Lean.Json.mkObj [("payload", Lean.Json.str "true"), ("schema", Lean.Json.str "trust-wp.pure-expr.v1"), ("smtlib", Lean.Json.null), ("sort", Lean.Json.null)]), ("function", Lean.Json.num (Lean.JsonNumber.fromNat 0)), ("id", Lean.Json.num (Lean.JsonNumber.fromNat 0)), ("kind", Lean.Json.str "Postcondition"), ("site", Lean.Json.null), ("source", Lean.Json.mkObj [("assertion_id", Lean.Json.str "trust-assertion:post"), ("public", Lean.Json.mkObj [("obligation_id", Lean.Json.str "obligation:post"), ("semantic_digest", Lean.Json.mkObj [("algorithm", Lean.Json.str "Sha256"), ("bytes", Lean.Json.arr #[(Lean.Json.num (Lean.JsonNumber.fromNat 93)), (Lean.Json.num (Lean.JsonNumber.fromNat 78)), (Lean.Json.num (Lean.JsonNumber.fromNat 163)), (Lean.Json.num (Lean.JsonNumber.fromNat 5)), (Lean.Json.num (Lean.JsonNumber.fromNat 202)), (Lean.Json.num (Lean.JsonNumber.fromNat 161)), (Lean.Json.num (Lean.JsonNumber.fromNat 213)), (Lean.Json.num (Lean.JsonNumber.fromNat 50)), (Lean.Json.num (Lean.JsonNumber.fromNat 152)), (Lean.Json.num (Lean.JsonNumber.fromNat 16)), (Lean.Json.num (Lean.JsonNumber.fromNat 235)), (Lean.Json.num (Lean.JsonNumber.fromNat 102)), (Lean.Json.num (Lean.JsonNumber.fromNat 85)), (Lean.Json.num (Lean.JsonNumber.fromNat 185)), (Lean.Json.num (Lean.JsonNumber.fromNat 221)), (Lean.Json.num (Lean.JsonNumber.fromNat 136)), (Lean.Json.num (Lean.JsonNumber.fromNat 13)), (Lean.Json.num (Lean.JsonNumber.fromNat 166)), (Lean.Json.num (Lean.JsonNumber.fromNat 29)), (Lean.Json.num (Lean.JsonNumber.fromNat 89)), (Lean.Json.num (Lean.JsonNumber.fromNat 59)), (Lean.Json.num (Lean.JsonNumber.fromNat 107)), (Lean.Json.num (Lean.JsonNumber.fromNat 13)), (Lean.Json.num (Lean.JsonNumber.fromNat 66)), (Lean.Json.num (Lean.JsonNumber.fromNat 169)), (Lean.Json.num (Lean.JsonNumber.fromNat 114)), (Lean.Json.num (Lean.JsonNumber.fromNat 157)), (Lean.Json.num (Lean.JsonNumber.fromNat 59)), (Lean.Json.num (Lean.JsonNumber.fromNat 116)), (Lean.Json.num (Lean.JsonNumber.fromNat 209)), (Lean.Json.num (Lean.JsonNumber.fromNat 24)), (Lean.Json.num (Lean.JsonNumber.fromNat 10))])])]), ("range", Lean.Json.null), ("source_id", Lean.Json.str "post")]), ("status", Lean.Json.str "Pending")]), (Lean.Json.mkObj [("description", Lean.Json.str "trust-wp proves the tMIR-carried postcondition"), ("formula", Lean.Json.mkObj [("bindings", Lean.Json.arr #[(Lean.Json.arr #[(Lean.Json.str "d"), (Lean.Json.mkObj [("place", Lean.Json.mkObj [("Param", Lean.Json.mkObj [("index", Lean.Json.num (Lean.JsonNumber.fromNat 0))])]), ("sort", Lean.Json.mkObj [("BitVec", Lean.Json.num (Lean.JsonNumber.fromNat 64))])])])]), ("payload", Lean.Json.str "d != 0"), ("schema", Lean.Json.str "trust-wp.pure-expr.v1"), ("smtlib", Lean.Json.null), ("sort", Lean.Json.null)]), ("function", Lean.Json.num (Lean.JsonNumber.fromNat 0)), ("id", Lean.Json.num (Lean.JsonNumber.fromNat 1)), ("kind", Lean.Json.str "Precondition"), ("site", Lean.Json.null), ("source", Lean.Json.mkObj [("assertion_id", Lean.Json.str "trust-assertion:entry"), ("public", Lean.Json.mkObj [("obligation_id", Lean.Json.str "obligation:entry"), ("semantic_digest", Lean.Json.mkObj [("algorithm", Lean.Json.str "Sha256"), ("bytes", Lean.Json.arr #[(Lean.Json.num (Lean.JsonNumber.fromNat 38)), (Lean.Json.num (Lean.JsonNumber.fromNat 89)), (Lean.Json.num (Lean.JsonNumber.fromNat 219)), (Lean.Json.num (Lean.JsonNumber.fromNat 91)), (Lean.Json.num (Lean.JsonNumber.fromNat 52)), (Lean.Json.num (Lean.JsonNumber.fromNat 49)), (Lean.Json.num (Lean.JsonNumber.fromNat 219)), (Lean.Json.num (Lean.JsonNumber.fromNat 212)), (Lean.Json.num (Lean.JsonNumber.fromNat 42)), (Lean.Json.num (Lean.JsonNumber.fromNat 220)), (Lean.Json.num (Lean.JsonNumber.fromNat 204)), (Lean.Json.num (Lean.JsonNumber.fromNat 218)), (Lean.Json.num (Lean.JsonNumber.fromNat 160)), (Lean.Json.num (Lean.JsonNumber.fromNat 117)), (Lean.Json.num (Lean.JsonNumber.fromNat 22)), (Lean.Json.num (Lean.JsonNumber.fromNat 99)), (Lean.Json.num (Lean.JsonNumber.fromNat 201)), (Lean.Json.num (Lean.JsonNumber.fromNat 123)), (Lean.Json.num (Lean.JsonNumber.fromNat 204)), (Lean.Json.num (Lean.JsonNumber.fromNat 34)), (Lean.Json.num (Lean.JsonNumber.fromNat 240)), (Lean.Json.num (Lean.JsonNumber.fromNat 245)), (Lean.Json.num (Lean.JsonNumber.fromNat 187)), (Lean.Json.num (Lean.JsonNumber.fromNat 244)), (Lean.Json.num (Lean.JsonNumber.fromNat 73)), (Lean.Json.num (Lean.JsonNumber.fromNat 63)), (Lean.Json.num (Lean.JsonNumber.fromNat 193)), (Lean.Json.num (Lean.JsonNumber.fromNat 51)), (Lean.Json.num (Lean.JsonNumber.fromNat 150)), (Lean.Json.num (Lean.JsonNumber.fromNat 34)), (Lean.Json.num (Lean.JsonNumber.fromNat 167)), (Lean.Json.num (Lean.JsonNumber.fromNat 216))])])]), ("range", Lean.Json.null), ("source_id", Lean.Json.str "entry")]), ("status", Lean.Json.str "Pending")])]), ("records", Lean.Json.arr #[]), ("spec_modules", Lean.Json.arr #[]), ("structs", Lean.Json.arr #[(Lean.Json.mkObj [("align", Lean.Json.num (Lean.JsonNumber.fromNat 8)), ("fields", Lean.Json.arr #[(Lean.Json.mkObj [("name", Lean.Json.str "value"), ("offset", Lean.Json.num (Lean.JsonNumber.fromNat 0)), ("ty", Lean.Json.str "I64")])]), ("id", Lean.Json.num (Lean.JsonNumber.fromNat 0)), ("name", Lean.Json.str "PairI64"), ("repr", Lean.Json.str "Rust"), ("size", Lean.Json.num (Lean.JsonNumber.fromNat 8))])]), ("target_info", Lean.Json.null), ("tuple_layouts", Lean.Json.arr #[]), ("types", Lean.Json.arr #[(Lean.Json.str "U8")]), ("universes", Lean.Json.arr #[])]

def sourceModule : SemR.Module := match SemR.decode originalBytes with
  | .ok value => value
  | .error _ => {funcTys := [], enums := [], functions := []}

def canonicalModule : TrustIrEval.Module := match TrustIrEval.module moduleJson with
  | .ok value => value
  | .error _ => {functions := [], funcTys := [], globals := [], enums := [], structs := [], types := []}

def sourceFunction : SemR.Func := sourceModule.functions.headD
  {id := 0, ty := 0, entry := 0, blocks := []}

def sourceBlock : SemR.Block := sourceFunction.blocks.headD {id := 0, params := [], body := []}

def context (depth : Nat) : EvalContext := match TrustIrEval.contextOf canonicalModule depth with
  | .ok value => value
  | .error _ => EvalContext.empty

def canonicalFunction (depth : Nat) : EvalFunction := ((context depth).functions ⟨0⟩).getD
  {body := {paramTys := [], returnTys := []}, cfg := fun _ => none, entryBlock := ⟨0⟩}

theorem original_source_decodes : SemR.decode originalBytes = .ok sourceModule := by trustIrReduce <;> simp

theorem original_canonical_decodes : TrustIrEval.module moduleJson = .ok canonicalModule := by
  trustIrReduce

theorem original_context_prepares (depth : Nat) :
    TrustIrEval.contextOf canonicalModule depth = .ok (context depth) := by trustIrReduce <;> simp

theorem original_pair_is_retained : sourceModule.structs = [CanonicalStructLayout.Checks.pair] := by
  trustIrReduce

theorem original_pair_has_canonical_geometry :
    CanonicalStructLayout.query sourceModule .execution 0 = .ok {
      size := 8, align := some 8,
      fields := [{ty := .I64, offset := 0, size := 8, align := 8}] } := by trustIrReduce <;> simp

theorem original_canonical_pair_is_retained : canonicalModule.structs = [{
    id := ⟨0⟩, name := "PairI64",
    fields := [{name := "value", ty := .I64, offset := some 0}],
    size := some 8, align := some 8, repr := .rust }] := by trustIrReduce <;> simp

theorem original_source_shape :
    sourceModule.functions.find? (fun f => f.id == 0) = some sourceFunction ∧
    SemR.nth? sourceModule.funcTys sourceFunction.ty = some signature ∧
    SemR.findBlock sourceFunction.blocks sourceFunction.entry = some sourceBlock ∧
    sourceBlock.params = [(0, .int .u64)] ∧
    sourceBlock.body = [constantNode, CanonicalScalarStep.divisionNode 1 0 2,
      CanonicalScalarReturn.returnNode 2] ∧
    sourceModule.executableTarget = true := by trustIrReduce <;> simp

theorem original_canonical_shape (depth : Nat) :
    (context depth).functions ⟨0⟩ = some (canonicalFunction depth) ∧
    (canonicalFunction depth).body.paramTys = [.U64] ∧
    (canonicalFunction depth).body.returnTys = [.U64] ∧
    (canonicalFunction depth).body.abi = none ∧
    (canonicalFunction depth).cfg (canonicalFunction depth).entryBlock = some entryBlock ∧
    ((context depth).forFunction (canonicalFunction depth)).instructionResultTypes
      (.Const .U64 (.int 1)) [⟨1⟩] 1 = .ok [.U64] ∧
    ((context depth).forFunction (canonicalFunction depth)).instructionResultTypes
      (.BinOp .UDiv .U64 ⟨1⟩ ⟨0⟩) [⟨2⟩] 1 = .ok [.U64] := by trustIrReduce <;> simp

/-- Instantiation on both actual decodes of the complete captured module.
The original integer-text requires remains retained data; the separate guarded
consumer does not yet accept it. Nonzero here is the exact owed execution domain. -/
theorem original_body_execution (divisor extra sourceDepth targetDepth fuel : Nat)
    (range : divisor < 2 ^ 64) (post : List SemR.Val → List Value → Prop) :
    (∃ left right after,
      SemR.runFunction sourceModule 0 [.int .u64 divisor] (extra + 3) sourceDepth = .ret left ∧
      Sem.run (evalFunctionInContext (context targetDepth) ⟨0⟩ [.int 64 (divisor : Int)]
        (fuel + 1) .abort) MachineState.empty = .ok (right, after) ∧ post left right) ↔
      divisor ≠ 0 ∧ post [.int .u64 (1 / divisor)] [.int 64 ((1 / divisor : Nat) : Int)] := by
  rcases original_source_shape with ⟨sf, ss, sb, sp, body, layout⟩
  rcases original_canonical_shape targetDepth with ⟨tf, tp, tr, ta, tb, tc, td⟩
  exact function_wp_iff sourceModule 0 sourceFunction sourceBlock (context targetDepth)
    (canonicalFunction targetDepth) divisor extra sourceDepth fuel sf ss sb sp body layout
    tf tp tr ta tb tc td range post

end SemR.CanonicalDeclaredDivision.Packet
