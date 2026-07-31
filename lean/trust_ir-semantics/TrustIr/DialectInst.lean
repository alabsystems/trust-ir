-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Dialect-op carrier — the non-semantic, round-trippable structure
-- embedded inside Inst.DialectOp.
-- Mirrors: crates/trust_ir/src/dialect/inst.rs (DialectInst, AttrEntry, AttrValue)

import TrustIr.Basic

namespace TrustIr

/-!
# Dialect Instruction Carrier

DialectInst is the Lean-side mirror of Rust trust_ir.dialect.DialectInst.
It is deliberately non-semantic: a plain record of the fields that
round-trip through every TrustIr serialization format (text, binary,
serde-JSON, MessagePack). Semantic interpretation is provided by a
separate dialect registry (TrustIr.Semantics.Dialect).

Keeping the carrier non-semantic in TrustIr.Inst avoids a cycle:
Inst is imported by the semantic monad, and dialect semantics depend
on the semantic monad. The carrier captures only what the IR
round-trips; DialectOpSem (in TrustIr.Semantics.Dialect) layers a
declared denotation on top for lowering-correctness proofs.
-/

/-! ## Attribute carriers -/

/-- Attribute value carried on a dialect op. Mirrors the Rust
    trust_ir.dialect.AttrValue enum.

    Bytes and Ty are included so the Lean side can describe every
    Rust dialect-op instance (round-trip faithfulness). No dialect
    semantics in TrustIr.Semantics.Dialect decode these — they are
    treated as opaque by the schema. -/
inductive AttrValue where
  | i64   : Int → AttrValue
  | u64   : Nat → AttrValue
  | f64   : Float → AttrValue
  | bool_ : Bool → AttrValue
  | str   : String → AttrValue
  | bytes : List UInt8 → AttrValue
  | ty    : Ty → AttrValue
  deriving Repr

/-- Named attribute entry. Mirrors Rust trust_ir.dialect.AttrEntry. -/
structure AttrEntry where
  name  : String
  value : AttrValue
  deriving Repr

/-! ## Dialect-op carrier -/

/-- In-IR dialect operation payload. Mirrors Rust
    trust_ir.dialect.DialectInst field-for-field.

    This structure carries no semantic denotation. It is the data
    payload serialized alongside core TrustIr instructions; semantics is
    layered on top in TrustIr.Semantics.Dialect (see DialectOpSem and
    the DialectLowerSound obligation). -/
structure DialectInst where
  /-- Dialect namespace (e.g. verif). Registry key. -/
  dialect   : String
  /-- Op name within the dialect (e.g. bfs_step). -/
  op        : String
  /-- SSA operands consumed by the op. -/
  operands  : List ValueId
  /-- Result types, length matches the enclosing node's result vector. -/
  resultTys : List Ty
  /-- Named compile-time attributes. Opaque to the core schema. -/
  attrs     : List AttrEntry
  /-- Schema version of the payload. Starts at 1; dialects may bump
      when the attribute layout changes. -/
  version   : Nat
  deriving Repr

namespace DialectInst

/-- Fully-qualified op name, dialect.op. Mirrors Rust
    DialectInst.qualified_name. -/
def qualifiedName (d : DialectInst) : String :=
  d.dialect ++ "." ++ d.op

end DialectInst

end TrustIr
