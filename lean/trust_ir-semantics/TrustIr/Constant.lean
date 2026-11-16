-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Constant values.
-- Mirrors: crates/trust_ir/src/constant.rs

import TrustIr.Basic

namespace TrustIr

/-!
# Constants

Mirrors Rust trust_ir::Constant.

TrustIr constants are used in Inst.Const instructions and SwitchCase values.

## Mapping from Rust

| Rust variant         | Lean variant           | Notes                           |
|----------------------|------------------------|---------------------------------|
| Constant::Int(i128)  | Constant.int (Int)     | Arbitrary precision in Lean     |
| Constant::Float(f64) | Constant.float (Float) | Lean Float = IEEE 754 f64       |
| Constant::Bool(bool) | Constant.bool (Bool)   | Standard                        |
| Constant::Aggregate  | Constant.aggregate     | Recursive heterogeneous tuple   |
| Constant::Vector     | Constant.vector        | Fixed-width homogeneous vector  |

New variants from designs/2026-04-18-ty-supremacy-trust_ir-scope.md section 3.3:

| Rust variant            | Lean variant       | Notes                        |
|-------------------------|--------------------|------------------------------|
| Constant::Sequence(..)  | Constant.sequence  | Ordered packed sequence      |
| Constant::Set(..)       | Constant.set       | Unordered set literal        |
| Constant::Record(..)    | Constant.record    | Named-field record           |
| Constant::Closure {..}  | Constant.closure   | func + captured env frame    |

## The link-time and carrier constants (WS2.18)

Every Rust `Constant` variant now has a constructor here — the
`Constant` axis of `crates/trust-ir/tests/lean_schema_parity.rs` holds with
an EMPTY allowlist, so an eighteenth Rust variant with no Lean constructor fails
that gate. The six below were previously "not modelled"; each is now carried,
and its runtime denotation (`Value.ofConstant`, Semantics/Aggregate.lean)
mirrors the reference interpreter's `constant_to_value`
(crates/trust-ir/src/interpret.rs):

| Rust variant                    | Lean constructor        | Runtime denotation                                   |
|---------------------------------|-------------------------|------------------------------------------------------|
| Constant::U128(u128)            | Constant.u128 (Nat)     | `.int 128 n` — canonical only above `i128::MAX`      |
| Constant::Bytes { data, utf8 }  | Constant.bytes data utf8| compact `.array` of `.int 8` byte lanes    |
| Constant::Array(..)             | Constant.array          | compact `.array` literal               |
| Constant::FnDef(FuncId)         | Constant.fnDef          | `.fnDef sig f` under `Ty.Func sig`; untyped projection `.closure f []` |
| Constant::SymbolAddr {..}       | Constant.symbolAddr     | NONE — refused fail-closed (see below)               |
| Constant::PhantomData           | Constant.phantomData    | `.aggregate []` (the zero-size unit value)           |
| Constant::Uninit (crystal E3b)  | Constant.uninit         | `.uninit` — an UNWRITTEN struct/tuple lane (wire v49)|
| Constant::Splat { elem, len }   | Constant.splat elem len  | `.array (CompactArray.Packed.uniform len (ofConstant elem))`  |

`splat` (wire v50) is `len` copies of one element: the constant-size spelling
of a uniform array. Its runtime denotation stores one element and its count;
indexed laws hold symbolically for every `len`, and execution can use the full
u64 logical domain without constructing a replicated list. The ONE-SPELLING rule (SPEC_RATIFICATIONS §3.1: `splat` is
canonical iff `len ≥ 2`, and a list of ≥ 2 equal elements must be a `splat`)
is enforced by the Rust validator and decoder, not by this mirror.

`symbolAddr` is the one constant with NO compile-time value: it is a
link-time relocation (`&symbol + addend`), and the reference interpreter
refuses it (its `constant_to_value` has no arm for it). The executable model
refuses it the same way: `Constant.hasSymbolAddr` (below) finds one at ANY
nesting depth, and all three constant entry points — the `Const` step
(Semantics/Step.lean), the global-initializer path (Semantics/Eval.lean
`valueOfConstAtTy` callers) and a `Switch` case the in-order scan reaches
(Semantics/Call.lean `semSwitch`) — raise `unsupported.link_time_address`
before `Value.ofConstant` is consulted or a case is skipped. A `Switch` case
may also be a canonical `u128`, which a width-128 scrutinee matches
(`switchCaseMatches`), exactly as the interpreter compares it. `Value.ofConstant`'s `symbolAddr` arm is
therefore unreachable from evaluation; it is spelled `.undef .Ptr` only
because `Value.ofConstant` is a total function, and nothing may read it as a
value (the executable refusal is what makes that true, not the arm).
-/

/-- Constant value. Mirrors Rust trust_ir::Constant.

    Design note: sequence and aggregate both carry a list of constants,
    but their variant identity matters -- sequence is ordered-packed with
    Ty.Sequence, while aggregate is the legacy heterogeneous tuple/array
    literal. Equality across variants is false by construction. -/
inductive Constant where
  | int       : Int → Constant
  | float     : Float → Constant
  | bool      : Bool → Constant
  | aggregate : List Constant → Constant
  | vector    : List Constant → Constant
  -- ty supremacy aggregate constants (issue #30 / #31).
  /-- Ordered packed sequence constant (mirrors Ty.Sequence). Element
      order is significant and preserved. -/
  | sequence  : List Constant → Constant
  /-- Unordered set literal (mirrors Ty.Set). Elements are stored in a
      canonical order chosen by the constructor; duplicate suppression is
      the frontend's responsibility. -/
  | set       : List Constant → Constant
  /-- Named-field record literal (mirrors Ty.Record). Field order is
      canonical (typically sorted by name) so records with equal field-
      sets compare equal. -/
  | record    : List (String × Constant) → Constant
  /-- First-class closure constant: captured environment frame bundled
      with a direct FuncId target (mirrors Ty.Closure). Captures are
      frozen at closure-literal time -- this is what prevents the
      ty issue 4145 stale-cache bug for self-referential FuncDefs. -/
  | closure   : FuncId → List Constant → Constant
  /-- Unsigned 128-bit integer ABOVE `i128::MAX` (Rust `Constant::U128`,
      wire v24). Canonical only in that upper half — every smaller value is
      spelled `int`; the Rust validator and decoder enforce that, this mirror
      carries the value. -/
  | u128      : Nat → Constant
  /-- Raw byte-array payload (Rust `Constant::Bytes { data, utf8 }`, wire
      v25). `utf8` is the checked str-origin claim; it is part of value
      identity, as in Rust. -/
  | bytes     : List UInt8 → Bool → Constant
  /-- Homogeneous fixed-length array literal (Rust `Constant::Array`,
      mirrors `Ty.Array`). -/
  | array     : List Constant → Constant
  /-- Bare function item with no captured environment (Rust
      `Constant::FnDef`, matches `Ty.Func`). Distinct from `closure`. -/
  | fnDef     : FuncId → Constant
  /-- Link-time address `&symbol + addend` (Rust `Constant::SymbolAddr`).
      Has NO compile-time value: every evaluation entry point refuses it
      (`Constant.hasSymbolAddr`). -/
  | symbolAddr : String → Int → Constant
  /-- Zero-sized `PhantomData` marker (Rust `Constant::PhantomData`), the
      canonical constant spelling of a `Ty.Unit` value. -/
  | phantomData : Constant
  /-- Crystal lane (E3b): an UNWRITTEN struct/tuple lane (Rust `Constant::Uninit`, wire
      v49). Typed by position: admissible only as a direct lane of an `Inst.Const`
      struct/tuple aggregate. That placement is the Rust validator's rule
      (`validate_uninit_lanes`), and this model takes it as a precondition, as it takes the
      validator's typing rules; it is not re-checked here. It is no value:
      `Value.ofConstant` lowers it to `Value.uninit`, which a write replaces and a read
      faults on. -/
  | uninit    : Constant
  /-- `len` copies of one element (Rust `Constant::Splat { elem, len }`,
      wire v50): the constant-size uniform array, mirrors `Ty.Array _ len`. -/
  | splat     : Constant → Nat → Constant
  /-- The singleton of an exact `Ty.FnItem` identity. Its declaration is
      checked against the source module independently of executable bodies. -/
  | fnItem    : FuncId → Constant
  deriving Repr

mutual

/-- Does the constant contain a link-time `symbolAddr` at ANY nesting depth?
    The executable model refuses every such constant (fail closed), exactly
    as the Rust reference interpreter does — an address that only the linker
    assigns has no value an evaluation step could produce. -/
def Constant.hasSymbolAddr : Constant → Bool
  | .symbolAddr _ _ => true
  | .aggregate cs   => Constant.listHasSymbolAddr cs
  | .vector cs      => Constant.listHasSymbolAddr cs
  | .sequence cs    => Constant.listHasSymbolAddr cs
  | .set cs         => Constant.listHasSymbolAddr cs
  | .array cs       => Constant.listHasSymbolAddr cs
  | .record fs      => Constant.fieldsHaveSymbolAddr fs
  | .closure _ caps => Constant.listHasSymbolAddr caps
  | .splat c _      => Constant.hasSymbolAddr c
  -- Every leaf constructor spelled out (no wildcard), so each equation
  -- lemma is unconditional and `simp [Constant.hasSymbolAddr]` decides a
  -- constructor application outright.
  | .int _          => false
  | .float _        => false
  | .bool _         => false
  | .u128 _         => false
  | .bytes _ _      => false
  | .fnDef _        => false
  | .fnItem _       => false
  | .phantomData    => false
  | .uninit         => false

/-- `hasSymbolAddr` over a constant list. -/
def Constant.listHasSymbolAddr : List Constant → Bool
  | []      => false
  | c :: cs => Constant.hasSymbolAddr c || Constant.listHasSymbolAddr cs

/-- `hasSymbolAddr` over a record field list. -/
def Constant.fieldsHaveSymbolAddr : List (String × Constant) → Bool
  | []           => false
  | (_, c) :: fs => Constant.hasSymbolAddr c || Constant.fieldsHaveSymbolAddr fs

end

end TrustIr
