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

## Verified-subset coverage (authoritative)

The Lean operational model covers the 9 constructors above. Four Rust
`Constant` variants are DELIBERATELY NOT modelled here — they carry no
computational value the executable semantics evaluates, only a symbolic/address
identity resolved at link/codegen time, so they are outside the verified subset:

| Rust variant            | Status        | Why outside the model                 |
|-------------------------|---------------|---------------------------------------|
| Constant::Array(..)     | not modelled  | Represented as `aggregate` at the value level; a distinct `array` ctor adds no semantics the interpreter exercises. |
| Constant::FnDef(FuncId) | not modelled  | A symbolic function reference; resolved by the call machinery, not a value the arithmetic/memory semantics compute on. |
| Constant::SymbolAddr    | not modelled  | A link-time address; no compile-time value. |
| Constant::PhantomData   | not modelled  | Zero-size marker; no runtime representation. |

A frontend that emits one of these as an `Inst.Const` operand is outside the
TrustIr verified subset for that instruction. (The Rust↔Lean `Ty` parity gate
already enforces type-axis coverage; this table is the constant-axis statement.)
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
  deriving Repr

end TrustIr
