// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! AY SMT encoding for TrustIr operations.
//!
//! Maps TrustIr types, instructions, and proof annotations to ay bitvector
//! formulas for automated verification. This adapter keeps solver-specific
//! logic outside the core `trust-ir` crate.
//!
//! # Supported encodings
//!
//! | Category | Function | TrustIr type |
//! |----------|----------|-----------|
//! | Types | `ty_to_sort` | `Ty` -> `Sort` |
//! | Binary ops | `encode_binop` | `BinOp` (integer, rotate, bool, and float variants; `FRem` as exact `fmod`; FMin/FMax/FCopySign refused) |
//! | Comparisons | `encode_icmp` | `ICmpOp` (10 variants) |
//! | Unary ops | `encode_unop` | integer `UnOp`, plus FNeg/FAbs |
//! | Casts | `encode_cast` | integer resize, FP conversion, saturating FP-to-integer, pointer/integer and same-sort bitcasts |
//! | Overflow | `encode_overflow_check` | `OverflowOp` (3 variants) |
//! | Borrows | `BorrowModel` | Borrow/BorrowMut/EndBorrow |
//! | ARC | `ArcModel` | Retain/Release/IsUnique |
//! | Proofs | `verify_proof_obligation` | `ProofAnnotation` |

// Production code cannot allow a method `clippy.toml` disallows: under the
// linter a `#[allow(clippy::disallowed_methods)]` outside a `cfg(test)` item is
// E0453. Test modules keep their own inner allow.
#![cfg_attr(not(test), forbid(clippy::disallowed_methods))]

use ay::{
    ArraySort, BitVecSort, DatatypeConstructor, DatatypeField, DatatypeSort, Logic, Solver, Sort,
    Term,
};

pub mod bvblast;
pub use bvblast::{
    BVBLAST_ALLOWED_KINDS, BVBLAST_CERT_SCHEMA, BVBLAST_PROVER, BvBlastAttachError,
    BvBlastAttachOutcome, BvBlastAuthority, BvBlastCertPayload, BvBlastCertificate,
    BvBlastPayloadError, ProveError, attach_bvblast_evidence, certify_obligation, prove,
    to_bv_expr,
};

pub mod vc;
pub use vc::{
    Counterexample, FunctionVc, VcApplyError, VcCondition, VcObligationOutcome, VcSource,
    VcVerdict, WitnessUnavailable, apply_vc_outcomes, generate_function_vc, model_counterexample,
    verify_function,
};

use trust_ir::inst::{BinOp, CastOp, FCmpOp, ICmpOp, OverflowOp, UnOp};
use trust_ir::proof::{ProofAnnotation, ProofCertificate, ProofEvidence, ProofStatus};
use trust_ir::ty::Ty;
use trust_ir::value::{FuncId, ProofId, ValueId};

/// Errors from ay encoding operations.
#[derive(Debug, Clone)]
pub enum AYError {
    /// The TrustIr type has no ay sort representation (e.g., Void, Struct).
    UnsupportedType(Ty),
    /// The operation is not encodable in the current logic.
    UnsupportedOp(String),
    /// ay solver creation failed.
    SolverError(String),
    /// The proof annotation is not encodable as a ay verification condition.
    UnsupportedAnnotation(String),
    /// A memory model operation failed.
    MemoryError(String),
}

impl core::fmt::Display for AYError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            AYError::UnsupportedType(ty) => write!(f, "unsupported type for ay encoding: {}", ty),
            AYError::UnsupportedOp(op) => {
                write!(f, "unsupported operation for ay encoding: {}", op)
            }
            AYError::SolverError(msg) => write!(f, "ay solver error: {}", msg),
            AYError::UnsupportedAnnotation(ann) => {
                write!(f, "unsupported proof annotation for ay encoding: {}", ann)
            }
            AYError::MemoryError(msg) => write!(f, "memory model error: {}", msg),
        }
    }
}

impl std::error::Error for AYError {}

/// Every fallible ay call (`Solver::try_*`) maps its refusal here, so a sort
/// mismatch, an out-of-range width or a solver-side failure on a
/// module-derived term is a typed error of THIS adapter, never a panic
/// inside ay. On a fact it removes the fact (hypotheses only weaken); on a
/// goal it leaves the condition unproved — never `Proved`.
impl From<ay::SolverError> for AYError {
    fn from(error: ay::SolverError) -> Self {
        AYError::SolverError(error.to_string())
    }
}

/// Map a TrustIr type to a ay sort.
///
/// Integer types map to `BitVec(width)`. Bool maps to `BitVec(1)`.
/// Ptr maps to `BitVec(64)`. F16 maps to `FloatingPoint(5, 11)`.
/// F32 maps to `FloatingPoint(8, 24)`.
/// F64 maps to `FloatingPoint(11, 53)`. SIMD vectors map to the
/// concatenated-lane bitvector model shared with [`encode_vector_binop`]
/// (lane 0 in the least-significant bits). Other compound types are
/// unsupported.
pub fn ty_to_sort(ty: &Ty) -> Result<Sort, AYError> {
    match ty {
        Ty::Bool => Ok(Sort::BitVec(BitVecSort { width: 1 })),
        Ty::I8 | Ty::U8 => Ok(Sort::BitVec(BitVecSort { width: 8 })),
        Ty::I16 | Ty::U16 => Ok(Sort::BitVec(BitVecSort { width: 16 })),
        Ty::I32 | Ty::U32 => Ok(Sort::BitVec(BitVecSort { width: 32 })),
        Ty::I64 | Ty::U64 => Ok(Sort::BitVec(BitVecSort { width: 64 })),
        Ty::I128 | Ty::U128 => Ok(Sort::BitVec(BitVecSort { width: 128 })),
        Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) => Ok(Sort::BitVec(BitVecSort { width: 64 })),
        Ty::Ref(_) | Ty::RefMut(_) | Ty::Rc(_) => Ok(Sort::BitVec(BitVecSort { width: 64 })),
        // IEEE 754 half precision: 5-bit exponent, 11-bit significand (10 + 1 implicit)
        Ty::F16 => Ok(Sort::FloatingPoint(5, 11)),
        // IEEE 754 single precision: 8-bit exponent, 24-bit significand (23 + 1 implicit)
        Ty::F32 => Ok(Sort::FloatingPoint(8, 24)),
        // IEEE 754 double precision: 11-bit exponent, 53-bit significand (52 + 1 implicit)
        Ty::F64 => Ok(Sort::FloatingPoint(11, 53)),
        // Compound types: Tuple has element types available for recursive encoding.
        // Struct/Array/Enum use opaque uninterpreted sorts (field info not in Ty).
        Ty::Tuple(elems) if elems.is_empty() => {
            // Empty tuple (unit-like). Use a zero-field datatype.
            Ok(Sort::Datatype(DatatypeSort::new(
                "Tuple0",
                vec![DatatypeConstructor::unit("Tuple0_mk")],
            )))
        }
        Ty::Tuple(elems) => {
            // Recursively encode element types into a datatype with named fields.
            let mut fields = Vec::with_capacity(elems.len());
            for (i, elem) in elems.iter().enumerate() {
                let elem_sort = ty_to_sort(elem)?;
                fields.push(DatatypeField::new(format!("_{}", i), elem_sort));
            }
            let name = format!("Tuple{}", elems.len());
            Ok(Sort::Datatype(DatatypeSort::new(
                name.clone(),
                vec![DatatypeConstructor::new(format!("{}_mk", name), fields)],
            )))
        }
        Ty::Struct(id) => {
            // Opaque uninterpreted sort. Full struct encoding requires StructDef
            // which is not available from Ty alone.
            Ok(Sort::Uninterpreted(format!("struct_{}", id.0)))
        }
        Ty::Array(elem_id, len) => {
            // Opaque uninterpreted sort. Full array encoding requires resolving
            // the element TyId to a Ty, which is module-level context.
            Ok(Sort::Uninterpreted(format!("array_{}_{}", elem_id.0, len)))
        }
        Ty::Enum(id) => {
            // Opaque uninterpreted sort. Full enum encoding requires EnumDef.
            Ok(Sort::Uninterpreted(format!("enum_{}", id.0)))
        }
        Ty::Unit => {
            // Unit type has a single value. Model as zero-field datatype.
            Ok(Sort::Datatype(DatatypeSort::new(
                "Unit",
                vec![DatatypeConstructor::unit("Unit_mk")],
            )))
        }
        Ty::Vector(elem, lanes) => {
            // Concatenated-lane bitvector model (the encoding
            // `encode_vector_binop` already operates on): lane 0 occupies the
            // least-significant `elem` bits.
            if *lanes == 0 {
                return Err(AYError::UnsupportedType(ty.clone()));
            }
            let elem_bits = sort_bit_width(&ty_to_sort(elem)?)
                .ok_or_else(|| AYError::UnsupportedType(ty.clone()))?;
            // A lane count whose concatenated width does not fit a `u32`
            // bit-vector width has no model: refuse it, never wrap it.
            let width = elem_bits
                .checked_mul(*lanes)
                .ok_or_else(|| AYError::UnsupportedType(ty.clone()))?;
            Ok(Sort::BitVec(BitVecSort { width }))
        }
        // Never type (diverging) has no values -- cannot be represented.
        // Func types are not first-class values in BV encoding.
        _ => Err(AYError::UnsupportedType(ty.clone())),
    }
}

/// Total bit width of a bit-vector or floating-point sort: the vector's width,
/// or `eb + sb` (exponent plus significand bits, the IEEE storage width) for a
/// float. `None` for any other sort.
///
/// The ONE width rule for the concatenated-lane and byte-addressable models
/// ([`ty_to_sort`]'s vector arm, [`encode_vector_binop`], and the
/// whole-function VC's `bit_width`). The float sum is CHECKED: every float sort
/// [`ty_to_sort`] produces is one of three closed pairs ((5, 11), (8, 24),
/// (11, 53)), but `Sort::FloatingPoint` is ay's open SMT-LIB sort, whose
/// `(eb, sb)` may legitimately be anything, so a pair whose sum overflows `u32`
/// is `None` rather than a wrapped width.
pub(crate) fn sort_bit_width(sort: &Sort) -> Option<u32> {
    match sort {
        Sort::BitVec(bv) => Some(bv.width),
        Sort::FloatingPoint(eb, sb) => eb.checked_add(*sb),
        _ => None,
    }
}

/// Create a QF_BV solver instance (integer-only).
pub fn create_bv_solver() -> Result<Solver, AYError> {
    Solver::try_new(Logic::QfBv).map_err(|e| AYError::SolverError(format!("{}", e)))
}

/// Create a solver supporting bitvectors, floating-point, and arrays.
///
/// Uses `Logic::All` which auto-detects the required theories.
pub fn create_fp_solver() -> Result<Solver, AYError> {
    Solver::try_new(Logic::All).map_err(|e| AYError::SolverError(format!("{}", e)))
}

// ============================================================================
// Symbol-Binding Schema (canonical operand -> ay symbol mapping)
// ============================================================================
//
// TrustIr owns the schema that binds IR operands to solver symbols
// (docs/roadmap/integration-ay-vc.md). ay owns the solver and the verdict;
// this section defines the deterministic naming/sorting contract that lets
// the per-op encoders below compose into a whole-function VC (see `vc`), and
// lets a counterexample model be mapped back to source `ValueId`s.

/// Canonical ay symbol name for an SSA value: `f{func}_v{value}`.
///
/// This is THE operand→symbol binding schema. It is a pure function of the
/// two ids — no hashing, no addresses, no map-iteration order — so the same
/// module produces the same symbol names on every run and machine
/// (docs/roadmap/build-determinism.md). A solver model over symbols bound by
/// this schema maps back to source values via [`parse_ay_symbol`].
pub fn ay_symbol(func: FuncId, value: ValueId) -> String {
    format!("f{}_v{}", func.index(), value.index())
}

/// Inverse of [`ay_symbol`]: recover `(FuncId, ValueId)` from a schema symbol
/// name. Returns `None` for names the schema did not produce (e.g. the
/// memory/permission/refcount state arrays, or hand-declared test symbols).
pub fn parse_ay_symbol(name: &str) -> Option<(FuncId, ValueId)> {
    let rest = name.strip_prefix('f')?;
    let (func, value) = rest.split_once("_v")?;
    Some((
        FuncId::new(func.parse().ok()?),
        ValueId::new(value.parse().ok()?),
    ))
}

/// Canonical ay sort for a value of TrustIr type `ty` — the sort half of the
/// binding schema. The mapping is exactly [`ty_to_sort`]'s (this is the
/// schema's canonical name for it): `BitVec(width)` for integers/Bool/
/// pointers, IEEE sorts for floats, concatenated-lane bitvectors for SIMD
/// vectors. Unsupported types fail closed with
/// [`AYError::UnsupportedType`].
pub fn ay_sort(ty: &Ty) -> Result<Sort, AYError> {
    ty_to_sort(ty)
}

/// Bind `value` to the solver under its canonical schema symbol and sort.
///
/// This is the one place a `(FuncId, ValueId, Ty)` triple becomes a solver
/// constant; every declared symbol goes through [`ay_symbol`]/[`ay_sort`] so
/// the resulting model is deterministic and back-translatable.
pub fn bind_value(
    solver: &mut Solver,
    func: FuncId,
    value: ValueId,
    ty: &Ty,
) -> Result<Term, AYError> {
    let sort = ay_sort(ty)?;
    Ok(solver.try_declare_const(&ay_symbol(func, value), sort)?)
}

/// The operand roles [`verify_proof_obligation`] expects for `annotation`,
/// in positional order.
///
/// This is the schema's replacement for hand-written string keys: a call
/// site supplies operand terms positionally (via
/// [`ProofOperands::for_annotation`] / [`ProofOperands::from_values`]) and
/// the role names come from the annotation itself instead of being
/// re-invented per call site. `NoOverflow`/`NoWrap` additionally require
/// [`ProofOperands::with_overflow_op`].
///
/// Annotations with no bitvector/FP encoding (the `DataRaceFree`-class
/// concurrency/NN/liveness annotations) fail closed with
/// [`AYError::UnsupportedAnnotation`], mirroring `verify_proof_obligation`.
pub fn annotation_operand_roles(
    annotation: &ProofAnnotation,
) -> Result<&'static [&'static str], AYError> {
    match annotation {
        ProofAnnotation::NoOverflow | ProofAnnotation::NoWrap => Ok(&["lhs", "rhs"]),
        ProofAnnotation::DivNonZero => Ok(&["divisor"]),
        ProofAnnotation::ShiftInRange => Ok(&["shift_amount", "bit_width"]),
        ProofAnnotation::InBounds => Ok(&["index", "length"]),
        ProofAnnotation::NotNull | ProofAnnotation::Aligned(_) => Ok(&["ptr"]),
        ProofAnnotation::ValidBorrow
        | ProofAnnotation::UniqueBorrow
        | ProofAnnotation::SharedBorrow
        | ProofAnnotation::ValidDealloc => Ok(&["ptr", "permission"]),
        ProofAnnotation::Pure | ProofAnnotation::Deterministic => Ok(&["result1", "result2"]),
        ProofAnnotation::Commutative => Ok(&["result_ab", "result_ba"]),
        ProofAnnotation::Associative => Ok(&["result_left", "result_right"]),
        ProofAnnotation::NoAlias => Ok(&["ptr1", "ptr2"]),
        ProofAnnotation::NoPanic => Ok(&["safe"]),
        ProofAnnotation::NoUndef => Ok(&["is_defined"]),
        other => Err(AYError::UnsupportedAnnotation(format!("{}", other))),
    }
}

/// Get the round-nearest-even rounding mode term.
///
/// IEEE 754 default rounding mode used for most FP operations.
fn rne(solver: &mut Solver) -> Result<Term, AYError> {
    Ok(solver.try_fp_rounding_mode("RNE")?)
}

/// Integer conversion discards the fractional part, unlike FP arithmetic.
fn rtz(solver: &mut Solver) -> Result<Term, AYError> {
    Ok(solver.try_fp_rounding_mode("RTZ")?)
}

/// Rust's saturating float casts: NaN -> zero, otherwise truncate and clamp.
/// Widening to binary64 is exact for every IR float width and lets bounds up
/// to 2^128 remain finite even when the source is binary16. Bounds are exact
/// powers of two, never rounded integer maxima such as i64::MAX as f64.
fn encode_saturating_fp_cast(
    solver: &mut Solver,
    operand: Term,
    dst_width: u32,
    signed: bool,
) -> Result<Term, AYError> {
    if dst_width == 0 || dst_width > 128 {
        return Err(AYError::UnsupportedOp(format!(
            "saturating float cast to width {dst_width}"
        )));
    }
    match solver.try_term_sort(operand)? {
        Sort::FloatingPoint(5, 11) | Sort::FloatingPoint(8, 24) | Sort::FloatingPoint(11, 53) => {}
        _ => {
            return Err(AYError::UnsupportedOp(
                "saturating cast operand is not an IR float".into(),
            ));
        }
    }
    let nearest = rne(solver)?;
    let wide = solver.try_fp_to_fp(nearest, operand, 11, 53)?;
    let zero = solver.try_bv_const_u64(0, dst_width)?;
    let (minimum, maximum) = if signed {
        let one = solver.try_bv_const_u64(1, dst_width)?;
        let shift = solver.try_bv_const_u64(u64::from(dst_width - 1), dst_width)?;
        let min = solver.try_bvshl(one, shift)?;
        (min, solver.try_bvnot(min)?)
    } else {
        (zero, solver.try_bvnot(zero)?)
    };
    let exponent = dst_width - u32::from(signed);
    let upper_bits = (u64::from(exponent) + 1023) << 52;
    let upper = solver.try_fp_const_from_bits(upper_bits, 11, 53)?;
    let lower = if signed {
        solver.try_fp_neg(upper)?
    } else {
        solver.try_fp_const_from_bits(0, 11, 53)?
    };
    let too_low = solver.try_fp_lt(wide, lower)?;
    let too_high = solver.try_fp_ge(wide, upper)?;
    let is_nan = solver.try_fp_is_nan(wide)?;
    let truncate = rtz(solver)?;
    let value = if signed {
        solver.try_fp_to_sbv(truncate, wide, dst_width)?
    } else {
        solver.try_fp_to_ubv(truncate, wide, dst_width)?
    };
    let upper_clamped = solver.try_ite(too_high, maximum, value)?;
    let clamped = solver.try_ite(too_low, minimum, upper_clamped)?;
    Ok(solver.try_ite(is_nan, zero, clamped)?)
}

/// Encode a TrustIr `BinOp` as a ay operation.
///
/// - 13 integer variants (Add through AShr) use bitvector operations, and the
///   WS3.20 rotates (RotL/RotR) exact bitvector rotations
/// - 3 boolean connectives (BAnd/BOr/BXor) reuse the bitwise BV ops, exact on
///   the 0/1 carrier
/// - FAdd/FSub/FMul/FDiv use the IEEE FP operations with RNE rounding
/// - FRem is the truncating C `fmod` (trust-ir's semantics of record), encoded
///   EXACTLY by [`encode_frem_fmod`] -- not SMT-LIB `fp.rem`, which is the
///   round-to-nearest IEEE remainder (`fp.rem(5, 3) = -1`, `5.0 % 3.0 = 2.0`)
/// - FMin/FMax/FCopySign are refused by name ([`AYError::UnsupportedOp`]):
///   no SMT-LIB FP operation has their trust-ir semantics
pub fn encode_binop(solver: &mut Solver, op: BinOp, lhs: Term, rhs: Term) -> Result<Term, AYError> {
    match op {
        BinOp::Add => Ok(solver.try_bvadd(lhs, rhs)?),
        BinOp::Sub => Ok(solver.try_bvsub(lhs, rhs)?),
        BinOp::Mul => Ok(solver.try_bvmul(lhs, rhs)?),
        BinOp::UDiv => Ok(solver.try_bvudiv(lhs, rhs)?),
        BinOp::SDiv => Ok(solver.try_bvsdiv(lhs, rhs)?),
        BinOp::URem => Ok(solver.try_bvurem(lhs, rhs)?),
        BinOp::SRem => Ok(solver.try_bvsrem(lhs, rhs)?),
        BinOp::And => Ok(solver.try_bvand(lhs, rhs)?),
        BinOp::Or => Ok(solver.try_bvor(lhs, rhs)?),
        BinOp::Xor => Ok(solver.try_bvxor(lhs, rhs)?),
        BinOp::Shl => Ok(solver.try_bvshl(lhs, rhs)?),
        BinOp::LShr => Ok(solver.try_bvlshr(lhs, rhs)?),
        BinOp::AShr => Ok(solver.try_bvashr(lhs, rhs)?),
        // Boolean connectives. The operands are the bool 0/1 carrier, encoded
        // here as bitvectors like every other scalar, and on 0/1 the bitwise BV
        // ops agree pointwise with the logical ones -- the same encoding
        // `AYBridge.lean`'s `encodeBinOp` uses, kept identical so the solver and
        // the Lean bridge cannot disagree about the same opcode.
        BinOp::BAnd => Ok(solver.try_bvand(lhs, rhs)?),
        BinOp::BOr => Ok(solver.try_bvor(lhs, rhs)?),
        BinOp::BXor => Ok(solver.try_bvxor(lhs, rhs)?),
        BinOp::FAdd => {
            let rm = rne(solver)?;
            Ok(solver.try_fp_add(rm, lhs, rhs)?)
        }
        BinOp::FSub => {
            let rm = rne(solver)?;
            Ok(solver.try_fp_sub(rm, lhs, rhs)?)
        }
        BinOp::FMul => {
            let rm = rne(solver)?;
            Ok(solver.try_fp_mul(rm, lhs, rhs)?)
        }
        BinOp::FDiv => {
            let rm = rne(solver)?;
            Ok(solver.try_fp_div(rm, lhs, rhs)?)
        }
        // C `fmod` / Rust `%`, NOT SMT-LIB `fp.rem` (the IEEE remainder):
        // `fp.rem` plus an exact one-step correction. See `encode_frem_fmod`.
        BinOp::FRem => encode_frem_fmod(solver, lhs, rhs),
        // FMin/FMax are NaN-propagating-away minimum/maximum (not IEEE fp.min/
        // fp.max). They are unsupported in this in-process encoder, like FSqrt
        // and the round family; trust-cg's CLI proof path (trust-cg-verify
        // SmtExpr) models them directly with ite/fp.lt/fp.isNaN.
        BinOp::FMin => Err(AYError::UnsupportedOp("fmin".to_string())),
        BinOp::FMax => Err(AYError::UnsupportedOp("fmax".to_string())),
        // WS3.20 rotates: exact bit-vector encodings, TOTAL like the
        // interpreter and Lean (`rotate_at_width` / `rotlWidth`): the amount
        // is reduced modulo the width, then `(x << n) | (x >> (w - n))`. When
        // `n = 0` the right shift is by `w`, which SMT-LIB defines as 0, so
        // the identity case needs no special arm.
        BinOp::RotL => encode_rotate(solver, lhs, rhs, true),
        BinOp::RotR => encode_rotate(solver, lhs, rhs, false),
        // `FCopySign` is left unsupported here on purpose: SMT-LIB's FP theory
        // has ONE NaN with no sign, so `fp.isNegative` cannot see the sign bit
        // the reference interpreter copies from a NaN `rhs` (the Lean model
        // refuses that case by name). Encoding it with `fp.isNegative` would
        // silently disagree with both engines on exactly that input; refusing
        // by name is the fail-closed choice, as for `FMin`/`FMax`.
        BinOp::FCopySign => Err(AYError::UnsupportedOp("fcopysign".to_string())),
    }
}

/// `FRem` exactly as trust-ir defines it: C `fmod` / LLVM `frem` / Rust `%`,
/// the TRUNCATING remainder `x - trunc(x / y) * y`, which has the dividend's
/// sign (docs/ub-numerics-policy.md §2; interpreter `lhs % rhs`; Lean
/// `floatFRem`, `Semantics/Arith.lean`).
///
/// SMT-LIB `fp.rem` is a different function, the IEEE 754 remainder
/// `x - n * y` with `n = roundTiesToEven(x / y)`. For example
/// `fp.rem(5, 3) = -1`, while `5.0 % 3.0 = 2.0`. Lowering `FRem` to `fp.rem`
/// alone proved the false `5 % 3 < 0` and refuted the true
/// `x >= 0 => x % 3 >= 0` (TRUST-IR-AY-FREM-1). The encoding is
///
/// ```text
/// r    = fp.rem(x, y)
/// fmod = ite(!isZero(r) && !isNaN(r) && isNegative(r) != isNegative(x),
///            fp.add(RNE, r, ite(isNegative(x), -|y|, |y|)),
///            r)
/// ```
///
/// **Why this is `fmod` (finite `x`, finite nonzero `y`).** Both functions
/// are odd in `x`: negating `x` negates the quotient, and round-to-nearest-even
/// and truncation are both symmetric about zero. Both are even in `y`:
/// negating `y` negates `n`, so `n * y` is unchanged. A zero result takes the
/// sign of `x` in both. Write `a = |x|`, `b = |y|`, and `s` for the sign of
/// `x`. Then `fmod(x, y) = s * fmod(a, b)` and `fp.rem(x, y) = s * rem(a, b)`.
/// Let `t = floor(a / b)`, so `fmod(a, b) = a - t * b`, which lies in
/// `[0, b)`. Round-to-nearest picks `n = t` or `n = t + 1`; a tie lands on
/// either one, depending on parity.
///
/// * If `n = t`, then `rem(a, b) = fmod(a, b) >= 0`. `r` is zero or has the
///   sign of `x`, and it is already `fmod`.
/// * If `n = t + 1`, then `rem(a, b) = fmod(a, b) - b`, which lies in
///   `[-b/2, 0)`. It is nonzero, has the opposite sign to `a`, and
///   `fmod(a, b) = rem(a, b) + b`.
///
/// So "`r` is nonzero, not NaN, and of the opposite sign to `x`" is exactly
/// the `n = t + 1` case. In that case
/// `fmod(x, y) = s * (rem(a, b) + b) = r + copysign(|y|, x)`. `copysign` is
/// spelled with `isNegative(x)`, which is sound here because `x` is not NaN
/// whenever `r` is not NaN.
///
/// **Why the add is EXACT.** Its real-valued sum is `fmod(x, y)`, which is a
/// float, so RNE (or any rounding mode) returns it unrounded. Proof that it
/// is a float: let `Q` be the smaller of the two operands' quanta (the weight
/// of the last significand bit, at the subnormal exponent for a subnormal).
/// `a` and `b` are integer multiples of `Q`, and so is `a - t * b`. Also
/// `fmod(a, b) <= a` and `fmod(a, b) < b`. Divide by `Q`: the result is at
/// most the integral significand of whichever operand has quantum `Q`, and
/// that significand is below `2^p`. A multiple of `Q`, at or above the
/// format's least quantum, with fewer than `p` significant bits is
/// representable. The sum lies in `s * [b/2, b)`, so it is nonzero and no
/// signed-zero rounding question arises.
///
/// **Special operands** never take the corrected branch, and `fp.rem` already
/// agrees with `fmod` on them (ay's `fp_rem_exact` documents the same table):
///
/// * `x` or `y` NaN, `x` infinite, or `y` zero: both give NaN. The guard
///   excludes a NaN `r`. NaN payload and sign are not pinned by the policy,
///   and SMT-LIB has a single NaN anyway.
/// * `y` infinite and `x` finite: `fp.rem(x, ±inf) = x = fmod(x, ±inf)`. `r`
///   has the sign of `x`, so the branch is not taken.
/// * `x` zero and `y` nonzero, not NaN: both return `x`, keeping its zero
///   sign. Excluded by `isZero(r)`.
/// * An exact multiple: both give a zero with the sign of `x`, for example
///   `-6.0 % 3.0 = -0.0`. Excluded by `isZero(r)`.
///
/// `crates/trust-ir-ay/tests/frem_fmod.rs` holds every case bit for bit to
/// the reference interpreter.
fn encode_frem_fmod(solver: &mut Solver, x: Term, y: Term) -> Result<Term, AYError> {
    let r = solver.try_fp_rem(x, y)?;
    let r_zero = solver.try_fp_is_zero(r)?;
    let r_nan = solver.try_fp_is_nan(r)?;
    let r_unadjusted = solver.try_or(r_zero, r_nan)?;
    let r_ordinary = solver.try_not(r_unadjusted)?;
    let r_negative = solver.try_fp_is_negative(r)?;
    let x_negative = solver.try_fp_is_negative(x)?;
    let sign_differs = solver.try_xor(r_negative, x_negative)?;
    let overshot = solver.try_and(r_ordinary, sign_differs)?;
    // copysign(|y|, x)
    let y_magnitude = solver.try_fp_abs(y)?;
    let y_magnitude_negated = solver.try_fp_neg(y_magnitude)?;
    let step = solver.try_ite(x_negative, y_magnitude_negated, y_magnitude)?;
    let rm = rne(solver)?;
    let corrected = solver.try_fp_add(rm, r, step)?;
    Ok(solver.try_ite(overshot, corrected, r)?)
}

/// The low `dst_width` bits of `operand` (`trunc` / narrowing `ptrtoint`).
/// A zero-width result has no top bit: refused by name, never computed as
/// `0 - 1` (r11 review L8: a debug panic, and a wrapped `u32::MAX` in
/// release that only ay's own range check then caught).
fn low_bits(solver: &mut Solver, operand: Term, dst_width: u32, op: &str) -> Result<Term, AYError> {
    let top = dst_width
        .checked_sub(1)
        .ok_or_else(|| AYError::UnsupportedOp(format!("{op} to a zero-width integer")))?;
    Ok(solver.try_bvextract(operand, top, 0)?)
}

/// The bit width of a bit-vector term, or a `SortMismatch` for anything else.
/// A handle `solver` did not issue is ay's typed `InvalidTermHandle` (via
/// `try_term_sort`), never a panic (r11 review M1).
fn bitvec_width_of(solver: &Solver, term: Term, op: &'static str) -> Result<u32, AYError> {
    solver
        .try_term_sort(term)?
        .bitvec_width()
        .ok_or_else(|| AYError::UnsupportedOp(format!("{op}: operand is not a bit-vector")))
}

/// `rotl` / `rotr` by a TERM amount (WS3.20). See `encode_binop`.
fn encode_rotate(solver: &mut Solver, lhs: Term, rhs: Term, left: bool) -> Result<Term, AYError> {
    let op = if left { "rotl" } else { "rotr" };
    let width = bitvec_width_of(solver, lhs, op)?;
    let w = solver.try_bv_const_u64(u64::from(width), width)?;
    let n = solver.try_bvurem(rhs, w)?;
    let w_minus_n = solver.try_bvsub(w, n)?;
    let (hi, lo) = if left {
        (
            solver.try_bvshl(lhs, n)?,
            solver.try_bvlshr(lhs, w_minus_n)?,
        )
    } else {
        (
            solver.try_bvlshr(lhs, n)?,
            solver.try_bvshl(lhs, w_minus_n)?,
        )
    };
    Ok(solver.try_bvor(hi, lo)?)
}

/// `ctlz` (WS3.20): a chain of `ite`s over the bits, low to high, so the
/// HIGHEST set bit wins: `w - 1 - index(highest set bit)`, and `w` when no
/// bit is set — the same total definition as the interpreter and Lean.
fn encode_ctlz(solver: &mut Solver, x: Term) -> Result<Term, AYError> {
    let width = bitvec_width_of(solver, x, "ctlz")?;
    let one = solver.try_bv_const_u64(1, 1)?;
    let mut acc = solver.try_bv_const_u64(u64::from(width), width)?;
    for i in 0..width {
        let bit = solver.try_bvextract(x, i, i)?;
        let set = solver.try_eq(bit, one)?;
        let count = solver.try_bv_const_u64(u64::from(width - 1 - i), width)?;
        acc = solver.try_ite(set, count, acc)?;
    }
    Ok(acc)
}

/// `cttz` (WS3.20): the same chain high to low, so the LOWEST set bit wins;
/// `w` when no bit is set.
fn encode_cttz(solver: &mut Solver, x: Term) -> Result<Term, AYError> {
    let width = bitvec_width_of(solver, x, "cttz")?;
    let one = solver.try_bv_const_u64(1, 1)?;
    let mut acc = solver.try_bv_const_u64(u64::from(width), width)?;
    for i in (0..width).rev() {
        let bit = solver.try_bvextract(x, i, i)?;
        let set = solver.try_eq(bit, one)?;
        let count = solver.try_bv_const_u64(u64::from(i), width)?;
        acc = solver.try_ite(set, count, acc)?;
    }
    Ok(acc)
}

/// Count a nonempty interval in a balanced tree. Each subtotal has exactly
/// enough bits to hold the interval length, so addition cannot wrap. Widen
/// only at the parent, keeping the formula small even for wide integers.
fn encode_ctpop_interval(solver: &mut Solver, x: Term, lo: u32, len: u32) -> Result<Term, AYError> {
    if len == 1 {
        return Ok(solver.try_bvextract(x, lo, lo)?);
    }
    let left_len = len / 2;
    let left = encode_ctpop_interval(solver, x, lo, left_len)?;
    let right = encode_ctpop_interval(solver, x, lo + left_len, len - left_len)?;
    let bits = u32::BITS - len.leading_zeros();
    let left_bits = u32::BITS - left_len.leading_zeros();
    let right_bits = u32::BITS - (len - left_len).leading_zeros();
    let left = if bits > left_bits {
        solver.try_bvzeroext(left, bits - left_bits)?
    } else {
        left
    };
    let right = if bits > right_bits {
        solver.try_bvzeroext(right, bits - right_bits)?
    } else {
        right
    };
    Ok(solver.try_bvadd(left, right)?)
}

fn encode_ctpop(solver: &mut Solver, x: Term) -> Result<Term, AYError> {
    let width = bitvec_width_of(solver, x, "ctpop")?;
    if width == 0 {
        return Err(AYError::UnsupportedOp(
            "ctpop of a zero-width bit-vector".into(),
        ));
    }
    let count = encode_ctpop_interval(solver, x, 0, width)?;
    let bits = u32::BITS - width.leading_zeros();
    if width > bits {
        Ok(solver.try_bvzeroext(count, width - bits)?)
    } else {
        Ok(count)
    }
}

/// `bswap` (WS3.20): the bytes re-concatenated in reverse order (`bvconcat`
/// puts its first argument on the HIGH side, so byte 0 ends up on top).
/// Every TrustIr integer width is a whole number of bytes; a width that is
/// not is refused rather than guessed.
fn encode_bswap(solver: &mut Solver, x: Term) -> Result<Term, AYError> {
    let width = bitvec_width_of(solver, x, "bswap")?;
    if width % 8 != 0 {
        return Err(AYError::UnsupportedOp(format!(
            "bswap at width {width} (not a whole number of bytes)"
        )));
    }
    let mut acc: Option<Term> = None;
    for byte in 0..width / 8 {
        let lane = solver.try_bvextract(x, byte * 8 + 7, byte * 8)?;
        acc = Some(match acc {
            None => lane,
            Some(acc) => solver.try_bvconcat(acc, lane)?,
        });
    }
    acc.ok_or_else(|| AYError::UnsupportedOp("bswap at width 0".to_string()))
}

/// `bitreverse` (WS3.20): the bits re-concatenated in reverse order.
fn encode_bitreverse(solver: &mut Solver, x: Term) -> Result<Term, AYError> {
    let width = bitvec_width_of(solver, x, "bitreverse")?;
    let mut acc: Option<Term> = None;
    for i in 0..width {
        let bit = solver.try_bvextract(x, i, i)?;
        acc = Some(match acc {
            None => bit,
            Some(acc) => solver.try_bvconcat(acc, bit)?,
        });
    }
    acc.ok_or_else(|| AYError::UnsupportedOp("bitreverse at width 0".to_string()))
}

/// Encode a TrustIr `ICmpOp` as a ay bitvector comparison.
///
/// All 10 integer comparison operations require equally wide bit-vector operands.
/// Returns an SMT Bool; schema Bool values use a separate BV1 carrier.
pub fn encode_icmp(solver: &mut Solver, op: ICmpOp, lhs: Term, rhs: Term) -> Result<Term, AYError> {
    // Equality is polymorphic in SMT. The IR integer comparison contract is
    // not: accepting two floating terms here would silently compare values
    // instead of their integer images (notably SMT's single NaN value).
    let lhs_width = bitvec_width_of(solver, lhs, "icmp")?;
    let rhs_width = bitvec_width_of(solver, rhs, "icmp")?;
    if lhs_width != rhs_width {
        return Err(AYError::UnsupportedOp(format!(
            "icmp requires equal bit-vector widths ({lhs_width} != {rhs_width})"
        )));
    }
    Ok(match op {
        ICmpOp::Eq => solver.try_eq(lhs, rhs)?,
        ICmpOp::Ne => {
            let eq = solver.try_eq(lhs, rhs)?;
            solver.try_not(eq)?
        }
        ICmpOp::Ult => solver.try_bvult(lhs, rhs)?,
        ICmpOp::Ule => solver.try_bvule(lhs, rhs)?,
        ICmpOp::Ugt => solver.try_bvugt(lhs, rhs)?,
        ICmpOp::Uge => solver.try_bvuge(lhs, rhs)?,
        ICmpOp::Slt => solver.try_bvslt(lhs, rhs)?,
        ICmpOp::Sle => solver.try_bvsle(lhs, rhs)?,
        ICmpOp::Sgt => solver.try_bvsgt(lhs, rhs)?,
        ICmpOp::Sge => solver.try_bvsge(lhs, rhs)?,
    })
}

/// Encode a TrustIr `UnOp` as a ay unary operation.
///
/// - `Not` -> `bvnot` (bitwise complement)
/// - `Neg` -> `bvneg` (two's complement negation)
/// - `FNeg` -> `fp.neg` (floating-point negation)
/// - `CtPop` -> exact balanced bit-count tree, widened to the operand width
pub fn encode_unop(solver: &mut Solver, op: UnOp, operand: Term) -> Result<Term, AYError> {
    match op {
        UnOp::Not => Ok(solver.try_bvnot(operand)?),
        UnOp::Neg => Ok(solver.try_bvneg(operand)?),
        UnOp::FNeg => Ok(solver.try_fp_neg(operand)?),
        UnOp::FAbs => Ok(solver.try_fp_abs(operand)?),
        UnOp::FSqrt => Err(AYError::UnsupportedOp("fsqrt".to_string())),
        UnOp::FFloor => Err(AYError::UnsupportedOp("ffloor".to_string())),
        UnOp::FCeil => Err(AYError::UnsupportedOp("fceil".to_string())),
        UnOp::FTrunc => Err(AYError::UnsupportedOp("ftrunc".to_string())),
        UnOp::CtPop => encode_ctpop(solver, operand),
        // WS3.20 bit intrinsics: exact bit-vector encodings (see each helper).
        UnOp::CtLz => encode_ctlz(solver, operand),
        UnOp::CtTz => encode_cttz(solver, operand),
        UnOp::BSwap => encode_bswap(solver, operand),
        UnOp::BitReverse => encode_bitreverse(solver, operand),
    }
}

/// Encode a TrustIr cast using typed AY bitvector and floating-point terms.
///
/// - `Trunc` -> `bvextract` (extract low bits)
/// - `ZExt` -> `bvzeroext` (zero-extend)
/// - `SExt` -> `bvsignext` (sign-extend)
///
/// Float-to-integer conversion uses RTZ; integer-to-float and float narrowing
/// use RNE. Saturating conversion handles NaN and range limits explicitly.
/// Raw float-to-integer terms cover defined inputs only: their construction
/// does not establish the IR's finite/range precondition. Reification,
/// transmute and pointer-to-pointer casts remain structured refusals.
pub fn encode_cast(
    solver: &mut Solver,
    op: CastOp,
    operand: Term,
    src_width: u32,
    dst_width: u32,
) -> Result<Term, AYError> {
    match op {
        CastOp::Trunc => {
            if dst_width >= src_width {
                return Err(AYError::UnsupportedOp(format!(
                    "trunc requires dst_width ({}) < src_width ({})",
                    dst_width, src_width
                )));
            }
            // Extract bits [dst_width-1:0]
            low_bits(solver, operand, dst_width, "trunc")
        }
        CastOp::ZExt => {
            if dst_width <= src_width {
                return Err(AYError::UnsupportedOp(format!(
                    "zext requires dst_width ({}) > src_width ({})",
                    dst_width, src_width
                )));
            }
            let extend_by = dst_width - src_width;
            Ok(solver.try_bvzeroext(operand, extend_by)?)
        }
        CastOp::SExt => {
            if dst_width <= src_width {
                return Err(AYError::UnsupportedOp(format!(
                    "sext requires dst_width ({}) > src_width ({})",
                    dst_width, src_width
                )));
            }
            let extend_by = dst_width - src_width;
            Ok(solver.try_bvsignext(operand, extend_by)?)
        }
        CastOp::FPToUI => {
            // Defined inputs truncate toward zero. Out-of-range / NaN inputs
            // remain outside the IR's raw-cast domain (not saturation).
            let rm = rtz(solver)?;
            Ok(solver.try_fp_to_ubv(rm, operand, dst_width)?)
        }
        CastOp::FPToSI => {
            let rm = rtz(solver)?;
            Ok(solver.try_fp_to_sbv(rm, operand, dst_width)?)
        }
        CastOp::UIToFP => {
            // Unsigned bitvector -> FP. dst_width encodes eb+sb.
            let rm = rne(solver)?;
            let (eb, sb) = fp_sort_from_total_width(dst_width)?;
            Ok(solver.try_bv_to_fp_unsigned(rm, operand, eb, sb)?)
        }
        CastOp::SIToFP => {
            // Signed bitvector -> FP. Uses bv_to_fp (signed interpretation).
            let rm = rne(solver)?;
            let (eb, sb) = fp_sort_from_total_width(dst_width)?;
            Ok(solver.try_bv_to_fp(rm, operand, eb, sb)?)
        }
        CastOp::FPTrunc => {
            // FP -> narrower FP (e.g., f64 -> f32)
            let rm = rne(solver)?;
            let (eb, sb) = fp_sort_from_total_width(dst_width)?;
            Ok(solver.try_fp_to_fp(rm, operand, eb, sb)?)
        }
        CastOp::FPExt => {
            // FP -> wider FP (e.g., f32 -> f64)
            let rm = rne(solver)?;
            let (eb, sb) = fp_sort_from_total_width(dst_width)?;
            Ok(solver.try_fp_to_fp(rm, operand, eb, sb)?)
        }
        CastOp::PtrToInt => {
            // Pointer is BitVec(64) in our encoding. Target is integer BitVec(dst_width).
            // src_width is the pointer width (always 64 in our model).
            if dst_width == 64 {
                // Same width: identity
                Ok(operand)
            } else if dst_width < 64 {
                // Narrowing: extract low bits
                low_bits(solver, operand, dst_width, "ptrtoint")
            } else {
                // Widening: zero-extend
                let extend_by = dst_width - 64;
                Ok(solver.try_bvzeroext(operand, extend_by)?)
            }
        }
        CastOp::IntToPtr => {
            // Integer is BitVec(src_width). Target is pointer BitVec(64).
            if src_width == 64 {
                // Same width: identity
                Ok(operand)
            } else if src_width < 64 {
                // Narrower integer: zero-extend to 64
                let extend_by = 64 - src_width;
                Ok(solver.try_bvzeroext(operand, extend_by)?)
            } else {
                // Wider integer: truncate to 64 (extract low 64 bits)
                Ok(solver.try_bvextract(operand, 63, 0)?)
            }
        }
        CastOp::Bitcast => {
            // Same-width reinterpretation. In bitvector encoding, both source
            // and destination types map to BitVec of the same width, so this
            // is the identity operation. An IEEE floating image requires a
            // separate encoding; returning an FP term would erase that image.
            if src_width != dst_width {
                return Err(AYError::UnsupportedOp(format!(
                    "bitcast requires src_width ({}) == dst_width ({})",
                    src_width, dst_width
                )));
            }
            let actual_width = bitvec_width_of(solver, operand, "bitcast")?;
            if actual_width != src_width {
                return Err(AYError::UnsupportedOp(format!(
                    "bitcast operand width ({actual_width}) differs from declared source ({src_width})"
                )));
            }
            Ok(operand)
        }
        CastOp::PtrToPtr | CastOp::Transmute | CastOp::ReifyFnPointer => {
            Err(AYError::UnsupportedOp(format!(
                "{op} is proof-grade classified but unsupported by BV encoding"
            )))
        }
        CastOp::FPToSISat => encode_saturating_fp_cast(solver, operand, dst_width, true),
        CastOp::FPToUISat => encode_saturating_fp_cast(solver, operand, dst_width, false),
    }
}

/// Map a total FP bit width to (exponent_bits, significand_bits).
///
/// IEEE 754: F32 = 32 bits (8 + 24), F64 = 64 bits (11 + 53).
fn fp_sort_from_total_width(total_width: u32) -> Result<(u32, u32), AYError> {
    match total_width {
        32 => Ok((8, 24)),
        64 => Ok((11, 53)),
        other => Err(AYError::UnsupportedOp(format!(
            "unsupported FP width: {} (expected 32 or 64)",
            other
        ))),
    }
}

/// Encode a TrustIr `FCmpOp` as a ay floating-point comparison.
///
/// Ordered comparisons (O-prefix) return false if either operand is NaN.
/// Unordered comparisons (U-prefix) return true if either operand is NaN.
/// Returns a boolean ay term.
pub fn encode_fcmp(solver: &mut Solver, op: FCmpOp, lhs: Term, rhs: Term) -> Result<Term, AYError> {
    Ok(match op {
        // Ordered comparisons: false if NaN
        FCmpOp::OEq => solver.try_fp_eq(lhs, rhs)?,
        FCmpOp::ONe => {
            let eq = solver.try_fp_eq(lhs, rhs)?;
            solver.try_not(eq)?
        }
        FCmpOp::OLt => solver.try_fp_lt(lhs, rhs)?,
        FCmpOp::OLe => solver.try_fp_le(lhs, rhs)?,
        FCmpOp::OGt => solver.try_fp_gt(lhs, rhs)?,
        FCmpOp::OGe => solver.try_fp_ge(lhs, rhs)?,
        // Unordered comparisons: true if NaN
        FCmpOp::UEq => {
            // UEq = isNaN(a) OR isNaN(b) OR fp.eq(a, b)
            let nan_a = solver.try_fp_is_nan(lhs)?;
            let nan_b = solver.try_fp_is_nan(rhs)?;
            let eq = solver.try_fp_eq(lhs, rhs)?;
            let nan_either = solver.try_or(nan_a, nan_b)?;
            solver.try_or(nan_either, eq)?
        }
        FCmpOp::UNe => {
            // UNe = isNaN(a) OR isNaN(b) OR NOT fp.eq(a, b)
            let nan_a = solver.try_fp_is_nan(lhs)?;
            let nan_b = solver.try_fp_is_nan(rhs)?;
            let eq = solver.try_fp_eq(lhs, rhs)?;
            let neq = solver.try_not(eq)?;
            let nan_either = solver.try_or(nan_a, nan_b)?;
            solver.try_or(nan_either, neq)?
        }
        FCmpOp::ULt => {
            // ULt = isNaN(a) OR isNaN(b) OR fp.lt(a, b)
            let nan_a = solver.try_fp_is_nan(lhs)?;
            let nan_b = solver.try_fp_is_nan(rhs)?;
            let lt = solver.try_fp_lt(lhs, rhs)?;
            let nan_either = solver.try_or(nan_a, nan_b)?;
            solver.try_or(nan_either, lt)?
        }
        FCmpOp::ULe => {
            let nan_a = solver.try_fp_is_nan(lhs)?;
            let nan_b = solver.try_fp_is_nan(rhs)?;
            let le = solver.try_fp_le(lhs, rhs)?;
            let nan_either = solver.try_or(nan_a, nan_b)?;
            solver.try_or(nan_either, le)?
        }
        FCmpOp::UGt => {
            let nan_a = solver.try_fp_is_nan(lhs)?;
            let nan_b = solver.try_fp_is_nan(rhs)?;
            let gt = solver.try_fp_gt(lhs, rhs)?;
            let nan_either = solver.try_or(nan_a, nan_b)?;
            solver.try_or(nan_either, gt)?
        }
        FCmpOp::UGe => {
            let nan_a = solver.try_fp_is_nan(lhs)?;
            let nan_b = solver.try_fp_is_nan(rhs)?;
            let ge = solver.try_fp_ge(lhs, rhs)?;
            let nan_either = solver.try_or(nan_a, nan_b)?;
            solver.try_or(nan_either, ge)?
        }
    })
}

// ============================================================================
// Memory Model (Array Theory)
// ============================================================================

/// Memory state modeled as ay `Array(BitVec64, BitVec8)`: address -> byte.
///
/// This provides a byte-addressable memory model for encoding Load, Store,
/// Alloca, and GEP operations as ay array theory formulas.
pub struct MemoryModel {
    /// The ay term representing the current memory state (Array sort).
    pub state: Term,
    /// The bump pointer: the base the next [`Self::encode_alloca`] hands out.
    /// Always a multiple of [`ALLOCA_GRANULE`], never below it.
    next_free: u64,
}

/// Every alloca base is a multiple of this, and the first base is this, so
/// page 0 is never allocated and no base is null. Bases are therefore aligned
/// to any power of two up to 4 KiB.
const ALLOCA_GRANULE: u64 = 0x1000;

/// The ay sort for memory: `Array(BitVec(64), BitVec(8))`.
pub fn memory_sort() -> Sort {
    Sort::Array(Box::new(ArraySort {
        index_sort: Sort::BitVec(BitVecSort { width: 64 }),
        element_sort: Sort::BitVec(BitVecSort { width: 8 }),
    }))
}

impl MemoryModel {
    /// Create a new symbolic memory state.
    pub fn new(solver: &mut Solver, name: &str) -> Result<Self, AYError> {
        let sort = memory_sort();
        let state = solver.try_declare_const(name, sort)?;
        Ok(Self {
            state,
            next_free: ALLOCA_GRANULE,
        })
    }

    /// Encode a multi-byte load from memory.
    ///
    /// Reads `byte_width` consecutive bytes from `addr` and concatenates
    /// them in little-endian order to produce a bitvector of the given width.
    pub fn encode_load(
        &self,
        solver: &mut Solver,
        addr: Term,
        byte_width: u32,
    ) -> Result<Term, AYError> {
        if byte_width == 0 {
            return Err(AYError::MemoryError("load of zero bytes".to_string()));
        }
        // Read byte 0 (least significant)
        let byte0 = solver.try_select(self.state, addr)?;
        if byte_width == 1 {
            return Ok(byte0);
        }
        // Read remaining bytes and concatenate (little-endian: high bytes on left)
        let mut result = byte0;
        for i in 1..byte_width {
            let offset = solver.try_bv_const(i as i64, 64)?;
            let byte_addr = solver.try_bvadd(addr, offset)?;
            let byte_val = solver.try_select(self.state, byte_addr)?;
            // Concat: byte_val is more significant, result is less significant
            result = solver.try_bvconcat(byte_val, result)?;
        }
        Ok(result)
    }

    /// Encode a multi-byte store to memory.
    ///
    /// Writes `byte_width` bytes from `value` to consecutive addresses starting
    /// at `addr` in little-endian order. Returns the updated memory state.
    pub fn encode_store(
        &mut self,
        solver: &mut Solver,
        addr: Term,
        value: Term,
        byte_width: u32,
    ) -> Result<Term, AYError> {
        if byte_width == 0 {
            return Err(AYError::MemoryError("store of zero bytes".to_string()));
        }
        // The stored value is a bit-vector of `byte_width * 8` bits, and a
        // bit-vector width is a `u32`: a wider store has no value to extract
        // from. Refused before any solver work, never wrapped into a bit
        // offset of some other byte.
        let too_wide = || {
            AYError::MemoryError(format!(
                "store of {byte_width} bytes: {byte_width} * 8 bits exceeds the u32 bit-vector \
                 width"
            ))
        };
        if byte_width.checked_mul(8).is_none() {
            return Err(too_wide());
        }
        let mut mem = self.state;
        for i in 0..byte_width {
            // Extract byte i from value (little-endian: byte 0 is bits [7:0]).
            // `lo` is a multiple of 8, so `lo | 7` is `lo + 7` without an add.
            let lo = i.checked_mul(8).ok_or_else(too_wide)?;
            let hi = lo | 7;
            let offset = solver.try_bv_const(i64::from(i), 64)?;
            let byte_addr = solver.try_bvadd(addr, offset)?;
            let byte_val = solver.try_bvextract(value, hi, lo)?;
            mem = solver.try_store(mem, byte_addr, byte_val)?;
        }
        self.state = mem;
        Ok(mem)
    }

    /// Encode an alloca: return a fresh, concrete, non-null address for
    /// `byte_size` bytes that overlaps no earlier allocation.
    ///
    /// Bases come from a bump pointer over [`ALLOCA_GRANULE`] (4 KiB)
    /// granules, starting at 0x1000: the allocation occupies
    /// `[base, base + max(byte_size, 1))` and the next base is the first
    /// granule boundary at or above its end. Allocations of at most 4 KiB keep
    /// the historical bases 0x1000, 0x2000, 0x3000, ...; a larger one now
    /// advances the pointer past its own end. (The earlier fixed 0x1000 stride
    /// overlapped any allocation larger than 4 KiB — a `<1024 x i64>` slot, as
    /// the whole-function VC sizes it — with the next one, so a store to one
    /// was visible through a load from the other.)
    ///
    /// # Errors
    ///
    /// [`AYError::MemoryError`] when the allocation and its granule padding do
    /// not fit below 2^64. The model refuses rather than wrap a base onto an
    /// earlier allocation, and so never asserts the (then false) no-wrap
    /// constraint that would make every later query vacuously unsatisfiable.
    pub fn encode_alloca(&mut self, solver: &mut Solver, byte_size: u64) -> Result<Term, AYError> {
        let base = self.next_free;
        let exhausted = || {
            AYError::MemoryError(format!(
                "alloca of {byte_size} bytes at base {base:#x} does not fit the 64-bit address space"
            ))
        };
        let end = base.checked_add(byte_size.max(1)).ok_or_else(exhausted)?;
        self.next_free =
            end.checked_add(ALLOCA_GRANULE - 1).ok_or_else(exhausted)? & !(ALLOCA_GRANULE - 1);
        let addr = solver.try_bv_const_u64(base, 64)?;

        // Assert non-null
        let null = solver.try_bv_const(0, 64)?;
        let not_null = solver.try_eq(addr, null)?;
        let not_null = solver.try_not(not_null)?;
        solver.try_assert_term(not_null)?;

        // Assert in-bounds: addr + size does not wrap around (true by the
        // checked arithmetic above; stated so the solver has it too).
        let size = solver.try_bv_const_u64(byte_size, 64)?;
        let end = solver.try_bvadd(addr, size)?;
        let no_wrap = solver.try_bvuge(end, addr)?;
        solver.try_assert_term(no_wrap)?;

        Ok(addr)
    }

    /// Encode a GEP (GetElementPtr) as pointer arithmetic.
    ///
    /// `base + offset_bytes` using bitvector addition on 64-bit pointers.
    pub fn encode_gep(
        &self,
        solver: &mut Solver,
        base: Term,
        offset_bytes: Term,
    ) -> Result<Term, AYError> {
        Ok(solver.try_bvadd(base, offset_bytes)?)
    }
}

// ============================================================================
// Borrow Model (Permission Map)
// ============================================================================

/// Borrow permission state modeled as ay `Array(BitVec64, BitVec2)`: pointer -> permission.
///
/// Permission encoding:
/// - 0 = NoPermission
/// - 1 = Owned
/// - 2 = SharedBorrow
/// - 3 = MutableBorrow
///
/// This models the Rust borrow checker's permission map. Each pointer address
/// maps to a 2-bit permission level. Transitions:
/// - `Borrow`: Owned(1) or SharedBorrow(2) -> SharedBorrow(2)
/// - `BorrowMut`: Owned(1) -> MutableBorrow(3)
/// - `EndBorrow`: any -> Owned(1)
pub struct BorrowModel {
    /// The ay term representing the current borrow permission state (Array sort).
    pub state: Term,
}

/// The ay sort for borrow permissions: `Array(BitVec(64), BitVec(2))`.
pub fn permission_sort() -> Sort {
    Sort::Array(Box::new(ArraySort {
        index_sort: Sort::BitVec(BitVecSort { width: 64 }),
        element_sort: Sort::BitVec(BitVecSort { width: 2 }),
    }))
}

impl BorrowModel {
    /// Create a new symbolic borrow permission state.
    pub fn new(solver: &mut Solver, name: &str) -> Result<Self, AYError> {
        let sort = permission_sort();
        let state = solver.try_declare_const(name, sort)?;
        Ok(Self { state })
    }

    /// Encode a shared borrow from `ptr`.
    ///
    /// The pointer must currently be `Owned` (1) or already `SharedBorrow` (2).
    /// Asserts this precondition and sets the permission to `SharedBorrow` (2).
    /// Returns the borrowed pointer and the updated permission state.
    pub fn encode_borrow(
        &mut self,
        solver: &mut Solver,
        ptr: Term,
    ) -> Result<(Term, Term), AYError> {
        let permission = self.get_permission(solver, ptr)?;
        let owned = solver.try_bv_const(1, 2)?;
        let shared_borrow = solver.try_bv_const(2, 2)?;
        let is_owned = solver.try_eq(permission, owned)?;
        let is_shared = solver.try_eq(permission, shared_borrow)?;
        let can_borrow = solver.try_or(is_owned, is_shared)?;
        solver.try_assert_term(can_borrow)?;

        let new_state = solver.try_store(self.state, ptr, shared_borrow)?;
        self.state = new_state;
        Ok((ptr, new_state))
    }

    /// Encode a mutable borrow from `ptr`.
    ///
    /// The pointer must currently be `Owned` (1). Asserts this precondition
    /// and sets the permission to `MutableBorrow` (3).
    /// Returns the borrowed pointer and the updated permission state.
    pub fn encode_borrow_mut(
        &mut self,
        solver: &mut Solver,
        ptr: Term,
    ) -> Result<(Term, Term), AYError> {
        let permission = self.get_permission(solver, ptr)?;
        let owned = solver.try_bv_const(1, 2)?;
        let mutable_borrow = solver.try_bv_const(3, 2)?;
        let is_owned = solver.try_eq(permission, owned)?;
        solver.try_assert_term(is_owned)?;

        let new_state = solver.try_store(self.state, ptr, mutable_borrow)?;
        self.state = new_state;
        Ok((ptr, new_state))
    }

    /// Encode the end of a borrow, restoring ownership.
    ///
    /// Sets the permission back to `Owned` (1). Returns the updated state.
    pub fn encode_end_borrow(
        &mut self,
        solver: &mut Solver,
        borrow_ptr: Term,
    ) -> Result<Term, AYError> {
        let owned = solver.try_bv_const(1, 2)?;
        let new_state = solver.try_store(self.state, borrow_ptr, owned)?;
        self.state = new_state;
        Ok(new_state)
    }

    /// Read the current permission for `ptr`.
    pub fn get_permission(&self, solver: &mut Solver, ptr: Term) -> Result<Term, AYError> {
        Ok(solver.try_select(self.state, ptr)?)
    }
}

// ============================================================================
// ARC Model (Refcount Map)
// ============================================================================

/// ARC refcount state modeled as ay `Array(BitVec64, BitVec32)`: pointer -> refcount.
///
/// Each pointer address maps to a 32-bit unsigned reference count.
/// - `Retain`: refcount += 1
/// - `Release`: refcount -= 1 (must be > 0)
/// - `IsUnique`: refcount == 1
pub struct ArcModel {
    /// The ay term representing the current ARC refcount state (Array sort).
    pub state: Term,
}

/// The ay sort for ARC refcounts: `Array(BitVec(64), BitVec(32))`.
pub fn refcount_sort() -> Sort {
    Sort::Array(Box::new(ArraySort {
        index_sort: Sort::BitVec(BitVecSort { width: 64 }),
        element_sort: Sort::BitVec(BitVecSort { width: 32 }),
    }))
}

impl ArcModel {
    /// Create a new symbolic ARC refcount state.
    pub fn new(solver: &mut Solver, name: &str) -> Result<Self, AYError> {
        let sort = refcount_sort();
        let state = solver.try_declare_const(name, sort)?;
        Ok(Self { state })
    }

    /// Encode an ARC retain by incrementing the refcount.
    ///
    /// Returns the updated refcount state.
    pub fn encode_retain(&mut self, solver: &mut Solver, ptr: Term) -> Result<Term, AYError> {
        let refcount = self.get_refcount(solver, ptr)?;
        let one = solver.try_bv_const(1, 32)?;
        let new_refcount = solver.try_bvadd(refcount, one)?;
        let new_state = solver.try_store(self.state, ptr, new_refcount)?;
        self.state = new_state;
        Ok(new_state)
    }

    /// Encode an ARC release by decrementing the refcount.
    ///
    /// Asserts that the refcount is > 0 before decrementing.
    /// Returns the updated refcount state.
    pub fn encode_release(&mut self, solver: &mut Solver, ptr: Term) -> Result<Term, AYError> {
        let refcount = self.get_refcount(solver, ptr)?;
        let zero = solver.try_bv_const(0, 32)?;
        let one = solver.try_bv_const(1, 32)?;
        let positive = solver.try_bvugt(refcount, zero)?;
        solver.try_assert_term(positive)?;

        let new_refcount = solver.try_bvsub(refcount, one)?;
        let new_state = solver.try_store(self.state, ptr, new_refcount)?;
        self.state = new_state;
        Ok(new_state)
    }

    /// Check whether `ptr` has a unique ARC reference (refcount == 1).
    ///
    /// Returns a boolean ay term.
    pub fn encode_is_unique(&self, solver: &mut Solver, ptr: Term) -> Result<Term, AYError> {
        let refcount = self.get_refcount(solver, ptr)?;
        let one = solver.try_bv_const(1, 32)?;
        Ok(solver.try_eq(refcount, one)?)
    }

    /// Read the current refcount for `ptr`.
    pub fn get_refcount(&self, solver: &mut Solver, ptr: Term) -> Result<Term, AYError> {
        Ok(solver.try_select(self.state, ptr)?)
    }
}

// ============================================================================
// Solver-verdict evidence-record pipeline
// ============================================================================

/// Result of the solver-verdict evidence-record pipeline.
#[derive(Debug)]
pub enum VerificationResult {
    /// ay returned UNSAT on the negated condition. This is a solver verdict,
    /// not reusable proof authority until ay exports a replayable proof.
    Verified(ProofCertificate),
    /// A counterexample was found (ay returned SAT, obligation does NOT hold).
    Refuted {
        /// The proof certificate with Failed status.
        certificate: ProofCertificate,
    },
    /// The solver could not determine satisfiability (timeout, resource limit).
    Unknown {
        /// The proof certificate with Pending status.
        certificate: ProofCertificate,
    },
}

/// End-to-end: check a proof annotation and produce an evidence record.
///
/// 1. Encodes the annotation as a ay verification condition
/// 2. Asserts the condition and checks satisfiability
/// 3. Maps the solver result to a [`VerificationResult`]:
///    - UNSAT -> `Verified` solver verdict, but public status remains `Pending`
///      until the certificate carries replayable proof bytes
///    - SAT -> Refuted (counterexample exists)
///    - Unknown -> Unknown (timeout or resource limit)
///
/// Returns a `VerificationResult` containing a non-authoritative
/// `ProofCertificate` record. Until AY exports proof bytes, callers must keep
/// successful obligations `Pending`; [`VerificationResult::status`] enforces
/// that fail-closed policy.
///
/// ONE SOLVER PER CALL. The condition is asserted into `solver` with no
/// push/pop frame, so it stays asserted afterwards: a later check on the same
/// solver is made under this one's negated goal. And on `Err` ay may have
/// left the solver corrupted (a caught panic is `SolverError::SolverPanic`).
/// Pass a fresh solver, and discard it after the call — always on `Err`. The
/// VC builder (`vc`) does not use this entry point; it frames each condition
/// and poisons its session on any error (r11 review H1, L8).
pub fn verify_and_certify(
    solver: &mut Solver,
    annotation: &ProofAnnotation,
    operands: &ProofOperands,
    obligation_id: ProofId,
) -> Result<VerificationResult, AYError> {
    let condition = verify_proof_obligation(solver, annotation, operands)?;

    // Assert the condition term
    solver.try_assert_term(condition.term)?;

    // Check satisfiability
    let sat_result = solver.try_check_sat()?;

    match condition.strategy {
        ProofStrategy::AssertAndCheckUnsat => {
            if sat_result.is_unsat() {
                // UNSAT => the negation is unsatisfiable => obligation holds.
                //
                // Cross-repo boundary (audit #86): this adapter IS a real
                // bridge — it owns the ay `Solver` FFI (`create_bv_solver` /
                // `create_fp_solver`), the full IR→SMT encoders
                // (`encode_binop`/`encode_icmp`/`encode_unop`/`encode_fcmp`/…),
                // and this end-to-end certificate pipeline.
                //
                // The `SmtProof` payload is EMPTY here, and the old reason for
                // that ("ay does not yet expose an UNSAT-proof / DRAT export
                // API") is obsolete: at the pinned rev
                // `Solver::set_produce_proofs(true)` +
                // `Solver::export_last_unsat_bundle()` do export an
                // offline-replayable `ay.proofbundle/v2`, and
                // `vc::replay_bundle_offline` re-checks one with no solver run.
                //
                // This single-obligation entry point still emits nothing,
                // deliberately: it is handed a bare `ProofCondition` with no
                // link back to the IR position the obligation is about, so a
                // payload attached here would certify "some formula is UNSAT"
                // with no way for any consumer to tell WHICH obligation it is
                // about. The payload is captured on the path that DOES have
                // that binding — `vc::generate_function_vc`, via
                // `ProofObligation::site`. See `vc::SmtReplayEvidence`.
                Ok(VerificationResult::Verified(ProofCertificate {
                    obligation: obligation_id,
                    prover: "ay".to_string(),
                    evidence: ProofEvidence::SmtProof(Vec::new()),
                    // v41: this adapter records no coverage bound of its own; the
                    // projection is the bundle writer's job, and `None` reads as
                    // UNKNOWN coverage rather than `Unbounded`.
                    assurance: None,
                }))
            } else if sat_result.is_sat() {
                // SAT => counterexample exists => obligation does NOT hold
                Ok(VerificationResult::Refuted {
                    certificate: ProofCertificate {
                        obligation: obligation_id,
                        prover: "ay".to_string(),
                        evidence: ProofEvidence::SmtProof(Vec::new()),
                        // v41: this adapter records no coverage bound of its own; the
                        // projection is the bundle writer's job, and `None` reads as
                        // UNKNOWN coverage rather than `Unbounded`.
                        assurance: None,
                    },
                })
            } else {
                // Unknown / timeout
                Ok(VerificationResult::Unknown {
                    certificate: ProofCertificate {
                        obligation: obligation_id,
                        prover: "ay".to_string(),
                        evidence: ProofEvidence::Trusted("ay returned unknown".to_string()),
                        // v41: this adapter records no coverage bound of its own; the
                        // projection is the bundle writer's job, and `None` reads as
                        // UNKNOWN coverage rather than `Unbounded`.
                        assurance: None,
                    },
                })
            }
        }
    }
}

impl VerificationResult {
    /// Returns the module-safe proof status.
    ///
    /// A `Verified` AY solver verdict remains [`ProofStatus::Pending`] because
    /// this entry point emits an empty `SmtProof` payload — not because no
    /// payload exists (one does; see `verify_proof_obligation`'s note and
    /// `vc::replay_bundle_offline`), but because a bare `ProofCondition`
    /// carries no binding back to the obligation it is about. Callers can
    /// inspect the enum variant to report solver progress, but must not mint
    /// `Discharged` from it.
    pub fn status(&self) -> ProofStatus {
        match self {
            VerificationResult::Verified(_) => ProofStatus::Pending,
            VerificationResult::Refuted { .. } => ProofStatus::Failed,
            VerificationResult::Unknown { .. } => ProofStatus::Pending,
        }
    }

    /// Whether AY proved the encoded condition in this process. This reports
    /// the solver verdict only; it is not replayable certificate authority.
    pub fn is_proved_by_solver(&self) -> bool {
        matches!(self, VerificationResult::Verified(_))
    }

    /// Consumes self and returns the non-authoritative evidence record.
    /// Successful records currently contain an empty `SmtProof` payload and
    /// therefore cannot discharge an obligation during module validation.
    pub fn into_certificate(self) -> ProofCertificate {
        match self {
            VerificationResult::Verified(cert) => cert,
            VerificationResult::Refuted { certificate } => certificate,
            VerificationResult::Unknown { certificate } => certificate,
        }
    }
}

/// Encode a TrustIr `OverflowOp` as a ay overflow detection formula.
///
/// Returns a boolean term that is `true` when NO overflow occurs (safe).
/// This uses ay's built-in overflow detection primitives, selected by the
/// operand type's SIGNEDNESS — the predicates are signedness-specific
/// (Z3-style API), and using the wrong lane is a SOUNDNESS bug, not a
/// precision bug.
///
/// CONFIRMED FALSE-ACCEPT (2026-07-09, tRust falsification probe): the
/// previous encoding hardcoded the signed lanes for every type, so a `U64`
/// `SubOverflow` was checked with `bvsub_no_underflow(a, b, is_signed=true)`
/// — under SIGNED semantics `0 - 1 = -1` does not underflow, so the borrow
/// case `a < b` was reported SAFE and `pub fn sub(a: usize, b: usize) ->
/// usize { a - b }` verified clean while it panics for `a < b` (and the
/// out-of-bounds write it guarded reached memory in release). The native
/// trust-mc/PDR lane proved the assert unreachable from exactly this
/// mis-encoded flag.
///
/// Signed (two's complement):
/// - `AddOverflow` -> `bvadd_no_overflow(a, b, true) AND bvadd_no_underflow(a, b)`
///   (pos+pos high overflow; neg+neg low underflow)
/// - `SubOverflow` -> `bvsub_no_overflow(a, b) AND bvsub_no_underflow(a, b, true)`
///   (pos-neg high overflow; neg-pos low underflow)
/// - `MulOverflow` -> `bvmul_no_overflow(a, b, true) AND bvmul_no_underflow(a, b)`
///
/// Unsigned:
/// - `AddOverflow` -> `bvadd_no_overflow(a, b, false)` (carry-out; no low case)
/// - `SubOverflow` -> `bvsub_no_underflow(a, b, false)` (borrow, i.e. `a >= b`;
///   no high case — an unsigned difference never exceeds the minuend)
/// - `MulOverflow` -> `bvmul_no_overflow(a, b, false)` (no low case)
pub fn encode_overflow_check(
    solver: &mut Solver,
    op: OverflowOp,
    is_signed: bool,
    lhs: Term,
    rhs: Term,
) -> Result<Term, AYError> {
    Ok(match (op, is_signed) {
        (OverflowOp::AddOverflow, true) => {
            let no_overflow = solver.try_bvadd_no_overflow(lhs, rhs, true)?;
            let no_underflow = solver.try_bvadd_no_underflow(lhs, rhs)?;
            solver.try_and(no_overflow, no_underflow)?
        }
        (OverflowOp::AddOverflow, false) => solver.try_bvadd_no_overflow(lhs, rhs, false)?,
        (OverflowOp::SubOverflow, true) => {
            let no_overflow = solver.try_bvsub_no_overflow(lhs, rhs)?;
            let no_underflow = solver.try_bvsub_no_underflow(lhs, rhs, true)?;
            solver.try_and(no_overflow, no_underflow)?
        }
        (OverflowOp::SubOverflow, false) => solver.try_bvsub_no_underflow(lhs, rhs, false)?,
        (OverflowOp::MulOverflow, true) => {
            let no_overflow = solver.try_bvmul_no_overflow(lhs, rhs, true)?;
            let no_underflow = solver.try_bvmul_no_underflow(lhs, rhs)?;
            solver.try_and(no_overflow, no_underflow)?
        }
        (OverflowOp::MulOverflow, false) => solver.try_bvmul_no_overflow(lhs, rhs, false)?,
    })
}

/// Generate a ay verification condition for a `ProofAnnotation`.
///
/// Given symbolic operand terms, generates the ay formula that must be
/// satisfiable/unsatisfiable to verify or refute the annotation.
///
/// Returns `(assertion, is_negated)`:
/// - `assertion`: the ay term encoding the proof condition
/// - `is_negated`: if true, assert the NEGATION and check for UNSAT
///   (i.e., the annotation holds iff `NOT assertion` is UNSAT)
///
/// # Supported annotations
///
/// | Annotation | Operands | Encoding |
/// |------------|----------|----------|
/// | `NoOverflow` | `(lhs, rhs, op)` via `overflow_op` | overflow check |
/// | `DivNonZero` | `divisor` | `divisor != 0` |
/// | `ShiftInRange` | `(shift_amount, bit_width_const)` | `shift_amount < bit_width` |
/// | `InBounds` | `(index, length)` | `index < length` (unsigned) |
/// | `NotNull` | `ptr` | `ptr != 0` |
/// | `NoWrap` | `(lhs, rhs, op)` via `overflow_op` | same as NoOverflow |
/// | `ValidBorrow` | `(ptr, permission)` | `permission == Owned(1)` |
/// | `UniqueBorrow` | `(ptr, permission)` | `permission != MutableBorrow(3)` |
/// | `SharedBorrow` | `(ptr, permission)` | `permission == Owned(1) OR SharedBorrow(2)` |
pub fn verify_proof_obligation(
    solver: &mut Solver,
    annotation: &ProofAnnotation,
    operands: &ProofOperands,
) -> Result<ProofCondition, AYError> {
    match annotation {
        ProofAnnotation::NoOverflow | ProofAnnotation::NoWrap => {
            let (lhs, rhs, op) = operands.overflow_operands()?;
            // FAIL CLOSED without the operand type's signedness: the overflow
            // predicates are signedness-specific and defaulting is exactly the
            // confirmed unsigned-sub false-accept (see `encode_overflow_check`).
            let Some(is_signed) = operands.signed else {
                return Err(AYError::UnsupportedAnnotation(format!(
                    "{annotation} requires the operand type's signedness \
                     (ProofOperands::with_signedness); refusing to default"
                )));
            };
            let safe = encode_overflow_check(solver, *op, is_signed, lhs, rhs)?;
            // Assert NOT safe, check UNSAT => safe always holds
            let negated = solver.try_not(safe)?;
            Ok(ProofCondition {
                term: negated,
                strategy: ProofStrategy::AssertAndCheckUnsat,
            })
        }
        ProofAnnotation::DivNonZero => {
            let divisor = operands.single_operand("divisor")?;
            let zero = solver.try_bv_const(0, operands.bit_width()?)?;
            let is_zero = solver.try_eq(divisor, zero)?;
            // Assert divisor == 0, check UNSAT => divisor never zero
            Ok(ProofCondition {
                term: is_zero,
                strategy: ProofStrategy::AssertAndCheckUnsat,
            })
        }
        ProofAnnotation::ShiftInRange => {
            let (shift_amount, bit_width_term) =
                operands.two_operands("shift_amount", "bit_width")?;
            let out_of_range = solver.try_bvuge(shift_amount, bit_width_term)?;
            // Assert shift >= width, check UNSAT => shift always in range
            Ok(ProofCondition {
                term: out_of_range,
                strategy: ProofStrategy::AssertAndCheckUnsat,
            })
        }
        ProofAnnotation::InBounds => {
            let (index, length) = operands.two_operands("index", "length")?;
            let out_of_bounds = solver.try_bvuge(index, length)?;
            // Assert index >= length, check UNSAT => always in bounds
            Ok(ProofCondition {
                term: out_of_bounds,
                strategy: ProofStrategy::AssertAndCheckUnsat,
            })
        }
        ProofAnnotation::NotNull => {
            let ptr = operands.single_operand("ptr")?;
            let null = solver.try_bv_const(0, 64)?;
            let is_null = solver.try_eq(ptr, null)?;
            // Assert ptr == 0, check UNSAT => ptr never null
            Ok(ProofCondition {
                term: is_null,
                strategy: ProofStrategy::AssertAndCheckUnsat,
            })
        }
        ProofAnnotation::ValidBorrow => {
            let (_ptr, permission) = operands.two_operands("ptr", "permission")?;
            let owned = solver.try_bv_const(1, 2)?;
            let is_owned = solver.try_eq(permission, owned)?;
            let invalid = solver.try_not(is_owned)?;
            // Assert permission != Owned, check UNSAT => permission is always Owned
            Ok(ProofCondition {
                term: invalid,
                strategy: ProofStrategy::AssertAndCheckUnsat,
            })
        }
        ProofAnnotation::UniqueBorrow => {
            let (_ptr, permission) = operands.two_operands("ptr", "permission")?;
            let mutable_borrow = solver.try_bv_const(3, 2)?;
            let has_mutable_borrow = solver.try_eq(permission, mutable_borrow)?;
            // Assert permission == MutableBorrow, check UNSAT => no concurrent mutable borrows exist
            Ok(ProofCondition {
                term: has_mutable_borrow,
                strategy: ProofStrategy::AssertAndCheckUnsat,
            })
        }
        ProofAnnotation::SharedBorrow => {
            let (_ptr, permission) = operands.two_operands("ptr", "permission")?;
            let owned = solver.try_bv_const(1, 2)?;
            let shared_borrow = solver.try_bv_const(2, 2)?;
            let is_owned = solver.try_eq(permission, owned)?;
            let is_shared = solver.try_eq(permission, shared_borrow)?;
            let readable = solver.try_or(is_owned, is_shared)?;
            let not_readable = solver.try_not(readable)?;
            // Assert NOT (permission == Owned OR permission == SharedBorrow),
            // check UNSAT => permission always allows shared reads
            Ok(ProofCondition {
                term: not_readable,
                strategy: ProofStrategy::AssertAndCheckUnsat,
            })
        }
        ProofAnnotation::ValidDealloc => {
            // Pointer must be Owned (permission == 1) to deallocate.
            let (_ptr, permission) = operands.two_operands("ptr", "permission")?;
            let owned = solver.try_bv_const(1, 2)?;
            let is_owned = solver.try_eq(permission, owned)?;
            let not_owned = solver.try_not(is_owned)?;
            // Assert permission != Owned, check UNSAT => always owned when deallocating
            Ok(ProofCondition {
                term: not_owned,
                strategy: ProofStrategy::AssertAndCheckUnsat,
            })
        }
        ProofAnnotation::Pure | ProofAnnotation::Deterministic => {
            // Pure/Deterministic: given same inputs, the operation produces the
            // same output. Operands: "result1" and "result2" are two evaluations
            // of the same operation with the same symbolic inputs.
            // Condition: result1 != result2, check UNSAT => always equal.
            let (result1, result2) = operands.two_operands("result1", "result2")?;
            let eq = solver.try_eq(result1, result2)?;
            let neq = solver.try_not(eq)?;
            Ok(ProofCondition {
                term: neq,
                strategy: ProofStrategy::AssertAndCheckUnsat,
            })
        }
        ProofAnnotation::Commutative => {
            // f(a,b) == f(b,a). Operands: "result_ab" is f(a,b), "result_ba" is f(b,a).
            // Condition: result_ab != result_ba, check UNSAT => always commutative.
            let (result_ab, result_ba) = operands.two_operands("result_ab", "result_ba")?;
            let eq = solver.try_eq(result_ab, result_ba)?;
            let neq = solver.try_not(eq)?;
            Ok(ProofCondition {
                term: neq,
                strategy: ProofStrategy::AssertAndCheckUnsat,
            })
        }
        ProofAnnotation::Associative => {
            // f(f(a,b),c) == f(a,f(b,c)). Operands: "result_left" and "result_right".
            // Condition: result_left != result_right, check UNSAT => always associative.
            let (result_left, result_right) =
                operands.two_operands("result_left", "result_right")?;
            let eq = solver.try_eq(result_left, result_right)?;
            let neq = solver.try_not(eq)?;
            Ok(ProofCondition {
                term: neq,
                strategy: ProofStrategy::AssertAndCheckUnsat,
            })
        }
        ProofAnnotation::NoAlias => {
            // Two pointers must not alias (point to same address).
            // Operands: "ptr1", "ptr2".
            // Condition: ptr1 == ptr2, check UNSAT => never alias.
            let (ptr1, ptr2) = operands.two_operands("ptr1", "ptr2")?;
            let eq = solver.try_eq(ptr1, ptr2)?;
            Ok(ProofCondition {
                term: eq,
                strategy: ProofStrategy::AssertAndCheckUnsat,
            })
        }
        ProofAnnotation::Aligned(n) => {
            // Pointer is aligned to n bytes: ptr % n == 0.
            // Operands: "ptr" (64-bit pointer).
            // Condition: ptr % n != 0, check UNSAT => always aligned.
            let ptr = operands.single_operand("ptr")?;
            let align = solver.try_bv_const(*n as i64, 64)?;
            let remainder = solver.try_bvurem(ptr, align)?;
            let zero = solver.try_bv_const(0, 64)?;
            let not_aligned = solver.try_eq(remainder, zero)?;
            let not_aligned = solver.try_not(not_aligned)?;
            Ok(ProofCondition {
                term: not_aligned,
                strategy: ProofStrategy::AssertAndCheckUnsat,
            })
        }
        ProofAnnotation::NoPanic => {
            // Operation is panic-free. Operands: "safe" (boolean term that is
            // true when no panic occurs).
            // Condition: NOT safe, check UNSAT => safe always holds.
            let safe = operands.single_operand("safe")?;
            let not_safe = solver.try_not(safe)?;
            Ok(ProofCondition {
                term: not_safe,
                strategy: ProofStrategy::AssertAndCheckUnsat,
            })
        }
        ProofAnnotation::NoUndef => {
            // Value is not undef/poison. Operands: "is_defined" (boolean term
            // that is true when the value is well-defined).
            // Condition: NOT is_defined, check UNSAT => always defined.
            let is_defined = operands.single_operand("is_defined")?;
            let not_defined = solver.try_not(is_defined)?;
            Ok(ProofCondition {
                term: not_defined,
                strategy: ProofStrategy::AssertAndCheckUnsat,
            })
        }
        // These annotations require richer models (liveness, concurrency,
        // neural network bounds) beyond BV/FP and are not encodable in ay.
        other => Err(AYError::UnsupportedAnnotation(format!("{}", other))),
    }
}

/// Strategy for verifying a proof condition.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProofStrategy {
    /// Assert the term and check for UNSAT.
    /// If UNSAT, the proof obligation holds (the negation is unsatisfiable).
    AssertAndCheckUnsat,
}

/// A generated ay verification condition.
#[derive(Debug)]
pub struct ProofCondition {
    /// The ay term to assert.
    pub term: Term,
    /// How to interpret the solver result.
    pub strategy: ProofStrategy,
}

impl ProofCondition {
    /// Execute this proof condition against the given solver.
    ///
    /// Returns `Ok(true)` if the proof obligation is verified (holds).
    ///
    /// ONE SOLVER PER CALL: the term is asserted with no push/pop frame, so
    /// it stays asserted, and on `Err` ay may have left the solver corrupted.
    /// Pass a fresh solver and discard it afterwards — always on `Err` (see
    /// [`verify_and_certify`]).
    ///
    /// # Errors
    ///
    /// [`AYError::SolverError`] when ay refuses the assertion or the check —
    /// never read as "verified".
    pub fn check(&self, solver: &mut Solver) -> Result<bool, AYError> {
        solver.try_assert_term(self.term)?;
        Ok(match self.strategy {
            ProofStrategy::AssertAndCheckUnsat => solver.try_check_sat()?.is_unsat(),
        })
    }
}

/// Operands for proof obligation verification.
///
/// Different proof annotations require different operand shapes. This
/// struct provides a uniform interface for passing operands to
/// `verify_proof_obligation`.
///
/// Construct via the schema constructors [`ProofOperands::from_values`]
/// (binds IR `ValueId`s under their canonical [`ay_symbol`] names) or
/// [`ProofOperands::for_annotation`] (binds existing terms positionally to
/// the annotation's roles). The by-name constructors
/// ([`ProofOperands::single`]/[`ProofOperands::pair`]/
/// [`ProofOperands::overflow`]) are legacy thin wrappers.
#[derive(Debug)]
pub struct ProofOperands {
    /// Named operand terms.
    pub terms: Vec<(String, Term)>,
    /// Optional overflow operation (for NoOverflow/NoWrap).
    pub overflow_op: Option<OverflowOp>,
    /// Bit width of the operands (used for constant generation).
    pub width: Option<u32>,
    /// Operand-type signedness (for NoOverflow/NoWrap): the overflow
    /// predicates are signedness-specific, so the check FAILS CLOSED when
    /// this is unset for an overflow annotation (see
    /// [`encode_overflow_check`]'s false-accept note). Set via
    /// [`ProofOperands::with_signedness`].
    pub signed: Option<bool>,
}

impl ProofOperands {
    /// Positional, role-derived operand binding — the schema successor of the
    /// by-name constructors.
    ///
    /// The annotation itself defines its operand role names (via
    /// [`annotation_operand_roles`]); `terms` are attached positionally, so
    /// call sites never hand-write string keys. `NoOverflow`/`NoWrap` also
    /// need [`ProofOperands::with_overflow_op`]. Fails closed on arity
    /// mismatch and on annotations with no ay encoding.
    pub fn for_annotation(
        annotation: &ProofAnnotation,
        terms: &[Term],
        width: u32,
    ) -> Result<Self, AYError> {
        let roles = annotation_operand_roles(annotation)?;
        if roles.len() != terms.len() {
            return Err(AYError::UnsupportedAnnotation(format!(
                "{} expects {} operand(s) ({}), got {}",
                annotation,
                roles.len(),
                roles.join(", "),
                terms.len()
            )));
        }
        Ok(Self {
            terms: roles
                .iter()
                .zip(terms)
                .map(|(role, term)| (role.to_string(), *term))
                .collect(),
            overflow_op: None,
            width: Some(width),
            signed: None,
        })
    }

    /// Full schema path: declare each `(ValueId, Ty)` under its canonical
    /// [`ay_symbol`]/[`ay_sort`] binding and attach the resulting terms
    /// positionally to the annotation's roles.
    ///
    /// This is the canonical way to bind IR operands to a proof obligation:
    /// symbol names are a pure function of `(func, value)`, so the emitted
    /// formula is identical on every machine and a counterexample model maps
    /// back to source `ValueId`s via [`parse_ay_symbol`]. The operand width
    /// is taken from the first bitvector-sorted value.
    pub fn from_values(
        solver: &mut Solver,
        annotation: &ProofAnnotation,
        func: FuncId,
        values: &[(ValueId, Ty)],
    ) -> Result<Self, AYError> {
        let mut terms = Vec::with_capacity(values.len());
        let mut width = None;
        for (value, ty) in values {
            let sort = ay_sort(ty)?;
            if width.is_none()
                && let Sort::BitVec(bv) = &sort
            {
                width = Some(bv.width);
            }
            terms.push(solver.try_declare_const(&ay_symbol(func, *value), sort)?);
        }
        let width = width.ok_or_else(|| {
            AYError::UnsupportedAnnotation(format!(
                "{}: no bitvector-sorted operand to derive a width from",
                annotation
            ))
        })?;
        Self::for_annotation(annotation, &terms, width)
    }

    /// Attach the overflow operation (`NoOverflow`/`NoWrap` need it to select
    /// the ay overflow-detection primitive).
    #[must_use]
    pub fn with_overflow_op(mut self, op: OverflowOp) -> Self {
        self.overflow_op = Some(op);
        self
    }

    /// Attach the operand type's signedness (required for NoOverflow/NoWrap —
    /// the overflow predicates are signedness-specific; the check fails
    /// closed without it).
    #[must_use]
    pub fn with_signedness(mut self, signed: bool) -> Self {
        self.signed = Some(signed);
        self
    }

    /// Legacy by-name constructor for a single-term annotation (DivNonZero,
    /// NotNull). Thin back-compat wrapper: prefer
    /// [`ProofOperands::from_values`]/[`ProofOperands::for_annotation`], which
    /// derive the role name from the annotation via the symbol-binding schema
    /// instead of a hand-written string key.
    pub fn single(name: &str, term: Term, width: u32) -> Self {
        Self {
            terms: vec![(name.to_string(), term)],
            overflow_op: None,
            width: Some(width),
            signed: None,
        }
    }

    /// Legacy by-name constructor for a two-term annotation (InBounds,
    /// ShiftInRange). Thin back-compat wrapper: prefer
    /// [`ProofOperands::from_values`]/[`ProofOperands::for_annotation`] (see
    /// [`ProofOperands::single`]).
    pub fn pair(name1: &str, term1: Term, name2: &str, term2: Term, width: u32) -> Self {
        Self {
            terms: vec![(name1.to_string(), term1), (name2.to_string(), term2)],
            overflow_op: None,
            width: Some(width),
            signed: None,
        }
    }

    /// Legacy constructor for an overflow check (NoOverflow, NoWrap). Thin
    /// back-compat wrapper: prefer
    /// `ProofOperands::for_annotation(..).with_overflow_op(op)` (see
    /// [`ProofOperands::single`]).
    pub fn overflow(lhs: Term, rhs: Term, op: OverflowOp, width: u32) -> Self {
        Self {
            terms: vec![("lhs".to_string(), lhs), ("rhs".to_string(), rhs)],
            overflow_op: Some(op),
            width: Some(width),
            signed: None,
        }
    }

    fn single_operand(&self, name: &str) -> Result<Term, AYError> {
        self.terms
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, t)| *t)
            .ok_or_else(|| AYError::UnsupportedAnnotation(format!("missing operand: {}", name)))
    }

    fn two_operands(&self, name1: &str, name2: &str) -> Result<(Term, Term), AYError> {
        let a = self.single_operand(name1)?;
        let b = self.single_operand(name2)?;
        Ok((a, b))
    }

    fn overflow_operands(&self) -> Result<(Term, Term, &OverflowOp), AYError> {
        let lhs = self.single_operand("lhs")?;
        let rhs = self.single_operand("rhs")?;
        let op = self
            .overflow_op
            .as_ref()
            .ok_or_else(|| AYError::UnsupportedAnnotation("missing overflow_op".to_string()))?;
        Ok((lhs, rhs, op))
    }

    fn bit_width(&self) -> Result<u32, AYError> {
        self.width
            .ok_or_else(|| AYError::UnsupportedAnnotation("missing bit width".to_string()))
    }
}

/// End-to-end overflow verification demo.
///
/// Creates a QF_BV solver, declares two symbolic 32-bit bitvectors,
/// asserts that overflow is impossible, and checks satisfiability.
/// Returns `true` if the addition of any two 32-bit values can overflow
/// (which it obviously can, so this should return `true`).
pub fn verify_no_overflow() -> Result<bool, AYError> {
    let mut solver = create_bv_solver()?;
    let sort = Sort::BitVec(BitVecSort { width: 32 });
    let a = solver.try_declare_const("a", sort.clone())?;
    let b = solver.try_declare_const("b", sort)?;

    let safe = encode_overflow_check(&mut solver, OverflowOp::AddOverflow, true, a, b)?;
    let not_safe = solver.try_not(safe)?;
    solver.try_assert_term(not_safe)?;

    // If SAT, there exist values a,b where addition overflows
    Ok(solver.try_check_sat()?.is_sat())
}

#[cfg(test)]
mod tests {
    #![allow(clippy::disallowed_methods)] // tests drive ay directly (r11 item 5)

    use super::*;

    // ---- ty_to_sort tests ----

    /// r11 review L8 (FAILING-FIRST in the debug test profile: the surface
    /// is unchanged). `trunc` / narrowing `ptrtoint` to width 0 computed
    /// `dst_width - 1`, an arithmetic-overflow panic in debug. Both are now a
    /// named refusal.
    #[test]
    fn a_cast_to_a_zero_width_integer_is_refused_not_underflowed() {
        let mut solver = create_bv_solver().expect("solver");
        let x = solver
            .try_declare_const("x", Sort::BitVec(BitVecSort { width: 64 }))
            .expect("declare");
        for (op, src) in [(CastOp::Trunc, 64), (CastOp::PtrToInt, 64)] {
            let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                encode_cast(&mut solver, op, x, src, 0)
            }))
            .expect("a zero-width cast must not underflow");
            assert!(
                matches!(&outcome, Err(AYError::UnsupportedOp(message))
                    if message.contains("zero-width")),
                "{op:?}: {outcome:?}"
            );
        }
    }

    /// r11 review M1. ay's `term_sort` PANICS (`require_term`) on a handle
    /// this solver did not issue; its total twin `try_term_sort` exists from
    /// AY `1128b49f2` on (pinned: `8e7b3fe6b`). The width
    /// query behind `rotl`/`rotr`/`ctlz`/`cttz`/`bswap`/`bitreverse` called
    /// it unguarded, so a public `encode_binop` / `encode_unop` caller holding
    /// another solver's term panicked inside ay. The query now calls ay's
    /// total twin `try_term_sort`, whose refusal is a typed
    /// `InvalidTermHandle`. Mutation check: calling the panicking `term_sort`
    /// instead turns this test red (the panic is caught and the `expect`
    /// fails).
    #[test]
    fn a_foreign_term_handle_is_refused_by_the_width_query_not_panicked() {
        let mut minting = create_bv_solver().expect("solver");
        let foreign = minting
            .try_declare_const("x", Sort::BitVec(BitVecSort { width: 8 }))
            .expect("declare");
        let mut other = create_bv_solver().expect("solver");
        let refused = |outcome: std::thread::Result<Result<Term, AYError>>| {
            let outcome = outcome.expect("a foreign handle must not panic inside ay");
            assert!(
                matches!(&outcome, Err(AYError::SolverError(message))
                    if message.contains("invalid term handle in term_sort")),
                "{outcome:?}"
            );
        };
        for op in [
            UnOp::CtPop,
            UnOp::CtLz,
            UnOp::CtTz,
            UnOp::BSwap,
            UnOp::BitReverse,
        ] {
            refused(std::panic::catch_unwind(std::panic::AssertUnwindSafe(
                || encode_unop(&mut other, op, foreign),
            )));
        }
        for op in [BinOp::RotL, BinOp::RotR] {
            refused(std::panic::catch_unwind(std::panic::AssertUnwindSafe(
                || encode_binop(&mut other, op, foreign, foreign),
            )));
        }
    }

    #[test]
    fn ty_to_sort_integers() {
        let cases = [
            (Ty::I8, 8),
            (Ty::I16, 16),
            (Ty::I32, 32),
            (Ty::I64, 64),
            (Ty::I128, 128),
        ];
        for (ty, expected_width) in &cases {
            let sort = ty_to_sort(ty).unwrap();
            match sort {
                Sort::BitVec(bv) => {
                    assert_eq!(bv.width, *expected_width, "width mismatch for {:?}", ty)
                }
                other => panic!("expected BitVec sort for {:?}, got {:?}", ty, other),
            }
        }
    }

    #[test]
    fn ty_to_sort_bool() {
        let sort = ty_to_sort(&Ty::Bool).unwrap();
        match sort {
            Sort::BitVec(bv) => assert_eq!(bv.width, 1),
            other => panic!("expected BitVec(1), got {:?}", other),
        }
    }

    #[test]
    fn ty_to_sort_ptr() {
        let sort = ty_to_sort(&Ty::Ptr).unwrap();
        match sort {
            Sort::BitVec(bv) => assert_eq!(bv.width, 64),
            other => panic!("expected BitVec(64), got {:?}", other),
        }
    }

    #[test]
    fn ty_to_sort_floats() {
        let f16_sort = ty_to_sort(&Ty::F16).unwrap();
        assert_eq!(f16_sort, Sort::FloatingPoint(5, 11));
        let f32_sort = ty_to_sort(&Ty::F32).unwrap();
        assert_eq!(f32_sort, Sort::FloatingPoint(8, 24));
        let f64_sort = ty_to_sort(&Ty::F64).unwrap();
        assert_eq!(f64_sort, Sort::FloatingPoint(11, 53));
    }

    #[test]
    fn ty_to_sort_unsupported() {
        // Never and Func remain unsupported
        assert!(ty_to_sort(&Ty::Never).is_err());
        assert!(ty_to_sort(&Ty::Func(trust_ir::value::FuncTyId::new(0))).is_err());
    }

    // ---- create_bv_solver ----

    #[test]
    fn create_bv_solver_succeeds() {
        let solver = create_bv_solver();
        assert!(solver.is_ok());
    }

    // ---- encode_binop tests ----

    #[test]
    fn encode_binop_add() {
        let mut solver = create_bv_solver().unwrap();
        let sort = Sort::BitVec(BitVecSort { width: 32 });
        let a = solver.declare_const("a", sort.clone());
        let b = solver.declare_const("b", sort);
        let result = encode_binop(&mut solver, BinOp::Add, a, b);
        assert!(result.is_ok());
    }

    #[test]
    fn encode_binop_all_integer_variants() {
        let mut solver = create_bv_solver().unwrap();
        let sort = Sort::BitVec(BitVecSort { width: 32 });
        let a = solver.declare_const("a", sort.clone());
        let b = solver.declare_const("b", sort);

        let integer_ops = [
            BinOp::Add,
            BinOp::Sub,
            BinOp::Mul,
            BinOp::UDiv,
            BinOp::SDiv,
            BinOp::URem,
            BinOp::SRem,
            BinOp::And,
            BinOp::Or,
            BinOp::Xor,
            BinOp::Shl,
            BinOp::LShr,
            BinOp::AShr,
        ];
        for op in &integer_ops {
            let result = encode_binop(&mut solver, *op, a, b);
            assert!(result.is_ok(), "encode_binop failed for {:?}", op);
        }
    }

    /// Which float ops BUILD a term at f32. Building is not correctness:
    /// `FRem` once built a term (bare `fp.rem`, the IEEE remainder) that
    /// computed the wrong function (TRUST-IR-AY-FREM-1). Its value is pinned
    /// to the interpreter by `tests/frem_fmod.rs`; this test only checks
    /// that the exact `fmod` encoding stays well-sorted.
    #[test]
    fn encode_binop_float_ops() {
        let mut solver = create_fp_solver().unwrap();
        let sort = Sort::FloatingPoint(8, 24); // f32
        let a = solver.declare_const("a", sort.clone());
        let b = solver.declare_const("b", sort);

        let float_ops = [
            BinOp::FAdd,
            BinOp::FSub,
            BinOp::FMul,
            BinOp::FDiv,
            BinOp::FRem,
        ];
        for op in &float_ops {
            let result = encode_binop(&mut solver, *op, a, b);
            assert!(result.is_ok(), "encode_binop failed for float op {:?}", op);
        }
    }

    #[test]
    fn encode_binop_add_concrete_check() {
        // Verify: 3 + 5 == 8
        let mut solver = create_bv_solver().unwrap();
        let three = solver.bv_const(3, 32);
        let five = solver.bv_const(5, 32);
        let sum = encode_binop(&mut solver, BinOp::Add, three, five).unwrap();
        let eight = solver.bv_const(8, 32);
        let eq = solver.eq(sum, eight);
        solver.assert_term(eq);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn encode_binop_sub_concrete_check() {
        // Verify: 10 - 3 == 7
        let mut solver = create_bv_solver().unwrap();
        let ten = solver.bv_const(10, 32);
        let three = solver.bv_const(3, 32);
        let diff = encode_binop(&mut solver, BinOp::Sub, ten, three).unwrap();
        let seven = solver.bv_const(7, 32);
        let eq = solver.eq(diff, seven);
        solver.assert_term(eq);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn encode_binop_and_concrete_check() {
        // Verify: 0xFF & 0x0F == 0x0F
        let mut solver = create_bv_solver().unwrap();
        let ff = solver.bv_const(0xFF, 8);
        let f0 = solver.bv_const(0x0F, 8);
        let result = encode_binop(&mut solver, BinOp::And, ff, f0).unwrap();
        let expected = solver.bv_const(0x0F, 8);
        let eq = solver.eq(result, expected);
        solver.assert_term(eq);
        assert!(solver.check_sat().is_sat());
    }

    // ---- encode_icmp tests ----

    #[test]
    fn encode_icmp_eq_true() {
        let mut solver = create_bv_solver().unwrap();
        let five = solver.bv_const(5, 32);
        let also_five = solver.bv_const(5, 32);
        let result =
            encode_icmp(&mut solver, ICmpOp::Eq, five, also_five).expect("the adapter encodes");
        solver.assert_term(result);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn encode_icmp_eq_false() {
        let mut solver = create_bv_solver().unwrap();
        let five = solver.bv_const(5, 32);
        let six = solver.bv_const(6, 32);
        let result = encode_icmp(&mut solver, ICmpOp::Eq, five, six).expect("the adapter encodes");
        solver.assert_term(result);
        assert!(solver.check_sat().is_unsat());
    }

    #[test]
    fn encode_icmp_ne() {
        let mut solver = create_bv_solver().unwrap();
        let five = solver.bv_const(5, 32);
        let six = solver.bv_const(6, 32);
        let result = encode_icmp(&mut solver, ICmpOp::Ne, five, six).expect("the adapter encodes");
        solver.assert_term(result);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn encode_icmp_ult() {
        // 5 < 10 unsigned
        let mut solver = create_bv_solver().unwrap();
        let five = solver.bv_const(5, 32);
        let ten = solver.bv_const(10, 32);
        let result = encode_icmp(&mut solver, ICmpOp::Ult, five, ten).expect("the adapter encodes");
        solver.assert_term(result);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn encode_icmp_slt_negative() {
        // -1 < 0 signed (0xFFFFFFFF < 0 in signed interpretation)
        let mut solver = create_bv_solver().unwrap();
        let neg_one = solver.bv_const(-1, 32);
        let zero = solver.bv_const(0, 32);
        let result =
            encode_icmp(&mut solver, ICmpOp::Slt, neg_one, zero).expect("the adapter encodes");
        solver.assert_term(result);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn encode_icmp_ult_negative_is_larger() {
        // -1 (0xFFFFFFFF) is NOT < 0 unsigned
        let mut solver = create_bv_solver().unwrap();
        let neg_one = solver.bv_const(-1, 32);
        let zero = solver.bv_const(0, 32);
        let result =
            encode_icmp(&mut solver, ICmpOp::Ult, neg_one, zero).expect("the adapter encodes");
        solver.assert_term(result);
        assert!(solver.check_sat().is_unsat());
    }

    #[test]
    fn encode_icmp_all_variants_construct() {
        let mut solver = create_bv_solver().unwrap();
        let sort = Sort::BitVec(BitVecSort { width: 32 });
        let a = solver.declare_const("a", sort.clone());
        let b = solver.declare_const("b", sort);

        let ops = [
            ICmpOp::Eq,
            ICmpOp::Ne,
            ICmpOp::Ult,
            ICmpOp::Ule,
            ICmpOp::Ugt,
            ICmpOp::Uge,
            ICmpOp::Slt,
            ICmpOp::Sle,
            ICmpOp::Sgt,
            ICmpOp::Sge,
        ];
        for op in &ops {
            let _result = encode_icmp(&mut solver, *op, a, b).expect("the adapter encodes");
            // Just verifying construction does not panic
        }
    }

    #[test]
    fn encode_icmp_ule_boundary() {
        // 5 <= 5
        let mut solver = create_bv_solver().unwrap();
        let five = solver.bv_const(5, 32);
        let also_five = solver.bv_const(5, 32);
        let result =
            encode_icmp(&mut solver, ICmpOp::Ule, five, also_five).expect("the adapter encodes");
        solver.assert_term(result);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn encode_icmp_ugt() {
        // 10 > 5 unsigned
        let mut solver = create_bv_solver().unwrap();
        let ten = solver.bv_const(10, 32);
        let five = solver.bv_const(5, 32);
        let result = encode_icmp(&mut solver, ICmpOp::Ugt, ten, five).expect("the adapter encodes");
        solver.assert_term(result);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn encode_icmp_sge() {
        // 0 >= -1 signed
        let mut solver = create_bv_solver().unwrap();
        let zero = solver.bv_const(0, 32);
        let neg_one = solver.bv_const(-1, 32);
        let result =
            encode_icmp(&mut solver, ICmpOp::Sge, zero, neg_one).expect("the adapter encodes");
        solver.assert_term(result);
        assert!(solver.check_sat().is_sat());
    }

    // ---- encode_unop tests ----

    #[test]
    fn encode_unop_not() {
        // NOT 0 == 0xFFFFFFFF for 32-bit
        let mut solver = create_bv_solver().unwrap();
        let zero = solver.bv_const(0, 32);
        let result = encode_unop(&mut solver, UnOp::Not, zero).unwrap();
        let all_ones = solver.bv_const(-1, 32);
        let eq = solver.eq(result, all_ones);
        solver.assert_term(eq);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn encode_unop_neg() {
        // NEG 5 == -5 (two's complement)
        let mut solver = create_bv_solver().unwrap();
        let five = solver.bv_const(5, 32);
        let result = encode_unop(&mut solver, UnOp::Neg, five).unwrap();
        let neg_five = solver.bv_const(-5, 32);
        let eq = solver.eq(result, neg_five);
        solver.assert_term(eq);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn encode_unop_fneg() {
        let mut solver = create_fp_solver().unwrap();
        let sort = Sort::FloatingPoint(11, 53); // f64
        let a = solver.declare_const("a", sort);
        let result = encode_unop(&mut solver, UnOp::FNeg, a);
        assert!(result.is_ok(), "FNeg should be supported");
    }

    #[test]
    fn encode_unop_ctpop_matches_rust_across_widths() {
        for width in [1, 2, 3, 7, 8, 16, 32, 64, 128] {
            let mask = if width == 128 {
                u128::MAX
            } else {
                (1u128 << width) - 1
            };
            let mut samples = vec![0, 1, mask, 1u128 << (width - 1), mask >> 1];
            if width == 8 {
                samples.extend(0..=255);
            }
            let mut seed = 0x7ac1_1905_b9e2_04d7u128;
            for _ in 0..16 {
                seed = seed
                    .wrapping_mul(0x01ed_8e91_513f_82a7_6d4c_308e_932b_66d5)
                    .wrapping_add(1);
                samples.push(seed & mask);
            }
            for raw in samples {
                let mut solver = create_bv_solver().unwrap();
                let x = solver.declare_const("x", Sort::BitVec(BitVecSort { width }));
                let hi = solver.bv_const_u64((raw >> 64) as u64, 64);
                let lo = solver.bv_const_u64(raw as u64, 64);
                let wide = solver.bvconcat(hi, lo);
                let value = solver.bvextract(wide, width - 1, 0);
                let pin = solver.eq(x, value);
                solver.assert_term(pin);
                let count = encode_unop(&mut solver, UnOp::CtPop, x).unwrap();
                assert_eq!(
                    solver.try_term_sort(count).unwrap().bitvec_width(),
                    Some(width)
                );
                let expected = solver.bv_const_u64(u64::from(raw.count_ones()), width);
                let equal = solver.eq(count, expected);
                let wrong = solver.not(equal);
                solver.assert_term(wrong);
                assert!(solver.check_sat().is_unsat(), "popcount{width}({raw:#x})");
            }
        }
    }

    #[test]
    fn encode_unop_ctpop_rejects_non_bitvectors() {
        for sort in [Sort::FloatingPoint(8, 24), Sort::Bool] {
            let mut solver = create_fp_solver().unwrap();
            let x = solver.declare_const("x", sort);
            assert!(matches!(encode_unop(&mut solver, UnOp::CtPop, x),
                Err(AYError::UnsupportedOp(message)) if message.contains("not a bit-vector")));
        }
    }

    // WS3.20 (F-057): the bit intrinsics against concrete Rust values. Each
    // asserts the encoding is UNSAT-distinct from the wrong answer: the term
    // must EQUAL the value `u32::leading_zeros` & co. compute, on a symbolic
    // operand pinned to the sample by an equality assertion.
    fn assert_bv_op_equals(
        op_name: &str,
        build: impl Fn(&mut Solver, Term) -> Term,
        x: u32,
        want: u32,
    ) {
        let mut solver = create_bv_solver().unwrap();
        let sort = Sort::BitVec(BitVecSort { width: 32 });
        let sym = solver.declare_const("x", sort);
        let xv = solver.bv_const_u64(u64::from(x), 32);
        let pin = solver.eq(sym, xv);
        solver.assert_term(pin);
        let got = build(&mut solver, sym);
        let wantv = solver.bv_const_u64(u64::from(want), 32);
        let eq = solver.eq(got, wantv);
        let ne = solver.not(eq);
        solver.assert_term(ne);
        assert!(
            solver.check_sat().is_unsat(),
            "{op_name}({x:#x}) must encode to exactly {want:#x}"
        );
    }

    #[test]
    fn encode_unop_ctlz_cttz_match_rust() {
        for x in [0u32, 1, 0x8000_0000, 0x1234_5678, u32::MAX, 0x0000_0100] {
            assert_bv_op_equals(
                "ctlz",
                |s, t| encode_unop(s, UnOp::CtLz, t).unwrap(),
                x,
                x.leading_zeros(),
            );
            assert_bv_op_equals(
                "cttz",
                |s, t| encode_unop(s, UnOp::CtTz, t).unwrap(),
                x,
                x.trailing_zeros(),
            );
        }
    }

    #[test]
    fn encode_unop_bswap_bitreverse_match_rust() {
        for x in [0u32, 1, 0x8000_0000, 0x1234_5678, u32::MAX, 0xDEAD_BEEF] {
            assert_bv_op_equals(
                "bswap",
                |s, t| encode_unop(s, UnOp::BSwap, t).unwrap(),
                x,
                x.swap_bytes(),
            );
            assert_bv_op_equals(
                "bitreverse",
                |s, t| encode_unop(s, UnOp::BitReverse, t).unwrap(),
                x,
                x.reverse_bits(),
            );
        }
    }

    #[test]
    fn encode_binop_rotates_match_rust_modulo_width() {
        for (x, n) in [
            (0x1234_5678u32, 0u32),
            (0x1234_5678, 8),
            (0x1234_5678, 40),
            (1, 31),
            (u32::MAX, 13),
        ] {
            assert_bv_op_equals(
                "rotl",
                |s, t| {
                    let amount = s.bv_const_u64(u64::from(n), 32);
                    encode_binop(s, BinOp::RotL, t, amount).unwrap()
                },
                x,
                x.rotate_left(n),
            );
            assert_bv_op_equals(
                "rotr",
                |s, t| {
                    let amount = s.bv_const_u64(u64::from(n), 32);
                    encode_binop(s, BinOp::RotR, t, amount).unwrap()
                },
                x,
                x.rotate_right(n),
            );
        }
    }

    #[test]
    fn encode_binop_fcopysign_unsupported_by_name() {
        let mut solver = create_fp_solver().unwrap();
        let sort = Sort::FloatingPoint(11, 53);
        let a = solver.declare_const("a", sort.clone());
        let b = solver.declare_const("b", sort);
        let result = encode_binop(&mut solver, BinOp::FCopySign, a, b);
        assert!(matches!(result, Err(AYError::UnsupportedOp(op)) if op == "fcopysign"));
    }

    #[test]
    fn encode_unop_not_involution() {
        // NOT(NOT(x)) == x
        let mut solver = create_bv_solver().unwrap();
        let sort = Sort::BitVec(BitVecSort { width: 32 });
        let x = solver.declare_const("x", sort);
        let not_x = encode_unop(&mut solver, UnOp::Not, x).unwrap();
        let not_not_x = encode_unop(&mut solver, UnOp::Not, not_x).unwrap();
        // Assert NOT(NOT(x)) != x, check UNSAT => involution holds
        let neq = solver.eq(not_not_x, x);
        let neg = solver.not(neq);
        solver.assert_term(neg);
        assert!(solver.check_sat().is_unsat());
    }

    #[test]
    fn encode_unop_neg_involution() {
        // NEG(NEG(x)) == x for all x
        let mut solver = create_bv_solver().unwrap();
        let sort = Sort::BitVec(BitVecSort { width: 32 });
        let x = solver.declare_const("x", sort);
        let neg_x = encode_unop(&mut solver, UnOp::Neg, x).unwrap();
        let neg_neg_x = encode_unop(&mut solver, UnOp::Neg, neg_x).unwrap();
        let neq = solver.eq(neg_neg_x, x);
        let neg = solver.not(neq);
        solver.assert_term(neg);
        assert!(solver.check_sat().is_unsat());
    }

    // ---- encode_cast tests ----

    #[test]
    fn encode_cast_trunc_32_to_16() {
        let mut solver = create_bv_solver().unwrap();
        // 0x0000ABCD truncated to 16 bits = 0xABCD
        let val = solver.bv_const(0x0000ABCD, 32);
        let truncated = encode_cast(&mut solver, CastOp::Trunc, val, 32, 16).unwrap();
        let expected = solver.bv_const(0xABCDu64 as i64, 16);
        let eq = solver.eq(truncated, expected);
        solver.assert_term(eq);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn encode_cast_zext_16_to_32() {
        let mut solver = create_bv_solver().unwrap();
        // 0xFFFF zero-extended to 32 bits = 0x0000FFFF
        let val = solver.bv_const(0xFFFFu64 as i64, 16);
        let extended = encode_cast(&mut solver, CastOp::ZExt, val, 16, 32).unwrap();
        let expected = solver.bv_const(0x0000FFFF, 32);
        let eq = solver.eq(extended, expected);
        solver.assert_term(eq);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn encode_cast_sext_16_to_32() {
        let mut solver = create_bv_solver().unwrap();
        // 0xFFFF (-1 in 16-bit signed) sign-extended to 32 bits = 0xFFFFFFFF (-1)
        let val = solver.bv_const(-1, 16);
        let extended = encode_cast(&mut solver, CastOp::SExt, val, 16, 32).unwrap();
        let expected = solver.bv_const(-1, 32);
        let eq = solver.eq(extended, expected);
        solver.assert_term(eq);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn encode_cast_sext_positive_value() {
        let mut solver = create_bv_solver().unwrap();
        // 0x007F (127 in 16-bit signed) sign-extended to 32 bits = 0x0000007F
        let val = solver.bv_const(127, 16);
        let extended = encode_cast(&mut solver, CastOp::SExt, val, 16, 32).unwrap();
        let expected = solver.bv_const(127, 32);
        let eq = solver.eq(extended, expected);
        solver.assert_term(eq);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn encode_cast_trunc_invalid_widths() {
        let mut solver = create_bv_solver().unwrap();
        let val = solver.bv_const(0, 16);
        // Trunc requires dst < src
        assert!(encode_cast(&mut solver, CastOp::Trunc, val, 16, 32).is_err());
        assert!(encode_cast(&mut solver, CastOp::Trunc, val, 16, 16).is_err());
    }

    #[test]
    fn encode_cast_zext_invalid_widths() {
        let mut solver = create_bv_solver().unwrap();
        let val = solver.bv_const(0, 32);
        // ZExt requires dst > src
        assert!(encode_cast(&mut solver, CastOp::ZExt, val, 32, 16).is_err());
        assert!(encode_cast(&mut solver, CastOp::ZExt, val, 32, 32).is_err());
    }

    // ---- PtrToInt / IntToPtr / Bitcast cast tests ----

    #[test]
    fn encode_cast_ptrtoint_same_width() {
        // PtrToInt with 64-bit pointer to 64-bit integer = identity
        let mut solver = create_bv_solver().unwrap();
        let ptr = solver.bv_const(0x1000, 64);
        let result = encode_cast(&mut solver, CastOp::PtrToInt, ptr, 64, 64).unwrap();
        let eq = solver.eq(result, ptr);
        solver.assert_term(eq);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn encode_cast_ptrtoint_narrowing() {
        // PtrToInt 64-bit pointer to 32-bit integer = truncation
        let mut solver = create_bv_solver().unwrap();
        let ptr = solver.bv_const(0x0000ABCD, 64);
        let result = encode_cast(&mut solver, CastOp::PtrToInt, ptr, 64, 32).unwrap();
        let expected = solver.bv_const(0xABCD, 32);
        let eq = solver.eq(result, expected);
        solver.assert_term(eq);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn encode_cast_ptrtoint_widening() {
        // PtrToInt 64-bit pointer to 128-bit integer = zero-extend
        let mut solver = create_bv_solver().unwrap();
        let ptr = solver.bv_const(0x1000, 64);
        let result = encode_cast(&mut solver, CastOp::PtrToInt, ptr, 64, 128).unwrap();
        // High 64 bits should be zero
        let high = solver.bvextract(result, 127, 64);
        let zero64 = solver.bv_const(0, 64);
        let eq = solver.eq(high, zero64);
        solver.assert_term(eq);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn encode_cast_inttoptr_same_width() {
        // IntToPtr with 64-bit integer = identity
        let mut solver = create_bv_solver().unwrap();
        let val = solver.bv_const(0x2000, 64);
        let result = encode_cast(&mut solver, CastOp::IntToPtr, val, 64, 64).unwrap();
        let eq = solver.eq(result, val);
        solver.assert_term(eq);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn encode_cast_inttoptr_widening() {
        // IntToPtr with 32-bit integer to 64-bit pointer = zero-extend
        let mut solver = create_bv_solver().unwrap();
        let val = solver.bv_const(0x1234, 32);
        let result = encode_cast(&mut solver, CastOp::IntToPtr, val, 32, 64).unwrap();
        let expected = solver.bv_const(0x1234, 64);
        let eq = solver.eq(result, expected);
        solver.assert_term(eq);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn encode_cast_inttoptr_narrowing() {
        // IntToPtr with 128-bit integer to 64-bit pointer = truncation
        let mut solver = create_bv_solver().unwrap();
        let sort = Sort::BitVec(BitVecSort { width: 128 });
        let val = solver.declare_const("val128", sort);
        let result = encode_cast(&mut solver, CastOp::IntToPtr, val, 128, 64);
        assert!(result.is_ok());
    }

    #[test]
    fn encode_cast_bitcast_same_width() {
        // Bitcast 32-bit to 32-bit = identity
        let mut solver = create_bv_solver().unwrap();
        let val = solver.bv_const(0x12345678, 32);
        let result = encode_cast(&mut solver, CastOp::Bitcast, val, 32, 32).unwrap();
        let eq = solver.eq(result, val);
        solver.assert_term(eq);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn encode_cast_bitcast_width_mismatch_fails() {
        // Bitcast with different widths should fail
        let mut solver = create_bv_solver().unwrap();
        let val = solver.bv_const(0, 32);
        assert!(encode_cast(&mut solver, CastOp::Bitcast, val, 32, 64).is_err());
    }

    #[test]
    fn bv_carrier_bitcast_requires_the_declared_width() {
        let mut solver = create_fp_solver().unwrap();
        let nan = solver
            .try_fp_const_from_bits(f64::NAN.to_bits(), 11, 53)
            .unwrap();
        assert!(matches!(
            encode_cast(&mut solver, CastOp::Bitcast, nan, 64, 64),
            Err(AYError::UnsupportedOp(_))
        ));
        let narrow = solver.try_bv_const(7, 16).unwrap();
        assert!(matches!(
            encode_cast(&mut solver, CastOp::Bitcast, narrow, 64, 64),
            Err(AYError::UnsupportedOp(_))
        ));
    }

    #[test]
    fn bv_carrier_integer_equality_requires_bitvectors() {
        let mut solver = create_fp_solver().unwrap();
        let nan = solver
            .try_fp_const_from_bits(f64::NAN.to_bits(), 11, 53)
            .unwrap();
        for op in [ICmpOp::Eq, ICmpOp::Ne] {
            assert!(matches!(
                encode_icmp(&mut solver, op, nan, nan),
                Err(AYError::UnsupportedOp(_))
            ));
        }
    }

    #[test]
    fn encode_cast_trunc_8_to_1() {
        // Truncate 8-bit value to 1-bit (boolean)
        let mut solver = create_bv_solver().unwrap();
        let val = solver.bv_const(0b10101011, 8);
        let truncated = encode_cast(&mut solver, CastOp::Trunc, val, 8, 1).unwrap();
        let one = solver.bv_const(1, 1);
        let eq = solver.eq(truncated, one);
        solver.assert_term(eq);
        assert!(solver.check_sat().is_sat());
    }

    // ---- encode_overflow_check tests ----

    #[test]
    fn encode_overflow_check_add_safe() {
        // 1 + 1 does not overflow in 32-bit signed
        let mut solver = create_bv_solver().unwrap();
        let one = solver.bv_const(1, 32);
        let also_one = solver.bv_const(1, 32);
        let safe = encode_overflow_check(&mut solver, OverflowOp::AddOverflow, true, one, also_one)
            .expect("the adapter encodes");
        solver.assert_term(safe);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn encode_overflow_check_add_overflows() {
        // INT_MAX + 1 overflows in 32-bit signed
        let mut solver = create_bv_solver().unwrap();
        let max = solver.bv_const(i32::MAX as i64, 32);
        let one = solver.bv_const(1, 32);
        let safe = encode_overflow_check(&mut solver, OverflowOp::AddOverflow, true, max, one)
            .expect("the adapter encodes");
        // Safe should be false (overflow occurs)
        let not_safe = solver.not(safe);
        solver.assert_term(not_safe);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn encode_overflow_check_sub() {
        // INT_MIN - 1 overflows (underflows) in 32-bit signed
        let mut solver = create_bv_solver().unwrap();
        let min = solver.bv_const(i32::MIN as i64, 32);
        let one = solver.bv_const(1, 32);
        let safe = encode_overflow_check(&mut solver, OverflowOp::SubOverflow, true, min, one)
            .expect("the adapter encodes");
        let not_safe = solver.not(safe);
        solver.assert_term(not_safe);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn encode_overflow_check_mul_safe() {
        // 2 * 3 does not overflow
        let mut solver = create_bv_solver().unwrap();
        let two = solver.bv_const(2, 32);
        let three = solver.bv_const(3, 32);
        let safe = encode_overflow_check(&mut solver, OverflowOp::MulOverflow, true, two, three)
            .expect("the adapter encodes");
        solver.assert_term(safe);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn encode_overflow_check_mul_overflows() {
        // INT_MAX * 2 overflows
        let mut solver = create_bv_solver().unwrap();
        let max = solver.bv_const(i32::MAX as i64, 32);
        let two = solver.bv_const(2, 32);
        let safe = encode_overflow_check(&mut solver, OverflowOp::MulOverflow, true, max, two)
            .expect("the adapter encodes");
        let not_safe = solver.not(safe);
        solver.assert_term(not_safe);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn encode_overflow_check_add_symbolic() {
        // For arbitrary 32-bit values, addition CAN overflow
        let mut solver = create_bv_solver().unwrap();
        let sort = Sort::BitVec(BitVecSort { width: 32 });
        let a = solver.declare_const("a", sort.clone());
        let b = solver.declare_const("b", sort);
        let safe = encode_overflow_check(&mut solver, OverflowOp::AddOverflow, true, a, b)
            .expect("the adapter encodes");
        let not_safe = solver.not(safe);
        solver.assert_term(not_safe);
        // Should be SAT: there exist a,b that overflow
        assert!(solver.check_sat().is_sat());
    }

    // ---- verify_proof_obligation tests ----

    #[test]
    fn verify_proof_no_overflow_fails_for_symbolic() {
        // Symbolic values can overflow => proof should NOT verify
        let mut solver = create_bv_solver().unwrap();
        let sort = Sort::BitVec(BitVecSort { width: 32 });
        let a = solver.declare_const("a", sort.clone());
        let b = solver.declare_const("b", sort);
        let operands = ProofOperands::for_annotation(&ProofAnnotation::NoOverflow, &[a, b], 32)
            .unwrap()
            .with_overflow_op(OverflowOp::AddOverflow)
            .with_signedness(true);
        let cond =
            verify_proof_obligation(&mut solver, &ProofAnnotation::NoOverflow, &operands).unwrap();
        // Should NOT verify (is_sat => UNSAT fails => obligation does not hold universally)
        assert!(!cond.check(&mut solver).expect("the condition checks"));
    }

    #[test]
    fn verify_proof_no_overflow_missing_signedness_fails_closed() {
        // The overflow predicates are signedness-specific; omitting the
        // operand type's signedness must be an ERROR, never a silent
        // signed default (the unsigned-sub false-accept).
        let mut solver = create_bv_solver().unwrap();
        let sort = Sort::BitVec(BitVecSort { width: 32 });
        let a = solver.declare_const("a", sort.clone());
        let b = solver.declare_const("b", sort);
        let operands = ProofOperands::for_annotation(&ProofAnnotation::NoOverflow, &[a, b], 32)
            .unwrap()
            .with_overflow_op(OverflowOp::AddOverflow);
        assert!(
            verify_proof_obligation(&mut solver, &ProofAnnotation::NoOverflow, &operands).is_err(),
            "missing signedness must fail closed"
        );
    }

    #[test]
    fn verify_proof_div_nonzero_constant() {
        // divisor = 5, which is nonzero => proof should verify
        let mut solver = create_bv_solver().unwrap();
        let five = solver.bv_const(5, 32);
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::DivNonZero, &[five], 32).unwrap();
        let cond =
            verify_proof_obligation(&mut solver, &ProofAnnotation::DivNonZero, &operands).unwrap();
        assert!(cond.check(&mut solver).expect("the condition checks"));
    }

    #[test]
    fn verify_proof_div_nonzero_symbolic_fails() {
        // symbolic divisor can be zero => proof should not verify
        let mut solver = create_bv_solver().unwrap();
        let sort = Sort::BitVec(BitVecSort { width: 32 });
        let d = solver.declare_const("d", sort);
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::DivNonZero, &[d], 32).unwrap();
        let cond =
            verify_proof_obligation(&mut solver, &ProofAnnotation::DivNonZero, &operands).unwrap();
        assert!(!cond.check(&mut solver).expect("the condition checks"));
    }

    #[test]
    fn verify_proof_shift_in_range_constant() {
        // shift_amount = 5, bit_width = 32 => in range
        let mut solver = create_bv_solver().unwrap();
        let shift = solver.bv_const(5, 32);
        let width = solver.bv_const(32, 32);
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::ShiftInRange, &[shift, width], 32)
                .unwrap();
        let cond = verify_proof_obligation(&mut solver, &ProofAnnotation::ShiftInRange, &operands)
            .unwrap();
        assert!(cond.check(&mut solver).expect("the condition checks"));
    }

    #[test]
    fn verify_proof_shift_in_range_out_of_range() {
        // shift_amount = 32, bit_width = 32 => out of range (32 >= 32)
        let mut solver = create_bv_solver().unwrap();
        let shift = solver.bv_const(32, 32);
        let width = solver.bv_const(32, 32);
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::ShiftInRange, &[shift, width], 32)
                .unwrap();
        let cond = verify_proof_obligation(&mut solver, &ProofAnnotation::ShiftInRange, &operands)
            .unwrap();
        assert!(!cond.check(&mut solver).expect("the condition checks"));
    }

    #[test]
    fn verify_proof_in_bounds_constant() {
        // index = 3, length = 10 => in bounds
        let mut solver = create_bv_solver().unwrap();
        let index = solver.bv_const(3, 32);
        let length = solver.bv_const(10, 32);
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::InBounds, &[index, length], 32)
                .unwrap();
        let cond =
            verify_proof_obligation(&mut solver, &ProofAnnotation::InBounds, &operands).unwrap();
        assert!(cond.check(&mut solver).expect("the condition checks"));
    }

    #[test]
    fn verify_proof_in_bounds_boundary() {
        // index = 10, length = 10 => out of bounds (10 >= 10)
        let mut solver = create_bv_solver().unwrap();
        let index = solver.bv_const(10, 32);
        let length = solver.bv_const(10, 32);
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::InBounds, &[index, length], 32)
                .unwrap();
        let cond =
            verify_proof_obligation(&mut solver, &ProofAnnotation::InBounds, &operands).unwrap();
        assert!(!cond.check(&mut solver).expect("the condition checks"));
    }

    #[test]
    fn verify_proof_not_null_constant() {
        // ptr = 0x1000 => not null
        let mut solver = create_bv_solver().unwrap();
        let ptr = solver.bv_const(0x1000, 64);
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::NotNull, &[ptr], 64).unwrap();
        let cond =
            verify_proof_obligation(&mut solver, &ProofAnnotation::NotNull, &operands).unwrap();
        assert!(cond.check(&mut solver).expect("the condition checks"));
    }

    #[test]
    fn verify_proof_not_null_null_fails() {
        // ptr = 0 => is null, proof fails
        let mut solver = create_bv_solver().unwrap();
        let ptr = solver.bv_const(0, 64);
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::NotNull, &[ptr], 64).unwrap();
        let cond =
            verify_proof_obligation(&mut solver, &ProofAnnotation::NotNull, &operands).unwrap();
        assert!(!cond.check(&mut solver).expect("the condition checks"));
    }

    #[test]
    fn verify_proof_still_unsupported_annotations() {
        // Terminates, DataRaceFree, BoundedOutput, Monotonic, Custom require
        // richer models beyond BV/FP and remain unsupported.
        let mut solver = create_bv_solver().unwrap();
        let operands = ProofOperands {
            terms: vec![],
            overflow_op: None,
            width: Some(32),
            signed: None,
        };
        assert!(
            verify_proof_obligation(&mut solver, &ProofAnnotation::Terminates, &operands).is_err()
        );
        assert!(
            verify_proof_obligation(&mut solver, &ProofAnnotation::DataRaceFree, &operands)
                .is_err()
        );
    }

    #[test]
    fn verify_proof_pure_missing_operands_is_err() {
        // Pure requires result1 and result2 operands; missing them should error
        let mut solver = create_bv_solver().unwrap();
        let operands = ProofOperands {
            terms: vec![],
            overflow_op: None,
            width: Some(32),
            signed: None,
        };
        assert!(verify_proof_obligation(&mut solver, &ProofAnnotation::Pure, &operands).is_err());
    }

    #[test]
    fn verify_proof_no_wrap_same_as_no_overflow() {
        // NoWrap is encoded the same as NoOverflow
        let mut solver = create_bv_solver().unwrap();
        let sort = Sort::BitVec(BitVecSort { width: 32 });
        let a = solver.declare_const("a", sort.clone());
        let b = solver.declare_const("b", sort);
        let operands = ProofOperands::for_annotation(&ProofAnnotation::NoWrap, &[a, b], 32)
            .unwrap()
            .with_overflow_op(OverflowOp::AddOverflow)
            .with_signedness(true);
        let cond =
            verify_proof_obligation(&mut solver, &ProofAnnotation::NoWrap, &operands).unwrap();
        // Symbolic => should not verify
        assert!(!cond.check(&mut solver).expect("the condition checks"));
    }

    // ---- verify_no_overflow end-to-end ----

    #[test]
    fn verify_no_overflow_demo() {
        // The demo should return true: 32-bit addition CAN overflow
        let result = verify_no_overflow().unwrap();
        assert!(result, "32-bit addition should be able to overflow");
    }

    // ---- AYError Display ----

    #[test]
    fn ay_error_display() {
        let e1 = AYError::UnsupportedType(Ty::Unit);
        assert!(format!("{}", e1).contains("()"));

        let e2 = AYError::UnsupportedOp("test_op".to_string());
        assert!(format!("{}", e2).contains("test_op"));

        let e3 = AYError::SolverError("init failed".to_string());
        assert!(format!("{}", e3).contains("init failed"));

        let e4 = AYError::UnsupportedAnnotation("pure".to_string());
        assert!(format!("{}", e4).contains("pure"));

        let e5 = AYError::MemoryError("out of bounds".to_string());
        assert!(format!("{}", e5).contains("out of bounds"));
    }

    // ---- ProofOperands construction ----

    #[test]
    fn proof_operands_single_construction() {
        let mut solver = create_bv_solver().unwrap();
        let term = solver.bv_const(42, 32);
        let ops = ProofOperands::single("divisor", term, 32);
        assert_eq!(ops.terms.len(), 1);
        assert_eq!(ops.terms[0].0, "divisor");
        assert!(ops.overflow_op.is_none());
        assert_eq!(ops.width, Some(32));
    }

    #[test]
    fn proof_operands_pair_construction() {
        let mut solver = create_bv_solver().unwrap();
        let t1 = solver.bv_const(0, 32);
        let t2 = solver.bv_const(10, 32);
        let ops = ProofOperands::pair("index", t1, "length", t2, 32);
        assert_eq!(ops.terms.len(), 2);
        assert!(ops.overflow_op.is_none());
    }

    #[test]
    fn proof_operands_overflow_construction() {
        let mut solver = create_bv_solver().unwrap();
        let a = solver.bv_const(1, 32);
        let b = solver.bv_const(2, 32);
        let ops = ProofOperands::overflow(a, b, OverflowOp::AddOverflow, 32);
        assert_eq!(ops.terms.len(), 2);
        assert_eq!(ops.overflow_op, Some(OverflowOp::AddOverflow));
    }

    // ---- Symbol-binding schema ----

    #[test]
    fn ay_symbol_is_deterministic_and_positional() {
        // Pure function of (FuncId, ValueId): stable format, no environment.
        assert_eq!(ay_symbol(FuncId::new(0), ValueId::new(0)), "f0_v0");
        assert_eq!(ay_symbol(FuncId::new(3), ValueId::new(17)), "f3_v17");
        // Same inputs, same name — repeated calls cannot drift.
        assert_eq!(
            ay_symbol(FuncId::new(3), ValueId::new(17)),
            ay_symbol(FuncId::new(3), ValueId::new(17))
        );
    }

    #[test]
    fn ay_symbol_parse_roundtrip() {
        for (f, v) in [(0, 0), (1, 2), (42, 4096), (u32::MAX, u32::MAX)] {
            let name = ay_symbol(FuncId::new(f), ValueId::new(v));
            assert_eq!(
                parse_ay_symbol(&name),
                Some((FuncId::new(f), ValueId::new(v)))
            );
        }
        // Non-schema names do not parse.
        assert_eq!(parse_ay_symbol("mem"), None);
        assert_eq!(parse_ay_symbol("divisor"), None);
        assert_eq!(parse_ay_symbol("f1"), None);
        assert_eq!(parse_ay_symbol("f1_vx"), None);
    }

    #[test]
    fn ay_sort_matches_ty_to_sort() {
        for ty in [Ty::I32, Ty::U64, Ty::Bool, Ty::Ptr, Ty::F64] {
            assert_eq!(ay_sort(&ty).unwrap(), ty_to_sort(&ty).unwrap());
        }
    }

    #[test]
    fn ay_sort_vector_is_concatenated_lanes() {
        // <4 x i32> => BitVec(128); <2 x i64> => BitVec(128) — the model
        // encode_vector_binop operates on.
        let v4i32 = Ty::Vector(Box::new(Ty::I32), 4);
        assert_eq!(
            ay_sort(&v4i32).unwrap(),
            Sort::BitVec(BitVecSort { width: 128 })
        );
        let v2i64 = Ty::Vector(Box::new(Ty::I64), 2);
        assert_eq!(
            ay_sort(&v2i64).unwrap(),
            Sort::BitVec(BitVecSort { width: 128 })
        );
        // Zero lanes and non-scalar lanes fail closed.
        assert!(ay_sort(&Ty::Vector(Box::new(Ty::I32), 0)).is_err());
        assert!(ay_sort(&Ty::Vector(Box::new(Ty::Unit), 4)).is_err());
    }

    #[test]
    fn for_annotation_binds_roles_positionally() {
        // for_annotation-built operands are accepted by the encoder exactly
        // like the by-name legacy constructors.
        let mut solver = create_bv_solver().unwrap();
        let five = solver.bv_const(5, 32);
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::DivNonZero, &[five], 32).unwrap();
        assert_eq!(operands.terms[0].0, "divisor");
        let cond =
            verify_proof_obligation(&mut solver, &ProofAnnotation::DivNonZero, &operands).unwrap();
        assert!(cond.check(&mut solver).expect("the condition checks"));
    }

    #[test]
    fn for_annotation_arity_mismatch_fails_closed() {
        let mut solver = create_bv_solver().unwrap();
        let t = solver.bv_const(1, 32);
        let err = ProofOperands::for_annotation(&ProofAnnotation::InBounds, &[t], 32);
        assert!(matches!(err, Err(AYError::UnsupportedAnnotation(_))));
    }

    #[test]
    fn for_annotation_unencodable_annotation_fails_closed() {
        let mut solver = create_bv_solver().unwrap();
        let t = solver.bv_const(1, 32);
        let err = ProofOperands::for_annotation(&ProofAnnotation::DataRaceFree, &[t], 32);
        assert!(matches!(err, Err(AYError::UnsupportedAnnotation(_))));
    }

    #[test]
    fn from_values_declares_schema_symbols() {
        // Binding an IR value through the schema declares `f{f}_v{v}`, and a
        // refuting model reports its assignment under exactly that name.
        let mut solver = create_bv_solver().unwrap();
        let func = FuncId::new(2);
        let divisor = ValueId::new(7);
        let operands = ProofOperands::from_values(
            &mut solver,
            &ProofAnnotation::DivNonZero,
            func,
            &[(divisor, Ty::I32)],
        )
        .unwrap();
        assert_eq!(operands.width, Some(32));
        let cond =
            verify_proof_obligation(&mut solver, &ProofAnnotation::DivNonZero, &operands).unwrap();
        // Symbolic divisor can be zero => refuted, with a model over f2_v7.
        assert!(!cond.check(&mut solver).expect("the condition checks"));
        let model = solver.model().expect("SAT result has a model");
        let (value, width) = model
            .model()
            .bv_val(&ay_symbol(func, divisor))
            .expect("model assigns the schema symbol");
        assert_eq!(width, 32);
        assert_eq!(value, 0.into());
    }

    // ---- Combined encoding: BinOp + ICmp ----

    #[test]
    fn combined_binop_icmp_theorem_has_strict_unsat_witness() {
        // For any a > 0 and b > 0, if no overflow, then a + b > 0
        let mut solver = create_bv_solver().unwrap();
        let sort = Sort::BitVec(BitVecSort { width: 32 });
        let a = solver.declare_const("a", sort.clone());
        let b = solver.declare_const("b", sort);

        let zero = solver.bv_const(0, 32);

        // Constraints: a > 0, b > 0 (signed)
        let a_pos = encode_icmp(&mut solver, ICmpOp::Sgt, a, zero).expect("the adapter encodes");
        let b_pos = encode_icmp(&mut solver, ICmpOp::Sgt, b, zero).expect("the adapter encodes");

        // No overflow
        let safe = encode_overflow_check(&mut solver, OverflowOp::AddOverflow, true, a, b)
            .expect("the adapter encodes");

        // a + b
        let sum = encode_binop(&mut solver, BinOp::Add, a, b).unwrap();

        // Assert sum <= 0 (negation of sum > 0)
        let sum_not_pos =
            encode_icmp(&mut solver, ICmpOp::Sle, sum, zero).expect("the adapter encodes");

        // Keep the exact authored query as one conjunction. AY's mandatory
        // UNSAT boundary replays a strict proof against this immutable source
        // root.
        let positive_inputs = solver.and(a_pos, b_pos);
        let premises = solver.and(positive_inputs, safe);
        let contradiction = solver.and(premises, sum_not_pos);
        solver.assert_term(contradiction);

        // Ratchet the upgraded AY proof boundary: this mixed BV derivation is
        // now strictly checked and must carry the one-shot UNSAT witness. A
        // future regression to Unknown is a loss of certified coverage.
        let result = solver.check_sat();
        assert!(result.is_unsat(), "strictly proved theorem became {result}");
        assert!(result.has_unsat_emission_witness());
    }

    // ---- Cast + ICmp combination ----

    #[test]
    fn combined_zext_preserves_value() {
        // For any 16-bit x, zext(x, 32) == x when compared as unsigned 32-bit
        let mut solver = create_bv_solver().unwrap();
        let sort16 = Sort::BitVec(BitVecSort { width: 16 });
        let x = solver.declare_const("x", sort16);

        let extended = encode_cast(&mut solver, CastOp::ZExt, x, 16, 32).unwrap();

        // x as 32-bit via zext
        let x_as_32 = solver.bvzeroext(x, 16);

        // extended should equal x_as_32
        let neq = solver.eq(extended, x_as_32);
        let neg = solver.not(neq);
        solver.assert_term(neg);
        assert!(solver.check_sat().is_unsat());
    }

    // ---- 8-bit width tests (smaller BV) ----

    #[test]
    fn encode_binop_8bit() {
        let mut solver = create_bv_solver().unwrap();
        let a = solver.bv_const(100, 8);
        let b = solver.bv_const(28, 8);
        let sum = encode_binop(&mut solver, BinOp::Add, a, b).unwrap();
        let expected = solver.bv_const(128u64 as i64, 8);
        let eq = solver.eq(sum, expected);
        solver.assert_term(eq);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn encode_overflow_check_8bit() {
        // 127 + 1 overflows in signed 8-bit
        let mut solver = create_bv_solver().unwrap();
        let max = solver.bv_const(127, 8);
        let one = solver.bv_const(1, 8);
        let safe = encode_overflow_check(&mut solver, OverflowOp::AddOverflow, true, max, one)
            .expect("the adapter encodes");
        let not_safe = solver.not(safe);
        solver.assert_term(not_safe);
        assert!(solver.check_sat().is_sat());
    }

    // ============================================================
    // UNSIGNED overflow-lane regression tests — the confirmed
    // false-accept (2026-07-09): the signed lanes were hardcoded for
    // every type, so `0 - 1` on an UNSIGNED type reported SAFE
    // (signed 0-1 = -1 does not underflow) and tRust verified
    // `fn sub(a: usize, b: usize) -> usize { a - b }` clean. Each
    // test pins one unsigned lane: the unsafe case must be
    // detectable (asserting NOT-safe is SAT) and the safe case must
    // be provable (asserting NOT-safe is UNSAT).
    // ============================================================

    #[test]
    fn encode_overflow_check_unsigned_sub_borrow_is_unsafe() {
        // THE false-accept shape: u64 `0 - 1` borrows — must NOT be safe.
        let mut solver = create_bv_solver().unwrap();
        let zero = solver.bv_const(0, 64);
        let one = solver.bv_const(1, 64);
        let safe = encode_overflow_check(&mut solver, OverflowOp::SubOverflow, false, zero, one)
            .expect("the adapter encodes");
        let not_safe = solver.not(safe);
        solver.assert_term(not_safe);
        assert!(
            solver.check_sat().is_sat(),
            "unsigned 0 - 1 must be detected as underflow (the sub(a,b) false-accept)"
        );
    }

    #[test]
    fn encode_overflow_check_unsigned_sub_no_borrow_is_safe() {
        // u64 `1 - 0` cannot borrow — must be provably safe.
        let mut solver = create_bv_solver().unwrap();
        let one = solver.bv_const(1, 64);
        let zero = solver.bv_const(0, 64);
        let safe = encode_overflow_check(&mut solver, OverflowOp::SubOverflow, false, one, zero)
            .expect("the adapter encodes");
        let not_safe = solver.not(safe);
        solver.assert_term(not_safe);
        assert!(
            !solver.check_sat().is_sat(),
            "unsigned 1 - 0 must be provably safe"
        );
    }

    #[test]
    fn encode_overflow_check_unsigned_add_carry_is_unsafe() {
        // u8 `255 + 1` carries out — must NOT be safe. (The signed lane
        // misses this: -1 + 1 = 0 has no signed overflow.)
        let mut solver = create_bv_solver().unwrap();
        let max = solver.bv_const(255, 8);
        let one = solver.bv_const(1, 8);
        let safe = encode_overflow_check(&mut solver, OverflowOp::AddOverflow, false, max, one)
            .expect("the adapter encodes");
        let not_safe = solver.not(safe);
        solver.assert_term(not_safe);
        assert!(
            solver.check_sat().is_sat(),
            "unsigned 255 + 1 (u8) must be detected"
        );
    }

    #[test]
    fn encode_overflow_check_unsigned_add_small_is_safe() {
        // u8 `1 + 1` cannot carry — must be provably safe.
        let mut solver = create_bv_solver().unwrap();
        let one = solver.bv_const(1, 8);
        let also_one = solver.bv_const(1, 8);
        let safe =
            encode_overflow_check(&mut solver, OverflowOp::AddOverflow, false, one, also_one)
                .expect("the adapter encodes");
        let not_safe = solver.not(safe);
        solver.assert_term(not_safe);
        assert!(
            !solver.check_sat().is_sat(),
            "unsigned 1 + 1 (u8) must be provably safe"
        );
    }

    #[test]
    fn encode_overflow_check_unsigned_mul_is_unsafe_and_safe() {
        // u8 `16 * 16` = 256 overflows; `3 * 5` does not.
        let mut solver = create_bv_solver().unwrap();
        let sixteen = solver.bv_const(16, 8);
        let safe = encode_overflow_check(
            &mut solver,
            OverflowOp::MulOverflow,
            false,
            sixteen,
            sixteen,
        )
        .expect("the adapter encodes");
        let not_safe = solver.not(safe);
        solver.assert_term(not_safe);
        assert!(
            solver.check_sat().is_sat(),
            "unsigned 16 * 16 (u8) must be detected"
        );

        let mut solver2 = create_bv_solver().unwrap();
        let three = solver2.bv_const(3, 8);
        let five = solver2.bv_const(5, 8);
        let safe2 =
            encode_overflow_check(&mut solver2, OverflowOp::MulOverflow, false, three, five)
                .expect("the adapter encodes");
        let not_safe2 = solver2.not(safe2);
        solver2.assert_term(not_safe2);
        assert!(
            !solver2.check_sat().is_sat(),
            "unsigned 3 * 5 (u8) must be provably safe"
        );
    }

    // ============================================================
    // Floating-point encoding tests
    // ============================================================

    #[test]
    fn create_fp_solver_succeeds() {
        let solver = create_fp_solver();
        assert!(solver.is_ok());
    }

    #[test]
    fn encode_binop_fadd_construction() {
        let mut solver = create_fp_solver().unwrap();
        let sort = Sort::FloatingPoint(8, 24);
        let a = solver.declare_const("a", sort.clone());
        let b = solver.declare_const("b", sort);
        let result = encode_binop(&mut solver, BinOp::FAdd, a, b);
        assert!(result.is_ok());
    }

    /// EVERY float `BinOp` at f64: the five with an exact SMT encoding build
    /// a term (`FRem` as the exact `fmod`, see [`encode_frem_fmod`]; its value
    /// is pinned by `tests/frem_fmod.rs`). The three with no SMT-LIB FP
    /// counterpart are refused BY NAME, never approximated.
    #[test]
    fn encode_binop_all_float_variants() {
        let mut solver = create_fp_solver().unwrap();
        let sort = Sort::FloatingPoint(11, 53); // f64
        let a = solver.declare_const("a", sort.clone());
        let b = solver.declare_const("b", sort);
        let float_ops = [
            BinOp::FAdd,
            BinOp::FSub,
            BinOp::FMul,
            BinOp::FDiv,
            BinOp::FRem,
        ];
        for op in &float_ops {
            let result = encode_binop(&mut solver, *op, a, b);
            assert!(result.is_ok(), "encode_binop failed for {:?}", op);
        }
        for (op, name) in [
            (BinOp::FMin, "fmin"),
            (BinOp::FMax, "fmax"),
            (BinOp::FCopySign, "fcopysign"),
        ] {
            match encode_binop(&mut solver, op, a, b) {
                Err(AYError::UnsupportedOp(refused)) => assert_eq!(refused, name),
                other => panic!("{op:?} must be refused by name, got {other:?}"),
            }
        }
    }

    #[test]
    fn encode_unop_fneg_construction() {
        let mut solver = create_fp_solver().unwrap();
        let sort = Sort::FloatingPoint(8, 24);
        let a = solver.declare_const("a", sort);
        let result = encode_unop(&mut solver, UnOp::FNeg, a);
        assert!(result.is_ok());
    }

    // ---- FCmp tests ----

    #[test]
    fn encode_fcmp_all_ordered_variants() {
        let mut solver = create_fp_solver().unwrap();
        let sort = Sort::FloatingPoint(8, 24);
        let a = solver.declare_const("a", sort.clone());
        let b = solver.declare_const("b", sort);
        let ordered = [
            FCmpOp::OEq,
            FCmpOp::ONe,
            FCmpOp::OLt,
            FCmpOp::OLe,
            FCmpOp::OGt,
            FCmpOp::OGe,
        ];
        for op in &ordered {
            let _result = encode_fcmp(&mut solver, *op, a, b).expect("the adapter encodes");
            // Just verifying construction does not panic
        }
    }

    #[test]
    fn encode_fcmp_all_unordered_variants() {
        let mut solver = create_fp_solver().unwrap();
        let sort = Sort::FloatingPoint(8, 24);
        let a = solver.declare_const("a", sort.clone());
        let b = solver.declare_const("b", sort);
        let unordered = [
            FCmpOp::UEq,
            FCmpOp::UNe,
            FCmpOp::ULt,
            FCmpOp::ULe,
            FCmpOp::UGt,
            FCmpOp::UGe,
        ];
        for op in &unordered {
            let _result = encode_fcmp(&mut solver, *op, a, b).expect("the adapter encodes");
        }
    }

    // ---- FP cast tests ----

    #[test]
    fn encode_cast_fp_to_ui() {
        let mut solver = create_fp_solver().unwrap();
        let sort = Sort::FloatingPoint(8, 24);
        let val = solver.declare_const("val", sort);
        let result = encode_cast(&mut solver, CastOp::FPToUI, val, 32, 32);
        assert!(result.is_ok());
    }

    #[test]
    fn encode_cast_fp_to_si() {
        let mut solver = create_fp_solver().unwrap();
        let sort = Sort::FloatingPoint(8, 24);
        let val = solver.declare_const("val", sort);
        let result = encode_cast(&mut solver, CastOp::FPToSI, val, 32, 32);
        assert!(result.is_ok());
    }

    #[test]
    fn encode_cast_ui_to_fp() {
        let mut solver = create_fp_solver().unwrap();
        let val = solver.bv_const(42, 32);
        // dst_width=32 => F32 (8, 24)
        let result = encode_cast(&mut solver, CastOp::UIToFP, val, 32, 32);
        assert!(result.is_ok());
    }

    #[test]
    fn encode_cast_si_to_fp() {
        let mut solver = create_fp_solver().unwrap();
        let val = solver.bv_const(-5, 32);
        let result = encode_cast(&mut solver, CastOp::SIToFP, val, 32, 64);
        assert!(result.is_ok());
    }

    #[test]
    fn encode_cast_fp_trunc() {
        // f64 -> f32
        let mut solver = create_fp_solver().unwrap();
        let sort = Sort::FloatingPoint(11, 53);
        let val = solver.declare_const("val", sort);
        let result = encode_cast(&mut solver, CastOp::FPTrunc, val, 64, 32);
        assert!(result.is_ok());
    }

    #[test]
    fn encode_cast_fp_ext() {
        // f32 -> f64
        let mut solver = create_fp_solver().unwrap();
        let sort = Sort::FloatingPoint(8, 24);
        let val = solver.declare_const("val", sort);
        let result = encode_cast(&mut solver, CastOp::FPExt, val, 32, 64);
        assert!(result.is_ok());
    }

    #[test]
    fn fp_sort_from_total_width_valid() {
        assert_eq!(fp_sort_from_total_width(32).unwrap(), (8, 24));
        assert_eq!(fp_sort_from_total_width(64).unwrap(), (11, 53));
    }

    #[test]
    fn fp_sort_from_total_width_invalid() {
        assert!(fp_sort_from_total_width(16).is_err());
        assert!(fp_sort_from_total_width(128).is_err());
    }

    // ============================================================
    // Memory model tests
    // ============================================================

    #[test]
    fn memory_sort_construction() {
        let sort = memory_sort();
        match sort {
            Sort::Array(arr) => {
                assert_eq!(arr.index_sort, Sort::BitVec(BitVecSort { width: 64 }));
                assert_eq!(arr.element_sort, Sort::BitVec(BitVecSort { width: 8 }));
            }
            other => panic!("expected Array sort, got {:?}", other),
        }
    }

    #[test]
    fn memory_model_new() {
        let mut solver = create_fp_solver().unwrap();
        let mem = MemoryModel::new(&mut solver, "mem0").expect("the adapter encodes");
        assert_eq!(mem.next_free, ALLOCA_GRANULE);
    }

    #[test]
    fn memory_model_load_single_byte() {
        let mut solver = create_fp_solver().unwrap();
        let mem = MemoryModel::new(&mut solver, "mem").expect("the adapter encodes");
        let addr = solver.bv_const(0x1000, 64);
        let result = mem.encode_load(&mut solver, addr, 1);
        assert!(result.is_ok());
    }

    #[test]
    fn memory_model_load_multi_byte() {
        let mut solver = create_fp_solver().unwrap();
        let mem = MemoryModel::new(&mut solver, "mem").expect("the adapter encodes");
        let addr = solver.bv_const(0x1000, 64);
        let result = mem.encode_load(&mut solver, addr, 4);
        assert!(result.is_ok());
    }

    #[test]
    fn memory_model_load_zero_bytes_error() {
        let mut solver = create_fp_solver().unwrap();
        let mem = MemoryModel::new(&mut solver, "mem").expect("the adapter encodes");
        let addr = solver.bv_const(0x1000, 64);
        let result = mem.encode_load(&mut solver, addr, 0);
        assert!(result.is_err());
    }

    #[test]
    fn memory_model_store_single_byte() {
        let mut solver = create_fp_solver().unwrap();
        let mut mem = MemoryModel::new(&mut solver, "mem").expect("the adapter encodes");
        let addr = solver.bv_const(0x1000, 64);
        let val = solver.bv_const(0x42, 8);
        let result = mem.encode_store(&mut solver, addr, val, 1);
        assert!(result.is_ok());
    }

    #[test]
    fn memory_model_store_zero_bytes_error() {
        let mut solver = create_fp_solver().unwrap();
        let mut mem = MemoryModel::new(&mut solver, "mem").expect("the adapter encodes");
        let addr = solver.bv_const(0x1000, 64);
        let val = solver.bv_const(0, 8);
        let result = mem.encode_store(&mut solver, addr, val, 0);
        assert!(result.is_err());
    }

    #[test]
    fn memory_model_store_then_load_roundtrip() {
        // Store a 32-bit value and load it back, verify they are equal
        let mut solver = create_fp_solver().unwrap();
        let mut mem = MemoryModel::new(&mut solver, "mem").expect("the adapter encodes");

        let addr = solver.bv_const(0x2000, 64);
        let val = solver.bv_const(0x12345678, 32);

        // Store 4 bytes
        mem.encode_store(&mut solver, addr, val, 4).unwrap();

        // Load 4 bytes from same address
        let loaded = mem.encode_load(&mut solver, addr, 4).unwrap();

        // Assert loaded == original
        let eq = solver.eq(loaded, val);
        solver.assert_term(eq);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn memory_model_alloca_returns_nonnull() {
        let mut solver = create_fp_solver().unwrap();
        let mut mem = MemoryModel::new(&mut solver, "mem").expect("the adapter encodes");
        let addr = mem.encode_alloca(&mut solver, 16).unwrap();

        // The addr should be non-null (we asserted it)
        let null = solver.bv_const(0, 64);
        let is_null = solver.eq(addr, null);
        solver.assert_term(is_null);
        // Should be UNSAT because we asserted non-null
        assert!(solver.check_sat().is_unsat());
    }

    /// Is `addr == expected` satisfiable in a fresh scope of `solver`?
    fn address_is(solver: &mut Solver, addr: Term, expected: u64) -> bool {
        solver.push();
        let want = solver.bv_const_u64(expected, 64);
        let eq = solver.eq(addr, want);
        solver.assert_term(eq);
        let sat = solver.check_sat().is_sat();
        solver.pop();
        sat
    }

    #[test]
    fn memory_model_small_allocas_keep_the_historical_bases() {
        let mut solver = create_fp_solver().unwrap();
        let mut mem = MemoryModel::new(&mut solver, "mem").expect("the adapter encodes");
        let addr1 = mem.encode_alloca(&mut solver, 8).unwrap();
        let addr2 = mem.encode_alloca(&mut solver, 8).unwrap();
        let addr3 = mem.encode_alloca(&mut solver, ALLOCA_GRANULE).unwrap();
        assert!(address_is(&mut solver, addr1, 0x1000));
        assert!(address_is(&mut solver, addr2, 0x2000));
        assert!(address_is(&mut solver, addr3, 0x3000));
        assert_eq!(mem.next_free, 0x4000);
    }

    #[test]
    fn memory_model_a_large_alloca_does_not_overlap_the_next() {
        // 0x2800 bytes at 0x1000 end at 0x3800; the fixed 0x1000 stride put
        // the next allocation at 0x2000, inside it.
        let mut solver = create_fp_solver().unwrap();
        let mut mem = MemoryModel::new(&mut solver, "mem").expect("the adapter encodes");
        let big = mem.encode_alloca(&mut solver, 0x2800).unwrap();
        let next = mem.encode_alloca(&mut solver, 8).unwrap();
        assert!(address_is(&mut solver, big, 0x1000));
        assert!(address_is(&mut solver, next, 0x4000));
        assert!(!address_is(&mut solver, next, 0x2000));
    }

    #[test]
    fn memory_model_a_zero_sized_alloca_still_gets_its_own_base() {
        let mut solver = create_fp_solver().unwrap();
        let mut mem = MemoryModel::new(&mut solver, "mem").expect("the adapter encodes");
        let zst = mem.encode_alloca(&mut solver, 0).unwrap();
        let next = mem.encode_alloca(&mut solver, 0).unwrap();
        assert!(address_is(&mut solver, zst, 0x1000));
        assert!(address_is(&mut solver, next, 0x2000));
    }

    #[test]
    fn memory_model_alloca_past_the_address_space_is_refused_not_wrapped() {
        let mut solver = create_fp_solver().unwrap();
        let mut mem = MemoryModel::new(&mut solver, "mem").expect("the adapter encodes");
        // An allocation that would end past 2^64.
        let error = mem.encode_alloca(&mut solver, u64::MAX).unwrap_err();
        assert!(
            matches!(&error, AYError::MemoryError(msg) if msg.contains("does not fit the 64-bit address space")),
            "unexpected refusal: {error}"
        );
        assert_eq!(
            mem.next_free, ALLOCA_GRANULE,
            "a refused alloca consumes nothing"
        );
        // The last granule: the allocation itself fits, its padding does not.
        mem.next_free = !(ALLOCA_GRANULE - 1);
        assert!(mem.encode_alloca(&mut solver, 1).is_err());
        // The solver state is not poisoned: nothing false was asserted.
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn memory_model_store_wider_than_a_bit_vector_is_refused_before_any_work() {
        // 2^29 bytes is 2^32 bits, one more than a `u32` bit-vector width can
        // hold. The loop used to compute `i * 8` for every byte, which wraps
        // past byte 2^29 in release; the store is now refused up front, and
        // the memory state is untouched.
        let mut solver = create_fp_solver().unwrap();
        let mut mem = MemoryModel::new(&mut solver, "mem").expect("the adapter encodes");
        let before = mem.state;
        let addr = solver.bv_const(0x1000, 64);
        let val = solver.bv_const(0, 8);
        let error = mem
            .encode_store(&mut solver, addr, val, 1 << 29)
            .unwrap_err();
        assert!(
            matches!(&error, AYError::MemoryError(msg) if msg.contains("exceeds the u32 bit-vector width")),
            "unexpected refusal: {error}"
        );
        assert!(
            mem.state == before,
            "a refused store must not move the memory state"
        );
        // The widest representable store is admitted by the width check.
        assert_eq!(((1u32 << 29) - 1).checked_mul(8), Some(u32::MAX - 7));
    }

    #[test]
    fn memory_model_gep() {
        let mut solver = create_fp_solver().unwrap();
        let mem = MemoryModel::new(&mut solver, "mem").expect("the adapter encodes");
        let base = solver.bv_const(0x1000, 64);
        let offset = solver.bv_const(16, 64);
        let result = mem
            .encode_gep(&mut solver, base, offset)
            .expect("the adapter encodes");

        // result should be base + offset = 0x1010
        let expected = solver.bv_const(0x1010, 64);
        let eq = solver.eq(result, expected);
        solver.assert_term(eq);
        assert!(solver.check_sat().is_sat());
    }

    // ============================================================
    // Solver-verdict evidence-record pipeline tests
    // ============================================================

    #[test]
    fn verify_and_certify_verified() {
        // Constant divisor = 5, DivNonZero should be verified
        let mut solver = create_bv_solver().unwrap();
        let five = solver.bv_const(5, 32);
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::DivNonZero, &[five], 32).unwrap();
        let result = verify_and_certify(
            &mut solver,
            &ProofAnnotation::DivNonZero,
            &operands,
            ProofId::new(0),
        )
        .unwrap();
        assert!(result.is_proved_by_solver());
        assert_eq!(result.status(), ProofStatus::Pending);
        let cert = result.into_certificate();
        assert_eq!(cert.obligation, ProofId::new(0));
        assert_eq!(cert.prover, "ay");
    }

    #[test]
    fn verify_and_certify_refuted() {
        // Symbolic divisor can be zero => refuted
        let mut solver = create_bv_solver().unwrap();
        let sort = Sort::BitVec(BitVecSort { width: 32 });
        let d = solver.declare_const("d", sort);
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::DivNonZero, &[d], 32).unwrap();
        let result = verify_and_certify(
            &mut solver,
            &ProofAnnotation::DivNonZero,
            &operands,
            ProofId::new(1),
        )
        .unwrap();
        assert_eq!(result.status(), ProofStatus::Failed);
        let cert = result.into_certificate();
        assert_eq!(cert.obligation, ProofId::new(1));
        assert_eq!(cert.prover, "ay");
    }

    #[test]
    fn verify_and_certify_not_null_verified() {
        let mut solver = create_bv_solver().unwrap();
        let ptr = solver.bv_const(0x1000, 64);
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::NotNull, &[ptr], 64).unwrap();
        let result = verify_and_certify(
            &mut solver,
            &ProofAnnotation::NotNull,
            &operands,
            ProofId::new(2),
        )
        .unwrap();
        assert!(result.is_proved_by_solver());
        assert_eq!(result.status(), ProofStatus::Pending);
    }

    #[test]
    fn verify_and_certify_not_null_refuted() {
        let mut solver = create_bv_solver().unwrap();
        let ptr = solver.bv_const(0, 64);
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::NotNull, &[ptr], 64).unwrap();
        let result = verify_and_certify(
            &mut solver,
            &ProofAnnotation::NotNull,
            &operands,
            ProofId::new(3),
        )
        .unwrap();
        assert_eq!(result.status(), ProofStatus::Failed);
    }

    #[test]
    fn verification_result_into_certificate() {
        let cert = ProofCertificate {
            obligation: ProofId::new(42),
            prover: "ay".to_string(),
            evidence: ProofEvidence::SmtProof(vec![]),
            // v41: this adapter records no coverage bound of its own; the
            // projection is the bundle writer's job, and `None` reads as
            // UNKNOWN coverage rather than `Unbounded`.
            assurance: None,
        };
        let vr = VerificationResult::Verified(cert);
        assert!(vr.is_proved_by_solver());
        assert_eq!(vr.status(), ProofStatus::Pending);
        let cert = vr.into_certificate();
        assert_eq!(cert.obligation, ProofId::new(42));
    }

    #[test]
    fn verification_result_refuted_status() {
        let cert = ProofCertificate {
            obligation: ProofId::new(0),
            prover: "ay".to_string(),
            evidence: ProofEvidence::SmtProof(vec![]),
            // v41: this adapter records no coverage bound of its own; the
            // projection is the bundle writer's job, and `None` reads as
            // UNKNOWN coverage rather than `Unbounded`.
            assurance: None,
        };
        let vr = VerificationResult::Refuted { certificate: cert };
        assert_eq!(vr.status(), ProofStatus::Failed);
    }

    #[test]
    fn verification_result_unknown_status() {
        let cert = ProofCertificate {
            obligation: ProofId::new(0),
            prover: "ay".to_string(),
            evidence: ProofEvidence::Trusted("timeout".to_string()),
            // v41: this adapter records no coverage bound of its own; the
            // projection is the bundle writer's job, and `None` reads as
            // UNKNOWN coverage rather than `Unbounded`.
            assurance: None,
        };
        let vr = VerificationResult::Unknown { certificate: cert };
        assert_eq!(vr.status(), ProofStatus::Pending);
    }

    // ============================================================
    // Borrow model tests
    // ============================================================

    #[test]
    fn permission_sort_construction() {
        let sort = permission_sort();
        match sort {
            Sort::Array(arr) => {
                assert_eq!(arr.index_sort, Sort::BitVec(BitVecSort { width: 64 }));
                assert_eq!(arr.element_sort, Sort::BitVec(BitVecSort { width: 2 }));
            }
            other => panic!("expected Array sort, got {:?}", other),
        }
    }

    #[test]
    fn borrow_model_new() {
        let mut solver = create_fp_solver().unwrap();
        let _model = BorrowModel::new(&mut solver, "perms0").expect("the adapter encodes");
    }

    #[test]
    fn borrow_model_get_permission() {
        let mut solver = create_fp_solver().unwrap();
        let model = BorrowModel::new(&mut solver, "perms").expect("the adapter encodes");
        let ptr = solver.bv_const(0x1000, 64);
        let _perm = model
            .get_permission(&mut solver, ptr)
            .expect("the adapter encodes");
        // Just verifying construction does not panic
    }

    #[test]
    fn borrow_model_encode_borrow_from_owned() {
        // If permission is Owned(1), shared borrow should succeed
        let mut solver = create_fp_solver().unwrap();
        let mut model = BorrowModel::new(&mut solver, "perms").expect("the adapter encodes");
        let ptr = solver.bv_const(0x1000, 64);

        // Set initial permission to Owned(1)
        let owned = solver.bv_const(1, 2);
        model.state = solver.store(model.state, ptr, owned);

        let (_borrow_ptr, new_state) = model
            .encode_borrow(&mut solver, ptr)
            .expect("the adapter encodes");

        // After borrow, permission should be SharedBorrow(2)
        let perm = solver.select(new_state, ptr);
        let shared = solver.bv_const(2, 2);
        let eq = solver.eq(perm, shared);
        solver.assert_term(eq);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn borrow_model_encode_borrow_from_shared() {
        // If permission is already SharedBorrow(2), another shared borrow should succeed
        let mut solver = create_fp_solver().unwrap();
        let mut model = BorrowModel::new(&mut solver, "perms").expect("the adapter encodes");
        let ptr = solver.bv_const(0x2000, 64);

        // Set initial permission to SharedBorrow(2)
        let shared = solver.bv_const(2, 2);
        model.state = solver.store(model.state, ptr, shared);

        let (_borrow_ptr, new_state) = model
            .encode_borrow(&mut solver, ptr)
            .expect("the adapter encodes");

        // Should still be SharedBorrow(2)
        let perm = solver.select(new_state, ptr);
        let eq = solver.eq(perm, shared);
        solver.assert_term(eq);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn borrow_model_encode_borrow_mut_from_owned() {
        let mut solver = create_fp_solver().unwrap();
        let mut model = BorrowModel::new(&mut solver, "perms").expect("the adapter encodes");
        let ptr = solver.bv_const(0x1000, 64);

        // Set initial permission to Owned(1)
        let owned = solver.bv_const(1, 2);
        model.state = solver.store(model.state, ptr, owned);

        let (_borrow_ptr, new_state) = model
            .encode_borrow_mut(&mut solver, ptr)
            .expect("the adapter encodes");

        // After borrow_mut, permission should be MutableBorrow(3)
        let perm = solver.select(new_state, ptr);
        let mutable = solver.bv_const(3, 2);
        let eq = solver.eq(perm, mutable);
        solver.assert_term(eq);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn borrow_model_encode_end_borrow_restores_owned() {
        let mut solver = create_fp_solver().unwrap();
        let mut model = BorrowModel::new(&mut solver, "perms").expect("the adapter encodes");
        let ptr = solver.bv_const(0x1000, 64);

        // Set permission to MutableBorrow(3)
        let mutable = solver.bv_const(3, 2);
        model.state = solver.store(model.state, ptr, mutable);

        let new_state = model
            .encode_end_borrow(&mut solver, ptr)
            .expect("the adapter encodes");

        // After end_borrow, permission should be Owned(1)
        let perm = solver.select(new_state, ptr);
        let owned = solver.bv_const(1, 2);
        let eq = solver.eq(perm, owned);
        solver.assert_term(eq);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn borrow_model_full_lifecycle() {
        // Owned -> SharedBorrow -> EndBorrow -> Owned -> BorrowMut -> EndBorrow -> Owned
        let mut solver = create_fp_solver().unwrap();
        let mut model = BorrowModel::new(&mut solver, "perms").expect("the adapter encodes");
        let ptr = solver.bv_const(0x3000, 64);

        // Start Owned
        let owned = solver.bv_const(1, 2);
        model.state = solver.store(model.state, ptr, owned);

        // Shared borrow
        model
            .encode_borrow(&mut solver, ptr)
            .expect("the adapter encodes");

        // End shared borrow
        model
            .encode_end_borrow(&mut solver, ptr)
            .expect("the adapter encodes");

        // Mutable borrow (now Owned again)
        model
            .encode_borrow_mut(&mut solver, ptr)
            .expect("the adapter encodes");

        // End mutable borrow
        let final_state = model
            .encode_end_borrow(&mut solver, ptr)
            .expect("the adapter encodes");

        // Should be Owned(1) at the end
        let perm = solver.select(final_state, ptr);
        let eq = solver.eq(perm, owned);
        solver.assert_term(eq);
        assert!(solver.check_sat().is_sat());
    }

    // ============================================================
    // ARC model tests
    // ============================================================

    #[test]
    fn refcount_sort_construction() {
        let sort = refcount_sort();
        match sort {
            Sort::Array(arr) => {
                assert_eq!(arr.index_sort, Sort::BitVec(BitVecSort { width: 64 }));
                assert_eq!(arr.element_sort, Sort::BitVec(BitVecSort { width: 32 }));
            }
            other => panic!("expected Array sort, got {:?}", other),
        }
    }

    #[test]
    fn arc_model_new() {
        let mut solver = create_fp_solver().unwrap();
        let _model = ArcModel::new(&mut solver, "refcounts0").expect("the adapter encodes");
    }

    #[test]
    fn arc_model_get_refcount() {
        let mut solver = create_fp_solver().unwrap();
        let model = ArcModel::new(&mut solver, "refcounts").expect("the adapter encodes");
        let ptr = solver.bv_const(0x1000, 64);
        let _rc = model
            .get_refcount(&mut solver, ptr)
            .expect("the adapter encodes");
    }

    #[test]
    fn arc_model_encode_retain_increments() {
        let mut solver = create_fp_solver().unwrap();
        let mut model = ArcModel::new(&mut solver, "refcounts").expect("the adapter encodes");
        let ptr = solver.bv_const(0x1000, 64);

        // Set initial refcount to 1
        let one = solver.bv_const(1, 32);
        model.state = solver.store(model.state, ptr, one);

        let new_state = model
            .encode_retain(&mut solver, ptr)
            .expect("the adapter encodes");

        // After retain, refcount should be 2
        let rc = solver.select(new_state, ptr);
        let two = solver.bv_const(2, 32);
        let eq = solver.eq(rc, two);
        solver.assert_term(eq);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn arc_model_encode_release_decrements() {
        let mut solver = create_fp_solver().unwrap();
        let mut model = ArcModel::new(&mut solver, "refcounts").expect("the adapter encodes");
        let ptr = solver.bv_const(0x1000, 64);

        // Set initial refcount to 2
        let two = solver.bv_const(2, 32);
        model.state = solver.store(model.state, ptr, two);

        let new_state = model.encode_release(&mut solver, ptr).unwrap();

        // After release, refcount should be 1
        let rc = solver.select(new_state, ptr);
        let one = solver.bv_const(1, 32);
        let eq = solver.eq(rc, one);
        solver.assert_term(eq);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn arc_model_encode_is_unique_true() {
        let mut solver = create_fp_solver().unwrap();
        let mut model = ArcModel::new(&mut solver, "refcounts").expect("the adapter encodes");
        let ptr = solver.bv_const(0x1000, 64);

        // Set refcount to 1
        let one = solver.bv_const(1, 32);
        model.state = solver.store(model.state, ptr, one);

        let is_unique = model
            .encode_is_unique(&mut solver, ptr)
            .expect("the adapter encodes");
        solver.assert_term(is_unique);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn arc_model_encode_is_unique_false() {
        let mut solver = create_fp_solver().unwrap();
        let mut model = ArcModel::new(&mut solver, "refcounts").expect("the adapter encodes");
        let ptr = solver.bv_const(0x1000, 64);

        // Set refcount to 3
        let three = solver.bv_const(3, 32);
        model.state = solver.store(model.state, ptr, three);

        let is_unique = model
            .encode_is_unique(&mut solver, ptr)
            .expect("the adapter encodes");
        // Assert is_unique => should be UNSAT because refcount is 3, not 1
        solver.assert_term(is_unique);
        assert!(solver.check_sat().is_unsat());
    }

    #[test]
    fn arc_model_retain_release_lifecycle() {
        // Start at 1, retain to 2, retain to 3, release to 2, release to 1
        let mut solver = create_fp_solver().unwrap();
        let mut model = ArcModel::new(&mut solver, "refcounts").expect("the adapter encodes");
        let ptr = solver.bv_const(0x4000, 64);

        // Set initial refcount to 1
        let one = solver.bv_const(1, 32);
        model.state = solver.store(model.state, ptr, one);

        // Retain twice
        model
            .encode_retain(&mut solver, ptr)
            .expect("the adapter encodes");
        model
            .encode_retain(&mut solver, ptr)
            .expect("the adapter encodes");

        // Release twice
        model.encode_release(&mut solver, ptr).unwrap();
        let final_state = model.encode_release(&mut solver, ptr).unwrap();

        // Should be back to 1
        let rc = solver.select(final_state, ptr);
        let eq = solver.eq(rc, one);
        solver.assert_term(eq);
        assert!(solver.check_sat().is_sat());
    }

    // ============================================================
    // Borrow proof obligation tests
    // ============================================================

    #[test]
    fn verify_proof_valid_borrow_constant_owned() {
        // permission = Owned(1) => ValidBorrow should verify
        let mut solver = create_fp_solver().unwrap();
        let ptr = solver.bv_const(0x1000, 64);
        let permission = solver.bv_const(1, 2); // Owned
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::ValidBorrow, &[ptr, permission], 2)
                .unwrap();
        let cond =
            verify_proof_obligation(&mut solver, &ProofAnnotation::ValidBorrow, &operands).unwrap();
        assert!(cond.check(&mut solver).expect("the condition checks"));
    }

    #[test]
    fn verify_proof_valid_borrow_not_owned_fails() {
        // permission = SharedBorrow(2) => ValidBorrow should NOT verify
        let mut solver = create_fp_solver().unwrap();
        let ptr = solver.bv_const(0x1000, 64);
        let permission = solver.bv_const(2, 2); // SharedBorrow
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::ValidBorrow, &[ptr, permission], 2)
                .unwrap();
        let cond =
            verify_proof_obligation(&mut solver, &ProofAnnotation::ValidBorrow, &operands).unwrap();
        assert!(!cond.check(&mut solver).expect("the condition checks"));
    }

    #[test]
    fn verify_proof_valid_borrow_symbolic_fails() {
        // symbolic permission can be non-Owned => should NOT verify
        let mut solver = create_fp_solver().unwrap();
        let ptr = solver.bv_const(0x1000, 64);
        let sort = Sort::BitVec(BitVecSort { width: 2 });
        let permission = solver.declare_const("perm", sort);
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::ValidBorrow, &[ptr, permission], 2)
                .unwrap();
        let cond =
            verify_proof_obligation(&mut solver, &ProofAnnotation::ValidBorrow, &operands).unwrap();
        assert!(!cond.check(&mut solver).expect("the condition checks"));
    }

    #[test]
    fn verify_proof_unique_borrow_owned() {
        // permission = Owned(1) => no mutable borrow exists => UniqueBorrow should verify
        let mut solver = create_fp_solver().unwrap();
        let ptr = solver.bv_const(0x1000, 64);
        let permission = solver.bv_const(1, 2); // Owned
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::UniqueBorrow, &[ptr, permission], 2)
                .unwrap();
        let cond = verify_proof_obligation(&mut solver, &ProofAnnotation::UniqueBorrow, &operands)
            .unwrap();
        assert!(cond.check(&mut solver).expect("the condition checks"));
    }

    #[test]
    fn verify_proof_unique_borrow_shared() {
        // permission = SharedBorrow(2) => not MutableBorrow(3) => UniqueBorrow should verify
        let mut solver = create_fp_solver().unwrap();
        let ptr = solver.bv_const(0x1000, 64);
        let permission = solver.bv_const(2, 2); // SharedBorrow
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::UniqueBorrow, &[ptr, permission], 2)
                .unwrap();
        let cond = verify_proof_obligation(&mut solver, &ProofAnnotation::UniqueBorrow, &operands)
            .unwrap();
        assert!(cond.check(&mut solver).expect("the condition checks"));
    }

    #[test]
    fn verify_proof_unique_borrow_mutable_fails() {
        // permission = MutableBorrow(3) => concurrent mutable borrow exists => should NOT verify
        let mut solver = create_fp_solver().unwrap();
        let ptr = solver.bv_const(0x1000, 64);
        let permission = solver.bv_const(3, 2); // MutableBorrow
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::UniqueBorrow, &[ptr, permission], 2)
                .unwrap();
        let cond = verify_proof_obligation(&mut solver, &ProofAnnotation::UniqueBorrow, &operands)
            .unwrap();
        assert!(!cond.check(&mut solver).expect("the condition checks"));
    }

    #[test]
    fn verify_proof_unique_borrow_symbolic_fails() {
        // symbolic permission can be MutableBorrow => should NOT verify
        let mut solver = create_fp_solver().unwrap();
        let ptr = solver.bv_const(0x1000, 64);
        let sort = Sort::BitVec(BitVecSort { width: 2 });
        let permission = solver.declare_const("perm", sort);
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::UniqueBorrow, &[ptr, permission], 2)
                .unwrap();
        let cond = verify_proof_obligation(&mut solver, &ProofAnnotation::UniqueBorrow, &operands)
            .unwrap();
        assert!(!cond.check(&mut solver).expect("the condition checks"));
    }

    #[test]
    fn verify_proof_shared_borrow_owned() {
        // permission = Owned(1) => readable => SharedBorrow should verify
        let mut solver = create_fp_solver().unwrap();
        let ptr = solver.bv_const(0x1000, 64);
        let permission = solver.bv_const(1, 2); // Owned
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::SharedBorrow, &[ptr, permission], 2)
                .unwrap();
        let cond = verify_proof_obligation(&mut solver, &ProofAnnotation::SharedBorrow, &operands)
            .unwrap();
        assert!(cond.check(&mut solver).expect("the condition checks"));
    }

    #[test]
    fn verify_proof_shared_borrow_shared() {
        // permission = SharedBorrow(2) => readable => SharedBorrow should verify
        let mut solver = create_fp_solver().unwrap();
        let ptr = solver.bv_const(0x1000, 64);
        let permission = solver.bv_const(2, 2); // SharedBorrow
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::SharedBorrow, &[ptr, permission], 2)
                .unwrap();
        let cond = verify_proof_obligation(&mut solver, &ProofAnnotation::SharedBorrow, &operands)
            .unwrap();
        assert!(cond.check(&mut solver).expect("the condition checks"));
    }

    #[test]
    fn verify_proof_shared_borrow_mutable_fails() {
        // permission = MutableBorrow(3) => NOT readable for shared => should NOT verify
        let mut solver = create_fp_solver().unwrap();
        let ptr = solver.bv_const(0x1000, 64);
        let permission = solver.bv_const(3, 2); // MutableBorrow
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::SharedBorrow, &[ptr, permission], 2)
                .unwrap();
        let cond = verify_proof_obligation(&mut solver, &ProofAnnotation::SharedBorrow, &operands)
            .unwrap();
        assert!(!cond.check(&mut solver).expect("the condition checks"));
    }

    #[test]
    fn verify_proof_shared_borrow_no_permission_fails() {
        // permission = NoPermission(0) => NOT readable => should NOT verify
        let mut solver = create_fp_solver().unwrap();
        let ptr = solver.bv_const(0x1000, 64);
        let permission = solver.bv_const(0, 2); // NoPermission
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::SharedBorrow, &[ptr, permission], 2)
                .unwrap();
        let cond = verify_proof_obligation(&mut solver, &ProofAnnotation::SharedBorrow, &operands)
            .unwrap();
        assert!(!cond.check(&mut solver).expect("the condition checks"));
    }

    #[test]
    fn verify_proof_shared_borrow_symbolic_fails() {
        // symbolic permission can be MutableBorrow or NoPermission => should NOT verify
        let mut solver = create_fp_solver().unwrap();
        let ptr = solver.bv_const(0x1000, 64);
        let sort = Sort::BitVec(BitVecSort { width: 2 });
        let permission = solver.declare_const("perm", sort);
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::SharedBorrow, &[ptr, permission], 2)
                .unwrap();
        let cond = verify_proof_obligation(&mut solver, &ProofAnnotation::SharedBorrow, &operands)
            .unwrap();
        assert!(!cond.check(&mut solver).expect("the condition checks"));
    }

    // ============================================================
    // Integration: BorrowModel + proof obligations
    // ============================================================

    #[test]
    fn borrow_model_valid_borrow_after_init_owned() {
        // Initialize a pointer as Owned, then verify ValidBorrow holds
        let mut solver = create_fp_solver().unwrap();
        let mut model = BorrowModel::new(&mut solver, "perms").expect("the adapter encodes");
        let ptr = solver.bv_const(0x5000, 64);

        // Set permission to Owned
        let owned = solver.bv_const(1, 2);
        model.state = solver.store(model.state, ptr, owned);

        // Read permission back
        let perm = model
            .get_permission(&mut solver, ptr)
            .expect("the adapter encodes");

        // Verify ValidBorrow
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::ValidBorrow, &[ptr, perm], 2).unwrap();
        let cond =
            verify_proof_obligation(&mut solver, &ProofAnnotation::ValidBorrow, &operands).unwrap();
        assert!(cond.check(&mut solver).expect("the condition checks"));
    }

    #[test]
    fn borrow_model_shared_borrow_readable_after_borrow() {
        // After a shared borrow, SharedBorrow proof obligation should hold
        let mut solver = create_fp_solver().unwrap();
        let mut model = BorrowModel::new(&mut solver, "perms").expect("the adapter encodes");
        let ptr = solver.bv_const(0x6000, 64);

        // Set permission to Owned, then borrow
        let owned = solver.bv_const(1, 2);
        model.state = solver.store(model.state, ptr, owned);
        model
            .encode_borrow(&mut solver, ptr)
            .expect("the adapter encodes");

        // Read permission (should be SharedBorrow(2))
        let perm = model
            .get_permission(&mut solver, ptr)
            .expect("the adapter encodes");

        // Verify SharedBorrow
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::SharedBorrow, &[ptr, perm], 2).unwrap();
        let cond = verify_proof_obligation(&mut solver, &ProofAnnotation::SharedBorrow, &operands)
            .unwrap();
        assert!(cond.check(&mut solver).expect("the condition checks"));
    }

    // ============================================================
    // Integration: ArcModel + is_unique verification
    // ============================================================

    #[test]
    fn arc_model_is_unique_after_single_retain() {
        let mut solver = create_fp_solver().unwrap();
        let mut model = ArcModel::new(&mut solver, "refcounts").expect("the adapter encodes");
        let ptr = solver.bv_const(0x7000, 64);

        // Set refcount to 0, then retain once
        let zero = solver.bv_const(0, 32);
        model.state = solver.store(model.state, ptr, zero);
        model
            .encode_retain(&mut solver, ptr)
            .expect("the adapter encodes");

        // Should be unique (refcount == 1)
        let is_unique = model
            .encode_is_unique(&mut solver, ptr)
            .expect("the adapter encodes");
        solver.assert_term(is_unique);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn arc_model_not_unique_after_two_retains() {
        let mut solver = create_fp_solver().unwrap();
        let mut model = ArcModel::new(&mut solver, "refcounts").expect("the adapter encodes");
        let ptr = solver.bv_const(0x7000, 64);

        // Set refcount to 0, retain twice
        let zero = solver.bv_const(0, 32);
        model.state = solver.store(model.state, ptr, zero);
        model
            .encode_retain(&mut solver, ptr)
            .expect("the adapter encodes");
        model
            .encode_retain(&mut solver, ptr)
            .expect("the adapter encodes");

        // Should NOT be unique (refcount == 2)
        let is_unique = model
            .encode_is_unique(&mut solver, ptr)
            .expect("the adapter encodes");
        solver.assert_term(is_unique);
        assert!(solver.check_sat().is_unsat());
    }

    // ============================================================
    // Compound type encoding tests (ty_to_sort)
    // ============================================================

    #[test]
    fn ty_to_sort_unit() {
        let sort = ty_to_sort(&Ty::Unit).unwrap();
        match sort {
            Sort::Datatype(dt) => {
                assert_eq!(dt.name, "Unit");
                assert_eq!(dt.constructors.len(), 1);
                assert_eq!(dt.constructors[0].name, "Unit_mk");
                assert!(dt.constructors[0].fields.is_empty());
            }
            other => panic!("expected Datatype sort for Unit, got {:?}", other),
        }
    }

    #[test]
    fn ty_to_sort_empty_tuple() {
        let sort = ty_to_sort(&Ty::Tuple(vec![])).unwrap();
        match sort {
            Sort::Datatype(dt) => {
                assert_eq!(dt.name, "Tuple0");
                assert_eq!(dt.constructors.len(), 1);
                assert!(dt.constructors[0].fields.is_empty());
            }
            other => panic!("expected Datatype sort for empty tuple, got {:?}", other),
        }
    }

    #[test]
    fn ty_to_sort_pair_tuple() {
        let sort = ty_to_sort(&Ty::Tuple(vec![Ty::I32, Ty::Bool])).unwrap();
        match sort {
            Sort::Datatype(dt) => {
                assert_eq!(dt.name, "Tuple2");
                assert_eq!(dt.constructors.len(), 1);
                assert_eq!(dt.constructors[0].name, "Tuple2_mk");
                assert_eq!(dt.constructors[0].fields.len(), 2);
                assert_eq!(dt.constructors[0].fields[0].name, "_0");
                assert_eq!(
                    dt.constructors[0].fields[0].sort,
                    Sort::BitVec(BitVecSort { width: 32 })
                );
                assert_eq!(dt.constructors[0].fields[1].name, "_1");
                assert_eq!(
                    dt.constructors[0].fields[1].sort,
                    Sort::BitVec(BitVecSort { width: 1 })
                );
            }
            other => panic!("expected Datatype sort for pair tuple, got {:?}", other),
        }
    }

    #[test]
    fn ty_to_sort_triple_tuple() {
        let sort = ty_to_sort(&Ty::Tuple(vec![Ty::I64, Ty::F32, Ty::U8])).unwrap();
        match sort {
            Sort::Datatype(dt) => {
                assert_eq!(dt.name, "Tuple3");
                assert_eq!(dt.constructors[0].fields.len(), 3);
                assert_eq!(
                    dt.constructors[0].fields[0].sort,
                    Sort::BitVec(BitVecSort { width: 64 })
                );
                assert_eq!(
                    dt.constructors[0].fields[1].sort,
                    Sort::FloatingPoint(8, 24)
                );
                assert_eq!(
                    dt.constructors[0].fields[2].sort,
                    Sort::BitVec(BitVecSort { width: 8 })
                );
            }
            other => panic!("expected Datatype sort for triple tuple, got {:?}", other),
        }
    }

    #[test]
    fn ty_to_sort_nested_tuple() {
        // (i32, (bool, u64))
        let inner = Ty::Tuple(vec![Ty::Bool, Ty::U64]);
        let sort = ty_to_sort(&Ty::Tuple(vec![Ty::I32, inner])).unwrap();
        match sort {
            Sort::Datatype(dt) => {
                assert_eq!(dt.name, "Tuple2");
                // Second field should be a nested Datatype
                match &dt.constructors[0].fields[1].sort {
                    Sort::Datatype(inner_dt) => {
                        assert_eq!(inner_dt.name, "Tuple2");
                        assert_eq!(inner_dt.constructors[0].fields.len(), 2);
                    }
                    other => panic!("expected nested Datatype, got {:?}", other),
                }
            }
            other => panic!("expected Datatype sort, got {:?}", other),
        }
    }

    #[test]
    fn ty_to_sort_tuple_with_unsupported_element_fails() {
        // Tuple containing Never should fail (Never is unsupported)
        let result = ty_to_sort(&Ty::Tuple(vec![Ty::I32, Ty::Never]));
        assert!(result.is_err());
    }

    #[test]
    fn ty_to_sort_struct() {
        use trust_ir::value::StructId;
        let sort = ty_to_sort(&Ty::Struct(StructId::new(42))).unwrap();
        match sort {
            Sort::Uninterpreted(name) => assert_eq!(name, "struct_42"),
            other => panic!("expected Uninterpreted sort for struct, got {:?}", other),
        }
    }

    #[test]
    fn ty_to_sort_array() {
        use trust_ir::value::TyId;
        let sort = ty_to_sort(&Ty::Array(TyId::new(3), 10)).unwrap();
        match sort {
            Sort::Uninterpreted(name) => assert_eq!(name, "array_3_10"),
            other => panic!("expected Uninterpreted sort for array, got {:?}", other),
        }
    }

    #[test]
    fn ty_to_sort_enum() {
        use trust_ir::value::EnumId;
        let sort = ty_to_sort(&Ty::Enum(EnumId::new(7))).unwrap();
        match sort {
            Sort::Uninterpreted(name) => assert_eq!(name, "enum_7"),
            other => panic!("expected Uninterpreted sort for enum, got {:?}", other),
        }
    }

    // ============================================================
    // New proof annotation tests
    // ============================================================

    #[test]
    fn verify_proof_pure_constant_same_results() {
        // Two identical constant results => Pure should verify
        let mut solver = create_bv_solver().unwrap();
        let r1 = solver.bv_const(42, 32);
        let r2 = solver.bv_const(42, 32);
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::Pure, &[r1, r2], 32).unwrap();
        let cond = verify_proof_obligation(&mut solver, &ProofAnnotation::Pure, &operands).unwrap();
        assert!(cond.check(&mut solver).expect("the condition checks"));
    }

    #[test]
    fn verify_proof_pure_different_results_fails() {
        // Two different constant results => Pure should NOT verify
        let mut solver = create_bv_solver().unwrap();
        let r1 = solver.bv_const(42, 32);
        let r2 = solver.bv_const(43, 32);
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::Pure, &[r1, r2], 32).unwrap();
        let cond = verify_proof_obligation(&mut solver, &ProofAnnotation::Pure, &operands).unwrap();
        assert!(!cond.check(&mut solver).expect("the condition checks"));
    }

    #[test]
    fn verify_proof_deterministic_same_as_pure() {
        // Deterministic uses the same encoding as Pure
        let mut solver = create_bv_solver().unwrap();
        let r1 = solver.bv_const(10, 32);
        let r2 = solver.bv_const(10, 32);
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::Deterministic, &[r1, r2], 32).unwrap();
        let cond = verify_proof_obligation(&mut solver, &ProofAnnotation::Deterministic, &operands)
            .unwrap();
        assert!(cond.check(&mut solver).expect("the condition checks"));
    }

    #[test]
    fn verify_proof_commutative_add() {
        // Addition is commutative: a+b == b+a for all a,b
        let mut solver = create_bv_solver().unwrap();
        let sort = Sort::BitVec(BitVecSort { width: 32 });
        let a = solver.declare_const("a", sort.clone());
        let b = solver.declare_const("b", sort);
        let ab = encode_binop(&mut solver, BinOp::Add, a, b).unwrap();
        let ba = encode_binop(&mut solver, BinOp::Add, b, a).unwrap();
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::Commutative, &[ab, ba], 32).unwrap();
        let cond =
            verify_proof_obligation(&mut solver, &ProofAnnotation::Commutative, &operands).unwrap();
        assert!(cond.check(&mut solver).expect("the condition checks"));
    }

    #[test]
    fn verify_proof_commutative_sub_fails() {
        // Subtraction is NOT commutative: a-b != b-a in general
        let mut solver = create_bv_solver().unwrap();
        let sort = Sort::BitVec(BitVecSort { width: 32 });
        let a = solver.declare_const("a", sort.clone());
        let b = solver.declare_const("b", sort);
        let ab = encode_binop(&mut solver, BinOp::Sub, a, b).unwrap();
        let ba = encode_binop(&mut solver, BinOp::Sub, b, a).unwrap();
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::Commutative, &[ab, ba], 32).unwrap();
        let cond =
            verify_proof_obligation(&mut solver, &ProofAnnotation::Commutative, &operands).unwrap();
        assert!(!cond.check(&mut solver).expect("the condition checks"));
    }

    #[test]
    fn verify_proof_associative_add() {
        // Addition is associative: (a+b)+c == a+(b+c) for all a,b,c
        let mut solver = create_bv_solver().unwrap();
        let sort = Sort::BitVec(BitVecSort { width: 32 });
        let a = solver.declare_const("a", sort.clone());
        let b = solver.declare_const("b", sort.clone());
        let c = solver.declare_const("c", sort);
        let ab = encode_binop(&mut solver, BinOp::Add, a, b).unwrap();
        let left = encode_binop(&mut solver, BinOp::Add, ab, c).unwrap();
        let bc = encode_binop(&mut solver, BinOp::Add, b, c).unwrap();
        let right = encode_binop(&mut solver, BinOp::Add, a, bc).unwrap();
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::Associative, &[left, right], 32)
                .unwrap();
        let cond =
            verify_proof_obligation(&mut solver, &ProofAnnotation::Associative, &operands).unwrap();
        assert!(cond.check(&mut solver).expect("the condition checks"));
    }

    #[test]
    fn verify_proof_associative_sub_fails() {
        // Subtraction is NOT associative: (a-b)-c != a-(b-c) in general
        let mut solver = create_bv_solver().unwrap();
        let sort = Sort::BitVec(BitVecSort { width: 32 });
        let a = solver.declare_const("a", sort.clone());
        let b = solver.declare_const("b", sort.clone());
        let c = solver.declare_const("c", sort);
        let ab = encode_binop(&mut solver, BinOp::Sub, a, b).unwrap();
        let left = encode_binop(&mut solver, BinOp::Sub, ab, c).unwrap();
        let bc = encode_binop(&mut solver, BinOp::Sub, b, c).unwrap();
        let right = encode_binop(&mut solver, BinOp::Sub, a, bc).unwrap();
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::Associative, &[left, right], 32)
                .unwrap();
        let cond =
            verify_proof_obligation(&mut solver, &ProofAnnotation::Associative, &operands).unwrap();
        assert!(!cond.check(&mut solver).expect("the condition checks"));
    }

    #[test]
    fn verify_proof_no_alias_distinct_constant_ptrs() {
        // Two distinct constant pointers => NoAlias should verify
        let mut solver = create_bv_solver().unwrap();
        let p1 = solver.bv_const(0x1000, 64);
        let p2 = solver.bv_const(0x2000, 64);
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::NoAlias, &[p1, p2], 64).unwrap();
        let cond =
            verify_proof_obligation(&mut solver, &ProofAnnotation::NoAlias, &operands).unwrap();
        assert!(cond.check(&mut solver).expect("the condition checks"));
    }

    #[test]
    fn verify_proof_no_alias_same_ptr_fails() {
        // Same pointer address => NoAlias should NOT verify
        let mut solver = create_bv_solver().unwrap();
        let p = solver.bv_const(0x1000, 64);
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::NoAlias, &[p, p], 64).unwrap();
        let cond =
            verify_proof_obligation(&mut solver, &ProofAnnotation::NoAlias, &operands).unwrap();
        assert!(!cond.check(&mut solver).expect("the condition checks"));
    }

    #[test]
    fn verify_proof_no_alias_symbolic_fails() {
        // Symbolic pointers CAN alias => NoAlias should NOT verify
        let mut solver = create_bv_solver().unwrap();
        let sort = Sort::BitVec(BitVecSort { width: 64 });
        let p1 = solver.declare_const("p1", sort.clone());
        let p2 = solver.declare_const("p2", sort);
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::NoAlias, &[p1, p2], 64).unwrap();
        let cond =
            verify_proof_obligation(&mut solver, &ProofAnnotation::NoAlias, &operands).unwrap();
        assert!(!cond.check(&mut solver).expect("the condition checks"));
    }

    #[test]
    fn verify_proof_aligned_constant_16() {
        // ptr = 0x1000 is 16-byte aligned (0x1000 % 16 == 0)
        let mut solver = create_bv_solver().unwrap();
        let ptr = solver.bv_const(0x1000, 64);
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::Aligned(16), &[ptr], 64).unwrap();
        let cond =
            verify_proof_obligation(&mut solver, &ProofAnnotation::Aligned(16), &operands).unwrap();
        assert!(cond.check(&mut solver).expect("the condition checks"));
    }

    #[test]
    fn verify_proof_aligned_constant_not_aligned() {
        // ptr = 0x1001 is NOT 16-byte aligned
        let mut solver = create_bv_solver().unwrap();
        let ptr = solver.bv_const(0x1001, 64);
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::Aligned(16), &[ptr], 64).unwrap();
        let cond =
            verify_proof_obligation(&mut solver, &ProofAnnotation::Aligned(16), &operands).unwrap();
        assert!(!cond.check(&mut solver).expect("the condition checks"));
    }

    #[test]
    fn verify_proof_aligned_symbolic_fails() {
        // Symbolic pointer is not necessarily aligned
        let mut solver = create_bv_solver().unwrap();
        let sort = Sort::BitVec(BitVecSort { width: 64 });
        let ptr = solver.declare_const("ptr", sort);
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::Aligned(8), &[ptr], 64).unwrap();
        let cond =
            verify_proof_obligation(&mut solver, &ProofAnnotation::Aligned(8), &operands).unwrap();
        assert!(!cond.check(&mut solver).expect("the condition checks"));
    }

    #[test]
    fn verify_proof_no_panic_constant_true() {
        // safe = true => NoPanic should verify
        let mut solver = create_bv_solver().unwrap();
        let safe = solver.bool_const(true);
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::NoPanic, &[safe], 1).unwrap();
        let cond =
            verify_proof_obligation(&mut solver, &ProofAnnotation::NoPanic, &operands).unwrap();
        assert!(cond.check(&mut solver).expect("the condition checks"));
    }

    #[test]
    fn verify_proof_no_panic_constant_false_fails() {
        // safe = false => NoPanic should NOT verify
        let mut solver = create_bv_solver().unwrap();
        let safe = solver.bool_const(false);
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::NoPanic, &[safe], 1).unwrap();
        let cond =
            verify_proof_obligation(&mut solver, &ProofAnnotation::NoPanic, &operands).unwrap();
        assert!(!cond.check(&mut solver).expect("the condition checks"));
    }

    #[test]
    fn verify_proof_no_undef_constant_true() {
        // is_defined = true => NoUndef should verify
        let mut solver = create_bv_solver().unwrap();
        let defined = solver.bool_const(true);
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::NoUndef, &[defined], 1).unwrap();
        let cond =
            verify_proof_obligation(&mut solver, &ProofAnnotation::NoUndef, &operands).unwrap();
        assert!(cond.check(&mut solver).expect("the condition checks"));
    }

    #[test]
    fn verify_proof_no_undef_constant_false_fails() {
        // is_defined = false => NoUndef should NOT verify
        let mut solver = create_bv_solver().unwrap();
        let defined = solver.bool_const(false);
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::NoUndef, &[defined], 1).unwrap();
        let cond =
            verify_proof_obligation(&mut solver, &ProofAnnotation::NoUndef, &operands).unwrap();
        assert!(!cond.check(&mut solver).expect("the condition checks"));
    }

    #[test]
    fn verify_proof_valid_dealloc_owned() {
        // permission = Owned(1) => ValidDealloc should verify
        let mut solver = create_fp_solver().unwrap();
        let ptr = solver.bv_const(0x1000, 64);
        let permission = solver.bv_const(1, 2); // Owned
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::ValidDealloc, &[ptr, permission], 2)
                .unwrap();
        let cond = verify_proof_obligation(&mut solver, &ProofAnnotation::ValidDealloc, &operands)
            .unwrap();
        assert!(cond.check(&mut solver).expect("the condition checks"));
    }

    #[test]
    fn verify_proof_valid_dealloc_shared_fails() {
        // permission = SharedBorrow(2) => ValidDealloc should NOT verify
        let mut solver = create_fp_solver().unwrap();
        let ptr = solver.bv_const(0x1000, 64);
        let permission = solver.bv_const(2, 2); // SharedBorrow
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::ValidDealloc, &[ptr, permission], 2)
                .unwrap();
        let cond = verify_proof_obligation(&mut solver, &ProofAnnotation::ValidDealloc, &operands)
            .unwrap();
        assert!(!cond.check(&mut solver).expect("the condition checks"));
    }

    #[test]
    fn verify_proof_valid_dealloc_symbolic_fails() {
        // Symbolic permission can be non-Owned => should NOT verify
        let mut solver = create_fp_solver().unwrap();
        let ptr = solver.bv_const(0x1000, 64);
        let sort = Sort::BitVec(BitVecSort { width: 2 });
        let permission = solver.declare_const("perm", sort);
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::ValidDealloc, &[ptr, permission], 2)
                .unwrap();
        let cond = verify_proof_obligation(&mut solver, &ProofAnnotation::ValidDealloc, &operands)
            .unwrap();
        assert!(!cond.check(&mut solver).expect("the condition checks"));
    }

    // ============================================================
    // Integration: verify_and_certify with new annotations
    // ============================================================

    #[test]
    fn verify_and_certify_aligned_verified() {
        let mut solver = create_bv_solver().unwrap();
        let ptr = solver.bv_const(0x1000, 64);
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::Aligned(16), &[ptr], 64).unwrap();
        let result = verify_and_certify(
            &mut solver,
            &ProofAnnotation::Aligned(16),
            &operands,
            ProofId::new(10),
        )
        .unwrap();
        assert!(result.is_proved_by_solver());
        assert_eq!(result.status(), ProofStatus::Pending);
    }

    #[test]
    fn verify_and_certify_no_alias_refuted() {
        // Symbolic pointers can alias => refuted
        let mut solver = create_bv_solver().unwrap();
        let sort = Sort::BitVec(BitVecSort { width: 64 });
        let p1 = solver.declare_const("p1", sort.clone());
        let p2 = solver.declare_const("p2", sort);
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::NoAlias, &[p1, p2], 64).unwrap();
        let result = verify_and_certify(
            &mut solver,
            &ProofAnnotation::NoAlias,
            &operands,
            ProofId::new(11),
        )
        .unwrap();
        assert_eq!(result.status(), ProofStatus::Failed);
    }

    #[test]
    fn verify_and_certify_commutative_xor_verified() {
        // XOR is commutative
        let mut solver = create_bv_solver().unwrap();
        let sort = Sort::BitVec(BitVecSort { width: 32 });
        let a = solver.declare_const("a", sort.clone());
        let b = solver.declare_const("b", sort);
        let ab = encode_binop(&mut solver, BinOp::Xor, a, b).unwrap();
        let ba = encode_binop(&mut solver, BinOp::Xor, b, a).unwrap();
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::Commutative, &[ab, ba], 32).unwrap();
        let result = verify_and_certify(
            &mut solver,
            &ProofAnnotation::Commutative,
            &operands,
            ProofId::new(12),
        )
        .unwrap();
        assert!(result.is_proved_by_solver());
        assert_eq!(result.status(), ProofStatus::Pending);
    }
}

/// Encode integer (or boolean `Not`) unary operations independently per lane.
/// Lane zero occupies the least-significant bits. Shape and operand width are
/// checked before extraction; float lanes require a separate IEEE lane model.
pub fn encode_vector_unop(
    solver: &mut Solver,
    op: UnOp,
    elem_ty: &Ty,
    lane_count: u32,
    operand: Term,
) -> Result<Term, AYError> {
    let unsupported =
        || AYError::UnsupportedType(Ty::Vector(Box::new(elem_ty.clone()), lane_count));
    if !(elem_ty.is_integer() || (*elem_ty == Ty::Bool && op == UnOp::Not)) {
        return Err(unsupported());
    }
    let elem_width = ty_to_sort(elem_ty)?
        .bitvec_width()
        .ok_or_else(unsupported)?;
    let total = elem_width.checked_mul(lane_count).ok_or_else(unsupported)?;
    if total == 0 {
        return Err(unsupported());
    }
    if bitvec_width_of(solver, operand, "vector unary operation")? != total {
        return Err(AYError::UnsupportedOp(
            "vector unary operand width does not match its lanes".into(),
        ));
    }
    let mut result = None;
    for lane in 0..lane_count {
        let lo = lane * elem_width;
        let value = solver.try_bvextract(operand, lo + elem_width - 1, lo)?;
        let encoded = encode_unop(solver, op, value)?;
        result = Some(match result {
            None => encoded,
            Some(lower) => solver.try_bvconcat(encoded, lower)?,
        });
    }
    result.ok_or_else(unsupported)
}

/// Encode a vector binary operation.
///
/// Vectors are modeled as concatenated bitvectors: lane_count * elem_width.
/// The operation is applied independently to each lane.
///
/// # Errors
///
/// [`AYError::UnsupportedType`] for a zero-lane vector (it has no bit-vector
/// model — [`ty_to_sort`] refuses it too), for an element type with no bit
/// width, and for a lane count whose concatenated width does not fit a `u32`.
/// Each is refused before any lane is encoded.
pub fn encode_vector_binop(
    solver: &mut Solver,
    op: BinOp,
    elem_ty: &Ty,
    lane_count: u32,
    lhs: Term,
    rhs: Term,
) -> Result<Term, AYError> {
    let unsupported =
        || AYError::UnsupportedType(Ty::Vector(Box::new(elem_ty.clone()), lane_count));
    let elem_width = sort_bit_width(&ty_to_sort(elem_ty)?).ok_or_else(unsupported)?;
    if lane_count == 0 || elem_width == 0 || elem_width.checked_mul(lane_count).is_none() {
        return Err(unsupported());
    }

    // Each lane is concatenated onto the accumulator as soon as it is encoded
    // (little-endian: lane 0 is least significant), so nothing sized by the
    // lane count — an unchecked number from the module — is allocated up front.
    let mut result: Option<Term> = None;
    for i in 0..lane_count {
        let lo = i.checked_mul(elem_width).ok_or_else(unsupported)?;
        let hi = lo.checked_add(elem_width - 1).ok_or_else(unsupported)?;

        let l_lane = solver.try_bvextract(lhs, hi, lo)?;
        let r_lane = solver.try_bvextract(rhs, hi, lo)?;

        let res_lane = encode_binop(solver, op, l_lane, r_lane)?;
        result = Some(match result {
            None => res_lane,
            Some(lower) => solver.try_bvconcat(res_lane, lower)?,
        });
    }

    result.ok_or_else(unsupported)
}

#[cfg(test)]
mod vector_tests {
    #![allow(clippy::disallowed_methods)] // tests drive ay directly (r11 item 5)

    use super::*;

    #[test]
    fn integer_vector_unops_keep_lane_boundaries() {
        for (elem, width, lanes) in [
            (Ty::U8, 8u32, 4u32),
            (Ty::U16, 16, 8),
            (Ty::U32, 32, 4),
            (Ty::U64, 64, 2),
        ] {
            let mask = (1u128 << width) - 1;
            let raw = 0xff01_8000_00ff_0001_0100_ffff_8000_0001u128;
            for op in [
                UnOp::Neg,
                UnOp::Not,
                UnOp::CtPop,
                UnOp::CtLz,
                UnOp::CtTz,
                UnOp::BSwap,
                UnOp::BitReverse,
            ] {
                let mut expected = 0u128;
                for lane in 0..lanes {
                    let value = (raw >> (lane * width)) & mask;
                    let count = match op {
                        UnOp::Neg => value.wrapping_neg() & mask,
                        UnOp::Not => !value & mask,
                        UnOp::CtPop => u128::from(value.count_ones()),
                        UnOp::CtLz => u128::from(value.leading_zeros() - (128 - width)),
                        UnOp::CtTz => {
                            if value == 0 {
                                u128::from(width)
                            } else {
                                u128::from(value.trailing_zeros())
                            }
                        }
                        UnOp::BSwap => (0..width / 8)
                            .fold(0, |acc, byte| (acc << 8) | ((value >> (8 * byte)) & 255)),
                        UnOp::BitReverse => value.reverse_bits() >> (128 - width),
                        _ => unreachable!(),
                    };
                    expected |= count << (lane * width);
                }
                let mut solver = create_bv_solver().unwrap();
                let total = width * lanes;
                let x = solver.declare_const("x", Sort::BitVec(BitVecSort { width: total }));
                let mut packed = |raw: u128| {
                    let hi = solver.bv_const_u64((raw >> 64) as u64, 64);
                    let lo = solver.bv_const_u64(raw as u64, 64);
                    let wide = solver.bvconcat(hi, lo);
                    solver.bvextract(wide, total - 1, 0)
                };
                let value = packed(raw);
                let want = packed(expected);
                let pin = solver.eq(x, value);
                solver.assert_term(pin);
                let got = encode_vector_unop(&mut solver, op, &elem, lanes, x).unwrap();
                let equal = solver.eq(got, want);
                let wrong = solver.not(equal);
                solver.assert_term(wrong);
                assert!(solver.check_sat().is_unsat(), "{op:?} <{lanes} x {elem}>");
            }
        }
    }

    #[test]
    fn vector_unop_rejects_bad_shapes_and_widths() {
        let mut solver = create_bv_solver().unwrap();
        let x = solver.bv_const(0, 32);
        for (elem, lanes) in [
            (Ty::U8, 0),
            (Ty::U64, u32::MAX),
            (Ty::F32, 1),
            (Ty::Bool, 4),
        ] {
            assert!(matches!(
                encode_vector_unop(&mut solver, UnOp::CtPop, &elem, lanes, x),
                Err(AYError::UnsupportedType(_))
            ));
        }
        for width in [24, 40] {
            let wrong = solver.bv_const(0, width);
            assert!(matches!(
                encode_vector_unop(&mut solver, UnOp::CtPop, &Ty::U8, 4, wrong),
                Err(AYError::UnsupportedOp(_))
            ));
        }
        let input = solver.bv_const(5, 4);
        let got = encode_vector_unop(&mut solver, UnOp::Not, &Ty::Bool, 4, input).unwrap();
        let want = solver.bv_const(10, 4);
        let eq = solver.eq(got, want);
        let wrong = solver.not(eq);
        solver.assert_term(wrong);
        assert!(solver.check_sat().is_unsat());
    }

    #[test]
    fn sort_bit_width_is_checked_on_the_open_float_sort() {
        assert_eq!(
            sort_bit_width(&Sort::BitVec(BitVecSort { width: 7 })),
            Some(7)
        );
        assert_eq!(sort_bit_width(&Sort::FloatingPoint(5, 11)), Some(16));
        assert_eq!(sort_bit_width(&Sort::FloatingPoint(8, 24)), Some(32));
        assert_eq!(sort_bit_width(&Sort::FloatingPoint(11, 53)), Some(64));
        // ay's sort admits any pair; one whose sum overflows has no width.
        assert_eq!(sort_bit_width(&Sort::FloatingPoint(u32::MAX, 1)), None);
        assert_eq!(sort_bit_width(&memory_sort()), None);
        // The float sorts `ty_to_sort` produces are their IEEE storage widths.
        for (ty, bits) in [(Ty::F16, 16), (Ty::F32, 32), (Ty::F64, 64)] {
            assert_eq!(sort_bit_width(&ty_to_sort(&ty).unwrap()), Some(bits));
        }
    }

    #[test]
    fn a_vector_wider_than_a_u32_bit_width_has_no_sort() {
        // u32::MAX lanes of 64 bits: the concatenated width wrapped in release.
        let wide = Ty::Vector(Box::new(Ty::I64), u32::MAX);
        assert!(matches!(ty_to_sort(&wide), Err(AYError::UnsupportedType(t)) if t == wide));
        let wide_float = Ty::Vector(Box::new(Ty::F64), u32::MAX);
        assert!(matches!(
            ty_to_sort(&wide_float),
            Err(AYError::UnsupportedType(_))
        ));
        // The widest representable one still maps.
        let fits = Ty::Vector(Box::new(Ty::I8), u32::MAX / 8);
        assert_eq!(
            ty_to_sort(&fits).unwrap(),
            Sort::BitVec(BitVecSort {
                width: (u32::MAX / 8) * 8
            })
        );
    }

    #[test]
    fn a_zero_lane_vector_binop_is_refused_not_an_index_panic() {
        let mut solver = create_bv_solver().unwrap();
        let sort = Sort::BitVec(BitVecSort { width: 32 });
        let lhs = solver.declare_const("lhs", sort.clone());
        let rhs = solver.declare_const("rhs", sort);
        let error =
            encode_vector_binop(&mut solver, BinOp::Add, &Ty::I32, 0, lhs, rhs).unwrap_err();
        assert!(matches!(error, AYError::UnsupportedType(Ty::Vector(_, 0))));
    }

    #[test]
    fn a_vector_binop_wider_than_a_u32_bit_width_is_refused_before_any_lane() {
        let mut solver = create_bv_solver().unwrap();
        let sort = Sort::BitVec(BitVecSort { width: 64 });
        let lhs = solver.declare_const("lhs", sort.clone());
        let rhs = solver.declare_const("rhs", sort);
        let error =
            encode_vector_binop(&mut solver, BinOp::Add, &Ty::I64, u32::MAX, lhs, rhs).unwrap_err();
        assert!(matches!(error, AYError::UnsupportedType(Ty::Vector(_, n)) if n == u32::MAX));
    }

    #[test]
    fn test_encode_vector_binop_add() {
        let mut solver = create_bv_solver().unwrap();
        // <2 x i32>
        let elem_ty = Ty::I32;
        let lane_count = 2;
        let vec_sort = Sort::BitVec(BitVecSort { width: 64 });

        let lhs = solver.declare_const("lhs", vec_sort.clone());
        let rhs = solver.declare_const("rhs", vec_sort);

        let res =
            encode_vector_binop(&mut solver, BinOp::Add, &elem_ty, lane_count, lhs, rhs).unwrap();

        // Assert that (lhs[31:0] + rhs[31:0]) == res[31:0]
        let l0 = solver.bvextract(lhs, 31, 0);
        let r0 = solver.bvextract(rhs, 31, 0);
        let res0 = solver.bvextract(res, 31, 0);
        let expected0 = solver.bvadd(l0, r0);
        let eq0 = solver.eq(res0, expected0);
        solver.assert_term(eq0);

        // Assert that (lhs[63:32] + rhs[63:32]) == res[63:32]
        let l1 = solver.bvextract(lhs, 63, 32);
        let r1 = solver.bvextract(rhs, 63, 32);
        let res1 = solver.bvextract(res, 63, 32);
        let expected1 = solver.bvadd(l1, r1);
        let eq1 = solver.eq(res1, expected1);
        solver.assert_term(eq1);

        assert!(solver.check_sat().is_sat());
    }
}

#[cfg(test)]
mod fp_integer_cast_tests {
    #![allow(clippy::disallowed_methods)]
    use super::*;

    fn input(value: f64, width: u32) -> (u64, u32, u32, f64) {
        match width {
            16 => {
                let bits = trust_ir::interpret::f64_to_f16_bits(value);
                (
                    u64::from(bits),
                    5,
                    11,
                    trust_ir::interpret::f16_bits_to_f64(bits),
                )
            }
            32 => (
                u64::from((value as f32).to_bits()),
                8,
                24,
                f64::from(value as f32),
            ),
            64 => (value.to_bits(), 11, 53, value),
            _ => unreachable!(),
        }
    }

    fn expected(value: f64, width: u32, signed: bool) -> u128 {
        let raw = if signed {
            (match width {
                8 => i128::from(value as i8),
                16 => i128::from(value as i16),
                32 => i128::from(value as i32),
                64 => i128::from(value as i64),
                128 => value as i128,
                _ => unreachable!(),
            }) as u128
        } else {
            match width {
                8 => u128::from(value as u8),
                16 => u128::from(value as u16),
                32 => u128::from(value as u32),
                64 => u128::from(value as u64),
                128 => value as u128,
                _ => unreachable!(),
            }
        };
        if width == 128 {
            raw
        } else {
            raw & ((1u128 << width) - 1)
        }
    }

    #[test]
    fn fp_to_integer_casts_match_rust_values_and_boundaries() {
        let mut checks = 0;
        for source in [16, 32, 64] {
            for width in [8u32, 16, 32, 64, 128] {
                for signed in [false, true] {
                    let exponent = width - u32::from(signed);
                    let upper = 2.0f64.powi(exponent as i32);
                    let lower = if signed { -upper } else { 0.0 };
                    let mut samples = vec![
                        0.0,
                        -0.0,
                        0.75,
                        -0.75,
                        1.5,
                        -1.5,
                        1.75,
                        -1.75,
                        2.5,
                        -2.5,
                        127.75,
                        -127.75,
                        -128.5,
                        255.75,
                        65504.0,
                        65520.0,
                        f64::INFINITY,
                        f64::NEG_INFINITY,
                        f64::NAN,
                        -f64::NAN,
                        2.0f64.powi(-24),
                        -2.0f64.powi(-24),
                        f64::MAX,
                        -f64::MAX,
                    ];
                    for bound in [lower, upper] {
                        for offset in [-1i64, 0, 1] {
                            samples
                                .push(f64::from_bits(bound.to_bits().wrapping_add_signed(offset)));
                            // Adjacent F64 inputs can round to the same F16/F32.
                            // Also probe each source format's own neighbors.
                            let source_bits = input(bound, source).0;
                            samples.push(match source {
                                16 => trust_ir::interpret::f16_bits_to_f64(
                                    (source_bits as u16).wrapping_add_signed(offset as i16),
                                ),
                                32 => f64::from(f32::from_bits(
                                    (source_bits as u32).wrapping_add_signed(offset as i32),
                                )),
                                64 => f64::from_bits(source_bits.wrapping_add_signed(offset)),
                                _ => unreachable!(),
                            });
                        }
                    }
                    for value in samples {
                        let (bits, eb, sb, value) = input(value, source);
                        for saturating in [false, true] {
                            if !saturating
                                && (!value.is_finite() || value < lower || value >= upper)
                            {
                                continue;
                            }
                            let op = match (signed, saturating) {
                                (false, false) => CastOp::FPToUI,
                                (true, false) => CastOp::FPToSI,
                                (false, true) => CastOp::FPToUISat,
                                (true, true) => CastOp::FPToSISat,
                            };
                            let mut solver = create_fp_solver().unwrap();
                            let operand = solver.fp_const_from_bits(bits, eb, sb);
                            let result =
                                encode_cast(&mut solver, op, operand, source, width).unwrap();
                            assert_eq!(
                                solver.try_term_sort(result).unwrap().bitvec_width(),
                                Some(width)
                            );
                            let raw = expected(value, width, signed);
                            let hi = solver.bv_const_u64((raw >> 64) as u64, 64);
                            let lo = solver.bv_const_u64(raw as u64, 64);
                            let wide = solver.bvconcat(hi, lo);
                            let want = solver.bvextract(wide, width - 1, 0);
                            let eq = solver.eq(result, want);
                            let wrong = solver.not(eq);
                            solver.assert_term(wrong);
                            assert!(
                                solver.check_sat().is_unsat(),
                                "{op:?} f{source} {value:?} -> {width}"
                            );
                            checks += 1;
                        }
                    }
                }
            }
        }
        eprintln!("{checks} FP-to-integer numeric queries passed");
    }

    #[test]
    fn saturating_fp_cast_refuses_invalid_width_sort_and_foreign_handle() {
        let mut solver = create_fp_solver().unwrap();
        let fp = solver.fp_const_from_bits(1.75f64.to_bits(), 11, 53);
        let bv = solver.bv_const(1, 32);
        for op in [CastOp::FPToSISat, CastOp::FPToUISat] {
            for width in [0, 129, u32::MAX] {
                assert!(matches!(
                    encode_cast(&mut solver, op, fp, 64, width),
                    Err(AYError::UnsupportedOp(_))
                ));
            }
            assert!(matches!(
                encode_cast(&mut solver, op, bv, 32, 32),
                Err(AYError::UnsupportedOp(_))
            ));
            let mut other = create_fp_solver().unwrap();
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                encode_cast(&mut other, op, fp, 64, 32)
            }));
            assert!(matches!(result.unwrap(), Err(AYError::SolverError(_))));
        }
    }
}
