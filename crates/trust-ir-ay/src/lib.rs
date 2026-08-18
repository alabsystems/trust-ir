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
//! | Binary ops | `encode_binop` | `BinOp` (13 integer variants) |
//! | Comparisons | `encode_icmp` | `ICmpOp` (10 variants) |
//! | Unary ops | `encode_unop` | `UnOp` (Not, Neg; CtPop unsupported) |
//! | Casts | `encode_cast` | `CastOp` (Trunc, ZExt, SExt) |
//! | Overflow | `encode_overflow_check` | `OverflowOp` (3 variants) |
//! | Borrows | `BorrowModel` | Borrow/BorrowMut/EndBorrow |
//! | ARC | `ArcModel` | Retain/Release/IsUnique |
//! | Proofs | `verify_proof_obligation` | `ProofAnnotation` |

use ay::{
    ArraySort, BitVecSort, DatatypeConstructor, DatatypeField, DatatypeSort, Logic, Solver, Sort,
    Term,
};

pub mod bvblast;
pub use bvblast::{
    BVBLAST_ALLOWED_KINDS, BVBLAST_CERT_SCHEMA, BVBLAST_PROVER, BvBlastAttachError,
    BvBlastAttachOutcome, BvBlastAuthority, BvBlastCertPayload, BvBlastCertificate, ProveError,
    attach_bvblast_evidence, certify_obligation, prove, to_bv_expr,
};

pub mod vc;
pub use vc::{
    FunctionVc, VcApplyError, VcCondition, VcObligationOutcome, VcSource, VcVerdict,
    apply_vc_outcomes, generate_function_vc, model_counterexample, verify_function,
};

use trust_ir::inst::{BinOp, CastOp, FCmpOp, ICmpOp, OverflowOp, UnOp};
use trust_ir::proof::{ProofAnnotation, ProofCertificate, ProofEvidence, ProofStatus};
use trust_ir::ty::Ty;
use trust_ir::value::{FuncId, ProofId, ValueId};

/// Errors from ay encoding operations.
#[derive(Debug)]
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
            let elem_bits = match ty_to_sort(elem)? {
                Sort::BitVec(bv) => bv.width,
                Sort::FloatingPoint(eb, sb) => eb + sb,
                _ => return Err(AYError::UnsupportedType(ty.clone())),
            };
            Ok(Sort::BitVec(BitVecSort {
                width: elem_bits * lanes,
            }))
        }
        // Never type (diverging) has no values -- cannot be represented.
        // Func types are not first-class values in BV encoding.
        _ => Err(AYError::UnsupportedType(ty.clone())),
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
    Ok(solver.declare_const(&ay_symbol(func, value), sort))
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
fn rne(solver: &mut Solver) -> Term {
    solver.fp_rounding_mode("RNE")
}

/// Encode a TrustIr `BinOp` as a ay operation.
///
/// Supports all 23 BinOp variants:
/// - 13 integer variants (Add through AShr) use bitvector operations
/// - 3 boolean connectives (BAnd/BOr/BXor) reuse the bitwise BV ops, exact on
///   the 0/1 carrier
/// - 7 float variants (FAdd through FMax) use FP operations with RNE rounding
pub fn encode_binop(solver: &mut Solver, op: BinOp, lhs: Term, rhs: Term) -> Result<Term, AYError> {
    match op {
        BinOp::Add => Ok(solver.bvadd(lhs, rhs)),
        BinOp::Sub => Ok(solver.bvsub(lhs, rhs)),
        BinOp::Mul => Ok(solver.bvmul(lhs, rhs)),
        BinOp::UDiv => Ok(solver.bvudiv(lhs, rhs)),
        BinOp::SDiv => Ok(solver.bvsdiv(lhs, rhs)),
        BinOp::URem => Ok(solver.bvurem(lhs, rhs)),
        BinOp::SRem => Ok(solver.bvsrem(lhs, rhs)),
        BinOp::And => Ok(solver.bvand(lhs, rhs)),
        BinOp::Or => Ok(solver.bvor(lhs, rhs)),
        BinOp::Xor => Ok(solver.bvxor(lhs, rhs)),
        BinOp::Shl => Ok(solver.bvshl(lhs, rhs)),
        BinOp::LShr => Ok(solver.bvlshr(lhs, rhs)),
        BinOp::AShr => Ok(solver.bvashr(lhs, rhs)),
        // Boolean connectives. The operands are the bool 0/1 carrier, encoded
        // here as bitvectors like every other scalar, and on 0/1 the bitwise BV
        // ops agree pointwise with the logical ones -- the same encoding
        // `AYBridge.lean`'s `encodeBinOp` uses, kept identical so the solver and
        // the Lean bridge cannot disagree about the same opcode.
        BinOp::BAnd => Ok(solver.bvand(lhs, rhs)),
        BinOp::BOr => Ok(solver.bvor(lhs, rhs)),
        BinOp::BXor => Ok(solver.bvxor(lhs, rhs)),
        BinOp::FAdd => {
            let rm = rne(solver);
            Ok(solver.fp_add(rm, lhs, rhs))
        }
        BinOp::FSub => {
            let rm = rne(solver);
            Ok(solver.fp_sub(rm, lhs, rhs))
        }
        BinOp::FMul => {
            let rm = rne(solver);
            Ok(solver.fp_mul(rm, lhs, rhs))
        }
        BinOp::FDiv => {
            let rm = rne(solver);
            Ok(solver.fp_div(rm, lhs, rhs))
        }
        BinOp::FRem => {
            // fp.rem does not take a rounding mode
            Ok(solver.fp_rem(lhs, rhs))
        }
        // FMin/FMax are NaN-propagating-away minimum/maximum (not IEEE fp.min/
        // fp.max). They are unsupported in this in-process encoder, like FSqrt
        // and the round family; trust-cg's CLI proof path (trust-cg-verify
        // SmtExpr) models them directly with ite/fp.lt/fp.isNaN.
        BinOp::FMin => Err(AYError::UnsupportedOp("fmin".to_string())),
        BinOp::FMax => Err(AYError::UnsupportedOp("fmax".to_string())),
    }
}

/// Encode a TrustIr `ICmpOp` as a ay bitvector comparison.
///
/// All 10 integer comparison operations are supported.
/// Returns a 1-bit bitvector (Bool sort) in ay.
pub fn encode_icmp(solver: &mut Solver, op: ICmpOp, lhs: Term, rhs: Term) -> Term {
    match op {
        ICmpOp::Eq => solver.eq(lhs, rhs),
        ICmpOp::Ne => {
            let eq = solver.eq(lhs, rhs);
            solver.not(eq)
        }
        ICmpOp::Ult => solver.bvult(lhs, rhs),
        ICmpOp::Ule => solver.bvule(lhs, rhs),
        ICmpOp::Ugt => solver.bvugt(lhs, rhs),
        ICmpOp::Uge => solver.bvuge(lhs, rhs),
        ICmpOp::Slt => solver.bvslt(lhs, rhs),
        ICmpOp::Sle => solver.bvsle(lhs, rhs),
        ICmpOp::Sgt => solver.bvsgt(lhs, rhs),
        ICmpOp::Sge => solver.bvsge(lhs, rhs),
    }
}

/// Encode a TrustIr `UnOp` as a ay unary operation.
///
/// - `Not` -> `bvnot` (bitwise complement)
/// - `Neg` -> `bvneg` (two's complement negation)
/// - `FNeg` -> `fp.neg` (floating-point negation)
/// - `CtPop` -> unsupported until ay exposes a bitvector popcount operator
pub fn encode_unop(solver: &mut Solver, op: UnOp, operand: Term) -> Result<Term, AYError> {
    match op {
        UnOp::Not => Ok(solver.bvnot(operand)),
        UnOp::Neg => Ok(solver.bvneg(operand)),
        UnOp::FNeg => Ok(solver.fp_neg(operand)),
        UnOp::FAbs => Ok(solver.fp_abs(operand)),
        UnOp::FSqrt => Err(AYError::UnsupportedOp("fsqrt".to_string())),
        UnOp::FFloor => Err(AYError::UnsupportedOp("ffloor".to_string())),
        UnOp::FCeil => Err(AYError::UnsupportedOp("fceil".to_string())),
        UnOp::FTrunc => Err(AYError::UnsupportedOp("ftrunc".to_string())),
        UnOp::CtPop => Err(AYError::UnsupportedOp("ctpop".to_string())),
    }
}

/// Encode a TrustIr `CastOp` as a ay bitvector resize operation.
///
/// - `Trunc` -> `bvextract` (extract low bits)
/// - `ZExt` -> `bvzeroext` (zero-extend)
/// - `SExt` -> `bvsignext` (sign-extend)
///
/// Other cast ops (float conversions, pointer casts, bitcast) are unsupported
/// in the BV encoding.
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
            Ok(solver.bvextract(operand, dst_width - 1, 0))
        }
        CastOp::ZExt => {
            if dst_width <= src_width {
                return Err(AYError::UnsupportedOp(format!(
                    "zext requires dst_width ({}) > src_width ({})",
                    dst_width, src_width
                )));
            }
            let extend_by = dst_width - src_width;
            Ok(solver.bvzeroext(operand, extend_by))
        }
        CastOp::SExt => {
            if dst_width <= src_width {
                return Err(AYError::UnsupportedOp(format!(
                    "sext requires dst_width ({}) > src_width ({})",
                    dst_width, src_width
                )));
            }
            let extend_by = dst_width - src_width;
            Ok(solver.bvsignext(operand, extend_by))
        }
        CastOp::FPToUI => {
            // FP -> unsigned bitvector
            let rm = rne(solver);
            Ok(solver.fp_to_ubv(rm, operand, dst_width))
        }
        CastOp::FPToSI => {
            // FP -> signed bitvector
            let rm = rne(solver);
            Ok(solver.fp_to_sbv(rm, operand, dst_width))
        }
        CastOp::UIToFP => {
            // Unsigned bitvector -> FP. dst_width encodes eb+sb.
            let rm = rne(solver);
            let (eb, sb) = fp_sort_from_total_width(dst_width)?;
            Ok(solver.bv_to_fp_unsigned(rm, operand, eb, sb))
        }
        CastOp::SIToFP => {
            // Signed bitvector -> FP. Uses bv_to_fp (signed interpretation).
            let rm = rne(solver);
            let (eb, sb) = fp_sort_from_total_width(dst_width)?;
            Ok(solver.bv_to_fp(rm, operand, eb, sb))
        }
        CastOp::FPTrunc => {
            // FP -> narrower FP (e.g., f64 -> f32)
            let rm = rne(solver);
            let (eb, sb) = fp_sort_from_total_width(dst_width)?;
            Ok(solver.fp_to_fp(rm, operand, eb, sb))
        }
        CastOp::FPExt => {
            // FP -> wider FP (e.g., f32 -> f64)
            let rm = rne(solver);
            let (eb, sb) = fp_sort_from_total_width(dst_width)?;
            Ok(solver.fp_to_fp(rm, operand, eb, sb))
        }
        CastOp::PtrToInt => {
            // Pointer is BitVec(64) in our encoding. Target is integer BitVec(dst_width).
            // src_width is the pointer width (always 64 in our model).
            if dst_width == 64 {
                // Same width: identity
                Ok(operand)
            } else if dst_width < 64 {
                // Narrowing: extract low bits
                Ok(solver.bvextract(operand, dst_width - 1, 0))
            } else {
                // Widening: zero-extend
                let extend_by = dst_width - 64;
                Ok(solver.bvzeroext(operand, extend_by))
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
                Ok(solver.bvzeroext(operand, extend_by))
            } else {
                // Wider integer: truncate to 64 (extract low 64 bits)
                Ok(solver.bvextract(operand, 63, 0))
            }
        }
        CastOp::Bitcast => {
            // Same-width reinterpretation. In bitvector encoding, both source
            // and destination types map to BitVec of the same width, so this
            // is the identity operation.
            if src_width != dst_width {
                return Err(AYError::UnsupportedOp(format!(
                    "bitcast requires src_width ({}) == dst_width ({})",
                    src_width, dst_width
                )));
            }
            Ok(operand)
        }
        CastOp::PtrToPtr | CastOp::Transmute | CastOp::ReifyFnPointer => {
            Err(AYError::UnsupportedOp(format!(
                "{op} is proof-grade classified but unsupported by BV encoding"
            )))
        }
        CastOp::FPToSISat | CastOp::FPToUISat => {
            // Saturating float→int (Rust `f as iN`/`uN`): NaN→0 and clamp to
            // [MIN,MAX]. A faithful BV/FP encoding is an ite-chain over
            // fp.isNaN / fp.geq / fp.lt plus fp.to_sbv on the in-range branch;
            // until that is written and cross-checked we fail CLOSED here rather
            // than risk an unsound approximation. The reference interpreter
            // (trust-ir::interpret) carries the exact saturating semantics.
            Err(AYError::UnsupportedOp(format!(
                "{op} (saturating float→int) is not yet supported by the BV encoding"
            )))
        }
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
pub fn encode_fcmp(solver: &mut Solver, op: FCmpOp, lhs: Term, rhs: Term) -> Term {
    match op {
        // Ordered comparisons: false if NaN
        FCmpOp::OEq => solver.fp_eq(lhs, rhs),
        FCmpOp::ONe => {
            let eq = solver.fp_eq(lhs, rhs);
            solver.not(eq)
        }
        FCmpOp::OLt => solver.fp_lt(lhs, rhs),
        FCmpOp::OLe => solver.fp_le(lhs, rhs),
        FCmpOp::OGt => solver.fp_gt(lhs, rhs),
        FCmpOp::OGe => solver.fp_ge(lhs, rhs),
        // Unordered comparisons: true if NaN
        FCmpOp::UEq => {
            // UEq = isNaN(a) OR isNaN(b) OR fp.eq(a, b)
            let nan_a = solver.fp_is_nan(lhs);
            let nan_b = solver.fp_is_nan(rhs);
            let eq = solver.fp_eq(lhs, rhs);
            let nan_either = solver.or(nan_a, nan_b);
            solver.or(nan_either, eq)
        }
        FCmpOp::UNe => {
            // UNe = isNaN(a) OR isNaN(b) OR NOT fp.eq(a, b)
            let nan_a = solver.fp_is_nan(lhs);
            let nan_b = solver.fp_is_nan(rhs);
            let eq = solver.fp_eq(lhs, rhs);
            let neq = solver.not(eq);
            let nan_either = solver.or(nan_a, nan_b);
            solver.or(nan_either, neq)
        }
        FCmpOp::ULt => {
            // ULt = isNaN(a) OR isNaN(b) OR fp.lt(a, b)
            let nan_a = solver.fp_is_nan(lhs);
            let nan_b = solver.fp_is_nan(rhs);
            let lt = solver.fp_lt(lhs, rhs);
            let nan_either = solver.or(nan_a, nan_b);
            solver.or(nan_either, lt)
        }
        FCmpOp::ULe => {
            let nan_a = solver.fp_is_nan(lhs);
            let nan_b = solver.fp_is_nan(rhs);
            let le = solver.fp_le(lhs, rhs);
            let nan_either = solver.or(nan_a, nan_b);
            solver.or(nan_either, le)
        }
        FCmpOp::UGt => {
            let nan_a = solver.fp_is_nan(lhs);
            let nan_b = solver.fp_is_nan(rhs);
            let gt = solver.fp_gt(lhs, rhs);
            let nan_either = solver.or(nan_a, nan_b);
            solver.or(nan_either, gt)
        }
        FCmpOp::UGe => {
            let nan_a = solver.fp_is_nan(lhs);
            let nan_b = solver.fp_is_nan(rhs);
            let ge = solver.fp_ge(lhs, rhs);
            let nan_either = solver.or(nan_a, nan_b);
            solver.or(nan_either, ge)
        }
    }
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
    /// Counter for generating fresh allocation base addresses.
    alloc_counter: u64,
}

/// The ay sort for memory: `Array(BitVec(64), BitVec(8))`.
pub fn memory_sort() -> Sort {
    Sort::Array(Box::new(ArraySort {
        index_sort: Sort::BitVec(BitVecSort { width: 64 }),
        element_sort: Sort::BitVec(BitVecSort { width: 8 }),
    }))
}

impl MemoryModel {
    /// Create a new symbolic memory state.
    pub fn new(solver: &mut Solver, name: &str) -> Self {
        let sort = memory_sort();
        let state = solver.declare_const(name, sort);
        Self {
            state,
            alloc_counter: 0,
        }
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
        let byte0 = solver.select(self.state, addr);
        if byte_width == 1 {
            return Ok(byte0);
        }
        // Read remaining bytes and concatenate (little-endian: high bytes on left)
        let mut result = byte0;
        for i in 1..byte_width {
            let offset = solver.bv_const(i as i64, 64);
            let byte_addr = solver.bvadd(addr, offset);
            let byte_val = solver.select(self.state, byte_addr);
            // Concat: byte_val is more significant, result is less significant
            result = solver.bvconcat(byte_val, result);
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
        let mut mem = self.state;
        for i in 0..byte_width {
            let offset = solver.bv_const(i as i64, 64);
            let byte_addr = solver.bvadd(addr, offset);
            // Extract byte i from value (little-endian: byte 0 is bits [7:0])
            let lo = i * 8;
            let hi = lo + 7;
            let byte_val = solver.bvextract(value, hi, lo);
            mem = solver.store(mem, byte_addr, byte_val);
        }
        self.state = mem;
        Ok(mem)
    }

    /// Encode an alloca: return a fresh symbolic address with non-overlap constraints.
    ///
    /// The returned address is constrained to be non-null and non-overlapping
    /// with previous allocations (using a monotonically increasing base).
    pub fn encode_alloca(&mut self, solver: &mut Solver, byte_size: u64) -> Term {
        // Use a well-separated base address for each allocation
        // Base addresses: 0x1000, 0x2000, 0x3000, ...
        self.alloc_counter += 1;
        let base = self.alloc_counter * 0x1000;
        let addr = solver.bv_const(base as i64, 64);

        // Assert non-null
        let null = solver.bv_const(0, 64);
        let not_null = solver.eq(addr, null);
        let not_null = solver.not(not_null);
        solver.assert_term(not_null);

        // Assert in-bounds: addr + size does not wrap around
        let size = solver.bv_const(byte_size as i64, 64);
        let end = solver.bvadd(addr, size);
        let no_wrap = solver.bvuge(end, addr);
        solver.assert_term(no_wrap);

        addr
    }

    /// Encode a GEP (GetElementPtr) as pointer arithmetic.
    ///
    /// `base + offset_bytes` using bitvector addition on 64-bit pointers.
    pub fn encode_gep(&self, solver: &mut Solver, base: Term, offset_bytes: Term) -> Term {
        solver.bvadd(base, offset_bytes)
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
    pub fn new(solver: &mut Solver, name: &str) -> Self {
        let sort = permission_sort();
        let state = solver.declare_const(name, sort);
        Self { state }
    }

    /// Encode a shared borrow from `ptr`.
    ///
    /// The pointer must currently be `Owned` (1) or already `SharedBorrow` (2).
    /// Asserts this precondition and sets the permission to `SharedBorrow` (2).
    /// Returns the borrowed pointer and the updated permission state.
    pub fn encode_borrow(&mut self, solver: &mut Solver, ptr: Term) -> (Term, Term) {
        let permission = self.get_permission(solver, ptr);
        let owned = solver.bv_const(1, 2);
        let shared_borrow = solver.bv_const(2, 2);
        let is_owned = solver.eq(permission, owned);
        let is_shared = solver.eq(permission, shared_borrow);
        let can_borrow = solver.or(is_owned, is_shared);
        solver.assert_term(can_borrow);

        let new_state = solver.store(self.state, ptr, shared_borrow);
        self.state = new_state;
        (ptr, new_state)
    }

    /// Encode a mutable borrow from `ptr`.
    ///
    /// The pointer must currently be `Owned` (1). Asserts this precondition
    /// and sets the permission to `MutableBorrow` (3).
    /// Returns the borrowed pointer and the updated permission state.
    pub fn encode_borrow_mut(&mut self, solver: &mut Solver, ptr: Term) -> (Term, Term) {
        let permission = self.get_permission(solver, ptr);
        let owned = solver.bv_const(1, 2);
        let mutable_borrow = solver.bv_const(3, 2);
        let is_owned = solver.eq(permission, owned);
        solver.assert_term(is_owned);

        let new_state = solver.store(self.state, ptr, mutable_borrow);
        self.state = new_state;
        (ptr, new_state)
    }

    /// Encode the end of a borrow, restoring ownership.
    ///
    /// Sets the permission back to `Owned` (1). Returns the updated state.
    pub fn encode_end_borrow(&mut self, solver: &mut Solver, borrow_ptr: Term) -> Term {
        let owned = solver.bv_const(1, 2);
        let new_state = solver.store(self.state, borrow_ptr, owned);
        self.state = new_state;
        new_state
    }

    /// Read the current permission for `ptr`.
    pub fn get_permission(&self, solver: &mut Solver, ptr: Term) -> Term {
        solver.select(self.state, ptr)
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
    pub fn new(solver: &mut Solver, name: &str) -> Self {
        let sort = refcount_sort();
        let state = solver.declare_const(name, sort);
        Self { state }
    }

    /// Encode an ARC retain by incrementing the refcount.
    ///
    /// Returns the updated refcount state.
    pub fn encode_retain(&mut self, solver: &mut Solver, ptr: Term) -> Term {
        let refcount = self.get_refcount(solver, ptr);
        let one = solver.bv_const(1, 32);
        let new_refcount = solver.bvadd(refcount, one);
        let new_state = solver.store(self.state, ptr, new_refcount);
        self.state = new_state;
        new_state
    }

    /// Encode an ARC release by decrementing the refcount.
    ///
    /// Asserts that the refcount is > 0 before decrementing.
    /// Returns the updated refcount state.
    pub fn encode_release(&mut self, solver: &mut Solver, ptr: Term) -> Result<Term, AYError> {
        let refcount = self.get_refcount(solver, ptr);
        let zero = solver.bv_const(0, 32);
        let one = solver.bv_const(1, 32);
        let positive = solver.bvugt(refcount, zero);
        solver.assert_term(positive);

        let new_refcount = solver.bvsub(refcount, one);
        let new_state = solver.store(self.state, ptr, new_refcount);
        self.state = new_state;
        Ok(new_state)
    }

    /// Check whether `ptr` has a unique ARC reference (refcount == 1).
    ///
    /// Returns a boolean ay term.
    pub fn encode_is_unique(&self, solver: &mut Solver, ptr: Term) -> Term {
        let refcount = self.get_refcount(solver, ptr);
        let one = solver.bv_const(1, 32);
        solver.eq(refcount, one)
    }

    /// Read the current refcount for `ptr`.
    pub fn get_refcount(&self, solver: &mut Solver, ptr: Term) -> Term {
        solver.select(self.state, ptr)
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
pub fn verify_and_certify(
    solver: &mut Solver,
    annotation: &ProofAnnotation,
    operands: &ProofOperands,
    obligation_id: ProofId,
) -> Result<VerificationResult, AYError> {
    let condition = verify_proof_obligation(solver, annotation, operands)?;

    // Assert the condition term
    solver.assert_term(condition.term);

    // Check satisfiability
    let sat_result = solver.check_sat();

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
                }))
            } else if sat_result.is_sat() {
                // SAT => counterexample exists => obligation does NOT hold
                Ok(VerificationResult::Refuted {
                    certificate: ProofCertificate {
                        obligation: obligation_id,
                        prover: "ay".to_string(),
                        evidence: ProofEvidence::SmtProof(Vec::new()),
                    },
                })
            } else {
                // Unknown / timeout
                Ok(VerificationResult::Unknown {
                    certificate: ProofCertificate {
                        obligation: obligation_id,
                        prover: "ay".to_string(),
                        evidence: ProofEvidence::Trusted("ay returned unknown".to_string()),
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
) -> Term {
    match (op, is_signed) {
        (OverflowOp::AddOverflow, true) => {
            let no_overflow = solver.bvadd_no_overflow(lhs, rhs, true);
            let no_underflow = solver.bvadd_no_underflow(lhs, rhs);
            solver.and(no_overflow, no_underflow)
        }
        (OverflowOp::AddOverflow, false) => solver.bvadd_no_overflow(lhs, rhs, false),
        (OverflowOp::SubOverflow, true) => {
            let no_overflow = solver.bvsub_no_overflow(lhs, rhs);
            let no_underflow = solver.bvsub_no_underflow(lhs, rhs, true);
            solver.and(no_overflow, no_underflow)
        }
        (OverflowOp::SubOverflow, false) => solver.bvsub_no_underflow(lhs, rhs, false),
        (OverflowOp::MulOverflow, true) => {
            let no_overflow = solver.bvmul_no_overflow(lhs, rhs, true);
            let no_underflow = solver.bvmul_no_underflow(lhs, rhs);
            solver.and(no_overflow, no_underflow)
        }
        (OverflowOp::MulOverflow, false) => solver.bvmul_no_overflow(lhs, rhs, false),
    }
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
            let safe = encode_overflow_check(solver, *op, is_signed, lhs, rhs);
            // Assert NOT safe, check UNSAT => safe always holds
            let negated = solver.not(safe);
            Ok(ProofCondition {
                term: negated,
                strategy: ProofStrategy::AssertAndCheckUnsat,
            })
        }
        ProofAnnotation::DivNonZero => {
            let divisor = operands.single_operand("divisor")?;
            let zero = solver.bv_const(0, operands.bit_width()?);
            let is_zero = solver.eq(divisor, zero);
            // Assert divisor == 0, check UNSAT => divisor never zero
            Ok(ProofCondition {
                term: is_zero,
                strategy: ProofStrategy::AssertAndCheckUnsat,
            })
        }
        ProofAnnotation::ShiftInRange => {
            let (shift_amount, bit_width_term) =
                operands.two_operands("shift_amount", "bit_width")?;
            let out_of_range = solver.bvuge(shift_amount, bit_width_term);
            // Assert shift >= width, check UNSAT => shift always in range
            Ok(ProofCondition {
                term: out_of_range,
                strategy: ProofStrategy::AssertAndCheckUnsat,
            })
        }
        ProofAnnotation::InBounds => {
            let (index, length) = operands.two_operands("index", "length")?;
            let out_of_bounds = solver.bvuge(index, length);
            // Assert index >= length, check UNSAT => always in bounds
            Ok(ProofCondition {
                term: out_of_bounds,
                strategy: ProofStrategy::AssertAndCheckUnsat,
            })
        }
        ProofAnnotation::NotNull => {
            let ptr = operands.single_operand("ptr")?;
            let null = solver.bv_const(0, 64);
            let is_null = solver.eq(ptr, null);
            // Assert ptr == 0, check UNSAT => ptr never null
            Ok(ProofCondition {
                term: is_null,
                strategy: ProofStrategy::AssertAndCheckUnsat,
            })
        }
        ProofAnnotation::ValidBorrow => {
            let (_ptr, permission) = operands.two_operands("ptr", "permission")?;
            let owned = solver.bv_const(1, 2);
            let is_owned = solver.eq(permission, owned);
            let invalid = solver.not(is_owned);
            // Assert permission != Owned, check UNSAT => permission is always Owned
            Ok(ProofCondition {
                term: invalid,
                strategy: ProofStrategy::AssertAndCheckUnsat,
            })
        }
        ProofAnnotation::UniqueBorrow => {
            let (_ptr, permission) = operands.two_operands("ptr", "permission")?;
            let mutable_borrow = solver.bv_const(3, 2);
            let has_mutable_borrow = solver.eq(permission, mutable_borrow);
            // Assert permission == MutableBorrow, check UNSAT => no concurrent mutable borrows exist
            Ok(ProofCondition {
                term: has_mutable_borrow,
                strategy: ProofStrategy::AssertAndCheckUnsat,
            })
        }
        ProofAnnotation::SharedBorrow => {
            let (_ptr, permission) = operands.two_operands("ptr", "permission")?;
            let owned = solver.bv_const(1, 2);
            let shared_borrow = solver.bv_const(2, 2);
            let is_owned = solver.eq(permission, owned);
            let is_shared = solver.eq(permission, shared_borrow);
            let readable = solver.or(is_owned, is_shared);
            let not_readable = solver.not(readable);
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
            let owned = solver.bv_const(1, 2);
            let is_owned = solver.eq(permission, owned);
            let not_owned = solver.not(is_owned);
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
            let eq = solver.eq(result1, result2);
            let neq = solver.not(eq);
            Ok(ProofCondition {
                term: neq,
                strategy: ProofStrategy::AssertAndCheckUnsat,
            })
        }
        ProofAnnotation::Commutative => {
            // f(a,b) == f(b,a). Operands: "result_ab" is f(a,b), "result_ba" is f(b,a).
            // Condition: result_ab != result_ba, check UNSAT => always commutative.
            let (result_ab, result_ba) = operands.two_operands("result_ab", "result_ba")?;
            let eq = solver.eq(result_ab, result_ba);
            let neq = solver.not(eq);
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
            let eq = solver.eq(result_left, result_right);
            let neq = solver.not(eq);
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
            let eq = solver.eq(ptr1, ptr2);
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
            let align = solver.bv_const(*n as i64, 64);
            let remainder = solver.bvurem(ptr, align);
            let zero = solver.bv_const(0, 64);
            let not_aligned = solver.eq(remainder, zero);
            let not_aligned = solver.not(not_aligned);
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
            let not_safe = solver.not(safe);
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
            let not_defined = solver.not(is_defined);
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
    /// Returns `true` if the proof obligation is verified (holds).
    pub fn check(&self, solver: &mut Solver) -> bool {
        solver.assert_term(self.term);
        match self.strategy {
            ProofStrategy::AssertAndCheckUnsat => solver.check_sat().is_unsat(),
        }
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
            terms.push(solver.declare_const(&ay_symbol(func, *value), sort));
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
    let a = solver.declare_const("a", sort.clone());
    let b = solver.declare_const("b", sort);

    let safe = encode_overflow_check(&mut solver, OverflowOp::AddOverflow, true, a, b);
    let not_safe = solver.not(safe);
    solver.assert_term(not_safe);

    // If SAT, there exist values a,b where addition overflows
    Ok(solver.check_sat().is_sat())
}

#[cfg(test)]
mod tests {
    use super::*;

    // ---- ty_to_sort tests ----

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
        let result = encode_icmp(&mut solver, ICmpOp::Eq, five, also_five);
        solver.assert_term(result);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn encode_icmp_eq_false() {
        let mut solver = create_bv_solver().unwrap();
        let five = solver.bv_const(5, 32);
        let six = solver.bv_const(6, 32);
        let result = encode_icmp(&mut solver, ICmpOp::Eq, five, six);
        solver.assert_term(result);
        assert!(solver.check_sat().is_unsat());
    }

    #[test]
    fn encode_icmp_ne() {
        let mut solver = create_bv_solver().unwrap();
        let five = solver.bv_const(5, 32);
        let six = solver.bv_const(6, 32);
        let result = encode_icmp(&mut solver, ICmpOp::Ne, five, six);
        solver.assert_term(result);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn encode_icmp_ult() {
        // 5 < 10 unsigned
        let mut solver = create_bv_solver().unwrap();
        let five = solver.bv_const(5, 32);
        let ten = solver.bv_const(10, 32);
        let result = encode_icmp(&mut solver, ICmpOp::Ult, five, ten);
        solver.assert_term(result);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn encode_icmp_slt_negative() {
        // -1 < 0 signed (0xFFFFFFFF < 0 in signed interpretation)
        let mut solver = create_bv_solver().unwrap();
        let neg_one = solver.bv_const(-1, 32);
        let zero = solver.bv_const(0, 32);
        let result = encode_icmp(&mut solver, ICmpOp::Slt, neg_one, zero);
        solver.assert_term(result);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn encode_icmp_ult_negative_is_larger() {
        // -1 (0xFFFFFFFF) is NOT < 0 unsigned
        let mut solver = create_bv_solver().unwrap();
        let neg_one = solver.bv_const(-1, 32);
        let zero = solver.bv_const(0, 32);
        let result = encode_icmp(&mut solver, ICmpOp::Ult, neg_one, zero);
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
            let _result = encode_icmp(&mut solver, *op, a, b);
            // Just verifying construction does not panic
        }
    }

    #[test]
    fn encode_icmp_ule_boundary() {
        // 5 <= 5
        let mut solver = create_bv_solver().unwrap();
        let five = solver.bv_const(5, 32);
        let also_five = solver.bv_const(5, 32);
        let result = encode_icmp(&mut solver, ICmpOp::Ule, five, also_five);
        solver.assert_term(result);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn encode_icmp_ugt() {
        // 10 > 5 unsigned
        let mut solver = create_bv_solver().unwrap();
        let ten = solver.bv_const(10, 32);
        let five = solver.bv_const(5, 32);
        let result = encode_icmp(&mut solver, ICmpOp::Ugt, ten, five);
        solver.assert_term(result);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn encode_icmp_sge() {
        // 0 >= -1 signed
        let mut solver = create_bv_solver().unwrap();
        let zero = solver.bv_const(0, 32);
        let neg_one = solver.bv_const(-1, 32);
        let result = encode_icmp(&mut solver, ICmpOp::Sge, zero, neg_one);
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
    fn encode_unop_ctpop_unsupported() {
        let mut solver = create_bv_solver().unwrap();
        let x = solver.bv_const(0x55, 8);
        let result = encode_unop(&mut solver, UnOp::CtPop, x);
        assert!(matches!(result, Err(AYError::UnsupportedOp(op)) if op == "ctpop"));
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
        let safe = encode_overflow_check(&mut solver, OverflowOp::AddOverflow, true, one, also_one);
        solver.assert_term(safe);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn encode_overflow_check_add_overflows() {
        // INT_MAX + 1 overflows in 32-bit signed
        let mut solver = create_bv_solver().unwrap();
        let max = solver.bv_const(i32::MAX as i64, 32);
        let one = solver.bv_const(1, 32);
        let safe = encode_overflow_check(&mut solver, OverflowOp::AddOverflow, true, max, one);
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
        let safe = encode_overflow_check(&mut solver, OverflowOp::SubOverflow, true, min, one);
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
        let safe = encode_overflow_check(&mut solver, OverflowOp::MulOverflow, true, two, three);
        solver.assert_term(safe);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn encode_overflow_check_mul_overflows() {
        // INT_MAX * 2 overflows
        let mut solver = create_bv_solver().unwrap();
        let max = solver.bv_const(i32::MAX as i64, 32);
        let two = solver.bv_const(2, 32);
        let safe = encode_overflow_check(&mut solver, OverflowOp::MulOverflow, true, max, two);
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
        let safe = encode_overflow_check(&mut solver, OverflowOp::AddOverflow, true, a, b);
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
        assert!(!cond.check(&mut solver));
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
        assert!(cond.check(&mut solver));
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
        assert!(!cond.check(&mut solver));
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
        assert!(cond.check(&mut solver));
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
        assert!(!cond.check(&mut solver));
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
        assert!(cond.check(&mut solver));
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
        assert!(!cond.check(&mut solver));
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
        assert!(cond.check(&mut solver));
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
        assert!(!cond.check(&mut solver));
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
        assert!(!cond.check(&mut solver));
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
        assert!(cond.check(&mut solver));
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
        assert!(!cond.check(&mut solver));
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
        let a_pos = encode_icmp(&mut solver, ICmpOp::Sgt, a, zero);
        let b_pos = encode_icmp(&mut solver, ICmpOp::Sgt, b, zero);

        // No overflow
        let safe = encode_overflow_check(&mut solver, OverflowOp::AddOverflow, true, a, b);

        // a + b
        let sum = encode_binop(&mut solver, BinOp::Add, a, b).unwrap();

        // Assert sum <= 0 (negation of sum > 0)
        let sum_not_pos = encode_icmp(&mut solver, ICmpOp::Sle, sum, zero);

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
        let safe = encode_overflow_check(&mut solver, OverflowOp::AddOverflow, true, max, one);
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
        let safe = encode_overflow_check(&mut solver, OverflowOp::SubOverflow, false, zero, one);
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
        let safe = encode_overflow_check(&mut solver, OverflowOp::SubOverflow, false, one, zero);
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
        let safe = encode_overflow_check(&mut solver, OverflowOp::AddOverflow, false, max, one);
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
            encode_overflow_check(&mut solver, OverflowOp::AddOverflow, false, one, also_one);
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
        );
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
            encode_overflow_check(&mut solver2, OverflowOp::MulOverflow, false, three, five);
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
            let _result = encode_fcmp(&mut solver, *op, a, b);
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
            let _result = encode_fcmp(&mut solver, *op, a, b);
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
        let mem = MemoryModel::new(&mut solver, "mem0");
        assert_eq!(mem.alloc_counter, 0);
    }

    #[test]
    fn memory_model_load_single_byte() {
        let mut solver = create_fp_solver().unwrap();
        let mem = MemoryModel::new(&mut solver, "mem");
        let addr = solver.bv_const(0x1000, 64);
        let result = mem.encode_load(&mut solver, addr, 1);
        assert!(result.is_ok());
    }

    #[test]
    fn memory_model_load_multi_byte() {
        let mut solver = create_fp_solver().unwrap();
        let mem = MemoryModel::new(&mut solver, "mem");
        let addr = solver.bv_const(0x1000, 64);
        let result = mem.encode_load(&mut solver, addr, 4);
        assert!(result.is_ok());
    }

    #[test]
    fn memory_model_load_zero_bytes_error() {
        let mut solver = create_fp_solver().unwrap();
        let mem = MemoryModel::new(&mut solver, "mem");
        let addr = solver.bv_const(0x1000, 64);
        let result = mem.encode_load(&mut solver, addr, 0);
        assert!(result.is_err());
    }

    #[test]
    fn memory_model_store_single_byte() {
        let mut solver = create_fp_solver().unwrap();
        let mut mem = MemoryModel::new(&mut solver, "mem");
        let addr = solver.bv_const(0x1000, 64);
        let val = solver.bv_const(0x42, 8);
        let result = mem.encode_store(&mut solver, addr, val, 1);
        assert!(result.is_ok());
    }

    #[test]
    fn memory_model_store_zero_bytes_error() {
        let mut solver = create_fp_solver().unwrap();
        let mut mem = MemoryModel::new(&mut solver, "mem");
        let addr = solver.bv_const(0x1000, 64);
        let val = solver.bv_const(0, 8);
        let result = mem.encode_store(&mut solver, addr, val, 0);
        assert!(result.is_err());
    }

    #[test]
    fn memory_model_store_then_load_roundtrip() {
        // Store a 32-bit value and load it back, verify they are equal
        let mut solver = create_fp_solver().unwrap();
        let mut mem = MemoryModel::new(&mut solver, "mem");

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
        let mut mem = MemoryModel::new(&mut solver, "mem");
        let addr = mem.encode_alloca(&mut solver, 16);

        // The addr should be non-null (we asserted it)
        let null = solver.bv_const(0, 64);
        let is_null = solver.eq(addr, null);
        solver.assert_term(is_null);
        // Should be UNSAT because we asserted non-null
        assert!(solver.check_sat().is_unsat());
    }

    #[test]
    fn memory_model_alloca_increments_counter() {
        let mut solver = create_fp_solver().unwrap();
        let mut mem = MemoryModel::new(&mut solver, "mem");
        assert_eq!(mem.alloc_counter, 0);
        let _addr1 = mem.encode_alloca(&mut solver, 8);
        assert_eq!(mem.alloc_counter, 1);
        let _addr2 = mem.encode_alloca(&mut solver, 8);
        assert_eq!(mem.alloc_counter, 2);
    }

    #[test]
    fn memory_model_gep() {
        let mut solver = create_fp_solver().unwrap();
        let mem = MemoryModel::new(&mut solver, "mem");
        let base = solver.bv_const(0x1000, 64);
        let offset = solver.bv_const(16, 64);
        let result = mem.encode_gep(&mut solver, base, offset);

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
        let _model = BorrowModel::new(&mut solver, "perms0");
    }

    #[test]
    fn borrow_model_get_permission() {
        let mut solver = create_fp_solver().unwrap();
        let model = BorrowModel::new(&mut solver, "perms");
        let ptr = solver.bv_const(0x1000, 64);
        let _perm = model.get_permission(&mut solver, ptr);
        // Just verifying construction does not panic
    }

    #[test]
    fn borrow_model_encode_borrow_from_owned() {
        // If permission is Owned(1), shared borrow should succeed
        let mut solver = create_fp_solver().unwrap();
        let mut model = BorrowModel::new(&mut solver, "perms");
        let ptr = solver.bv_const(0x1000, 64);

        // Set initial permission to Owned(1)
        let owned = solver.bv_const(1, 2);
        model.state = solver.store(model.state, ptr, owned);

        let (_borrow_ptr, new_state) = model.encode_borrow(&mut solver, ptr);

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
        let mut model = BorrowModel::new(&mut solver, "perms");
        let ptr = solver.bv_const(0x2000, 64);

        // Set initial permission to SharedBorrow(2)
        let shared = solver.bv_const(2, 2);
        model.state = solver.store(model.state, ptr, shared);

        let (_borrow_ptr, new_state) = model.encode_borrow(&mut solver, ptr);

        // Should still be SharedBorrow(2)
        let perm = solver.select(new_state, ptr);
        let eq = solver.eq(perm, shared);
        solver.assert_term(eq);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn borrow_model_encode_borrow_mut_from_owned() {
        let mut solver = create_fp_solver().unwrap();
        let mut model = BorrowModel::new(&mut solver, "perms");
        let ptr = solver.bv_const(0x1000, 64);

        // Set initial permission to Owned(1)
        let owned = solver.bv_const(1, 2);
        model.state = solver.store(model.state, ptr, owned);

        let (_borrow_ptr, new_state) = model.encode_borrow_mut(&mut solver, ptr);

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
        let mut model = BorrowModel::new(&mut solver, "perms");
        let ptr = solver.bv_const(0x1000, 64);

        // Set permission to MutableBorrow(3)
        let mutable = solver.bv_const(3, 2);
        model.state = solver.store(model.state, ptr, mutable);

        let new_state = model.encode_end_borrow(&mut solver, ptr);

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
        let mut model = BorrowModel::new(&mut solver, "perms");
        let ptr = solver.bv_const(0x3000, 64);

        // Start Owned
        let owned = solver.bv_const(1, 2);
        model.state = solver.store(model.state, ptr, owned);

        // Shared borrow
        model.encode_borrow(&mut solver, ptr);

        // End shared borrow
        model.encode_end_borrow(&mut solver, ptr);

        // Mutable borrow (now Owned again)
        model.encode_borrow_mut(&mut solver, ptr);

        // End mutable borrow
        let final_state = model.encode_end_borrow(&mut solver, ptr);

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
        let _model = ArcModel::new(&mut solver, "refcounts0");
    }

    #[test]
    fn arc_model_get_refcount() {
        let mut solver = create_fp_solver().unwrap();
        let model = ArcModel::new(&mut solver, "refcounts");
        let ptr = solver.bv_const(0x1000, 64);
        let _rc = model.get_refcount(&mut solver, ptr);
    }

    #[test]
    fn arc_model_encode_retain_increments() {
        let mut solver = create_fp_solver().unwrap();
        let mut model = ArcModel::new(&mut solver, "refcounts");
        let ptr = solver.bv_const(0x1000, 64);

        // Set initial refcount to 1
        let one = solver.bv_const(1, 32);
        model.state = solver.store(model.state, ptr, one);

        let new_state = model.encode_retain(&mut solver, ptr);

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
        let mut model = ArcModel::new(&mut solver, "refcounts");
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
        let mut model = ArcModel::new(&mut solver, "refcounts");
        let ptr = solver.bv_const(0x1000, 64);

        // Set refcount to 1
        let one = solver.bv_const(1, 32);
        model.state = solver.store(model.state, ptr, one);

        let is_unique = model.encode_is_unique(&mut solver, ptr);
        solver.assert_term(is_unique);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn arc_model_encode_is_unique_false() {
        let mut solver = create_fp_solver().unwrap();
        let mut model = ArcModel::new(&mut solver, "refcounts");
        let ptr = solver.bv_const(0x1000, 64);

        // Set refcount to 3
        let three = solver.bv_const(3, 32);
        model.state = solver.store(model.state, ptr, three);

        let is_unique = model.encode_is_unique(&mut solver, ptr);
        // Assert is_unique => should be UNSAT because refcount is 3, not 1
        solver.assert_term(is_unique);
        assert!(solver.check_sat().is_unsat());
    }

    #[test]
    fn arc_model_retain_release_lifecycle() {
        // Start at 1, retain to 2, retain to 3, release to 2, release to 1
        let mut solver = create_fp_solver().unwrap();
        let mut model = ArcModel::new(&mut solver, "refcounts");
        let ptr = solver.bv_const(0x4000, 64);

        // Set initial refcount to 1
        let one = solver.bv_const(1, 32);
        model.state = solver.store(model.state, ptr, one);

        // Retain twice
        model.encode_retain(&mut solver, ptr);
        model.encode_retain(&mut solver, ptr);

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
        assert!(cond.check(&mut solver));
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
        assert!(!cond.check(&mut solver));
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
        assert!(!cond.check(&mut solver));
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
        assert!(cond.check(&mut solver));
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
        assert!(cond.check(&mut solver));
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
        assert!(!cond.check(&mut solver));
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
        assert!(!cond.check(&mut solver));
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
        assert!(cond.check(&mut solver));
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
        assert!(cond.check(&mut solver));
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
        assert!(!cond.check(&mut solver));
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
        assert!(!cond.check(&mut solver));
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
        assert!(!cond.check(&mut solver));
    }

    // ============================================================
    // Integration: BorrowModel + proof obligations
    // ============================================================

    #[test]
    fn borrow_model_valid_borrow_after_init_owned() {
        // Initialize a pointer as Owned, then verify ValidBorrow holds
        let mut solver = create_fp_solver().unwrap();
        let mut model = BorrowModel::new(&mut solver, "perms");
        let ptr = solver.bv_const(0x5000, 64);

        // Set permission to Owned
        let owned = solver.bv_const(1, 2);
        model.state = solver.store(model.state, ptr, owned);

        // Read permission back
        let perm = model.get_permission(&mut solver, ptr);

        // Verify ValidBorrow
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::ValidBorrow, &[ptr, perm], 2).unwrap();
        let cond =
            verify_proof_obligation(&mut solver, &ProofAnnotation::ValidBorrow, &operands).unwrap();
        assert!(cond.check(&mut solver));
    }

    #[test]
    fn borrow_model_shared_borrow_readable_after_borrow() {
        // After a shared borrow, SharedBorrow proof obligation should hold
        let mut solver = create_fp_solver().unwrap();
        let mut model = BorrowModel::new(&mut solver, "perms");
        let ptr = solver.bv_const(0x6000, 64);

        // Set permission to Owned, then borrow
        let owned = solver.bv_const(1, 2);
        model.state = solver.store(model.state, ptr, owned);
        model.encode_borrow(&mut solver, ptr);

        // Read permission (should be SharedBorrow(2))
        let perm = model.get_permission(&mut solver, ptr);

        // Verify SharedBorrow
        let operands =
            ProofOperands::for_annotation(&ProofAnnotation::SharedBorrow, &[ptr, perm], 2).unwrap();
        let cond = verify_proof_obligation(&mut solver, &ProofAnnotation::SharedBorrow, &operands)
            .unwrap();
        assert!(cond.check(&mut solver));
    }

    // ============================================================
    // Integration: ArcModel + is_unique verification
    // ============================================================

    #[test]
    fn arc_model_is_unique_after_single_retain() {
        let mut solver = create_fp_solver().unwrap();
        let mut model = ArcModel::new(&mut solver, "refcounts");
        let ptr = solver.bv_const(0x7000, 64);

        // Set refcount to 0, then retain once
        let zero = solver.bv_const(0, 32);
        model.state = solver.store(model.state, ptr, zero);
        model.encode_retain(&mut solver, ptr);

        // Should be unique (refcount == 1)
        let is_unique = model.encode_is_unique(&mut solver, ptr);
        solver.assert_term(is_unique);
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn arc_model_not_unique_after_two_retains() {
        let mut solver = create_fp_solver().unwrap();
        let mut model = ArcModel::new(&mut solver, "refcounts");
        let ptr = solver.bv_const(0x7000, 64);

        // Set refcount to 0, retain twice
        let zero = solver.bv_const(0, 32);
        model.state = solver.store(model.state, ptr, zero);
        model.encode_retain(&mut solver, ptr);
        model.encode_retain(&mut solver, ptr);

        // Should NOT be unique (refcount == 2)
        let is_unique = model.encode_is_unique(&mut solver, ptr);
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
        assert!(cond.check(&mut solver));
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
        assert!(!cond.check(&mut solver));
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
        assert!(cond.check(&mut solver));
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
        assert!(cond.check(&mut solver));
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
        assert!(!cond.check(&mut solver));
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
        assert!(cond.check(&mut solver));
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
        assert!(!cond.check(&mut solver));
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
        assert!(cond.check(&mut solver));
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
        assert!(!cond.check(&mut solver));
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
        assert!(!cond.check(&mut solver));
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
        assert!(cond.check(&mut solver));
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
        assert!(!cond.check(&mut solver));
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
        assert!(!cond.check(&mut solver));
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
        assert!(cond.check(&mut solver));
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
        assert!(!cond.check(&mut solver));
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
        assert!(cond.check(&mut solver));
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
        assert!(!cond.check(&mut solver));
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
        assert!(cond.check(&mut solver));
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
        assert!(!cond.check(&mut solver));
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
        assert!(!cond.check(&mut solver));
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

/// Encode a vector binary operation.
///
/// Vectors are modeled as concatenated bitvectors: lane_count * elem_width.
/// The operation is applied independently to each lane.
pub fn encode_vector_binop(
    solver: &mut Solver,
    op: BinOp,
    elem_ty: &Ty,
    lane_count: u32,
    lhs: Term,
    rhs: Term,
) -> Result<Term, AYError> {
    let elem_width = match ty_to_sort(elem_ty)? {
        Sort::BitVec(bv) => bv.width,
        Sort::FloatingPoint(eb, sb) => eb + sb,
        _ => return Err(AYError::UnsupportedType(elem_ty.clone())),
    };

    let mut result_lanes = Vec::with_capacity(lane_count as usize);

    for i in 0..lane_count {
        let lo = i * elem_width;
        let hi = lo + elem_width - 1;

        let l_lane = solver.bvextract(lhs, hi, lo);
        let r_lane = solver.bvextract(rhs, hi, lo);

        let res_lane = encode_binop(solver, op, l_lane, r_lane)?;
        result_lanes.push(res_lane);
    }

    // Concatenate lanes (little-endian: lane 0 is least significant)
    let mut result = result_lanes[0];
    for &lane in &result_lanes[1..] {
        result = solver.bvconcat(lane, result);
    }

    Ok(result)
}

#[cfg(test)]
mod vector_tests {
    use super::*;

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
