// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! # Lowering-target conformance subset — machine-readable allowlists
//!
//! This module is the machine-readable mirror of
//! [`lowering-target-subset.md`](../../../lowering-target-subset.md) (repo root):
//! the exact `Inst` / `Ty` / `ProofAnnotation` (+ `CastOp` and dialect-op)
//! surface a frontend may emit on the "perfectly proven" path. The two MUST
//! stay in lockstep — the gate test (`tests/lowering_subset.rs`) fails if a
//! name listed here is missing from the spec doc, and any subset change must
//! bump [`SUBSET_VERSION`] in both places (see the doc's "Versioning and bump
//! policy" section).
//!
//! Exclusions are keyed to the B3 **depth ledger**
//! (`docs/roadmap/B3-lean-ir-parity.md`): name-level Rust↔Lean parity is
//! closed (all three schema-parity allowlists in
//! `crates/trust-ir/tests/lean_schema_parity.rs` are empty), so what remains
//! outside the subset is precisely the constructs whose Lean semantics are
//! honest, documented *partials* — plus dialect ops without a proven
//! trust-ir lowering and the by-construction-unpinned `Custom` annotation.
//!
//! The checker ([`module_subset_violations`]) is fail-closed on every axis:
//! a construct is in the subset only if it is explicitly matched AND
//! allowlisted here. New Rust IR variants either break the exhaustive
//! matches (compile error) or fall to a catch-all violation arm.

use trust_ir::inst::{CastOp, Inst};
use trust_ir::proof::ProofAnnotation;
use trust_ir::ty::Ty;
use trust_ir::{Function, Module};

/// Version of the lowering-target conformance subset described by these
/// constants. Bump in lockstep with `lowering-target-subset.md` (repo root).
pub const SUBSET_VERSION: u32 = 2;

/// `Inst` variants a conforming frontend may emit (54 of 57).
///
/// Excluded (see the spec doc for the full rationale):
/// * `CoroSuspend` — depth ledger "Coroutine resume dispatch": the suspend
///   side is modelled, but the whole-module resume state-machine theorem is
///   open and the macro-expansion lock is definitional, not a `stepInst`
///   equivalence.
/// * `LandingPad` — depth ledger "Host unwinding" + "Multi-result binding
///   convention": selector dispatch on a taken unwind edge is unmodelled and
///   the two-result binding is packed, not faithful.
/// * `Resume` — depth ledger "Host unwinding": a structured
///   `unsupported.host_unwind` in the executable model, i.e. no semantics.
///
/// `Invoke` IS allowed, on the normal-path contract: under the ratified
/// `panic=abort` policy the unwind edge is never taken, and the Lean
/// executable model + reference interpreter agree on the normal edge.
pub const INST_ALLOWLIST_V1: &[&str] = &[
    "Alloca",
    "Assert",
    "Assume",
    "AtomicLoad",
    "AtomicRMW",
    "AtomicStore",
    "BinOp",
    "BindSlot",
    "Borrow",
    "BorrowMut",
    "Br",
    "Call",
    "CallIndirect",
    "Cast",
    "CloseFrame",
    "CmpXchg",
    "CondBr",
    "Const",
    "Copy",
    "Dealloc",
    "DialectOp",
    "EndBorrow",
    "ExtractElement",
    "ExtractField",
    "FCmp",
    "Fence",
    "GEP",
    "GlobalAddr",
    "HeapAlloc",
    "ICmp",
    "InsertElement",
    "InsertField",
    "Invoke",
    "IsUnique",
    "Load",
    "LoadSlot",
    "NullPtr",
    "OpenFrame",
    "Overflow",
    "PtrData",
    "PtrFromParts",
    "PtrMetadata",
    "Release",
    "Retain",
    "Return",
    "Select",
    "SeqMap",
    "SeqMapAddK",
    "SeqMapNot",
    "Store",
    "Switch",
    "UnOp",
    "Undef",
    "Unreachable",
];

/// v2 changes no instruction names; it promotes the already-allowlisted
/// pointer trio from the thin-only structural condition to both thin and
/// first-class fat-pointer regimes.
pub const INST_ALLOWLIST_V2: &[&str] = INST_ALLOWLIST_V1;

/// Frozen v1 `Ty` variants. This historical list predates the v2 fat-pointer
/// promotion and the later B1 scalar schema additions.
///
/// Excluded:
/// * `F16` — depth ledger "F16 executable semantics": type-level only; no
///   binary16 width/rounding model (policy-gated).
/// * `FatPtr` — v1 predated first-class fat-pointer memory semantics.
pub const TY_ALLOWLIST_V1: &[&str] = &[
    "Array", "Bool", "Closure", "Enum", "F32", "F64", "Func", "I128", "I16", "I32", "I64", "I8",
    "Never", "Ptr", "PtrConst", "PtrMut", "Rc", "Record", "Ref", "RefMut", "Sequence", "Set",
    "Struct", "Tuple", "U128", "U16", "U32", "U64", "U8", "Unit", "Vector",
];

/// `Ty` variants a v2 frontend may emit (32 of 38). v2 promotes `FatPtr`
/// after the Rust and Lean interpreters acquired matching two-lane values,
/// pointer-trio semantics, and 16-byte Store/Load semantics. The promotion is
/// restricted structurally to the executable model's pinned 64-bit
/// little-endian target.
pub const TY_ALLOWLIST_V2: &[&str] = &[
    "Array", "Bool", "Closure", "Enum", "F32", "F64", "FatPtr", "Func", "I128", "I16", "I32",
    "I64", "I8", "Never", "Ptr", "PtrConst", "PtrMut", "Rc", "Record", "Ref", "RefMut", "Sequence",
    "Set", "Struct", "Tuple", "U128", "U16", "U32", "U64", "U8", "Unit", "Vector",
];

/// `CastOp` sub-ops a conforming frontend may emit (14 of 17).
///
/// Excluded:
/// * `ReifyFnPointer` — depth ledger "ReifyFnPointer addressability": the
///   reified pointer is not `CallIndirect`-resolvable, and trust-cg's
///   backend does not support it (use `Constant::FnDef` / `fn_addr`).
/// * `FPToSISat` / `FPToUISat` — no proven lowering yet: ay `encode_cast`
///   fails closed on them and they are Lean-excluded (see
///   `docs/roadmap/B3-lean-ir-parity.md`), so the subset excludes them too.
///
/// Conditionally allowed:
/// * `Transmute` — scalar-to-scalar ONLY (depth ledger "Transmute
///   generality": aggregate/pointer transmutes are structured unsupported).
///   Enforced structurally by [`module_subset_violations`].
pub const CASTOP_ALLOWLIST_V1: &[&str] = &[
    "Bitcast",
    "FPExt",
    "FPToSI",
    "FPToUI",
    "FPTrunc",
    "IntToPtr",
    "PtrToInt",
    "PtrToPtr",
    "SExt",
    "SIToFP",
    "Transmute",
    "Trunc",
    "UIToFP",
    "ZExt",
];

pub const CASTOP_ALLOWLIST_V2: &[&str] = CASTOP_ALLOWLIST_V1;

/// Fully-qualified dialect ops (`dialect.op`) a conforming frontend may emit.
///
/// Exactly the portable `vector.*` ops with a proven trust-ir lowering (or a
/// deliberate single-instruction identity) — see
/// `docs/roadmap/fast-4-vector-crosslane-ops.md`. Notably excluded:
/// * `vector.fma` — carried without a trust-ir lowering by ratified policy
///   (single-rounding contract; nothing in-repo to refine).
/// * every other dialect (`clean.*`, `gpu.*`, `avx512.*`, `ane.*`,
///   `verif.*`, …) — no proven lowerings. `clean.*` (Clean's managed
///   runtime, its Dialect emission mode) was audited for admission on
///   2026-07-04 and refused — no B3 depth-ledger backing; Dialect mode is
///   a debug/round-trip surface, not a handoff mode (see the spec doc's
///   "Producer notes").
pub const DIALECT_OP_ALLOWLIST_V1: &[&str] = &[
    "vector.extract_lane",
    "vector.insert_lane",
    "vector.mask_to_bits",
    "vector.pack_lanes",
    "vector.reduce",
    "vector.shuffle",
];

pub const DIALECT_OP_ALLOWLIST_V2: &[&str] = DIALECT_OP_ALLOWLIST_V1;

/// `ProofAnnotation` variants a conforming frontend may emit (36 of 39).
///
/// Excluded:
/// * `Custom` — producer-defined tag; its meaning is not pinned by this
///   contract, so it cannot be part of a *pinned* subset.
/// * `FreshSymbolicHavoc` — the inert `Inst::Undef` marker. NOT feature-gated
///   and wire-encodable (binary tag `0x25`), but never ratified into the
///   subset, so it is reported as out-of-subset.
///
/// The feature-gated `Goal` (`clean-expr`) is outside the v1 scope by
/// construction (off the default zero-dep surface); the checker fails closed
/// on any annotation it does not recognize.
pub const PROOF_ALLOWLIST_V1: &[&str] = &[
    "Aligned",
    "AppendOnlyBuffer",
    "Associative",
    "AtomicOrdering",
    "AtomicSetInsert",
    "BoundedLoop",
    "BoundedOutput",
    "BranchWeights",
    "Commutative",
    "DataRaceFree",
    "Deterministic",
    "DivNonZero",
    "DivergenceClass",
    "InBounds",
    "KnownBits",
    "Monotonic",
    "NoAlias",
    "NoOverflow",
    "NoPanic",
    "NoUndef",
    "NoWrap",
    "NotNull",
    "ParallelMap",
    "ProofRef",
    "Pure",
    "ReadonlyTable",
    "SharedBorrow",
    "ShiftInRange",
    "Tainted",
    "Terminates",
    "TrustedSink",
    "UniqueBorrow",
    "ValidBorrow",
    "ValidDealloc",
    "ValueRange",
    "Wrapping",
];

pub const PROOF_ALLOWLIST_V2: &[&str] = PROOF_ALLOWLIST_V1;

fn allow(list: &[&str], name: &str) -> bool {
    list.contains(&name)
}

/// True for the scalar types a `Transmute` may reinterpret between in v1
/// (the Lean `semCast` scalar partial). `F16` is deliberately absent (it is
/// outside the type subset altogether).
pub fn is_transmute_scalar(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::I8
            | Ty::I16
            | Ty::I32
            | Ty::I64
            | Ty::I128
            | Ty::U8
            | Ty::U16
            | Ty::U32
            | Ty::U64
            | Ty::U128
            | Ty::F32
            | Ty::F64
            | Ty::Bool
            | Ty::Ptr
    )
}

/// Variant name of a `Ty` (compile-breaks when a variant is added).
pub fn ty_name(ty: &Ty) -> &'static str {
    match ty {
        Ty::I8 => "I8",
        // v25 B1 scalars (NOT in the lowering-target subset yet: trust-cg has
        // no pointer-width-int / char lowering; Error is never wire-legal).
        Ty::Isize => "Isize",
        Ty::Usize => "Usize",
        Ty::Char => "Char",
        Ty::Error => "Error",
        Ty::I16 => "I16",
        Ty::I32 => "I32",
        Ty::I64 => "I64",
        Ty::I128 => "I128",
        Ty::U8 => "U8",
        Ty::U16 => "U16",
        Ty::U32 => "U32",
        Ty::U64 => "U64",
        Ty::U128 => "U128",
        Ty::F16 => "F16",
        Ty::F32 => "F32",
        Ty::F64 => "F64",
        Ty::Bool => "Bool",
        Ty::Ptr => "Ptr",
        Ty::FatPtr(_) => "FatPtr",
        Ty::Vector(_, _) => "Vector",
        Ty::Unit => "Unit",
        Ty::Never => "Never",
        Ty::Array(_, _) => "Array",
        Ty::Tuple(_) => "Tuple",
        Ty::Struct(_) => "Struct",
        Ty::Enum(_) => "Enum",
        Ty::Func(_) => "Func",
        Ty::Sequence(_) => "Sequence",
        Ty::Set(_, _) => "Set",
        Ty::Record(_) => "Record",
        Ty::Closure(_) => "Closure",
        // v30 typed value model. Representation-preserving, so it never
        // changes what a backend must lower — the base type does.
        Ty::Refine(_, _) => "Refine",
        Ty::Ref(_) => "Ref",
        Ty::RefMut(_) => "RefMut",
        Ty::PtrConst(_) => "PtrConst",
        Ty::PtrMut(_) => "PtrMut",
        Ty::Rc(_) => "Rc",
    }
}

/// Recursively check `ty` (and its structural children) against the current type
/// subset, appending violations tagged with `at`.
fn check_ty(ty: &Ty, at: &str, pointer_bits: u32, little_endian: bool, out: &mut Vec<String>) {
    let name = ty_name(ty);
    if !allow(TY_ALLOWLIST_V2, name) {
        out.push(format!(
            "{at}: Ty::{name} is outside lowering-target subset v{SUBSET_VERSION}"
        ));
    }
    if matches!(ty, Ty::FatPtr(_))
        && (pointer_bits != trust_ir::shape::DEFAULT_POINTER_BITS || !little_endian)
    {
        out.push(format!(
            "{at}: Ty::FatPtr is executable only on the pinned {}-bit little-endian target, \
             got {pointer_bits}-bit {}-endian",
            trust_ir::shape::DEFAULT_POINTER_BITS,
            if little_endian { "little" } else { "big" }
        ));
    }
    match ty {
        Ty::Vector(inner, _)
        | Ty::Ref(inner)
        | Ty::RefMut(inner)
        | Ty::PtrConst(inner)
        | Ty::PtrMut(inner)
        | Ty::Rc(inner) => check_ty(inner, at, pointer_bits, little_endian, out),
        Ty::Tuple(xs) => {
            for x in xs {
                check_ty(x, at, pointer_bits, little_endian, out);
            }
        }
        // Id-indexed types (Array/Sequence/Set element `TyId`s, Struct/Enum/
        // Record/Func/Closure defs) are resolved through the module tables,
        // which `module_subset_violations` walks directly.
        _ => {}
    }
}

/// Variant name of an `Inst` (compile-breaks when a variant is added).
pub fn inst_name(inst: &Inst) -> &'static str {
    match inst {
        Inst::BinOp { .. } => "BinOp",
        Inst::SeqMapAddK { .. } => "SeqMapAddK",
        Inst::SeqMapNot { .. } => "SeqMapNot",
        Inst::SeqMap { .. } => "SeqMap",
        Inst::UnOp { .. } => "UnOp",
        Inst::Overflow { .. } => "Overflow",
        Inst::ICmp { .. } => "ICmp",
        Inst::FCmp { .. } => "FCmp",
        Inst::Cast { .. } => "Cast",
        Inst::Load { .. } => "Load",
        Inst::Store { .. } => "Store",
        Inst::Alloca { .. } => "Alloca",
        Inst::HeapAlloc { .. } => "HeapAlloc",
        Inst::GEP { .. } => "GEP",
        Inst::Dealloc { .. } => "Dealloc",
        Inst::AtomicLoad { .. } => "AtomicLoad",
        Inst::AtomicStore { .. } => "AtomicStore",
        Inst::AtomicRMW { .. } => "AtomicRMW",
        Inst::CmpXchg { .. } => "CmpXchg",
        Inst::Fence { .. } => "Fence",
        Inst::Borrow { .. } => "Borrow",
        Inst::BorrowMut { .. } => "BorrowMut",
        Inst::EndBorrow { .. } => "EndBorrow",
        Inst::Retain { .. } => "Retain",
        Inst::Release { .. } => "Release",
        Inst::IsUnique { .. } => "IsUnique",
        Inst::Br { .. } => "Br",
        Inst::CondBr { .. } => "CondBr",
        Inst::Switch { .. } => "Switch",
        Inst::Return { .. } => "Return",
        Inst::Unreachable => "Unreachable",
        Inst::Call { .. } => "Call",
        Inst::CallIndirect { .. } => "CallIndirect",
        Inst::ExtractField { .. } => "ExtractField",
        Inst::InsertField { .. } => "InsertField",
        Inst::ExtractElement { .. } => "ExtractElement",
        Inst::InsertElement { .. } => "InsertElement",
        Inst::Const { .. } => "Const",
        Inst::NullPtr => "NullPtr",
        Inst::GlobalAddr { .. } => "GlobalAddr",
        Inst::Undef { .. } => "Undef",
        Inst::Assume { .. } => "Assume",
        Inst::Assert { .. } => "Assert",
        Inst::Copy { .. } => "Copy",
        Inst::Select { .. } => "Select",
        Inst::PtrData { .. } => "PtrData",
        Inst::PtrMetadata { .. } => "PtrMetadata",
        Inst::PtrFromParts { .. } => "PtrFromParts",
        Inst::OpenFrame { .. } => "OpenFrame",
        Inst::BindSlot { .. } => "BindSlot",
        Inst::LoadSlot { .. } => "LoadSlot",
        Inst::CloseFrame { .. } => "CloseFrame",
        Inst::DialectOp(_) => "DialectOp",
        Inst::CoroSuspend { .. } => "CoroSuspend",
        Inst::Invoke { .. } => "Invoke",
        Inst::LandingPad { .. } => "LandingPad",
        Inst::Resume { .. } => "Resume",
    }
}

pub fn castop_name(op: CastOp) -> &'static str {
    match op {
        CastOp::Trunc => "Trunc",
        CastOp::ZExt => "ZExt",
        CastOp::SExt => "SExt",
        CastOp::FPTrunc => "FPTrunc",
        CastOp::FPExt => "FPExt",
        CastOp::FPToUI => "FPToUI",
        CastOp::FPToSI => "FPToSI",
        CastOp::UIToFP => "UIToFP",
        CastOp::SIToFP => "SIToFP",
        CastOp::PtrToInt => "PtrToInt",
        CastOp::IntToPtr => "IntToPtr",
        CastOp::PtrToPtr => "PtrToPtr",
        CastOp::Bitcast => "Bitcast",
        CastOp::Transmute => "Transmute",
        CastOp::ReifyFnPointer => "ReifyFnPointer",
        CastOp::FPToSISat => "FPToSISat",
        CastOp::FPToUISat => "FPToUISat",
    }
}

/// Name of a `ProofAnnotation`, or `None` for anything unrecognized
/// (feature-gated / future variants) — which the checker treats as a
/// violation, so the subset fails closed.
fn proof_name(p: &ProofAnnotation) -> Option<&'static str> {
    use ProofAnnotation::*;
    #[allow(unreachable_patterns)]
    match p {
        InBounds => Some("InBounds"),
        NotNull => Some("NotNull"),
        ValidBorrow => Some("ValidBorrow"),
        UniqueBorrow => Some("UniqueBorrow"),
        SharedBorrow => Some("SharedBorrow"),
        ValidDealloc => Some("ValidDealloc"),
        NoOverflow => Some("NoOverflow"),
        NoWrap => Some("NoWrap"),
        DivNonZero => Some("DivNonZero"),
        ShiftInRange => Some("ShiftInRange"),
        Wrapping => Some("Wrapping"),
        Pure => Some("Pure"),
        Terminates => Some("Terminates"),
        Deterministic => Some("Deterministic"),
        Associative => Some("Associative"),
        Commutative => Some("Commutative"),
        DataRaceFree => Some("DataRaceFree"),
        AtomicOrdering(_) => Some("AtomicOrdering"),
        BoundedOutput { .. } => Some("BoundedOutput"),
        Monotonic => Some("Monotonic"),
        NoAlias => Some("NoAlias"),
        Aligned(_) => Some("Aligned"),
        NoPanic => Some("NoPanic"),
        NoUndef => Some("NoUndef"),
        Tainted => Some("Tainted"),
        TrustedSink => Some("TrustedSink"),
        ReadonlyTable => Some("ReadonlyTable"),
        AppendOnlyBuffer => Some("AppendOnlyBuffer"),
        AtomicSetInsert => Some("AtomicSetInsert"),
        ParallelMap => Some("ParallelMap"),
        BoundedLoop(_) => Some("BoundedLoop"),
        DivergenceClass(_) => Some("DivergenceClass"),
        // Recognized but NOT allowlisted: reported by name as out-of-subset
        // rather than falling to the catch-all's "unrecognized/feature-gated"
        // message, which would misdescribe an ungated, wire-encodable variant.
        FreshSymbolicHavoc => Some("FreshSymbolicHavoc"),
        Custom(_) => Some("Custom"),
        ProofRef(_) => Some("ProofRef"),
        ValueRange { .. } => Some("ValueRange"),
        KnownBits { .. } => Some("KnownBits"),
        BranchWeights(_) => Some("BranchWeights"),
        // Feature-gated (e.g. `clean-expr`'s `Goal`) or future variants:
        // unrecognized here ⇒ reported as out-of-subset (fail-closed).
        _ => None,
    }
}

fn check_proof(p: &ProofAnnotation, at: &str, out: &mut Vec<String>) {
    match proof_name(p) {
        Some(name) if allow(PROOF_ALLOWLIST_V2, name) => {}
        Some(name) => out.push(format!(
            "{at}: ProofAnnotation::{name} is outside lowering-target subset v{SUBSET_VERSION}"
        )),
        None => out.push(format!(
            "{at}: unrecognized/feature-gated ProofAnnotation ({p:?}) is outside lowering-target subset v{SUBSET_VERSION}"
        )),
    }
}

/// Check one instruction (variant, cast sub-op + Transmute scalar condition,
/// canonical thin/fat pointer metadata condition, dialect-op allowlist, and every
/// embedded type).
fn check_inst(
    inst: &Inst,
    at: &str,
    pointer_bits: u32,
    little_endian: bool,
    out: &mut Vec<String>,
) {
    let name = inst_name(inst);
    if !allow(INST_ALLOWLIST_V2, name) {
        out.push(format!(
            "{at}: Inst::{name} is outside lowering-target subset v{SUBSET_VERSION}"
        ));
    }

    // Structural conditions + embedded-type checks.
    match inst {
        Inst::Cast {
            op, src_ty, dst_ty, ..
        } => {
            let op_name = castop_name(*op);
            if !allow(CASTOP_ALLOWLIST_V2, op_name) {
                out.push(format!(
                    "{at}: CastOp::{op_name} is outside lowering-target subset v{SUBSET_VERSION}"
                ));
            }
            if *op == CastOp::Transmute
                && !(is_transmute_scalar(src_ty) && is_transmute_scalar(dst_ty))
            {
                out.push(format!(
                    "{at}: non-scalar Transmute ({src_ty} -> {dst_ty}) is outside lowering-target \
                     subset v{SUBSET_VERSION} (scalar-to-scalar only)"
                ));
            }
            check_ty(src_ty, at, pointer_bits, little_endian, out);
            check_ty(dst_ty, at, pointer_bits, little_endian, out);
        }
        Inst::PtrMetadata {
            ptr_ty,
            metadata_ty,
            ..
        }
        | Inst::PtrFromParts {
            ptr_ty,
            metadata_ty,
            ..
        } => {
            match ptr_ty.pointer_metadata_ty(pointer_bits) {
                Some(expected) if &expected == metadata_ty => {}
                Some(expected) => out.push(format!(
                    "{at}: Inst::{name} metadata type `{metadata_ty}` does not match canonical \
                     `{expected}` for `{ptr_ty}` in lowering-target subset v{SUBSET_VERSION}"
                )),
                None => out.push(format!(
                    "{at}: Inst::{name} pointer type `{ptr_ty}` has no pointer metadata in \
                     lowering-target subset v{SUBSET_VERSION}"
                )),
            }
            check_ty(ptr_ty, at, pointer_bits, little_endian, out);
            check_ty(metadata_ty, at, pointer_bits, little_endian, out);
        }
        Inst::PtrData { ptr_ty, .. } => {
            if !matches!(
                ptr_ty,
                Ty::Ptr
                    | Ty::Ref(_)
                    | Ty::RefMut(_)
                    | Ty::PtrConst(_)
                    | Ty::PtrMut(_)
                    | Ty::Rc(_)
                    | Ty::FatPtr(_)
            ) {
                out.push(format!(
                    "{at}: Inst::PtrData pointer type `{ptr_ty}` is not executable in \
                     lowering-target subset v{SUBSET_VERSION}"
                ));
            }
            check_ty(ptr_ty, at, pointer_bits, little_endian, out);
        }
        Inst::DialectOp(op) => {
            let qualified = op.qualified_name();
            if !DIALECT_OP_ALLOWLIST_V2.contains(&qualified.as_str()) {
                out.push(format!(
                    "{at}: dialect op `{qualified}` is outside lowering-target subset \
                     v{SUBSET_VERSION} (no proven lowering)"
                ));
            }
            for t in &op.result_tys {
                check_ty(t, at, pointer_bits, little_endian, out);
            }
        }
        Inst::BinOp { ty, .. }
        | Inst::SeqMapAddK { ty, .. }
        | Inst::SeqMapNot { ty, .. }
        | Inst::SeqMap { ty, .. }
        | Inst::UnOp { ty, .. }
        | Inst::Overflow { ty, .. }
        | Inst::ICmp { ty, .. }
        | Inst::FCmp { ty, .. }
        | Inst::Load { ty, .. }
        | Inst::Store { ty, .. }
        | Inst::Alloca { ty, .. }
        | Inst::HeapAlloc { ty, .. }
        | Inst::AtomicLoad { ty, .. }
        | Inst::AtomicStore { ty, .. }
        | Inst::AtomicRMW { ty, .. }
        | Inst::CmpXchg { ty, .. }
        | Inst::ExtractField { ty, .. }
        | Inst::InsertField { ty, .. }
        | Inst::ExtractElement { ty, .. }
        | Inst::InsertElement { ty, .. }
        | Inst::Const { ty, .. }
        | Inst::Undef { ty }
        | Inst::Copy { ty, .. }
        | Inst::Select { ty, .. }
        | Inst::LoadSlot { ty, .. } => check_ty(ty, at, pointer_bits, little_endian, out),
        Inst::GEP { pointee_ty, .. } => check_ty(pointee_ty, at, pointer_bits, little_endian, out),
        Inst::OpenFrame { def } => {
            for slot in &def.slots {
                check_ty(&slot.ty, at, pointer_bits, little_endian, out);
            }
        }
        _ => {}
    }
}

fn check_function(func: &Function, pointer_bits: u32, little_endian: bool, out: &mut Vec<String>) {
    let fname = &func.name;
    for p in &func.proofs {
        check_proof(p, &format!("fn `{fname}` proofs"), out);
    }
    for block in &func.blocks {
        let bid = block.id.index();
        for (_, ty) in &block.params {
            check_ty(
                ty,
                &format!("fn `{fname}` bb{bid} params"),
                pointer_bits,
                little_endian,
                out,
            );
        }
        for (i, node) in block.body.iter().enumerate() {
            let at = format!("fn `{fname}` bb{bid} inst #{i}");
            check_inst(&node.inst, &at, pointer_bits, little_endian, out);
            for p in &node.proofs {
                check_proof(p, &at, out);
            }
        }
    }
}

/// Check a whole module against the current lowering-target subset.
///
/// Walks the interned type tables, function signatures, struct/enum/record/
/// closure definitions, globals, and every function body (instructions,
/// embedded types, instruction- and function-level proof annotations).
/// Returns one human-readable string per violation; empty means the module
/// stays inside the subset.
///
/// Scope note: this checks the *emission surface* (`Ty`/`Inst`/
/// `ProofAnnotation` + `CastOp`/dialect-op refinements). Proof-state tables
/// (`proof_obligations`, certificates, lineage) are verification metadata,
/// not emitted IR, and are not subset-restricted.
pub fn module_subset_violations(module: &Module) -> Vec<String> {
    let mut out = Vec::new();
    let pointer_bits = module.pointer_bits();
    let little_endian = module
        .target_info
        .as_ref()
        .is_none_or(|target| target.endianness == trust_ir::Endianness::Little);
    for (i, t) in module.types.iter().enumerate() {
        check_ty(
            t,
            &format!("module.types[{i}]"),
            pointer_bits,
            little_endian,
            &mut out,
        );
    }
    for (i, ft) in module.func_types.iter().enumerate() {
        for t in ft.params.iter().chain(ft.returns.iter()) {
            check_ty(
                t,
                &format!("module.func_types[{i}]"),
                pointer_bits,
                little_endian,
                &mut out,
            );
        }
    }
    for sd in &module.structs {
        for f in &sd.fields {
            check_ty(
                &f.ty,
                &format!("struct `{}`", sd.name),
                pointer_bits,
                little_endian,
                &mut out,
            );
        }
    }
    for ed in &module.enums {
        for v in &ed.variants {
            for t in &v.fields {
                check_ty(
                    t,
                    &format!("enum `{}`", ed.name),
                    pointer_bits,
                    little_endian,
                    &mut out,
                );
            }
        }
    }
    for rd in &module.records {
        for f in &rd.fields {
            check_ty(
                &f.ty,
                &format!("record `{}`", rd.name),
                pointer_bits,
                little_endian,
                &mut out,
            );
        }
    }
    for (i, ct) in module.closure_types.iter().enumerate() {
        for t in &ct.captures {
            check_ty(
                t,
                &format!("module.closure_types[{i}]"),
                pointer_bits,
                little_endian,
                &mut out,
            );
        }
    }
    for g in &module.globals {
        check_ty(
            &g.ty,
            &format!("global `{}`", g.name),
            pointer_bits,
            little_endian,
            &mut out,
        );
    }
    for f in &module.functions {
        check_function(f, pointer_bits, little_endian, &mut out);
    }
    out
}

/// Sanity guards over the constants themselves (sortedness gives stable
/// diffs; sets must not overlap with their documented exclusions).
#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeSet;

    fn assert_sorted_unique(name: &str, list: &[&str]) {
        let set: BTreeSet<&str> = list.iter().copied().collect();
        assert_eq!(set.len(), list.len(), "{name}: duplicate entries");
        let mut sorted = list.to_vec();
        sorted.sort_unstable();
        assert_eq!(sorted, list, "{name}: keep the allowlist sorted");
    }

    #[test]
    fn allowlists_are_sorted_and_unique() {
        assert_sorted_unique("INST_ALLOWLIST_V1", INST_ALLOWLIST_V1);
        assert_sorted_unique("TY_ALLOWLIST_V1", TY_ALLOWLIST_V1);
        assert_sorted_unique("CASTOP_ALLOWLIST_V1", CASTOP_ALLOWLIST_V1);
        assert_sorted_unique("DIALECT_OP_ALLOWLIST_V1", DIALECT_OP_ALLOWLIST_V1);
        assert_sorted_unique("PROOF_ALLOWLIST_V1", PROOF_ALLOWLIST_V1);
        assert_sorted_unique("INST_ALLOWLIST_V2", INST_ALLOWLIST_V2);
        assert_sorted_unique("TY_ALLOWLIST_V2", TY_ALLOWLIST_V2);
        assert_sorted_unique("CASTOP_ALLOWLIST_V2", CASTOP_ALLOWLIST_V2);
        assert_sorted_unique("DIALECT_OP_ALLOWLIST_V2", DIALECT_OP_ALLOWLIST_V2);
        assert_sorted_unique("PROOF_ALLOWLIST_V2", PROOF_ALLOWLIST_V2);
    }

    #[test]
    fn documented_exclusions_are_not_allowlisted() {
        for name in ["CoroSuspend", "LandingPad", "Resume"] {
            assert!(
                !INST_ALLOWLIST_V1.contains(&name),
                "{name} must be excluded"
            );
        }
        for name in ["F16", "FatPtr"] {
            assert!(!TY_ALLOWLIST_V1.contains(&name), "{name} must be excluded");
        }
        assert!(!CASTOP_ALLOWLIST_V1.contains(&"ReifyFnPointer"));
        assert!(!DIALECT_OP_ALLOWLIST_V1.contains(&"vector.fma"));
        assert!(!PROOF_ALLOWLIST_V1.contains(&"Custom"));

        for name in ["CoroSuspend", "LandingPad", "Resume"] {
            assert!(
                !INST_ALLOWLIST_V2.contains(&name),
                "{name} must be excluded"
            );
        }
        for name in ["F16", "Isize", "Usize", "Char", "Error"] {
            assert!(!TY_ALLOWLIST_V2.contains(&name), "{name} must be excluded");
        }
        assert!(TY_ALLOWLIST_V2.contains(&"FatPtr"));
        assert!(!CASTOP_ALLOWLIST_V2.contains(&"ReifyFnPointer"));
        assert!(!DIALECT_OP_ALLOWLIST_V2.contains(&"vector.fma"));
        assert!(!PROOF_ALLOWLIST_V2.contains(&"Custom"));
    }

    #[test]
    fn allowlist_sizes_match_the_spec_doc_counts() {
        assert_eq!(INST_ALLOWLIST_V1.len(), 54, "Inst: 54 of 57");
        assert_eq!(TY_ALLOWLIST_V1.len(), 31, "Ty: 31 of 38");
        assert_eq!(CASTOP_ALLOWLIST_V1.len(), 14, "CastOp: 14 of 17");
        assert_eq!(DIALECT_OP_ALLOWLIST_V1.len(), 6, "dialect ops: 6");
        assert_eq!(PROOF_ALLOWLIST_V1.len(), 36, "ProofAnnotation: 36 of 39");
        assert_eq!(INST_ALLOWLIST_V2.len(), 54, "Inst v2: 54 of 57");
        assert_eq!(TY_ALLOWLIST_V2.len(), 32, "Ty v2: 32 of 38");
        assert_eq!(CASTOP_ALLOWLIST_V2.len(), 14, "CastOp v2: 14 of 17");
        assert_eq!(DIALECT_OP_ALLOWLIST_V2.len(), 6, "dialect ops v2: 6");
        assert_eq!(PROOF_ALLOWLIST_V2.len(), 36, "ProofAnnotation v2: 36 of 39");
    }
}
