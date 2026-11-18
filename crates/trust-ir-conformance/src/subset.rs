// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! # Lowering-target conformance subset — machine-readable allowlists
//!
//! This module is the machine-readable mirror of
//! [`lowering-target-subset.md`](../../../lowering-target-subset.md) (repo root):
//! the exact `Inst` / `Ty` / `ProofAnnotation` (+ `CastOp` and dialect-op)
//! surface a frontend may emit on the "perfectly proven" path. The two MUST
//! stay in lockstep — the gate test (`tests/lowering_subset.rs`) fails unless
//! every variant of each closed axis is allowlisted here and in the doc's
//! Allowed list, or excluded here and in a row of the doc's Excluded table,
//! with the doc's counts equal to the code's — and any subset change must
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

use std::collections::{BTreeMap, HashMap};

use trust_ir::inst::{CastOp, Inst};
use trust_ir::proof::ProofAnnotation;
use trust_ir::ty::Ty;
use trust_ir::{Function, Module};

/// Version of the lowering-target conformance subset described by these
/// constants. Bump in lockstep with `lowering-target-subset.md` (repo root).
///
/// v3 (2026-09-19, WS2.9) is a breaking SHRINK under the bump policy's
/// "soundness hole" clause. No allowlist NAME moves; the structural
/// conditions do: `Transmute` is integer/pointer scalar only on both sides
/// ([`is_transmute_scalar`] lost `F32` / `F64` / `Bool`), and the whole module
/// must target the executable model's pinned 64-bit little-endian byte model
/// ([`module_targets_pinned_byte_model`], which replaces the v2
/// fat-pointer-only target gate). The core classifier
/// (`trust_ir::ConformanceSubset`) also stops admitting `Dealloc`, which this
/// mirror dropped in v2 (G18-1) — F-042.
///
/// v4 (2026-09-22, WS2.17) is an EXPANSION: the three v25 B1 scalars
/// `Isize` / `Usize` / `Char` join [`TY_ALLOWLIST_V4`], and one structural
/// condition is ADDED ([`char_origin_violation`], condition 6 — a `Char` may
/// only originate from a `Const` or a `ZExt` of a `U8`). Every v3 module is a
/// valid v4 module: condition 6 can only fire on a `Char`, which no v3 module
/// could carry.
/// v5 (2026-10-20) selects the proved wasm32 byte model as well as the
/// unchanged default64 model. No construct name or unrelated condition moves.
pub const SUBSET_VERSION: u32 = 6;

/// `Inst` variants a conforming frontend may emit (54 of 58).
///
/// Excluded (see the spec doc for the full rationale):
/// * `CallCannotUnwind` / `CallIndirectCannotUnwind` — an explicit host-unwind
///   boundary has no executable-model enforcement rule; normal return alone
///   is not its semantics. Rust/Lean/Core refuse and no NoPanic proof follows.
/// * `MakeAggregate` — WS3.5 (2026-09-19) landed it after both subset
///   versions were cut, without its wire tag (since tagged by the v51 INST
///   wire batch) or a backend lowering, and with enum / record construction
///   an honest Lean partial; the spec doc's v3 addendum records the
///   exclusion.
/// * `ArraySplat` (and `Constant::Splat` wherever a constant is emitted, see
///   [`constant_splat_violation`]) — v50 landed them WITH their wire tags,
///   Lean semantics and a lazy interpreter value, but after v3 was cut and
///   without a trust-cg lowering; admission is a subset-contract bump (the
///   spec doc's v3 addendum, 2026-09-23).
/// * `CoroSuspend` — depth ledger "Coroutine resume dispatch": the suspend
///   side is modelled, and since WS2.25 the `stepInst`-sequence equivalence
///   (`semCoroSuspend_step_equiv`) and the whole-module resume state-machine
///   theorem (`CoroGen.coro_two_state_roundtrip`) are PROVED in the Lean
///   package; the instruction stays excluded until a subset version bump
///   admits it with the WS2.1 validator arm as its precondition.
/// * `LandingPad` and `Resume` — modelled under `PanicStrategy::Unwind`
///   (amendment D Part 2, `docs/SPEC_RATIFICATIONS.md` §21: a pad binds
///   `(exception, selector)`, 1 catch-all / 0 cleanup, a typed catch is
///   refused; `Resume` re-raises the exception at its operand's address).
///   Under the `Abort` default both engines fail closed on a directly
///   entered pad and on `Resume`, as before. No consumer lowers a
///   panic=unwind build yet: excluded until a subset bump admits them.
/// * `AssertInvoke` — amendment P (wire v54, the v4 addendum of 2026-10-01):
///   both engines execute it (the panic=abort projection), but no consumer
///   lowers its unwind edge yet, and admitting an opcode no consumer lowers
///   is not admission. A plain sited `Assert` is inside the subset.
/// * `Drop` and `DropInvoke` — amendment D (wire v55, the v4 addendum of
///   2026-10-01): no backend lowers a drop yet; `DropInvoke` is also an
///   unwinding terminator no consumer lowers. Admission (with `Drop`) is the
///   v5 EXPANSION, with trust-cg's lowering and structural condition 9 (every
///   drop resolves).
/// * `InvokeIndirect` — amendment D, Part 2 (wire v56): `CallIndirect`'s
///   unwinding twin. Both engines execute it (its unwind edge under
///   `PanicStrategy::Unwind` only, §21), but no consumer lowers it; v5 admits
///   it with trust-cg's lowering.
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

/// v2 promotes the already-allowlisted pointer trio from the thin-only
/// structural condition to both thin and first-class fat-pointer regimes, and
/// **drops `Dealloc`** (G18-1, 2026-09-01).
///
/// `Dealloc` is the one name v2 removes from v1. It names ONE field (`ptr`)
/// against `HeapAlloc`'s four: no `AllocOrigin`, no layout. Rust's
/// `GlobalAlloc::dealloc` requires the exact `Layout` the allocation was made
/// with, Clean/Swift release goes through the reference-counted runtime, and
/// only C `free` takes a bare pointer — so no conforming backend can select a
/// release path from it, and trust-cg fails closed on it. Listing it as
/// backend-REQUIRED was therefore false. It remains wire-legal and
/// interpreter-executable; see `lowering-target-subset.md`, "Deallocation".
pub const INST_ALLOWLIST_V2: &[&str] = &[
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

/// v3 moves NO name on any axis: the shrink is entirely in the structural
/// conditions ([`is_transmute_scalar`], [`module_targets_pinned_byte_model`]).
/// The v3 lists alias v2 so the checker and the doc-lockstep gate read the
/// current version by name.
pub const INST_ALLOWLIST_V3: &[&str] = INST_ALLOWLIST_V2;
pub const TY_ALLOWLIST_V3: &[&str] = TY_ALLOWLIST_V2;
pub const CASTOP_ALLOWLIST_V3: &[&str] = CASTOP_ALLOWLIST_V2;

/// `Ty` variants a v4 frontend may emit (35 of 40) — v3's 32 plus the three
/// v25 B1 scalars `Isize` / `Usize` / `Char` (WS2.17, F-037).
///
/// This is an EXPANSION under the bump policy, not a re-reading of v3:
/// * `Isize` / `Usize` execute at the Lean model's 64-bit pin
///   (`Ty.bitWidth .Isize = some 64`, `Ty.isSigned .Isize = true`), and the
///   whole module is already pinned to that byte model by v3's structural
///   condition 5 — a wasm32 or big-endian module never reaches this list.
/// * `Char` is a 32-bit unsigned carrier whose inhabitants are the Unicode
///   scalar values. Admitting the TYPE needs the VALIDITY invariant to hold
///   at every origin, which is v4's structural condition 6
///   ([`char_origin_violation`]) plus the reference interpreter's UB check.
pub const TY_ALLOWLIST_V4: &[&str] = &[
    "Array", "Bool", "Char", "Closure", "Enum", "F32", "F64", "FatPtr", "Func", "I128", "I16",
    "I32", "I64", "I8", "Isize", "Never", "Ptr", "PtrConst", "PtrMut", "Rc", "Record", "Ref",
    "RefMut", "Sequence", "Set", "Struct", "Tuple", "U128", "U16", "U32", "U64", "U8", "Unit",
    "Usize", "Vector",
];

/// v4 moves no `Inst` or `CastOp` name: the expansion is on the `Ty` axis
/// ([`TY_ALLOWLIST_V4`]) plus one new structural condition
/// ([`char_origin_violation`]). `FPToSISat` / `FPToUISat` stay excluded —
/// their ay bit-blast encoding is still fail-closed, so the WS2.17 design's
/// interpreter/solver cross-check cannot be a test yet.
pub const INST_ALLOWLIST_V4: &[&str] = INST_ALLOWLIST_V3;
pub const CASTOP_ALLOWLIST_V4: &[&str] = CASTOP_ALLOWLIST_V3;

/// v5 changes target selection only. Keep every construct axis identical.
pub const INST_ALLOWLIST_V5: &[&str] = INST_ALLOWLIST_V4;
pub const TY_ALLOWLIST_V5: &[&str] = TY_ALLOWLIST_V4;
pub const CASTOP_ALLOWLIST_V5: &[&str] = CASTOP_ALLOWLIST_V4;
pub const DIALECT_OP_ALLOWLIST_V5: &[&str] = DIALECT_OP_ALLOWLIST_V3;
pub const PROOF_ALLOWLIST_V5: &[&str] = PROOF_ALLOWLIST_V3;

/// v6 adds nominal, authenticated zero-byte function-item values. Existing
/// instruction/cast/target exclusions retain their v5 meanings.
pub const INST_ALLOWLIST_V6: &[&str] = INST_ALLOWLIST_V5;
pub const TY_ALLOWLIST_V6: &[&str] = &[
    "Array", "Bool", "Char", "Closure", "Enum", "F32", "F64", "FatPtr", "FnItem", "Func", "I128",
    "I16", "I32", "I64", "I8", "Isize", "Never", "Ptr", "PtrConst", "PtrMut", "Rc", "Record",
    "Ref", "RefMut", "Sequence", "Set", "Struct", "Tuple", "U128", "U16", "U32", "U64", "U8",
    "Unit", "Usize", "Vector",
];
pub const CASTOP_ALLOWLIST_V6: &[&str] = CASTOP_ALLOWLIST_V5;
pub const DIALECT_OP_ALLOWLIST_V6: &[&str] = DIALECT_OP_ALLOWLIST_V5;
pub const PROOF_ALLOWLIST_V6: &[&str] = PROOF_ALLOWLIST_V5;

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
pub const DIALECT_OP_ALLOWLIST_V3: &[&str] = DIALECT_OP_ALLOWLIST_V2;

/// `ProofAnnotation` variants a conforming frontend may emit (36 of 40).
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
pub const PROOF_ALLOWLIST_V3: &[&str] = PROOF_ALLOWLIST_V2;

fn allow(list: &[&str], name: &str) -> bool {
    list.contains(&name)
}

/// True for the scalar types a `Transmute` may reinterpret between (the Lean
/// `semCast` scalar partial, structural condition 1): `I8`–`I128` /
/// `U8`–`U128` / `Ptr`, on BOTH sides. Mirrors `transmute_scalar_ty`
/// (`trust_ir::bridge`) and `transmuteScalarTy` (`Semantics/Cast.lean`).
///
/// v3 removed `F32` / `F64` / `Bool` (soundness erratum, WS2.9): the Lean
/// model has no byte buffer, so it refused a float/bool SOURCE but
/// MISTRANSLATED a float/bool DESTINATION — `transmute u32 -> f32` bound an
/// integer value at a float type, `transmute u8 -> bool` bound a `Bool` whose
/// payload could exceed 1. The sanctioned int↔float reinterpret is `Bitcast`.
/// `F16`, the pointer-width ints and `Char` are absent because they are
/// outside the type subset altogether.
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
            | Ty::Ptr
    )
}

/// Structural condition 6 (v4): **a `Char` value may originate only from a
/// range-validated `Const` or from `Cast ZExt` of a `U8`.**
///
/// `Ty::Char` is a 32-bit carrier whose inhabitants are the Unicode scalar
/// values (`0..=0x10FFFF` minus the surrogate block `0xD800..=0xDFFF`), so
/// admitting the type (v4) is only sound while every way of MAKING one
/// re-establishes that invariant:
///
/// * `Const` — `validate_module` checks the literal's range
///   (`char_constant_out_of_range`), so a constant origin is checked at
///   build time.
/// * `Cast { op: ZExt, src_ty: U8, dst_ty: Char }` — every `u8` is a valid
///   Unicode scalar value, so the invariant holds by construction. This is
///   the ONE admitted computed origin.
///
/// Every other origin that NAMES `Char` as the type it produces is refused:
/// a `Transmute` or `Bitcast` into `Char` (a byte reinterpretation of an
/// arbitrary 32-bit pattern), a `Trunc`/`SExt`/`IntToPtr`-style cast into
/// `Char`, and a `Load` / `AtomicLoad` / `LoadSlot` at a type that mentions
/// `Char` (a memory read of bytes the model cannot constrain). The reference
/// interpreter independently treats an invalid `Char` as UB at every bind
/// site, so an out-of-subset module still fails closed rather than carrying
/// a bad scalar silently.
///
/// Returns the reason a violating instruction is out of subset, or `None`.
/// Mirrors `trust_ir::ConformanceSubset::char_origin_excluded`; the
/// `bridge_subset_agreement` gate pins the two verdict-identical.
pub fn char_origin_violation(inst: &Inst) -> Option<&'static str> {
    match inst {
        Inst::Cast {
            op, src_ty, dst_ty, ..
        } if ty_carries_char_value(dst_ty) => {
            (!(*op == CastOp::ZExt && *src_ty == Ty::U8 && *dst_ty == Ty::Char)).then_some(
                "a `Char` may originate only from a range-validated `Const` or `Cast ZExt` of a \
                 `U8` (subset v4 condition 6)",
            )
        }
        Inst::Load { ty, .. } | Inst::AtomicLoad { ty, .. } | Inst::LoadSlot { ty, .. }
            if ty_carries_char_value(ty) =>
        {
            Some(
                "a `Char` may not be READ FROM MEMORY: its Unicode-scalar-value invariant is not \
                 re-established by a load (subset v4 condition 6)",
            )
        }
        _ => None,
    }
}

/// True when a value of `ty` CARRIES a `Char` by value — `Char` itself, a
/// vector of them, or a tuple with one somewhere inside.
///
/// Deliberately NOT true through a pointer arm (`Ref` / `RefMut` /
/// `PtrConst` / `PtrMut` / `Rc`): loading a `&char` produces a POINTER, not a
/// `Char`, so condition 6 has nothing to say about it and refusing it would
/// over-refuse. This is the INLINE surface only; a named aggregate names its
/// members through a module table, resolved by [`CharCarriers`].
fn ty_carries_char_value(ty: &Ty) -> bool {
    match ty {
        Ty::Char => true,
        Ty::Vector(inner, _) | Ty::Tensor(inner, _) => ty_carries_char_value(inner),
        Ty::Tuple(xs) => xs.iter().any(ty_carries_char_value),
        _ => false,
    }
}

/// Condition 6's `Char`-by-value verdict for every type node of one module:
/// whether a value of a type CARRIES a `Char` by value, **resolving named
/// aggregates through the module tables** (WS2.17 review).
///
/// [`ty_carries_char_value`] sees the inline type surface only, which lets a
/// producer spell the refused origin one level down: `load { char }` or
/// `load [char; 1]` plus an `ExtractField` / `ExtractElement` makes a `Char`
/// out of arbitrary memory bytes while every instruction looks in-subset. A
/// type carries a `Char` when, through tuple and vector elements, `Array` /
/// `Sequence` / `Set` / `Refine` entries, the definition an id resolves to
/// (`Module::struct_def` and its twins) and a closure's captures, it reaches
/// a `Char`, an id that resolves to nothing (a malformed module: the verdict
/// fails closed), or a by-value cycle (an infinitely large type, which the
/// validator refuses on its own). Pointer arms stop it.
///
/// Built once per module, in O(its types): every node's members are scanned
/// once, then the nodes are PEELED in reverse topological order (a node goes
/// once every member it names has gone, taking their verdicts), and every
/// node left unpeeled reaches a cycle. There is no depth limit. This mirror
/// replaced a native recursion with a 24-level budget that answered "carries
/// a `Char`" when it ran out (refusing every char-free type 24 levels deep)
/// and walked a shared sub-type once per path.
///
/// Mirrors `trust_ir::ConformanceSubset`'s `ty_carries_char_value_in`, which
/// decides the same predicate by another algorithm (a per-node memo that
/// finds cycles as strongly connected components).
#[derive(Debug, Clone)]
pub struct CharCarriers {
    /// Per node: does it carry a `Char` (see above)?
    carries: Vec<bool>,
    /// The type-table entry `i` is node `i`; the closure type `i` is node
    /// `types + i`.
    types: usize,
    closures: usize,
    /// The node of each struct, enum and record id the module defines.
    structs: HashMap<u32, usize>,
    enums: HashMap<u32, usize>,
    records: HashMap<u32, usize>,
    work: u64,
}

/// A table node a type names, or a dangling reference.
enum CharMember {
    Node(usize),
    Dangling,
}

/// The most type nodes [`CharCarriers::of`] builds verdicts for: the bulk
/// allocations it makes are one entry per node, and the hardened profile
/// bounds a bulk allocation below 2^28 elements. A module with more nodes
/// FAILS CLOSED ([`CharCarriers::refuse_all`]): every aggregate it names is
/// answered "carries a `Char`".
const MAX_CHAR_CARRIER_NODES: usize = (1 << 28) - 1;

/// The row each id of a definition table resolves to, as `Module::struct_def`
/// resolves it: the row at the id's position when it has that id, else the
/// first row with it. `ids` is the table's ids, row by row.
fn resolved_rows(ids: &[u32]) -> HashMap<u32, usize> {
    let mut rows: HashMap<u32, usize> = HashMap::new();
    for (at, &id) in ids.iter().enumerate() {
        rows.entry(id).or_insert(at);
    }
    for (id, at) in &mut rows {
        if let Ok(position) = usize::try_from(*id)
            && ids.get(position) == Some(id)
        {
            *at = position;
        }
    }
    rows
}

/// Number each id of `rows` from `first` on: the numbering and the next free
/// node number; `None` when a node number would reach
/// [`MAX_CHAR_CARRIER_NODES`]. By value, so the caller's count is never
/// borrowed and its bound check stays a plain local comparison.
fn number_rows(rows: &HashMap<u32, usize>, first: usize) -> Option<(HashMap<u32, usize>, usize)> {
    let mut numbered = HashMap::new();
    let mut next = first;
    for &id in rows.keys() {
        if next >= MAX_CHAR_CARRIER_NODES {
            return None;
        }
        numbered.insert(id, next);
        next += 1;
    }
    Some((numbered, next))
}

impl CharCarriers {
    /// The verdicts of every type node of `module`.
    ///
    /// Every table access is checked: an access the numbering makes
    /// impossible still fails CLOSED (the node, or the whole module, carries)
    /// rather than panicking.
    #[must_use]
    pub fn of(module: &Module) -> Self {
        let struct_ids: Vec<u32> = module.structs.iter().map(|def| def.id.index()).collect();
        let enum_ids: Vec<u32> = module.enums.iter().map(|def| def.id.index()).collect();
        let record_ids: Vec<u32> = module.records.iter().map(|def| def.id.index()).collect();
        let struct_rows = resolved_rows(&struct_ids);
        let enum_rows = resolved_rows(&enum_ids);
        let record_rows = resolved_rows(&record_ids);
        let types = module.types.len();
        let closures = module.closure_types.len();
        let Some(base) = types
            .checked_add(closures)
            .filter(|&count| count <= MAX_CHAR_CARRIER_NODES)
        else {
            return Self::refuse_all(0);
        };
        let Some((structs, after_structs)) = number_rows(&struct_rows, base) else {
            return Self::refuse_all(0);
        };
        let Some((enums, after_enums)) = number_rows(&enum_rows, after_structs) else {
            return Self::refuse_all(0);
        };
        let Some((records, count)) = number_rows(&record_rows, after_enums) else {
            return Self::refuse_all(0);
        };
        let mut carriers = CharCarriers {
            carries: Vec::new(),
            types,
            closures,
            structs,
            enums,
            records,
            work: 0,
        };

        // Every node's member types, scanned once: its seed, and the nodes
        // it names.
        let mut member_types: Vec<(usize, &Ty)> = Vec::new();
        member_types.extend(module.types.iter().enumerate());
        for (index, closure) in module.closure_types.iter().enumerate() {
            let Some(node) = types.checked_add(index) else {
                return Self::refuse_all(0);
            };
            member_types.extend(closure.captures.iter().map(|ty| (node, ty)));
        }
        for (id, &at) in &struct_rows {
            let (Some(&node), Some(def)) = (carriers.structs.get(id), module.structs.get(at))
            else {
                return Self::refuse_all(0);
            };
            member_types.extend(def.fields.iter().map(|f| (node, &f.ty)));
        }
        for (id, &at) in &enum_rows {
            let (Some(&node), Some(def)) = (carriers.enums.get(id), module.enums.get(at)) else {
                return Self::refuse_all(0);
            };
            member_types.extend(
                def.variants
                    .iter()
                    .flat_map(|variant| &variant.fields)
                    .map(|ty| (node, ty)),
            );
        }
        for (id, &at) in &record_rows {
            let (Some(&node), Some(def)) = (carriers.records.get(id), module.records.get(at))
            else {
                return Self::refuse_all(0);
            };
            member_types.extend(def.fields.iter().map(|f| (node, &f.ty)));
        }
        let mut work = 0u64;
        // `number_rows` already stops short of the bound; it is restated here,
        // where the per-node allocations it bounds are made.
        if count > MAX_CHAR_CARRIER_NODES {
            return Self::refuse_all(0);
        }
        let mut carries = vec![false; count];
        // Per node: the nodes that name it, and how many of its members are
        // not peeled yet.
        let mut named_by: Vec<Vec<usize>> = vec![Vec::new(); count];
        let mut waiting = vec![0usize; count];
        let mut named = Vec::new();
        for (node, ty) in member_types {
            named.clear();
            // A dangling reference fails closed.
            let mut carried = carriers.scan(ty, &mut named, &mut work);
            for member in &named {
                work = work.saturating_add(1);
                match member {
                    CharMember::Dangling => carried = true,
                    CharMember::Node(member) => {
                        // An edge that cannot be recorded leaves `node`
                        // carrying: never peeled is never cleared.
                        let recorded = match (named_by.get_mut(*member), waiting.get_mut(node)) {
                            (Some(by), Some(left)) => left.checked_add(1).map(|more| {
                                *left = more;
                                by.push(node);
                            }),
                            _ => None,
                        };
                        carried |= recorded.is_none();
                    }
                }
            }
            if carried && let Some(verdict) = carries.get_mut(node) {
                *verdict = true;
            }
        }

        // Peel: a node goes once every member it names has gone, taking
        // their verdicts.
        let mut ready: Vec<usize> = waiting
            .iter()
            .enumerate()
            .filter(|&(_, &left)| left == 0)
            .map(|(node, _)| node)
            .collect();
        let mut peeled = vec![false; count];
        while let Some(node) = ready.pop() {
            work = work.saturating_add(1);
            let (Some(gone), Some(&carried), Some(names)) =
                (peeled.get_mut(node), carries.get(node), named_by.get(node))
            else {
                continue;
            };
            *gone = true;
            for &by in names {
                work = work.saturating_add(1);
                if let Some(verdict) = carries.get_mut(by) {
                    *verdict |= carried;
                }
                // Every edge into `by` counted once in `waiting[by]`; one
                // past zero would be a second visit, which never readies it.
                if let Some(left) = waiting.get_mut(by)
                    && *left > 0
                {
                    *left -= 1;
                    if *left == 0 {
                        ready.push(by);
                    }
                }
            }
        }
        // Left unpeeled: on a by-value cycle, or naming a node that reaches
        // one.
        for (carries, peeled) in carries.iter_mut().zip(peeled) {
            *carries |= !peeled;
        }
        carriers.carries = carries;
        carriers.work = work;
        carriers
    }

    /// The fail-closed verdicts: no table node at all, so every member an
    /// aggregate names is `Dangling` and carries a `Char`. Only inline
    /// scalars and pointer arms answer "does not carry".
    fn refuse_all(work: u64) -> Self {
        CharCarriers {
            carries: Vec::new(),
            types: 0,
            closures: 0,
            structs: HashMap::new(),
            enums: HashMap::new(),
            records: HashMap::new(),
            work,
        }
    }

    /// Scan one inline spelling: `true` on an inline `Char`; pushes the table
    /// node of every member it holds by value, or `Dangling` for one the
    /// module does not define. Iterative.
    fn scan(&self, ty: &Ty, out: &mut Vec<CharMember>, work: &mut u64) -> bool {
        let node = |found: Option<usize>| found.map_or(CharMember::Dangling, CharMember::Node);
        let mut pending: Vec<&Ty> = vec![ty];
        while let Some(ty) = pending.pop() {
            *work = work.saturating_add(1);
            match ty {
                Ty::Char => return true,
                // A tensor's element is inline, as a vector's lane is.
                Ty::Vector(inner, _) | Ty::Tensor(inner, _) => pending.push(inner),
                Ty::Tuple(xs) => pending.extend(xs),
                // `Refine` narrows a base type without changing its
                // representation. It is out of subset on its own, but
                // resolving the base keeps the condition-6 verdict honest if
                // it is ever admitted.
                Ty::Array(elem, _)
                | Ty::Sequence(elem)
                | Ty::Set(elem, _)
                | Ty::Refine(elem, _) => {
                    out.push(node(
                        (elem.as_usize() < self.types).then(|| elem.as_usize()),
                    ));
                }
                Ty::Struct(id) => out.push(node(self.structs.get(&id.index()).copied())),
                Ty::Record(id) => out.push(node(self.records.get(&id.index()).copied())),
                Ty::Enum(id) => out.push(node(self.enums.get(&id.index()).copied())),
                // A closure VALUE is its code pointer plus its captured frame,
                // and the frame is carried by value. A node number past
                // `usize` cannot exist: dangling.
                Ty::Closure(id) => out.push(node(if id.as_usize() < self.closures {
                    self.types.checked_add(id.as_usize())
                } else {
                    None
                })),
                // Pointer arms and every scalar: a load at one of these
                // produces no `Char` by value.
                _ => {}
            }
        }
        false
    }

    /// Whether a value of `ty` carries a `Char` by value in the module these
    /// verdicts were built over (ask them of no other). A node these
    /// verdicts do not hold fails closed.
    #[must_use]
    pub fn carries(&self, ty: &Ty) -> bool {
        let mut named = Vec::new();
        self.scan(ty, &mut named, &mut 0)
            || named.iter().any(|member| match member {
                CharMember::Dangling => true,
                CharMember::Node(node) => self.carries.get(*node).copied().unwrap_or(true),
            })
    }

    /// The scans, member edges and peeling steps the verdicts took: O(the
    /// module's types).
    #[must_use]
    pub fn work(&self) -> u64 {
        self.work
    }
}

/// Condition 6 with the module's member tables RESOLVED — the form the
/// module walk uses (WS2.17 review).
///
/// [`char_origin_violation`] classifies one instruction from its inline
/// types alone. The memory arm needs more: `load { char }` reads a `Char`
/// out of arbitrary bytes while naming only a `Ty::Struct`, so the walk must
/// follow the member table the load actually reads.
///
/// This one-shot form builds the module's [`CharCarriers`] (O(its types));
/// the module walk ([`module_subset_violations`]) builds them once and asks
/// [`char_origin_violation_with`] at every instruction.
///
/// Mirrors `trust_ir::ConformanceSubset::char_origin_excluded_in`.
pub fn char_origin_violation_in(module: &Module, inst: &Inst) -> Option<&'static str> {
    char_origin_violation_with(&CharCarriers::of(module), inst)
}

/// [`char_origin_violation_in`] over the verdicts of the instruction's
/// module.
pub fn char_origin_violation_with(carriers: &CharCarriers, inst: &Inst) -> Option<&'static str> {
    if let Some(reason) = char_origin_violation(inst) {
        return Some(reason);
    }
    match inst {
        Inst::Load { ty, .. } | Inst::AtomicLoad { ty, .. } | Inst::LoadSlot { ty, .. }
            if carriers.carries(ty) =>
        {
            Some(
                "a `Char` may not be READ FROM MEMORY: its Unicode-scalar-value invariant is not \
                 re-established by a load (subset v4 condition 6)",
            )
        }
        _ => None,
    }
}

/// Structural condition5, expanded in v5: legacy64 little-endian or
/// canonical wasm32/4-byte little-endian, selected before execution. Other
/// 32-bit ABIs, big-endian and malformed raw sizes remain refused. A raw
/// word-size check never uses `pointer_bits`' malformed-input fallback.
/// Mirrors the independent core classifier; agreement is tested per module.
pub fn module_targets_pinned_byte_model(module: &Module) -> bool {
    module.target_info.as_ref().is_none_or(|target| {
        target.endianness == trust_ir::Endianness::Little
            && (target.pointer_size == PINNED_POINTER_SIZE_BYTES
                || (target.pointer_size == 4 && target.triple.split('-').next() == Some("wasm32")))
    })
}

/// The executable model's pointer width in bytes (`DEFAULT_POINTER_BITS / 8`).
const PINNED_POINTER_SIZE_BYTES: u32 = trust_ir::shape::DEFAULT_POINTER_BITS / 8;

/// Variant name of a `Ty` (compile-breaks when a variant is added).
pub fn ty_name(ty: &Ty) -> &'static str {
    match ty {
        Ty::I8 => "I8",
        // v25 B1 scalars (NOT in the lowering-target subset yet). The reason is
        // the LEAN SEMANTIC-DEPTH ledger, not the backend: `docs/roadmap/
        // B3-lean-ir-parity.md` records the ctors as landed with width/predicate
        // arms while full arithmetic/range semantics and proofs remain the
        // adoption-wave follow-up, and `Char` additionally carries an
        // unmodelled Unicode-scalar validity invariant. trust-cg DOES lower all
        // three (`trust-cg-lower/src/adapter.rs` maps Isize/Usize -> I64 and
        // Char -> I32, with the surrogate range rejected) — the earlier comment
        // blaming it was rotten. `Error` is never wire-legal.
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
        Ty::FnItem(_) => "FnItem",
        Ty::Sequence(_) => "Sequence",
        Ty::Set(_, _) => "Set",
        Ty::Record(_) => "Record",
        Ty::Closure(_) => "Closure",
        // v30 typed value model. Representation-preserving, so it never
        // changes what a backend must lower — the base type does.
        Ty::Refine(_, _) => "Refine",
        Ty::Dialect(_) => "Dialect",
        Ty::Handle(_) => "Handle",
        Ty::Storage(_) => "Storage",
        // PKG-U13a tensor region: no memory layout and no backend lowering,
        // so it is outside the subset (not on `TY_ALLOWLIST_V5`).
        Ty::Tensor(_, _) => "Tensor",
        Ty::Ref(_) => "Ref",
        Ty::RefMut(_) => "RefMut",
        Ty::PtrConst(_) => "PtrConst",
        Ty::PtrMut(_) => "PtrMut",
        Ty::Rc(_) => "Rc",
        Ty::Ext(e) => e.unreachable(),
    }
}

/// Recursively check `ty` (and its structural children) against the current type
/// subset, appending violations tagged with `at`.
///
/// The v2 per-type fat-pointer target gate that lived here is gone: v3's
/// module-level structural condition 5 ([`module_targets_pinned_byte_model`])
/// subsumes it, so a type check needs no target parameters.
fn check_ty(ty: &Ty, at: &str, out: &mut Vec<String>) {
    let name = ty_name(ty);
    if !allow(TY_ALLOWLIST_V6, name) {
        out.push(format!(
            "{at}: Ty::{name} is outside lowering-target subset v{SUBSET_VERSION}"
        ));
    }
    match ty {
        // A tensor's element is an inline child, exactly as a vector's lane.
        Ty::Vector(inner, _)
        | Ty::Tensor(inner, _)
        | Ty::Ref(inner)
        | Ty::RefMut(inner)
        | Ty::PtrConst(inner)
        | Ty::PtrMut(inner)
        | Ty::Rc(inner) => check_ty(inner, at, out),
        Ty::Tuple(xs) => {
            for x in xs {
                check_ty(x, at, out);
            }
        }
        // Id-indexed types (Array/Sequence/Set element `TyId`s, Struct/Enum/
        // Record/Func/Closure defs) are resolved through the module tables,
        // which `module_subset_violations` walks directly.
        _ => {}
    }
}

/// Variant name of an `Inst`: the name of its
/// [`InstShape`](trust_ir::inst::InstShape), so it is the variant's
/// identifier by construction (`variant_shape!` generates the shape enum and
/// `Inst::shape` from one list, and a new variant is a compile error there
/// until it is listed). Every name-level verdict below is keyed on it, and
/// the lockstep gate (`tests/lowering_subset.rs`) classifies every name of
/// `InstShape::ALL`, so no variant reaches the checker unclassified.
pub fn inst_name(inst: &Inst) -> &'static str {
    inst.shape().name()
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
        Some(name) if allow(PROOF_ALLOWLIST_V6, name) => {}
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
    carriers: &CharCarriers,
    inst: &Inst,
    at: &str,
    pointer_bits: u32,
    out: &mut Vec<String>,
) {
    let name = inst_name(inst);
    if !allow(INST_ALLOWLIST_V6, name) {
        out.push(format!(
            "{at}: Inst::{name} is outside lowering-target subset v{SUBSET_VERSION}"
        ));
    }
    // Crystal lane (D3): the WEAK form of an allowlisted variant. A weak compare-exchange may
    // fail spuriously, so its outcome is not a function of the state, and BOTH executable
    // models refuse it (the reference interpreter's `type_error`, the Lean model's
    // `unsupported.weak_cmpxchg`). Like `Drop`, it is emitted for the derived-MIR channel and
    // stays off the proven path; a strong `CmpXchg` is unaffected.
    if matches!(inst, Inst::CmpXchg { weak: true, .. }) {
        out.push(format!(
            "{at}: weak Inst::CmpXchg (spurious failure; no executable semantics) is outside \
             lowering-target subset v{SUBSET_VERSION}"
        ));
    }
    // Crystal lane (E3b): an UNWRITTEN aggregate lane (`Constant::Uninit`). Both executable
    // models define it, but the backend does not lower it: the callee sidecar emits it for
    // execution, never for codegen (structural condition 8 in lowering-target-subset.md).
    if let Inst::Const { value, .. } = inst
        && value
            .try_visit_constants(|c| {
                if matches!(c, trust_ir::Constant::Uninit) {
                    core::ops::ControlFlow::Break(())
                } else {
                    core::ops::ControlFlow::Continue(())
                }
            })
            .is_break()
    {
        out.push(format!(
            "{at}: Const carrying an unwritten lane (uninit) is outside lowering-target \
             subset v{SUBSET_VERSION}"
        ));
    }

    // Structural condition 6 (v4): a `Char` origin must re-establish the
    // Unicode-scalar-value invariant. Resolved against the module's member
    // tables (WS2.17 review) — `load { char }` names no `Char` inline.
    if let Some(reason) = char_origin_violation_with(carriers, inst) {
        out.push(format!(
            "{at}: Inst::{name}: {reason} in lowering-target subset v{SUBSET_VERSION}"
        ));
    }

    // Structural conditions + embedded-type checks.
    match inst {
        Inst::Cast {
            op, src_ty, dst_ty, ..
        } => {
            let op_name = castop_name(*op);
            if !allow(CASTOP_ALLOWLIST_V6, op_name) {
                out.push(format!(
                    "{at}: CastOp::{op_name} is outside lowering-target subset v{SUBSET_VERSION}"
                ));
            }
            if *op == CastOp::Transmute
                && !(is_transmute_scalar(src_ty) && is_transmute_scalar(dst_ty))
            {
                out.push(format!(
                    "{at}: non-scalar Transmute ({src_ty} -> {dst_ty}) is outside lowering-target \
                     subset v{SUBSET_VERSION} (scalar-to-scalar only: I8-I128 / U8-U128 / Ptr on \
                     both sides; int<->float is `Bitcast`)"
                ));
            }
            check_ty(src_ty, at, out);
            check_ty(dst_ty, at, out);
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
            check_ty(ptr_ty, at, out);
            check_ty(metadata_ty, at, out);
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
            check_ty(ptr_ty, at, out);
        }
        Inst::DialectOp(op) => {
            let qualified = op.qualified_name();
            if !DIALECT_OP_ALLOWLIST_V6.contains(&qualified.as_str()) {
                out.push(format!(
                    "{at}: dialect op `{qualified}` is outside lowering-target subset \
                     v{SUBSET_VERSION} (no proven lowering)"
                ));
            }
            for t in &op.result_tys {
                check_ty(t, at, out);
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
        | Inst::MakeAggregate { ty, .. }
        | Inst::ArraySplat { ty, .. }
        | Inst::TensorContract { ty, .. }
        | Inst::TensorMap { ty, .. }
        | Inst::TensorReduce { ty, .. }
        | Inst::TensorView { ty, .. }
        | Inst::TensorGather { ty, .. }
        | Inst::TensorScatter { ty, .. }
        | Inst::ExtractElement { ty, .. }
        | Inst::InsertElement { ty, .. }
        | Inst::Undef { ty }
        | Inst::Copy { ty, .. }
        | Inst::Select { ty, .. }
        | Inst::LoadSlot { ty, .. } => check_ty(ty, at, out),
        // v50: a constant carrying a `Constant::Splat` anywhere is outside
        // the subset (the core classifier's `constant_splat_excluded`).
        Inst::Const { ty, value } => {
            constant_splat_violation(value, at, out);
            check_ty(ty, at, out);
        }
        Inst::GEP { pointee_ty, .. } => check_ty(pointee_ty, at, out),
        Inst::OpenFrame { def } => {
            for slot in &def.slots {
                check_ty(&slot.ty, at, out);
            }
        }
        _ => {}
    }
}

/// v50: `Constant::Splat` at any depth of an emitted constant (an `Inst::Const`
/// value or a global initializer) is outside the subset until a
/// subset-contract bump admits the uniform array with a backend lowering.
/// The reason text is the core classifier's
/// ([`trust_ir::bridge::constant_splat_excluded`]), so the two spellings
/// cannot drift.
fn constant_splat_violation(constant: &trust_ir::Constant, at: &str, out: &mut Vec<String>) {
    if let Some(reason) = trust_ir::bridge::constant_splat_excluded(constant) {
        out.push(format!(
            "{at}: {reason}; outside lowering-target subset v{SUBSET_VERSION}"
        ));
    }
}

fn check_function(
    module: &Module,
    carriers: &CharCarriers,
    func: &Function,
    pointer_bits: u32,
    out: &mut Vec<String>,
) {
    let fname = &func.name;
    for p in &func.proofs {
        check_proof(p, &format!("fn `{fname}` proofs"), out);
    }
    // Structural condition 4 needs the callee's TYPE, which only the
    // function's value typing gives; computed once, and only for a function
    // that has an indirect call at all.
    let mut value_types: Option<BTreeMap<trust_ir::ValueId, Ty>> = None;
    for block in &func.blocks {
        let bid = block.id.index();
        for (_, ty) in &block.params {
            check_ty(ty, &format!("fn `{fname}` bb{bid} params"), out);
        }
        for (i, node) in block.body.iter().enumerate() {
            let at = format!("fn `{fname}` bb{bid} inst #{i}");
            check_inst(carriers, &node.inst, &at, pointer_bits, out);
            // Structural condition 4: closure APPLICATION (a `CallIndirect`
            // whose callee is a `Ty::Closure` value) is outside the subset.
            // The reason text is the core classifier's, so the two spellings
            // cannot drift.
            if let Inst::CallIndirect { callee, .. } = &node.inst {
                let types = value_types.get_or_insert_with(|| {
                    func.typed_values(module)
                        .into_iter()
                        .map(|entry| (entry.value, entry.ty))
                        .collect()
                });
                if matches!(types.get(callee), Some(Ty::Closure(_))) {
                    out.push(format!(
                        "{at}: {} in lowering-target subset v{SUBSET_VERSION}",
                        trust_ir::bridge::CLOSURE_APPLICATION_VIOLATION
                    ));
                }
            }
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
    module_subset_violations_at_version(module, SUBSET_VERSION)
}

/// Check a pinned receipt without treating a future epoch as implemented.
/// Historical old-type behavior is retained; FnItem first appears in v6.
pub fn module_subset_violations_at_version(module: &Module, requested: u32) -> Vec<String> {
    let mut out = Vec::new();
    if let Some(reason) = trust_ir::bridge::module_subset_epoch_violation(module, requested) {
        out.push(format!("module: {reason}"));
    }
    // Structural condition 5 (v3) is a WHOLE-MODULE property: reported once,
    // before any construct, and even for a module with no functions (its type
    // table and globals are still laid out against a byte model the proven
    // semantics do not describe).
    if !module_targets_pinned_byte_model(module) {
        out.push(module_target_violation(module));
    }
    let pointer_bits = module.pointer_bits();
    for (i, t) in module.types.iter().enumerate() {
        check_ty(t, &format!("module.types[{i}]"), &mut out);
    }
    for (i, ft) in module.func_types.iter().enumerate() {
        for t in ft.params.iter().chain(ft.returns.iter()) {
            check_ty(t, &format!("module.func_types[{i}]"), &mut out);
        }
    }
    for sd in &module.structs {
        for f in &sd.fields {
            check_ty(&f.ty, &format!("struct `{}`", sd.name), &mut out);
        }
    }
    for ed in &module.enums {
        for v in &ed.variants {
            for t in &v.fields {
                check_ty(t, &format!("enum `{}`", ed.name), &mut out);
            }
        }
    }
    for rd in &module.records {
        for f in &rd.fields {
            check_ty(&f.ty, &format!("record `{}`", rd.name), &mut out);
        }
    }
    for (i, ct) in module.closure_types.iter().enumerate() {
        for t in &ct.captures {
            check_ty(t, &format!("module.closure_types[{i}]"), &mut out);
        }
    }
    for g in &module.globals {
        let at = format!("global `{}`", g.name);
        check_ty(&g.ty, &at, &mut out);
        if let Some(initializer) = &g.initializer {
            constant_splat_violation(initializer, &at, &mut out);
        }
    }
    // Condition 6's verdicts, decided once for the whole module.
    let carriers = CharCarriers::of(module);
    for f in &module.functions {
        check_function(module, &carriers, f, pointer_bits, &mut out);
    }
    out
}

/// The condition-5 violation text, naming the pinned target that failed it.
fn module_target_violation(module: &Module) -> String {
    let got = match &module.target_info {
        Some(target) => format!(
            "{}-byte pointers, {}-endian ({})",
            target.pointer_size,
            match target.endianness {
                trust_ir::Endianness::Little => "little",
                trust_ir::Endianness::Big => "big",
            },
            target.triple
        ),
        None => "no target".to_string(),
    };
    format!(
        "module target is outside the executable model's pinned byte model in lowering-target \
         subset v{SUBSET_VERSION} (structural condition 5: `target_info` absent, or \
         little-endian with pointer_size == {PINNED_POINTER_SIZE_BYTES}, or \
         wasm32 with pointer_size == 4; got {got})"
    )
}

/// Sanity guards over the constants themselves (sortedness gives stable
/// diffs; sets must not overlap with their documented exclusions).
#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeSet;

    /// The fail-closed verdicts answer "carries" for every aggregate, so a
    /// module past `MAX_CHAR_CARRIER_NODES` refuses every aggregate load.
    #[test]
    fn refused_verdicts_fail_closed_on_every_aggregate() {
        use trust_ir::{ClosureTyId, EnumId, RecordId, StructId, TyId};
        let refused = CharCarriers::refuse_all(0);
        for ty in [
            Ty::Struct(StructId::new(0)),
            Ty::Enum(EnumId::new(0)),
            Ty::Record(RecordId::new(0)),
            Ty::Closure(ClosureTyId::new(0)),
            Ty::Array(TyId::new(0), 1),
            Ty::Sequence(TyId::new(0)),
            Ty::Tuple(vec![Ty::I32, Ty::Struct(StructId::new(7))]),
            Ty::Char,
        ] {
            assert!(refused.carries(&ty), "{ty} must fail closed");
        }
        for ty in [
            Ty::I32,
            Ty::Bool,
            Ty::Unit,
            Ty::Ptr,
            Ty::Tuple(vec![Ty::U8]),
        ] {
            assert!(!refused.carries(&ty), "{ty} carries no Char by value");
        }
    }

    /// `resolved_rows` resolves an id as `Module::struct_def` does: the row
    /// at the id's position when it has that id, else the first row with it.
    #[test]
    fn resolved_rows_prefers_the_positional_row_then_the_first() {
        let rows = resolved_rows(&[1, 1, 9, 9, u32::MAX]);
        assert_eq!(rows.get(&1), Some(&1), "position 1 holds id 1");
        assert_eq!(
            rows.get(&9),
            Some(&2),
            "position 9 is past the table: first row"
        );
        assert_eq!(rows.get(&u32::MAX), Some(&4));
        assert_eq!(rows.len(), 3);
        assert!(resolved_rows(&[]).is_empty());
    }

    /// Node numbering stops short of `MAX_CHAR_CARRIER_NODES` instead of
    /// overflowing, so every per-node allocation stays under the bound.
    #[test]
    fn node_numbering_stops_at_the_bound() {
        let rows: HashMap<u32, usize> = [(3, 0), (4, 1)].into_iter().collect();
        let (numbered, next) =
            number_rows(&rows, MAX_CHAR_CARRIER_NODES - 2).expect("two nodes fit");
        assert_eq!(next, MAX_CHAR_CARRIER_NODES);
        let mut nodes: Vec<usize> = numbered.values().copied().collect();
        nodes.sort_unstable();
        assert_eq!(
            nodes,
            [MAX_CHAR_CARRIER_NODES - 2, MAX_CHAR_CARRIER_NODES - 1]
        );
        assert!(
            number_rows(&rows, MAX_CHAR_CARRIER_NODES - 1).is_none(),
            "the second node is past the bound"
        );
        assert!(number_rows(&rows, usize::MAX).is_none());
        assert_eq!(
            number_rows(&HashMap::new(), usize::MAX).map(|(_, next)| next),
            Some(usize::MAX),
            "no rows, no node"
        );
    }

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
        assert_sorted_unique("INST_ALLOWLIST_V3", INST_ALLOWLIST_V3);
        assert_sorted_unique("TY_ALLOWLIST_V3", TY_ALLOWLIST_V3);
        assert_sorted_unique("CASTOP_ALLOWLIST_V3", CASTOP_ALLOWLIST_V3);
        assert_sorted_unique("DIALECT_OP_ALLOWLIST_V3", DIALECT_OP_ALLOWLIST_V3);
        assert_sorted_unique("PROOF_ALLOWLIST_V3", PROOF_ALLOWLIST_V3);
        assert_sorted_unique("INST_ALLOWLIST_V4", INST_ALLOWLIST_V4);
        assert_sorted_unique("TY_ALLOWLIST_V4", TY_ALLOWLIST_V4);
        assert_sorted_unique("CASTOP_ALLOWLIST_V4", CASTOP_ALLOWLIST_V4);
    }

    #[test]
    fn v5_moves_no_construct_name() {
        assert_eq!(INST_ALLOWLIST_V5, INST_ALLOWLIST_V4);
        assert_eq!(TY_ALLOWLIST_V5, TY_ALLOWLIST_V4);
        assert_eq!(CASTOP_ALLOWLIST_V5, CASTOP_ALLOWLIST_V4);
        assert_eq!(DIALECT_OP_ALLOWLIST_V5, DIALECT_OP_ALLOWLIST_V3);
        assert_eq!(PROOF_ALLOWLIST_V5, PROOF_ALLOWLIST_V3);
    }

    /// v4 is an EXPANSION on the `Ty` axis ONLY: `TY_ALLOWLIST_V4` is v3's
    /// list plus exactly the three v25 B1 scalars, and no `Inst` or `CastOp`
    /// name moves. A future edit that quietly drops a v3 name (a SHRINK
    /// dressed as an expansion) fails here.
    #[test]
    fn v4_adds_exactly_the_b1_scalars_and_moves_nothing_else() {
        let added: BTreeSet<&str> = TY_ALLOWLIST_V4
            .iter()
            .copied()
            .filter(|name| !TY_ALLOWLIST_V3.contains(name))
            .collect();
        assert_eq!(
            added,
            BTreeSet::from(["Char", "Isize", "Usize"]),
            "v4 adds exactly the three v25 B1 scalars"
        );
        for name in TY_ALLOWLIST_V3 {
            assert!(
                TY_ALLOWLIST_V4.contains(name),
                "v4 is an EXPANSION: it may not drop the v3 name `{name}`"
            );
        }
        assert_eq!(INST_ALLOWLIST_V4, INST_ALLOWLIST_V3);
        assert_eq!(CASTOP_ALLOWLIST_V4, CASTOP_ALLOWLIST_V3);
        // `FPToSISat` / `FPToUISat` stay out until their ay encoding lands.
        assert!(!CASTOP_ALLOWLIST_V4.contains(&"FPToSISat"));
        assert!(!CASTOP_ALLOWLIST_V4.contains(&"FPToUISat"));
    }

    /// v3 is a structural-condition shrink: every allowlist NAME is v2's.
    #[test]
    fn v3_moves_no_allowlist_name() {
        assert_eq!(INST_ALLOWLIST_V3, INST_ALLOWLIST_V2);
        assert_eq!(TY_ALLOWLIST_V3, TY_ALLOWLIST_V2);
        assert_eq!(CASTOP_ALLOWLIST_V3, CASTOP_ALLOWLIST_V2);
        assert_eq!(DIALECT_OP_ALLOWLIST_V3, DIALECT_OP_ALLOWLIST_V2);
        assert_eq!(PROOF_ALLOWLIST_V3, PROOF_ALLOWLIST_V2);
    }

    /// v3 structural condition 1: the Transmute scalar set is integer/pointer
    /// only. v2's `F32` / `F64` / `Bool` are gone on both sides.
    #[test]
    fn v3_transmute_scalar_set_is_integer_or_pointer_only() {
        for ty in [
            Ty::I8,
            Ty::I16,
            Ty::I32,
            Ty::I64,
            Ty::I128,
            Ty::U8,
            Ty::U16,
            Ty::U32,
            Ty::U64,
            Ty::U128,
            Ty::Ptr,
        ] {
            assert!(is_transmute_scalar(&ty), "{ty} is a transmute scalar");
        }
        for ty in [
            Ty::F16,
            Ty::F32,
            Ty::F64,
            Ty::Bool,
            Ty::Isize,
            Ty::Usize,
            Ty::Char,
            Ty::Unit,
        ] {
            assert!(
                !is_transmute_scalar(&ty),
                "{ty} is not a transmute scalar in v3"
            );
        }
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

        // `Dealloc` is v2-only exclusion (G18-1): it was allowlisted in v1.
        // `MakeAggregate` (WS3.5) landed after v3 was cut and is recorded as
        // an addendum exclusion until its backend lowering lands (its wire
        // tag landed with the v51 INST wire batch).
        for name in [
            "Dealloc",
            "CoroSuspend",
            "LandingPad",
            "Resume",
            "MakeAggregate",
            "ArraySplat",
            "AssertInvoke",
            "Drop",
            "DropInvoke",
            "InvokeIndirect",
        ] {
            assert!(
                !INST_ALLOWLIST_V2.contains(&name),
                "{name} must be excluded"
            );
        }
        assert!(
            INST_ALLOWLIST_V1.contains(&"Dealloc"),
            "v1 is a frozen historical record and DID allowlist Dealloc"
        );
        for name in ["F16", "Isize", "Usize", "Char", "Error"] {
            assert!(!TY_ALLOWLIST_V2.contains(&name), "{name} must be excluded");
        }
        assert!(TY_ALLOWLIST_V2.contains(&"FatPtr"));
        assert!(!CASTOP_ALLOWLIST_V2.contains(&"ReifyFnPointer"));
        assert!(!DIALECT_OP_ALLOWLIST_V2.contains(&"vector.fma"));
        assert!(!PROOF_ALLOWLIST_V2.contains(&"Custom"));
    }

    /// Crystal lane (E3b): a `Const` carrying an unwritten lane is outside the subset; the
    /// same aggregate with the lane written is inside.
    #[test]
    fn an_uninit_lane_const_is_outside_the_subset_and_a_written_one_is_not() {
        use trust_ir::Constant;
        let pair = Ty::Tuple(vec![Ty::I64, Ty::I64]);
        let konst = |lane| Inst::Const {
            ty: pair.clone(),
            value: Constant::Aggregate(vec![Constant::Int(0), lane]),
        };
        let module = trust_ir::Module::new("uninit_lane");
        let mut written = Vec::new();
        check_inst(
            &CharCarriers::of(&module),
            &konst(Constant::Int(1)),
            "f/bb0#0",
            64,
            &mut written,
        );
        assert!(
            written.is_empty(),
            "a written lane stays in the subset: {written:?}"
        );
        let mut unwritten = Vec::new();
        check_inst(
            &CharCarriers::of(&module),
            &konst(Constant::Uninit),
            "f/bb0#0",
            64,
            &mut unwritten,
        );
        assert_eq!(unwritten.len(), 1, "{unwritten:?}");
    }

    /// Crystal lane (D3): a WEAK compare-exchange is outside the subset although its variant
    /// is allowlisted; the strong one with the same operands is inside.
    #[test]
    fn weak_cmpxchg_is_outside_the_subset_and_strong_is_not() {
        use trust_ir::inst::Ordering;
        use trust_ir::value::ValueId;
        let cas = |weak| Inst::CmpXchg {
            ty: Ty::I64,
            ptr: ValueId::new(0),
            expected: ValueId::new(1),
            desired: ValueId::new(2),
            success: Ordering::SeqCst,
            failure: Ordering::Relaxed,
            weak,
        };
        let module = trust_ir::Module::new("cmpxchg_strength");
        let mut strong = Vec::new();
        check_inst(
            &CharCarriers::of(&module),
            &cas(false),
            "f/bb0#0",
            64,
            &mut strong,
        );
        assert!(
            strong.is_empty(),
            "strong CmpXchg stays in the subset: {strong:?}"
        );
        let mut weak = Vec::new();
        check_inst(
            &CharCarriers::of(&module),
            &cas(true),
            "f/bb0#0",
            64,
            &mut weak,
        );
        assert_eq!(weak.len(), 1, "exactly the weak-form violation: {weak:?}");
        assert!(weak[0].contains("weak Inst::CmpXchg"), "{weak:?}");
    }

    #[test]
    fn allowlist_sizes_match_the_spec_doc_counts() {
        assert_eq!(INST_ALLOWLIST_V1.len(), 54, "Inst: 54 of 58");
        assert_eq!(TY_ALLOWLIST_V1.len(), 31, "Ty: 31 of 38");
        assert_eq!(CASTOP_ALLOWLIST_V1.len(), 14, "CastOp: 14 of 17");
        assert_eq!(DIALECT_OP_ALLOWLIST_V1.len(), 6, "dialect ops: 6");
        assert_eq!(PROOF_ALLOWLIST_V1.len(), 36, "ProofAnnotation: 36 of 40");
        assert_eq!(INST_ALLOWLIST_V2.len(), 53, "Inst v2: 53 of 58");
        assert_eq!(TY_ALLOWLIST_V2.len(), 32, "Ty v2: 32 of 38");
        assert_eq!(CASTOP_ALLOWLIST_V2.len(), 14, "CastOp v2: 14 of 17");
        assert_eq!(DIALECT_OP_ALLOWLIST_V2.len(), 6, "dialect ops v2: 6");
        assert_eq!(PROOF_ALLOWLIST_V2.len(), 36, "ProofAnnotation v2: 36 of 40");
        assert_eq!(INST_ALLOWLIST_V3.len(), 53, "Inst v3: 53 of 58");
        assert_eq!(TY_ALLOWLIST_V3.len(), 32, "Ty v3: 32 of 38");
        assert_eq!(CASTOP_ALLOWLIST_V3.len(), 14, "CastOp v3: 14 of 17");
        assert_eq!(DIALECT_OP_ALLOWLIST_V3.len(), 6, "dialect ops v3: 6");
        assert_eq!(PROOF_ALLOWLIST_V3.len(), 36, "ProofAnnotation v3: 36 of 40");
    }
}
