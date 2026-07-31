// mir_lower — Phase 2 (best-effort) MINIMAL MIR -> trust-ir lowering.
//
// This is a deliberately SMALL, FAIL-LOUD port of trust-cg's `mir_to_trust_ir`,
// hosted on stage1. It lowers ONLY the simplest functions and returns a named
// Err for anything it does not handle, so the driver can tally lowered-ok vs
// failed-by-reason — the failed_roots-equivalent gap map at the lowering level.
//
// ============================== RUNG 0 (scalar SSA) ==========================
//   * locals whose type is a fixed-width scalar integer or bool, never
//     address-taken, modeled as an SSA register value.
//   * terminators: Return, Goto, SwitchInt (on a scalar operand), Unreachable.
//   * statements: Assign of Use / BinaryOp / UnaryOp over scalar operands.
//   * operands: Copy/Move of a bare scalar local; Constant scalar int/bool.
//
// ============================== RUNG 1 (PLACE / memory-backed locals) ========
//   ADDITIVE. Unblocks the dominant "non-scalar local" failure bucket.
//   * Local model: each MIR Local is classified as either an SSA scalar
//     (RUNG 0 behavior, unchanged) OR a MEMORY-BACKED stack slot when its type
//     is a non-scalar aggregate-with-scalar-leaves, OR its address is taken via
//     `Ref`/`RawPtr`/`CopyForDeref`. A memory-backed local gets one stable
//     `Alloca` (sized + aligned from `tcx.layout_of`) in the entry block; reads
//     Load and writes Store through the slot's computed address.
//   * Place projections (Field / Downcast / Deref / Index): compute a place's
//     ADDRESS (a `Ptr`, for `Ref` / assignment-LHS) and its VALUE (a typed
//     `Load`) separately, walking layout_of field offsets. A byte-offset
//     `GEP(I8, base, [offset])` addresses a field; `GEP(elem_ty, base, [index])`
//     addresses an array element.
//   * `Rvalue::Ref(_, _, place)` / `Rvalue::RawPtr(_, place)` -> the place's
//     ADDRESS (a `Ptr`). `Rvalue::CopyForDeref(place)` -> the place's VALUE.
//   * `StorageLive` / `StorageDead` remain no-ops (the slot is allocated once at
//     entry; lifetime markers do not change soundness for this minimal model).
//   * Assign to a PROJECTED place (or to a memory-backed bare local) -> Store at
//     the place address.
//
// ============================== RUNG 2 (cross-block phi + Call + Assert) ======
//   ADDITIVE. The biggest single unlock: real multi-block dataflow + calls.
//   * Cross-block phi (SSA threading): a scalar SSA Local defined in one block
//     and read in another now threads through trust-ir BLOCK PARAMETERS. We run a
//     standard backward liveness over the SSA-scalar locals only; each non-entry
//     block gets one block parameter per scalar local LIVE AT ITS ENTRY (in
//     stable local order), and every edge (`br`/`condbr`/`switch`) passes the
//     predecessor's current value for each successor live-in. This is
//     dominance/liveness-correct: a local is in a successor's live-in only if it
//     is live across the edge, hence live-out of the predecessor, hence either a
//     param of the predecessor block (its own live-in) or defined in it — so the
//     predecessor's env always has a value to pass (never an undefined param).
//     Memory-backed locals thread via their stable slot pointer (no phi).
//   * `TerminatorKind::Call { func, args, destination, target, .. }`: the callee
//     is declared as a 0-block EXTERN `Function` named by its symbol (deduped),
//     with a trust-ir signature SYNTHESIZED FROM THE LOWERED arg/dest types (so
//     the validator's arg/return-type checks pass by construction). Each arg is
//     lowered (scalar via env, memory place via its address `Ptr`); the result
//     binds the destination (scalar -> env def; memory -> Store at dest addr);
//     then `br` to the success `target`. A diverging call (target == None) emits
//     `unreachable` after the call.
//   * `TerminatorKind::Assert { cond, expected, target, .. }`: evaluate `cond`,
//     `condbr` to `target` when it matches `expected`, else a shared trap block
//     (`unreachable`) — the panic path. Unblocks debug overflow-checked
//     arithmetic (AddWithOverflow feeds a tuple dest, still RUNG 3, but the bare
//     bounds/overflow Assert terminator itself now lowers).
//
//   Later rungs (3..9.5, documented at their sites) landed aggregate
//   construction, the general aggregate return/param ABI (sret hidden pointer /
//   by-ref `Ptr` param), faithful enum layout, no-op/dealloc Drops, and a widened
//   cast set. RUNG 10 (below, `pair_ret_model`) upgrades the SMALL-PAIR subset of
//   aggregate returns — a 2-int/bool-lane `BackendRepr::ScalarPair` struct/tuple
//   of <= 16 bytes — from sret to a TRUE BY-VALUE single-SSA-2-tuple return, on
//   every LOWERED body and every IN-MODULE call edge (self-recursion /
//   emit-closure member); bodyless extern declarations keep the landed
//   conservative sret form. RUNG 11 (the DUAL, same `pair_ret_model` predicate +
//   same opt-in flag) does the same for a small-pair PARAM: it crosses BY VALUE as
//   one SSA 2-tuple param (NO by-ref `Ptr`), spilled into its entry slot at fn
//   entry, and the in-module caller passes it by value (whole-aggregate Load).
//   RUNG 11 ALSO pins the ABI classification the earlier rungs left implicit:
//   `byval` on every remaining by-ref aggregate `Ptr` param and `sret` on the
//   hidden return pointer (positional `ParamAttrs`). All of this is OPT-IN via
//   `--mir-pair-ret-by-value` (default OFF = byte-identical emits) — see the
//   RUNG 10 header for why the default flip is a coordinated trust-cg rung.
//
//   Still FAIL-LOUD on what genuinely remains (pointer-lane / enum / >16-byte
//   aggregate params and returns keep the by-ref `Ptr` / sret pointer — now
//   `byval`/`sret`-pinned under the flag, but still crossing through memory; real
//   Drop glue; the remaining Cast families) so the failure buckets stay honest.
//   NOTE: the text format writes `ParamAttrs` as `;`-COMMENT lines (display-only,
//   dropped on re-parse) — the pins live on the built/binary Module and are
//   `validate_module`-checked, but the text round-trip does not yet carry them.
//
// The lowered function is built through the SAME trust_ir_build
// ModuleBuilder/FunctionBuilder used by the THIR path, then validate_module is
// run: "lowered-ok" means validate_module reports 0 errors.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use rustc_abi::{BackendRepr, Integer, Primitive, Size, TagEncoding, VariantIdx, Variants};
use rustc_middle::mir::{
    AggregateKind, AssertKind, BasicBlock, BinOp as MirBinOp, Body, CastKind, ConstOperand,
    ConstValue, Local, Operand, Place, ProjectionElem, Rvalue, StatementKind, TerminatorKind,
    UnOp as MirUnOp,
};
use rustc_middle::mir::interpret::{alloc_range, AllocId, GlobalAlloc, Scalar};
use rustc_middle::ty::layout::LayoutCx;
use rustc_middle::ty::{self, Instance, ScalarInt, Ty, TyCtxt};

use trust_ir::inst::{
    AtomicRMWOp, BinOp, CastOp, FCmpOp, ICmpOp, Ordering as TIROrdering, OverflowOp, SwitchCase,
    UnOp,
};
use trust_ir::Constant;
use trust_ir::Ty as TIRTy;
use trust_ir_build::{validate_module, FunctionBuilder, ModuleBuilder, ValidationError};

use crate::span_map::SpanMap;

/// Reduce a failure reason to a stable HISTOGRAM BUCKET. The raw reasons quote
/// specific MIR shapes; we collapse to the leading category (text before the
/// first `:`), cap the length, so two bails of the same shape share a row.
pub fn bucket_reason(msg: &str) -> String {
    let cat = msg.split(':').next().unwrap_or(msg).trim();
    let collapsed: String = cat.split_whitespace().collect::<Vec<_>>().join(" ");
    let mut b: String = collapsed.chars().take(70).collect();
    if b.is_empty() {
        b = "<empty>".to_string();
    }
    b
}

/// Map a CONCRETE rustc scalar `Ty` to a trust-ir scalar `Ty`. Returns None for
/// anything that is not a fixed-width scalar int, bool, or float.
fn scalar_tir_ty(ty: Ty<'_>) -> Option<TIRTy> {
    match ty.kind() {
        ty::Bool => Some(TIRTy::Bool),
        ty::Int(i) => Some(match i {
            ty::IntTy::I8 => TIRTy::I8,
            ty::IntTy::I16 => TIRTy::I16,
            ty::IntTy::I32 => TIRTy::I32,
            ty::IntTy::I64 => TIRTy::I64,
            ty::IntTy::I128 => TIRTy::I128,
            ty::IntTy::Isize => TIRTy::I64,
        }),
        ty::Uint(u) => Some(match u {
            ty::UintTy::U8 => TIRTy::U8,
            ty::UintTy::U16 => TIRTy::U16,
            ty::UintTy::U32 => TIRTy::U32,
            ty::UintTy::U64 => TIRTy::U64,
            ty::UintTy::U128 => TIRTy::U128,
            ty::UintTy::Usize => TIRTy::U64,
        }),
        // FLOATS: `f32`/`f64` are single-register scalar leaves with first-class
        // trust-ir types and full trust-cg codegen (fadd..frem, fcmp, fsqrt-family,
        // casts, load/store, AAPCS64 v-register call args — all execution-verified).
        // `f16`/`f128` have NO verified backend lowering yet: stay fail-closed
        // (`None`), so a function touching them fails loud, never miscompiles.
        ty::Float(f) => match f {
            ty::FloatTy::F32 => Some(TIRTy::F32),
            ty::FloatTy::F64 => Some(TIRTy::F64),
            ty::FloatTy::F16 | ty::FloatTy::F128 => None,
        },
        _ => None,
    }
}

/// Map a CONCRETE rustc scalar LEAF `Ty` (the memory model can Load/Store with a
/// single typed access) to a trust-ir scalar `Ty`. Like `scalar_tir_ty`, but also
/// admits thin pointers / references as `Ptr` (the leaf width of a `&T` / `*T` /
/// `Box<T>` field). Returns None for fat pointers, aggregates, f16/f128, etc.
fn memory_leaf_tir_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<TIRTy> {
    if let Some(t) = scalar_tir_ty(ty) {
        return Some(t);
    }
    match ty.kind() {
        // A THIN reference / raw pointer is a single pointer-width scalar. A wide
        // (fat) pointer to a slice / str / dyn Trait / unsized-tail struct is a
        // ScalarPair — NOT a single-access leaf — so reject it (its pointee is
        // unsized).
        ty::Ref(_, pointee, _) | ty::RawPtr(pointee, _) => {
            if is_thin_pointee(tcx, *pointee) {
                Some(TIRTy::Ptr)
            } else {
                None
            }
        }
        // THREADS: a FUNCTION POINTER is a single pointer-width CODE pointer.
        // Without this, an `extern "C" fn(..)`-typed local was memory-backed
        // and the call-arg classifier passed its SLOT ADDRESS — `pthread_create`
        // received `&slot` (a stack address) as the start routine and the
        // child thread jumped INTO THE STACK.
        ty::FnPtr(..) => Some(TIRTy::Ptr),
        _ => None,
    }
}

/// Like `memory_leaf_tir_ty`, but ALSO admits a transparent single-scalar-field
/// newtype as its inner scalar (via the layout's `BackendRepr::Scalar`, the same
/// admission `cast_scalar_tir_ty` / `place_leaf_tir_ty` make). Used for PARAMETER
/// and CALL-ARG classification so a memory-backed single-scalar wrapper crosses
/// the ABI BY VALUE — matching how every other USE loads it (`lower_place_value`
/// via `place_leaf_tir_ty`) and how the true (AAPCS64/SysV/C) ABI passes a
/// register-width scalar.
///
/// Two families are admitted:
///   * an INTEGER newtype (`#[repr(transparent)] struct Tag(u8)`) -> its inner
///     integer (hashbrown's `repeat(tag: Tag) -> u64` passes `Tag` as a `u8`);
///   * a POINTER-LAYOUT wrapper (`NonNull`/`Unique`/`Arc`/`Rc`/`Box<Sized>`) ->
///     `Ptr`. This is REQUIRED for correctness: such a memory-backed local (a
///     `NonNull` is always memory-backed — `memory_leaf_tir_ty` rejects the ADT)
///     must be Loaded on the call-argument path exactly as the copy paths Load it,
///     not passed as its slot ADDRESS. Passing the slot address is caught by a
///     BODYLESS EXTERN callee that uses the real by-value C ABI: `grow_impl_runtime`
///     handed `__rust_realloc` the address of the `NonNull` slot instead of the
///     heap pointer, so `realloc` freed a stack slot and aborted. Both the callee
///     param setup (`spill_param`) and `classify_call_arg` consult THIS function,
///     so the two sides of every edge stay in agreement by construction.
///
/// Returns None for a true multi-field aggregate or a FAT wrapper (`Box<[T]>` is a
/// `ScalarPair`, not a `Scalar`), which correctly stays a by-ref aggregate.
fn param_scalar_leaf_tir_ty<'tcx>(cx: &Cx<'tcx, '_>, ty: Ty<'tcx>) -> Option<TIRTy> {
    if let Some(t) = memory_leaf_tir_ty(cx.tcx, ty) {
        return Some(t);
    }
    // LANE S: a `char` is a 4-byte unsigned scalar — `cast_scalar_tir_ty`
    // classifies every char PLACE as `U32`, and the CONSTANT call-arg path
    // already passes char literals by value as `U32`. Without this arm a
    // MEMORY-modeled char (an invoke-result temp under the EH lane) crossed
    // the call ABI as its SLOT ADDRESS, while a constant-char site registered
    // the same callee at `(.., u32)` — the wp14 `String::push(char)`
    // cross-module ABI mismatch (extern decl `(ptr, u32)` vs defining module
    // `(ptr, ptr)`). Admitting char here restores ONE classification for all
    // three sites (callee param spill, memory place arg, constant arg): the
    // by-value `U32` the real AAPCS64 ABI uses.
    if matches!(ty.kind(), ty::Char) {
        return Some(TIRTy::U32);
    }
    // Only an ADT newtype (struct/enum-with-one-variant) is considered; a bare
    // scalar already returned above, and we must not reinterpret a non-ADT type.
    if !matches!(ty.kind(), ty::Adt(_, _)) {
        return None;
    }
    // A single-scalar newtype (integer OR pointer-layout wrapper): pass by value as
    // that scalar. A multi-field / fat aggregate yields `None` and stays by-ref.
    cast_scalar_tir_ty(cx, ty)
}

/// Whether `pointee` is `Sized` in the sense the thin-pointer leaf model needs:
/// a `&T`/`*T` is a single pointer-width scalar iff `T` is sized (a slice / str /
/// dyn Trait pointee makes the reference a fat ScalarPair, which the single-leaf
/// model cannot Load/Store in one access).
///
/// THREADS: the historical SYNTACTIC check (`Slice | Str | Dynamic | Foreign`)
/// missed the UNSIZED-TAIL STRUCT pointees (`CStr` wraps `[c_char]`, `OsStr`
/// wraps `Slice` wraps `[u8]`), silently classifying `&CStr`/`&OsStr` as THIN
/// one-lane pointers — every consumer of their length metadata then failed
/// loud. Concrete (monomorphized) sizedness is exactly `Ty::is_sized`, so ask
/// rustc. The syntactic kinds are kept as a fast path; `Foreign` (extern types)
/// stays THIN by design (it IS `?Sized` but its pointers are thin), matching
/// the historical model.
fn is_thin_pointee<'tcx>(tcx: TyCtxt<'tcx>, pointee: Ty<'tcx>) -> bool {
    match pointee.kind() {
        ty::Slice(_) | ty::Str | ty::Dynamic(_, _) => false,
        ty::Foreign(_) => true,
        _ => pointee.is_sized(tcx, ty::TypingEnv::fully_monomorphized()),
    }
}

/// RUNG 4: whether `ty` is a FAT pointer — a `&T`/`*T`/`Box<T>`-ish reference whose
/// pointee is unsized (slice / str / dyn Trait), so the pointer is a `(data, meta)`
/// ScalarPair: 16 bytes, two pointer-width lanes (data ptr at offset 0, metadata =
/// length `usize` for slice/str or a vtable `*const ()` for dyn at offset 8). We
/// model such a local as a 2-lane (Ptr, U64) memory slot. The DATA half (lane 0) is
/// the address `Deref`/`Index` walks; the METADATA half (lane 1) is read by
/// `PtrMetadata`.
fn fat_pointer_pointee<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
    match ty.kind() {
        ty::Ref(_, pointee, _) | ty::RawPtr(pointee, _) => {
            if is_thin_pointee(tcx, *pointee) {
                None
            } else {
                Some(*pointee)
            }
        }
        _ => None,
    }
}

fn is_fat_pointer<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    fat_pointer_pointee(tcx, ty).is_some()
}

/// UNSIZED-LOCAL carrier (THREADS / `unsized_fn_params`): a LOCAL whose type is
/// itself unsized (`dyn Trait` / `[T]` / `str` — the alloc-crate
/// `<Box<dyn FnOnce>>::call_once` moves `*self` into such a local) is modeled as
/// a 16-byte, 8-aligned (data, metadata) CARRIER slot — rustc's own by-value-
/// unsized ABI (the value travels as its fat pair). Returns the carrier's
/// (size, align), or `None` for every sized type and for unsized types without
/// fat metadata (extern types), which stay on the fail-loud paths.
fn unsized_local_carrier<'tcx>(cx: &Cx<'tcx, '_>, ty: Ty<'tcx>) -> Option<(u64, u64)> {
    if !matches!(
        ty.kind(),
        ty::Dynamic(..) | ty::Slice(_) | ty::Str | ty::Adt(..)
    ) {
        return None;
    }
    let layout = cx
        .tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(ty))
        .ok()?;
    if layout.is_sized() {
        return None;
    }
    Some((16, 8))
}

/// Whether a trust-ir scalar type is signed (selects SDiv/SRem and signed ICmp).
fn is_signed(t: &TIRTy) -> bool {
    matches!(t, TIRTy::I8 | TIRTy::I16 | TIRTy::I32 | TIRTy::I64 | TIRTy::I128)
}

/// Whether a trust-ir scalar type is a float (selects the FAdd..FRem / FCmp /
/// FNeg families instead of the integer ops).
fn is_float_tir(t: &TIRTy) -> bool {
    matches!(t, TIRTy::F16 | TIRTy::F32 | TIRTy::F64)
}

/// How a MIR local is realized in trust-ir.
enum LocalModel {
    /// An SSA scalar register value of this trust-ir type (RUNG 0). Never
    /// address-taken. Held per-block in a `ValueId` env.
    Ssa(TIRTy),
    /// A memory-backed stack slot (RUNG 1). The slot pointer is a single stable
    /// `ValueId` produced by an entry-block `Alloca`; every read Loads and every
    /// write Stores through the place address computed off this pointer.
    Memory(MemSlot),
    /// A ZERO-SIZED local (RUNG 4). Unit `()`, a ZST struct/enum, `PhantomData`, a
    /// captureless (ZST) closure env, etc. A ZST occupies NO storage and NO ABI
    /// slot: it has no address, no value, no bytes. Reads produce nothing (the
    /// value is never observed — a ZST carries no information), Stores are no-ops,
    /// and a ZST argument/return crosses the boundary as zero ABI values. We model
    /// it as a first-class "no-op" local so a function whose ONLY blocker was a ZST
    /// local now lowers. A ZST is DISTINCT from an uninitialized non-ZST (which is
    /// still memory-backed); we only classify a local here when `layout_of` proves
    /// `size == 0`.
    Zst,
}

/// A memory-backed local's stack slot: the `Alloca` pointer plus enough layout
/// metadata to compute typed field/element addresses.
#[derive(Clone)]
struct MemSlot {
    /// The `Alloca` result: a `Ptr` to the slot's first byte.
    ptr: trust_ir::ValueId,
}

/// The interning key for a lazily-materialized module global (see
/// `Cx::const_globals`). A referenced CTFE allocation (a promoted `&STATIC`, or a
/// relocation TARGET inside a const aggregate) is keyed by `AllocId`; a thread-local
/// static (`Rvalue::ThreadLocalRef`) is keyed by its `DefId`.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum InternKey {
    Alloc(AllocId),
    Tls(rustc_span::def_id::DefId),
    /// A `&'static str` / `&'static [u8]` LITERAL, keyed by a content hash so
    /// identical literals share one rodata global (see `intern_str_literal_global`).
    StrBytes(u64),
}

/// A module global QUEUED during lowering (when `mb` is exclusively borrowed by
/// `fb`) and materialized into `mb` AFTER `fb.build()` releases the borrow. Models a
/// referenced static / TLS static as an `Array(U8, size)` blob whose ADDRESS
/// (`GlobalAddr`) is the value we lower a provenance-bearing constant / thread-local
/// reference to.
struct PendingGlobal {
    /// Deterministic module-local symbol name (Internal linkage; referenced only by
    /// `GlobalId`, never by name, so uniqueness within the module is enough).
    name: String,
    /// Byte size of the blob (the referenced allocation's extent).
    size: u64,
    /// Faithful byte image when the referenced static is POINTER-FREE (its bytes can
    /// be frozen); `None` for a TLS slot or a RELOCATED global (below).
    init: Option<Vec<u8>>,
    /// TLS model when this global models a thread-local static (`ThreadLocalRef`).
    tls: Option<trust_ir::TlsModel>,
    /// THREADS: a PROVENANCE-BEARING allocation's faithful image — a mixed
    /// aggregate of frozen bytes and `SymbolAddr` pointer slots (the LocalKey
    /// accessor fn-pointer, a `&&STATIC` chain, a nested const alloc). The old
    /// address-only model zeroed such a global, and any runtime READ of it (the
    /// `SPAWN_HOOKS` LocalKey's `inner` fn ptr) called/used NULL.
    reloc: Option<(TIRTy, Constant)>,
    /// Whether the underlying allocation is mutable (a `static mut`-like CTFE
    /// alloc); frozen consts are read-only.
    mutable: bool,
}

/// State carried while lowering one function.
struct Cx<'tcx, 'm> {
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
    body: &'m Body<'tcx>,
    /// trust-ir scalar type of each SSA scalar MIR local.
    local_ty: HashMap<Local, TIRTy>,
    /// How each local is realized (Ssa vs Memory).
    model: HashMap<Local, LocalModel>,
    /// EMIT mode only (`--mir-emit`): when a `Call` resolves to THIS SAME instance
    /// (a self-recursive call, e.g. `sz(a)` inside `sz`), wire the call to the real
    /// in-module body `FuncId` instead of a separate 0-block extern stub, so the
    /// emitted module is SELF-CONTAINED and round-trips/JITs without binding an
    /// extern. The coverage path (`--mir-lower`) leaves this `false`, so its
    /// behavior — declaring every callee (incl. self) as a 0-block extern — is
    /// UNCHANGED. The validator and JIT both resolve intra-module calls by `FuncId`.
    emit_self_recursion: bool,
    /// ADDITIVE (R3 stage 1 — &str-constant lowering): the per-function registry of
    /// MATERIALIZED `&'static str` / `&'static [u8]` LITERALS. Filled ONCE in the
    /// entry block by `materialize_str_consts` (byte content -> the literal's
    /// immortal heap byte-image pointer + its 16-byte (ptr,len) fat-pair slot);
    /// consulted by the call-arg emission and the fat-dst `Use(Constant)` assign.
    /// Content-keyed (a Vec: a function mentions a handful of literals at most),
    /// in FIRST-APPEARANCE order so emitted IR is deterministic. Functions with
    /// no such literals leave this EMPTY and emit zero extra instructions.
    str_consts: Vec<(Vec<u8>, StrConstMat)>,
    /// DYN/VTABLE rung: the synthesized vtable module global for each DISTINCT
    /// `(concrete self type, dyn destination pointee)` to-`dyn` Unsize coercion
    /// this body performs. Filled by `materialize_dyn_vtables` in the pre-`fb`
    /// pass (it needs `mb` to `add_global`); read by `lower_unsize_assign`'s dyn
    /// branch, which emits `global_addr(gid)` for the fat pointer's vtable lane.
    /// The `GlobalId` is the global's index in `module.globals` — globals are
    /// added EXCLUSIVELY by that pass (one per distinct vtable) over an initially
    /// empty table, so the next id equals `dyn_vtables.len()`. Empty (no drift)
    /// for a body with no to-`dyn` coercion.
    dyn_vtables: HashMap<(Ty<'tcx>, Ty<'tcx>), trust_ir::value::GlobalId>,
    /// LAZILY-interned module globals for provenance-bearing constants (a static
    /// reached through a const pointer, or a relocation TARGET inside a const
    /// aggregate) and thread-local statics (`Rvalue::ThreadLocalRef`). Filled DURING
    /// lowering via interior mutability — at that point `mb` is exclusively borrowed
    /// by `fb`, so the real globals cannot be added yet; their specs accumulate in
    /// `pending_globals` and are pushed to `mb` AFTER `fb.build()` (see
    /// `lower_with_signature`). Keyed so a repeated reference to one static shares a
    /// single global. The assigned `GlobalId` is `dyn_vtables.len() + <index into
    /// pending_globals>`: vtables occupy `0..dyn_vtables.len()` (added by the pre-`fb`
    /// pass), these follow in `pending_globals` order — exactly the final
    /// `module.globals` layout, so `GlobalAddr(gid)` resolves in-range.
    const_globals: std::cell::RefCell<HashMap<InternKey, trust_ir::value::GlobalId>>,
    /// Specs for the globals interned above, in `GlobalId` order; drained into `mb`
    /// once `fb` releases its borrow.
    pending_globals: std::cell::RefCell<Vec<PendingGlobal>>,
    /// UNWIND lane, `#[track_caller]` ABI (rustc 1.99 parity): when THIS body
    /// `requires_caller_location`, the hidden trailing `&'static
    /// core::panic::Location` parameter — a `Ptr` appended AFTER every real
    /// ABI param, exactly where rustc's `FnAbi` appends it (`fn_abi_new_uncached`
    /// chains `caller_location` last). Bound as an ENTRY-block param, so it
    /// dominates every use (the validator's dominance check admits it in any
    /// block, like the sret pointer). `None` for a non-track_caller body and
    /// always `None` under panic=abort (the abort lane keeps the historical
    /// no-hidden-param convention byte-for-byte).
    caller_location: Option<trust_ir::ValueId>,
}

/// ADDITIVE (R3 stage 1): one materialized `&'static str` / `&'static [u8]`
/// LITERAL — where its bytes live and where its (ptr,len) fat pair lives.
struct StrConstMat {
    /// The literal's byte image: the ADDRESS (`GlobalAddr`) of a READ-ONLY module
    /// global holding the literal's exact bytes (a frozen `Bytes` blob, Internal
    /// linkage — see `intern_str_literal_global`). Rodata (not a stack slot) so a
    /// literal reference that ESCAPES the frame — returned, stored into a
    /// longer-lived structure — stays valid, matching `&'static` lifetime semantics,
    /// with NO runtime allocation.
    data_ptr: trust_ir::ValueId,
    /// The 16-byte 2-lane fat-pair slot holding [data_ptr, len]: lane 0 the data
    /// pointer, lane 1 the byte length — the standard fat-pointer slot shape.
    /// Its ADDRESS is what an `ArgAbi::AggByRef` call arg passes (exactly the
    /// convention a lowered callee models its own fat `&str` param with).
    pair_ptr: trust_ir::ValueId,
    /// The literal's byte length (the metadata lane's value).
    len: u64,
}

impl<'tcx, 'm> Cx<'tcx, 'm> {
    fn mono(&self, ty: Ty<'tcx>) -> Ty<'tcx> {
        self.instance.instantiate_mir_and_normalize_erasing_regions(
            self.tcx,
            ty::TypingEnv::fully_monomorphized(),
            ty::EarlyBinder::bind(self.tcx, ty),
        )
    }

    /// Consume rustc's explicit "needs normalization" marker after an API has
    /// already instantiated its generic arguments. MIR lowering only operates
    /// on concrete instances, so a fully-monomorphized typing environment is
    /// the same normalization contract used by `mono` above.
    fn normalize_ty(&self, ty: ty::Unnormalized<'tcx, Ty<'tcx>>) -> Ty<'tcx> {
        self.tcx
            .normalize_erasing_regions(ty::TypingEnv::fully_monomorphized(), ty)
    }

    fn local_concrete_ty(&self, local: Local) -> Ty<'tcx> {
        self.mono(self.body.local_decls[local].ty)
    }

    /// Concrete (monomorphized) type of a PLACE — the type of the leaf the
    /// projection chain addresses. Reuses rustc's own place typing then
    /// monomorphizes.
    fn place_concrete_ty(&self, place: &Place<'tcx>) -> Ty<'tcx> {
        let pty = place.ty(&self.body.local_decls, self.tcx).ty;
        self.mono(pty)
    }

    fn is_memory_local(&self, local: Local) -> bool {
        matches!(self.model.get(&local), Some(LocalModel::Memory(_)))
    }

    fn slot_ptr(&self, local: Local) -> Option<trust_ir::ValueId> {
        match self.model.get(&local) {
            Some(LocalModel::Memory(s)) => Some(s.ptr),
            _ => None,
        }
    }

    fn is_zst_local(&self, local: Local) -> bool {
        matches!(self.model.get(&local), Some(LocalModel::Zst))
    }
}

/// Whether a concrete (monomorphized) type is ZERO-SIZED via `layout_of` (unit,
/// ZST struct/enum, `PhantomData`, captureless closure env, etc.). A ZST occupies
/// no storage and crosses an ABI boundary as zero values. Returns false (not an
/// error) when the layout cannot be computed — an unmodelable type is handled by
/// the normal fail-loud paths, not silently treated as a ZST.
fn ty_is_zst<'tcx>(cx: &Cx<'tcx, '_>, ty: Ty<'tcx>) -> bool {
    cx.tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(ty))
        .map(|tal| tal.is_sized() && tal.size.bytes() == 0)
        .unwrap_or(false)
}

// ===================== lazily-interned module globals ========================
//
// A provenance-bearing constant (a promoted `&STATIC`, or a relocation inside a
// const aggregate) and a thread-local reference (`Rvalue::ThreadLocalRef`) lower to
// the ADDRESS of a module global. Globals can only be added through `mb`, which is
// exclusively borrowed by `fb` during lowering, so we INTERN lazily: assign the
// `GlobalId` now (emitting `GlobalAddr` immediately) and queue the spec, then add
// the real globals after `fb.build()` (`flush_pending_globals`). Vtables occupy
// `0..dyn_vtables.len()`; these follow, matching final `module.globals` order.

/// Reserve/reuse a `GlobalId` for `key` and queue `spec` for post-lowering
/// materialization. Idempotent per key (a repeated reference shares one global).
fn intern_global_spec<'tcx>(
    cx: &Cx<'tcx, '_>,
    key: InternKey,
    spec: impl FnOnce() -> PendingGlobal,
) -> trust_ir::value::GlobalId {
    if let Some(gid) = cx.const_globals.borrow().get(&key).copied() {
        return gid;
    }
    let base = cx.dyn_vtables.len();
    let mut pend = cx.pending_globals.borrow_mut();
    let gid = trust_ir::value::GlobalId::new((base + pend.len()) as u32);
    pend.push(spec());
    drop(pend);
    cx.const_globals.borrow_mut().insert(key, gid);
    gid
}

/// Intern a module global for a referenced CTFE `Memory` ALLOCATION (a `&STATIC`
/// target, or a relocation target inside a const aggregate) and return its
/// `GlobalId`. The global is a byte blob of the allocation's extent: a FAITHFUL byte
/// image when the allocation is pointer-free (its bytes can be frozen), else an
/// ADDRESS-ONLY opaque global (its contents are never read in the lowered body).
/// Fail-closed on a non-`Memory` allocation (a bare function / vtable / extern
/// static has no data blob to address here).
fn intern_alloc_global<'tcx>(
    cx: &Cx<'tcx, '_>,
    alloc_id: AllocId,
) -> Result<trust_ir::value::GlobalId, String> {
    intern_alloc_global_at_depth(cx, alloc_id, 0)
}

fn intern_alloc_global_at_depth<'tcx>(
    cx: &Cx<'tcx, '_>,
    alloc_id: AllocId,
    depth: u32,
) -> Result<trust_ir::value::GlobalId, String> {
    if depth > 8 {
        return Err("const allocation graph too deep (possible cycle)".to_string());
    }
    let key = InternKey::Alloc(alloc_id);
    if let Some(gid) = cx.const_globals.borrow().get(&key).copied() {
        return Ok(gid);
    }
    let alloc = match cx.tcx.global_alloc(alloc_id) {
        GlobalAlloc::Memory(a) => a,
        _ => {
            return Err(
                "const provenance target is not a memory allocation — not resolvable to a global"
                    .to_string(),
            )
        }
    };
    let inner = alloc.inner();
    let size = inner.len() as u64;
    if size == 0 {
        // A ZERO-SIZE allocation target (`&""` / `&[]` / a unit const behind a
        // reference, incl. nested inside a reloc'd const struct). The reference
        // is never dereferenced (0 bytes to read), only its ADDRESS flows.
        // Materialize a minimal zeroed R/O placeholder so the address is a
        // real, stable, linkable symbol (trust-cg 8-byte-aligns every global,
        // covering the alignment of all ZST allocs the corpus produces).
        // Named EXACTLY like a non-empty interned alloc (`const.allocN`) —
        // `build_reloc_alloc_init` emits `symaddr<const.allocN>` relocations
        // to it, so the two spellings must agree.
        let pad = inner.align.bytes().clamp(1, 16);
        return Ok(intern_global_spec(cx, key, || PendingGlobal {
            name: format!("const.{alloc_id:?}"),
            size: pad,
            init: Some(vec![0u8; pad as usize]),
            tls: None,
            reloc: None,
            mutable: false,
        }));
    }
    let mutable = inner.mutability.is_mut();
    // Freeze the bytes when the whole allocation is pointer-free; otherwise build
    // the FAITHFUL RELOCATED image (bytes + `SymbolAddr` pointer slots) — the
    // old "address-only" zeroed model broke every runtime READ of such a global
    // (the `SPAWN_HOOKS` LocalKey's accessor fn-pointer loaded as NULL).
    let whole = alloc_range(Size::ZERO, Size::from_bytes(size));
    let (init, reloc) = if inner.provenance().range_empty(whole, &cx.tcx) {
        (
            Some(
                inner
                    .inspect_with_uninit_and_ptr_outside_interpreter(0..size as usize)
                    .to_vec(),
            ),
            None,
        )
    } else {
        (None, Some(build_reloc_alloc_init(cx, inner, depth)?))
    };
    let name = format!("const.{alloc_id:?}");
    Ok(intern_global_spec(cx, key, || PendingGlobal {
        name,
        size,
        init,
        tls: None,
        reloc,
        mutable,
    }))
}

/// Where a relocated-allocation walk (`build_reloc_alloc_init_with`) sends its
/// two side effects: interning a nested anonymous MEMORY allocation as a module
/// global (returning the module-local symbol name its `SymbolAddr` relocation
/// cites), and noting a referenced STATIC (LANE S: so the whole-program
/// `statics` module can DEFINE it with real bytes). Two impls: the per-function
/// `Cx` (pending-globals interning + the process-wide static registry) and the
/// driver-level statics-module emitter (direct `ModuleBuilder` interning + its
/// own worklist).
trait RelocSink {
    fn intern_mem_alloc(&mut self, alloc_id: AllocId, depth: u32) -> Result<String, String>;
    fn note_static(&mut self, def_id: rustc_span::def_id::DefId);
}

/// The per-function-lowering sink: nested Memory allocs intern through the
/// `Cx` pending-globals table (interior mutability — `&Cx` suffices); statics
/// are recorded in the process-wide registry for the driver's statics module.
struct CxRelocSink<'a, 'tcx, 'm>(&'a Cx<'tcx, 'm>);

impl RelocSink for CxRelocSink<'_, '_, '_> {
    fn intern_mem_alloc(&mut self, alloc_id: AllocId, depth: u32) -> Result<String, String> {
        intern_alloc_global_at_depth(self.0, alloc_id, depth)?;
        Ok(format!("const.{alloc_id:?}"))
    }
    fn note_static(&mut self, def_id: rustc_span::def_id::DefId) {
        record_referenced_static(def_id);
    }
}

/// THREADS: the faithful (type, initializer) image of a PROVENANCE-BEARING CTFE
/// allocation: a flat Tuple mixing per-byte `U8` gap fields with pointer-width
/// `Ptr` fields whose initializer elements are `SymbolAddr { symbol, addend }`
/// relocations. The addend is the pointer's stored offset into its target
/// (CTFE stores the offset as the pointer's raw little-endian bytes). Targets:
///   * a FUNCTION alloc — the mangled fn symbol (the LocalKey accessor);
///   * a STATIC alloc — the mangled static symbol;
///   * a nested MEMORY alloc — recursively interned as its own module global
///     (`const.allocN`, an object-local data symbol relocations resolve).
/// Fail-closed on unaligned/partial provenance and vtable/type-id targets.
fn build_reloc_alloc_init<'tcx>(
    cx: &Cx<'tcx, '_>,
    inner: &rustc_middle::mir::interpret::Allocation,
    depth: u32,
) -> Result<(TIRTy, Constant), String> {
    build_reloc_alloc_init_with(cx.tcx, inner, depth, &mut CxRelocSink(cx))
}

/// Sink-parameterized core of `build_reloc_alloc_init` (docs above): identical
/// walk, but nested-Memory interning and static-reference recording go through
/// `sink`, so the driver-level statics-module emitter (LANE S) reuses the exact
/// relocation model the per-function path pins.
fn build_reloc_alloc_init_with<'tcx>(
    tcx: TyCtxt<'tcx>,
    inner: &rustc_middle::mir::interpret::Allocation,
    depth: u32,
    sink: &mut dyn RelocSink,
) -> Result<(TIRTy, Constant), String> {
    let size = inner.len();
    let ptr_size = tcx.data_layout.pointer_size().bytes() as usize;
    let mut field_tys: Vec<TIRTy> = Vec::new();
    let mut elems: Vec<Constant> = Vec::new();
    let mut pos: usize = 0;
    let push_gap = |field_tys: &mut Vec<TIRTy>,
                    elems: &mut Vec<Constant>,
                    from: usize,
                    to: usize|
     -> Result<(), String> {
        if from > to {
            return Err("const alloc provenance entries overlap".to_string());
        }
        if from == to {
            return Ok(());
        }
        let bytes = inner.inspect_with_uninit_and_ptr_outside_interpreter(from..to);
        for b in bytes {
            field_tys.push(TIRTy::U8);
            elems.push(Constant::Int(i128::from(*b)));
        }
        Ok(())
    };
    let ptrs: Vec<(usize, rustc_middle::mir::interpret::CtfeProvenance)> = inner
        .provenance()
        .ptrs()
        .iter()
        .map(|(off, prov)| (off.bytes() as usize, *prov))
        .collect();
    for (off, prov) in ptrs {
        if off % ptr_size != 0 {
            return Err(format!(
                "const alloc pointer at unaligned offset {off} not modelable"
            ));
        }
        push_gap(&mut field_tys, &mut elems, pos, off)?;
        // Belt + braces: the gap we just froze must carry NO per-byte provenance
        // fragments (partial pointer copies) — `ptrs()` lists whole pointers only.
        if pos < off
            && !inner.provenance().range_empty(
                alloc_range(
                    Size::from_bytes(pos as u64),
                    Size::from_bytes((off - pos) as u64),
                ),
                &tcx,
            )
        {
            return Err("const alloc has partial-pointer provenance (not modelable)".to_string());
        }
        let raw = inner.inspect_with_uninit_and_ptr_outside_interpreter(off..off + ptr_size);
        let mut le = [0u8; 8];
        le.copy_from_slice(raw);
        let addend = i64::from_le_bytes(le);
        let target = prov.alloc_id();
        let symbol = match tcx.global_alloc(target) {
            GlobalAlloc::Function { instance } => {
                tcx.symbol_name(instance).name.to_string()
            }
            GlobalAlloc::Static(def_id) => {
                sink.note_static(def_id);
                tcx.symbol_name(Instance::mono(tcx, def_id)).name.to_string()
            }
            GlobalAlloc::Memory(_) => sink.intern_mem_alloc(target, depth + 1)?,
            // A `TypeId` provenance target: rustc codegen drops the provenance
            // — the pointer's OFFSET bytes are the type-id hash half — so the
            // slot is a plain pointer-width INTEGER of the addend, not a
            // relocation.
            GlobalAlloc::TypeId { .. } => {
                field_tys.push(TIRTy::Usize);
                elems.push(Constant::Int(addend as u64 as i128));
                pos = off + ptr_size;
                continue;
            }
            other => {
                return Err(format!(
                    "const alloc pointer target not modelable ({other:?})"
                ))
            }
        };
        field_tys.push(TIRTy::Ptr);
        elems.push(Constant::SymbolAddr { symbol, addend });
        pos = off + ptr_size;
    }
    push_gap(&mut field_tys, &mut elems, pos, size)?;
    Ok((TIRTy::Tuple(field_tys), Constant::Aggregate(elems)))
}

/// Intern the bytes of a `&'static str` / `&'static [u8]` LITERAL as a READ-ONLY
/// module global (a frozen `Bytes` blob, Internal linkage) and return its
/// `GlobalId`. This is the rodata home for an immutable 'static literal: its ADDRESS
/// (`GlobalAddr`) is the data pointer, with NO runtime allocation. `max(len,1)` bytes
/// so the empty literal `""` still gets a well-defined non-null 1-byte global (its
/// spare byte is never read). Keyed by a content hash so identical literals share one
/// global.
fn intern_str_literal_global(cx: &Cx<'_, '_>, bytes: &[u8]) -> trust_ir::value::GlobalId {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let mut h = DefaultHasher::new();
    bytes.hash(&mut h);
    let hash = h.finish();
    let size = (bytes.len() as u64).max(1);
    // The frozen `init` length must equal `size` (validator pin): pad `""` to 1 byte.
    let init: Vec<u8> = if bytes.is_empty() { vec![0u8] } else { bytes.to_vec() };
    intern_global_spec(cx, InternKey::StrBytes(hash), || PendingGlobal {
        name: format!("str.{hash:016x}"),
        size,
        init: Some(init),
        tls: None,
        reloc: None,
        mutable: false,
    })
}

/// Evaluate the init-value TEMPLATE of a thread-local static DEFINED in the
/// compiled crate. Returns `Some(bytes)` — the frozen little-endian template
/// image — only for a crate-LOCAL, provenance-free (POD) initializer; `None`
/// otherwise (non-local reference, un-evaluable initializer, size mismatch, or a
/// pointer-bearing template that would need the relocation model).
///
/// Why this exists: trust-cg emits the `__thread_vars` TLV descriptor for a
/// `tls(...)` global ONLY when it carries an initializer — an initializer-less
/// TLS global is classified as an unconditional cross-object IMPORT in the
/// backend (`compiler.rs`: a TLS definition is expressible solely through the
/// descriptor + init template, which requires an initializer). A thread-local
/// DEFINED in this crate therefore needs a real template here, or it lowers to
/// an undefined-external the linker can never satisfy. A NON-local thread-local
/// (std / another crate — merely referenced here, e.g. wp10's `RandomState`
/// keys) stays `None`: import, exactly as before. The `None` fallbacks are all
/// fail-closed — a genuinely-local static that cannot be frozen surfaces as a
/// LOUD undefined-external at link, never a silently wrong template.
fn tls_local_template_bytes<'tcx>(
    cx: &Cx<'tcx, '_>,
    def_id: rustc_span::def_id::DefId,
    size: u64,
) -> Option<Vec<u8>> {
    if !def_id.is_local() {
        return None;
    }
    let evaluated = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        cx.tcx.eval_static_initializer(def_id)
    }));
    let alloc = match evaluated {
        Ok(Ok(a)) => a,
        _ => return None,
    };
    let inner = alloc.inner();
    if inner.len() as u64 != size {
        return None;
    }
    // Freeze only a provenance-FREE (POD) image as a flat template; a
    // pointer-bearing initializer needs the relocation model (`reloc`) and stays
    // an import here — none arise for the scalar thread-local definitions this
    // targets, and the fail-closed import surfaces loudly at link if one ever does.
    let whole = alloc_range(Size::ZERO, Size::from_bytes(size));
    if !inner.provenance().range_empty(whole, &cx.tcx) {
        return None;
    }
    Some(
        inner
            .inspect_with_uninit_and_ptr_outside_interpreter(0..size as usize)
            .to_vec(),
    )
}

/// Intern a module global modeling a THREAD-LOCAL static (`Rvalue::ThreadLocalRef`)
/// and return its `GlobalId`. The global is a blob of the static's byte size,
/// flagged with a TLS model — `ThreadLocalRef` lowers to its `GlobalAddr` (the
/// canonical thread-local-address lowering).
///
/// A thread-local DEFINED in the compiled crate is emitted as a real TLS
/// DEFINITION: its evaluated init-value template is frozen as the global's
/// initializer (`tls_local_template_bytes`), so trust-cg emits the
/// `__thread_vars` descriptor + `__thread_data` template. A thread-local defined
/// elsewhere (std / another crate) keeps `init: None` and stays an import — its
/// contents are produced by its defining object at link. Fail-closed if the
/// static's layout is not computable.
fn intern_tls_global<'tcx>(
    cx: &Cx<'tcx, '_>,
    def_id: rustc_span::def_id::DefId,
) -> Result<trust_ir::value::GlobalId, String> {
    let key = InternKey::Tls(def_id);
    if let Some(gid) = cx.const_globals.borrow().get(&key).copied() {
        return Ok(gid);
    }
    let sty = cx.normalize_ty(cx.tcx.type_of(def_id).instantiate_identity());
    let (size, _align) = memory_layout_size_align(cx, sty)?;
    // A crate-LOCAL thread-local gets a real definition (init template present);
    // anything else stays an import (`None`). See `tls_local_template_bytes`.
    let init = tls_local_template_bytes(cx, def_id, size);
    // TEXT-SAFE interned name: the raw `def_id:?` Debug embeds the mangled path
    // (`{`, `}`, `~`, `::`, spaces) which the text Display/parser pair does not
    // quote — it breaks the emit→re-parse round-trip. The name is only an interning
    // key for the text format (the semantics live in `tls`/`GlobalAddr`), so a
    // content hash of the `DefId` — like the vtable globals — keeps it stable,
    // module-locally collision-free, and parser-safe. `Internal` linkage keeps it
    // module-private, so no cross-module symbol identity is lost.
    let name = {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::Hasher;
        let mut hasher = DefaultHasher::new();
        hasher.write(format!("{def_id:?}").as_bytes());
        format!("tls.{:016x}", hasher.finish())
    };
    Ok(intern_global_spec(cx, key, || PendingGlobal {
        name,
        size,
        init,
        tls: Some(trust_ir::TlsModel::LocalExec),
        reloc: None,
        mutable: false,
    }))
}

/// After `fb.build()` has released the `mb` borrow, add every queued global (in
/// `GlobalId` order) to the module. Each is an `Array(U8, size)` blob with an
/// optional frozen byte initializer and optional TLS model. A no-op when the body
/// interned nothing (the common case), so pre-existing output is byte-identical.
fn flush_pending_globals<'tcx>(cx: &Cx<'tcx, '_>, mb: &mut ModuleBuilder) {
    let pend = std::mem::take(&mut *cx.pending_globals.borrow_mut());
    for pg in pend {
        // THREADS: a RELOCATED provenance-bearing global carries its own mixed
        // (bytes + SymbolAddr) tuple image — see `build_reloc_alloc_init`.
        if let Some((ty, init)) = pg.reloc {
            mb.add_global(trust_ir::Global {
                name: pg.name,
                ty,
                mutable: pg.mutable || pg.tls.is_some(),
                initializer: Some(init),
                linkage: trust_ir::Linkage::Internal,
                tls: pg.tls,
                // No explicit over-alignment: the consumer derives alignment
                // from the (pointer-slot / byte) type layout.
                align: None,
            });
            continue;
        }
        // A `[u8; size]` blob — the validator pins a `Bytes` initializer to a `U8`
        // array element and `data.len() == size`.
        let elem = mb.add_type(TIRTy::U8);
        mb.add_global(trust_ir::Global {
            name: pg.name,
            ty: TIRTy::Array(elem, pg.size),
            mutable: pg.mutable || pg.tls.is_some(),
            initializer: pg
                .init
                .map(|data| Constant::Bytes { data, utf8: false }),
            linkage: trust_ir::Linkage::Internal,
            tls: pg.tls,
            // A `[u8; size]` blob is byte-aligned; consumer derives from type.
            align: None,
        });
    }
}

// ===================== LANE S: real std-static bytes =========================
//
// Whole-program emit-each historically left every referenced `static` as a bare
// `SymbolAddr` EXTERN and let the link-time runtime generator zero-init the
// missing symbols. That is correct for the documented-zero panic statics but
// SILENTLY WRONG for real-data statics (the unicode WHITESPACE_MAP /
// SHORT_OFFSET_RUNS / OFFSETS property tables, fmt's DECIMAL_PAIRS): a read
// sees zeros instead of the table. The fix: every static referenced during
// lowering is RECORDED here, and after the emit-each census the driver emits
// ONE dedicated `statics` module that DEFINES each one with its real CTFE
// initializer bytes under External linkage (single definition for the whole
// link; the per-module `SymbolAddr` references bind to it). Only statics whose
// allocation genuinely cannot be evaluated (true `extern` foreign statics,
// TLS statics — which flow through the TLS model instead) remain extern, and
// the driver reports each with its reason.

/// Process-wide registry of statics referenced by lowered code, in first-seen
/// order (deterministic given the deterministic mono-item walk). Drained once
/// by `emit_statics_module`.
static REFERENCED_STATICS: std::sync::Mutex<Vec<rustc_span::def_id::DefId>> =
    std::sync::Mutex::new(Vec::new());

/// Record one referenced static (dedup'd, order-preserving). Poison-tolerant:
/// a lowering panic elsewhere (the driver catches them per-module) must not
/// wedge the registry.
fn record_referenced_static(def_id: rustc_span::def_id::DefId) {
    let mut v = REFERENCED_STATICS
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    if !v.contains(&def_id) {
        v.push(def_id);
    }
}

/// The driver-level statics-module emitter state: interns nested anonymous
/// Memory allocations DIRECTLY into the module (no `fb` borrow exists here)
/// and queues newly-discovered statics (a `&STATIC` stored inside another
/// static's initializer) onto the definition worklist.
struct StaticsEmit<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    mb: &'a mut ModuleBuilder,
    /// nested anonymous allocation -> its module-local `const.allocN` symbol.
    mem_names: HashMap<AllocId, String>,
    /// Definition worklist (processed by index; `note_static` appends).
    pending: Vec<rustc_span::def_id::DefId>,
    queued: HashSet<rustc_span::def_id::DefId>,
}

impl RelocSink for StaticsEmit<'_, '_> {
    fn intern_mem_alloc(&mut self, alloc_id: AllocId, depth: u32) -> Result<String, String> {
        self.intern_mem(alloc_id, depth)
    }
    fn note_static(&mut self, def_id: rustc_span::def_id::DefId) {
        if self.queued.insert(def_id) {
            self.pending.push(def_id);
        }
    }
}

impl<'a, 'tcx> StaticsEmit<'a, 'tcx> {
    /// Intern a nested anonymous MEMORY allocation as an Internal module global
    /// (`const.allocN` — the same spelling the per-function modules use, but
    /// Internal linkage so the copies never collide across objects). The name is
    /// registered BEFORE the relocation walk so an allocation cycle terminates
    /// by name reuse; the depth guard is belt-and-braces.
    fn intern_mem(&mut self, alloc_id: AllocId, depth: u32) -> Result<String, String> {
        if let Some(n) = self.mem_names.get(&alloc_id) {
            return Ok(n.clone());
        }
        if depth > 16 {
            return Err("statics-module const allocation graph too deep".to_string());
        }
        let alloc = match self.tcx.global_alloc(alloc_id) {
            GlobalAlloc::Memory(a) => a,
            other => {
                return Err(format!(
                    "statics-module reloc target is not a memory allocation ({other:?})"
                ))
            }
        };
        let name = format!("const.{alloc_id:?}");
        self.mem_names.insert(alloc_id, name.clone());
        let inner = alloc.inner();
        let g = self.build_alloc_global(
            name.clone(),
            inner,
            depth,
            trust_ir::Linkage::Internal,
            /*force_mutable=*/ false,
        )?;
        self.mb.add_global(g);
        Ok(name)
    }

    /// The faithful trust-ir global for one CTFE allocation: a frozen
    /// `Bytes`/`Array(U8)` blob when pointer-free, else the mixed
    /// (bytes + `SymbolAddr`) tuple image `build_reloc_alloc_init_with` builds
    /// (nested allocs interned transitively through `self`). A zero-size
    /// allocation (a ZST static like the `Global` allocator) still gets a
    /// minimal zeroed blob so its ADDRESS is a real linkable symbol.
    ///
    /// ALIGNMENT: the emitted global carries the allocation's real byte
    /// alignment in `Global.align` (a power of two, from `inner.align`), and its
    /// byte image is the EXACT CTFE bytes (no tail padding). trust-cg honors the
    /// per-global alignment when it packs the `__DATA`/`__const` sections —
    /// aligning each global's section offset up to `Global.align` and widening
    /// the section's own alignment to cover it — so an atomic / SIMD / over-
    /// aligned static lands on a correctly-aligned address regardless of the
    /// preceding global's size. (This replaces the historical workaround that
    /// zero-padded every global to a multiple of 8 and rejected `align > 8`,
    /// which pre-dated per-global alignment in the backend.)
    fn build_alloc_global(
        &mut self,
        name: String,
        inner: &rustc_middle::mir::interpret::Allocation,
        depth: u32,
        linkage: trust_ir::Linkage,
        force_mutable: bool,
    ) -> Result<trust_ir::Global, String> {
        let size = inner.len() as u64;
        let mutable = force_mutable || inner.mutability.is_mut();
        // The static's declared storage alignment (power of two). Carried
        // through so trust-cg places the symbol at a correctly-aligned offset.
        let align = Some((inner.align.bytes() as u32).max(1));
        if size == 0 {
            let elem = self.mb.add_type(TIRTy::U8);
            return Ok(trust_ir::Global {
                name,
                ty: TIRTy::Array(elem, 1),
                mutable,
                initializer: Some(Constant::Bytes {
                    data: vec![0u8; 1],
                    utf8: false,
                }),
                linkage,
                tls: None,
                align,
            });
        }
        let whole = alloc_range(Size::ZERO, Size::from_bytes(size));
        if inner.provenance().range_empty(whole, &self.tcx) {
            let data = inner
                .inspect_with_uninit_and_ptr_outside_interpreter(0..size as usize)
                .to_vec();
            let elem = self.mb.add_type(TIRTy::U8);
            Ok(trust_ir::Global {
                name,
                ty: TIRTy::Array(elem, size),
                mutable,
                initializer: Some(Constant::Bytes { data, utf8: false }),
                linkage,
                tls: None,
                align,
            })
        } else {
            let tcx = self.tcx;
            let (ty, init) = build_reloc_alloc_init_with(tcx, inner, depth, self)?;
            let (field_tys, elems) = match (ty, init) {
                (TIRTy::Tuple(f), Constant::Aggregate(e)) => (f, e),
                other => {
                    return Err(format!(
                        "relocated-alloc image has unexpected shape: {other:?}"
                    ))
                }
            };
            Ok(trust_ir::Global {
                name,
                ty: TIRTy::Tuple(field_tys),
                mutable,
                initializer: Some(Constant::Aggregate(elems)),
                linkage,
                tls: None,
                align,
            })
        }
    }
}

/// One definition/skip report row from `emit_statics_module`.
pub struct StaticDefReport {
    pub symbol: String,
    pub size: u64,
    pub mutable: bool,
}

/// LANE S entry point (driver, after the emit-each census): build the dedicated
/// whole-program `statics` module — one External-linkage DEFINITION with the
/// real CTFE initializer (bytes + `SymbolAddr` relocations, nested anonymous
/// allocs interned transitively) for every referenced static that evaluates —
/// and report the statics that must REMAIN extern declarations, each with its
/// reason. Returns `None` when no static was referenced (module elided, output
/// byte-identical to pre-LANE-S).
///
/// Fail-closed placement: a static is only defined here when its allocation
/// evaluates, its alignment fits trust-cg's 8-byte global sections, and its
/// image models (no vtable-target relocations); everything else stays an
/// undefined extern so the LINK (not a silent zero-filled read) reports it.
pub fn emit_statics_module<'tcx>(
    tcx: TyCtxt<'tcx>,
) -> (
    Option<(trust_ir::Module, Vec<ValidationError>)>,
    Vec<StaticDefReport>,
    Vec<(String, String)>,
) {
    let roots = std::mem::take(
        &mut *REFERENCED_STATICS
            .lock()
            .unwrap_or_else(|e| e.into_inner()),
    );
    if roots.is_empty() {
        return (None, Vec::new(), Vec::new());
    }
    let mut defined: Vec<StaticDefReport> = Vec::new();
    let mut externs: Vec<(String, String)> = Vec::new();
    let mut mb = ModuleBuilder::new("mir::statics".to_string());
    {
        let mut st = StaticsEmit {
            tcx,
            mb: &mut mb,
            mem_names: HashMap::new(),
            queued: roots.iter().copied().collect(),
            pending: roots,
        };
        let mut i = 0;
        while i < st.pending.len() {
            let def_id = st.pending[i];
            i += 1;
            let sym = tcx
                .symbol_name(Instance::mono(tcx, def_id))
                .name
                .to_string();
            // TLS statics flow through the TLS model (`tls.*` globals +
            // `ThreadLocalRef`); a plain data definition here would be wrong.
            if tcx.is_thread_local_static(def_id) {
                externs.push((sym, "thread-local static (TLS model path)".to_string()));
                continue;
            }
            // A true `extern` block static has no Rust initializer to evaluate
            // (and `eval_static_initializer` has no metadata entry for it).
            if tcx.is_foreign_item(def_id) {
                externs.push((sym, "foreign extern static (no Rust initializer)".to_string()));
                continue;
            }
            let evaluated = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                tcx.eval_static_initializer(def_id)
            }));
            let alloc = match evaluated {
                Ok(Ok(a)) => a,
                Ok(Err(e)) => {
                    externs.push((sym, format!("eval_static_initializer failed: {e:?}")));
                    continue;
                }
                Err(_) => {
                    externs.push((sym, "eval_static_initializer panicked".to_string()));
                    continue;
                }
            };
            let inner = alloc.inner();
            // WRITABLE unless immutable AND Freeze. Belt-and-braces OR of the
            // allocation's own interning mutability (rustc marks interior-mutable
            // statics' base allocation Mut), the declared `static mut`, and the
            // !Freeze type check — an interior-mutable static placed in rodata
            // would fault on its first atomic store.
            let declared_mut = tcx
                .static_mutability(def_id)
                .is_some_and(|m| m.is_mut());
            let interior_mut = !tcx
                .normalize_erasing_regions(
                    ty::TypingEnv::fully_monomorphized(),
                    tcx.type_of(def_id).instantiate_identity(),
                )
                .is_freeze(tcx, ty::TypingEnv::fully_monomorphized());
            let size = inner.len() as u64;
            match st.build_alloc_global(
                sym.clone(),
                inner,
                0,
                trust_ir::Linkage::External,
                declared_mut || interior_mut,
            ) {
                Ok(g) => {
                    let mutable = g.mutable;
                    st.mb.add_global(g);
                    defined.push(StaticDefReport {
                        symbol: sym,
                        size,
                        mutable,
                    });
                }
                Err(reason) => externs.push((sym, reason)),
            }
        }
    }
    // trust-cg refuses a zero-function module ("empty module: no functions to
    // compile") and this module is pure data — anchor it with one trivial no-op
    // so the object (data sections + external static symbols) is emitted. The
    // statics module exists ONCE per whole-program link, so the anchor symbol
    // cannot collide.
    let anchor_ty = mb.add_func_type(Vec::new(), Vec::new());
    let mut fb = mb.function("trust_ir.statics.anchor".to_string(), anchor_ty);
    let entry = fb.create_block();
    fb.set_entry(entry);
    fb.switch_to_block(entry);
    fb.ret(Vec::new());
    fb.build();
    let mut module = mb.build();
    module.target_info = Some(emit_target_info(tcx));
    let errs = validate_module(&module);
    (Some((module, errs)), defined, externs)
}

/// Attempt the minimal lowering of one mono-item fn. Ok(()) means it lowered AND
/// validate_module reported 0 errors. Err(reason) names the first unsupported
/// construct (the bucketed gap-map reason).
/// Target identity for emitted modules. The lowering is target-dependent by
/// construction (every layout comes from `tcx.layout_of`), and trust-ir's ABI
/// pinning (v20) requires `target_info` on any module with a bodyless external
/// declaration — which every emitted fixture module has (host-shim leaves).
/// Stamped on all emit paths so `validate_module` judges the module the text
/// actually carries.
fn emit_target_info(tcx: TyCtxt<'_>) -> trust_ir::TargetInfo {
    trust_ir::TargetInfo {
        triple: tcx.sess.opts.target_triple.to_string(),
        pointer_size: u32::from(tcx.sess.target.pointer_width / 8),
        endianness: match tcx.sess.target.endian {
            rustc_abi::Endian::Little => trust_ir::Endianness::Little,
            rustc_abi::Endian::Big => trust_ir::Endianness::Big,
        },
        abi: None,
        struct_passing: Default::default(),
    }
}

pub fn try_lower_minimal<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
    body: &Body<'tcx>,
) -> Result<ObligationTally, String> {
    let (mut cx, ret_abi, address_taken) =
        classify_locals_and_ret_abi(tcx, instance, body, /*emit_self_recursion=*/ false)?;
    let sym = tcx.def_path_str(instance.def_id());
    let mut mb = ModuleBuilder::new(format!("mir::{sym}"));
    lower_with_signature(&mut cx, &mut mb, /*wiring=*/ None, body, ret_abi, &address_taken)?;
    let mut module = mb.build();
    module.target_info = Some(emit_target_info(tcx));
    // Coverage path: "lowered-ok" == validate_module reports 0 errors.
    let errs = validate_module(&module);
    if errs.is_empty() {
        // The panic-class obligations this body recorded (see
        // `record_assert_obligations`), reported by the census.
        Ok(ObligationTally::of_module(&module))
    } else {
        Err(format!(
            "VALIDATE: {} error(s) — first: {:?}",
            errs.len(),
            errs.first()
        ))
    }
}

/// EMIT path (`--mir-emit`): fully lower one mono-item fn and return its SELF-CONTAINED
/// trust-ir `Module` (self-recursive calls wired to the in-module body, not a 0-block
/// extern stub) PLUS the validator's error list (empty == 0 errors). The caller writes
/// the module text and reports the validation result. This shares the exact same
/// classification + lowering as the coverage path; the ONLY difference is
/// `emit_self_recursion = true`, so a `whnf`/`sz`-style self-recursion round-trips/JITs.
pub fn lower_module_for_emit<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
    body: &Body<'tcx>,
) -> Result<(trust_ir::Module, Vec<ValidationError>), String> {
    let (mut cx, ret_abi, address_taken) =
        classify_locals_and_ret_abi(tcx, instance, body, /*emit_self_recursion=*/ true)?;
    let sym = tcx.def_path_str(instance.def_id());
    let mut mb = ModuleBuilder::new(format!("mir::{sym}"));
    lower_with_signature(&mut cx, &mut mb, /*wiring=*/ None, body, ret_abi, &address_taken)?;
    let mut module = mb.build();
    module.target_info = Some(emit_target_info(tcx));
    let errs = validate_module(&module);
    Ok((module, errs))
}

/// A closure member: the resolved monomorphic `Instance` to lower, plus its symbol
/// (the stable `tcx.symbol_name`, the key callers wire by) and its MIR `Body`.
struct ClosureMember<'tcx> {
    instance: Instance<'tcx>,
    symbol: String,
    body: &'tcx Body<'tcx>,
}

/// RUNG 9 (non-escaping closure): if `func` resolves to a callee that is part of a
/// closure-combinator chain — either (a) a CLOSURE BODY itself (the closure the
/// combinator invokes), or (b) a generic combinator (`Option::and_then`/`map`,
/// `Iterator::all`/`any`/`map`, ...) MONOMORPHIZED at a concrete closure type (one
/// of its generic args is a closure) — return that callee `Instance` so the BFS
/// pulls it IN-MODULE. The combinator's body has MIR (`is_mir_available`) and bottoms
/// out at the closure call (`<{closure} as FnOnce>::call_once`, which
/// `Instance::try_resolve` collapses to the closure body) plus leaf arithmetic that
/// stays extern. Returns `None` for any OTHER callee, so the existing
/// `eligible_local_callees` logic (crate-local `Item` only) is reached UNCHANGED for
/// every non-closure call — the additive guarantee.
///
/// FAIL-CLOSED: requires the callee resolve, be an `InstanceKind::Item` (a real body,
/// not a vtable/drop shim), and have MIR available (so `instance_mir` on it does not
/// ICE). A closure body is always local with MIR; a combinator is a non-local core
/// generic with MIR. We deliberately do NOT pull in the closure-carrying combinator's
/// own leaf arithmetic (`checked_mul`/`wrapping_add`) — that has NO closure generic
/// arg, so it stays an extern leaf (bound as a host symbol by the JIT harness),
/// bounding the pull-in to exactly the combinator + the closure body.
fn closure_chain_callee<'tcx>(
    cx: &Cx<'tcx, '_>,
    func: &Operand<'tcx>,
) -> Option<Instance<'tcx>> {
    let callee = resolve_call_callee(cx, func)?;
    let did = callee.def_id();
    // Only a real Item body (a closure body, or a generic fn) — never a synthetic
    // shim (a separate `ClosureOnceShim`/vtable/drop instance), which has no
    // user-lowerable MIR here.
    if !matches!(callee.def, ty::InstanceKind::Item(_)) {
        return None;
    }
    if !cx.tcx.is_mir_available(did) {
        return None;
    }
    // A FOREIGN item (an `extern "C"` decl) is a true link-time leaf — never pull it
    // in (its `instance_mir` would ICE).
    if cx.tcx.is_foreign_item(did) {
        return None;
    }
    // (a) The callee IS a closure body — the closure the combinator invokes.
    // `SyntheticCoroutineBody` is the AsyncFnOnce BY-MOVE coroutine body
    // (`coroutine_by_move_body_def_id`, reached by `Future::poll` resolution
    // when the awaited coroutine's kind ty was tweaked to FnOnce by the
    // `ConstructCoroutineInClosure` shim): a coroutine body under a synthetic
    // def, with NO `item_name`/`fn_sig` — it must take this closure-safe wiring
    // (ABI-derived signature) exactly like a plain coroutine body, or the
    // inline-recognizers below ICE interrogating it.
    if matches!(
        cx.tcx.def_kind(did),
        rustc_hir::def::DefKind::Closure | rustc_hir::def::DefKind::SyntheticCoroutineBody
    ) {
        return Some(callee);
    }
    // (b) The callee is a generic combinator monomorphized at a CLOSURE type: one of
    // its generic args is a closure (`and_then::<U, {closure}>`). This is the
    // self-identifying gate — a closure-free callee (e.g. `checked_mul`, `clone`,
    // `cmp`) has no closure-typed generic arg, so it is NOT pulled in and the
    // existing closure-free modules are unaffected.
    let carries_closure = callee.args.iter().any(|a| {
        a.as_type()
            .is_some_and(|t| matches!(t.kind(), ty::Closure(..)))
    });
    if carries_closure {
        return Some(callee);
    }
    None
}

/// The crate-local `Item` callee instances of `body` that are ELIGIBLE to be
/// closure members — i.e. calls the real lowering would otherwise emit as an extern
/// stub but which we can instead wire IN-MODULE. We EXCLUDE every call shape the
/// lowering already handles specially, so the closure follows exactly the
/// real-fn → real-fn edges:
///   - self-recursion (already wired in-module by `emit_self_recursion`);
///   - the inlined shapes (Arc deref/new, into_iter/next, Box new_uninit/into_vec,
///     saturating-add) — those become pointer arithmetic / cursors, NOT calls;
///   - non-`Item` instances (drop glue / clone / vtable shims — synthetic leaves);
///   - non-local callees (monomorphized std/dep generics — true leaves).
/// Returns the resolved `Instance` for each eligible callee (deduped by symbol by
/// the BFS caller). FAIL-LOUD is deferred to the per-member lowering: if an eligible
/// member cannot itself lower, `lower_closure_for_emit` reports which + why.
fn eligible_local_callees<'tcx>(cx: &Cx<'tcx, '_>, body: &Body<'tcx>) -> Vec<Instance<'tcx>> {
    let mut out: Vec<Instance<'tcx>> = Vec::new();
    for data in body.basic_blocks.iter() {
        let Some(term) = data.terminator.as_ref() else {
            continue;
        };
        let TerminatorKind::Call { func, args, .. } = &term.kind else {
            continue;
        };
        // RUNG 9 (non-escaping closure): a call whose callee IS a closure body, or a
        // generic combinator (`Option::and_then`/`map`, `Iterator::all`/`any`/`map`)
        // MONOMORPHIZED at a concrete closure type, is pulled IN-MODULE so the
        // closure-combinator chain is executable end-to-end (the closure body the
        // combinator invokes, and the combinator itself which has MIR). These are
        // resolved + classified WITHOUT the `item_name`/`fn_sig` inline-recognizers
        // below, which ICE on a closure def-path (a closure has no `item_name`, and
        // its signature needs `args.as_closure().sig()` not `fn_sig`). This branch is
        // STRICTLY ADDITIVE: it fires ONLY for a closure-body callee or a closure-
        // carrying combinator — a shape that never appears in the existing
        // closure-free verified modules (whnf / def_eq / structural_eq), so their
        // member sets are byte-for-byte unchanged.
        if let Some(c) = closure_chain_callee(cx, func) {
            out.push(c);
            continue;
        }
        // Skip the inlined shapes (these never become a real `call`).
        if arc_deref_inline_offset(cx, func).is_some() {
            continue;
        }
        if matches!(arc_new_inner_layout(cx, func), Ok(Some(_))) {
            continue;
        }
        if matches!(into_iter_inline(cx, func), Ok(Some(_))) {
            continue;
        }
        if matches!(iter_next_inline(cx, func), Ok(Some(_))) {
            continue;
        }
        if matches!(box_new_uninit_inline(cx, func), Ok(Some(_))) {
            continue;
        }
        if matches!(box_into_vec_inline(cx, func), Ok(Some(_))) {
            continue;
        }
        // ADDITIVE (R4 stage 2): the in-module str/byte call shapes.
        if matches!(str_inline_op(cx, func), Ok(Some(_))) {
            continue;
        }
        if saturating_add_msg_call(cx, func, args).is_some() {
            continue;
        }
        // Resolve the callee. Only a crate-local `Item` (a real user fn body) is a
        // closure-member candidate; everything else stays a leaf extern.
        let Some(callee) = resolve_call_callee(cx, func) else {
            continue;
        };
        if !callee.def_id().is_local() {
            continue;
        }
        // A FOREIGN item (an `extern "C" { fn .. }` declaration) is local to the
        // crate but has NO MIR body — it is a TRUE leaf (its definition lives
        // outside, bound at link/JIT time). It must NOT enter the closure (a later
        // `instance_mir` on it would ICE); it stays a 0-block extern decl, exactly
        // like a library callee. Skip it here.
        if cx.tcx.is_foreign_item(callee.def_id()) {
            continue;
        }
        if !matches!(callee.def, ty::InstanceKind::Item(_)) {
            continue;
        }
        out.push(callee);
    }
    out
}

/// EMIT-EACH reference-closure: every callee `Instance` DIRECTLY referenced by a
/// `Call` terminator in `body` that is an `InstanceKind::Item` with a lowerable MIR
/// body (not foreign, not a synthetic shim/intrinsic leaf).
///
/// WHY: `collect_and_partition_mono_items` returns exactly the CODEGEN set — the
/// functions rustc would hand to LLVM. It legitimately OMITS functions that our
/// non-optimizing, non-inlining lowering nonetheless emits as real `Call`s:
///   1. Callees inside a branch guarded by a compile-time-constant condition that is
///      never taken (`if needs_drop::<(i64,i64)>() { .. iterate+drop .. }` — a
///      `condbr const false`). rustc relies on LLVM to DCE the dead block, so it
///      never collects those callees; we emit the block verbatim.
///   2. `mentioned`-not-`used` items (a `Debug::fmt` reached only through a vtable /
///      formatting machinery the optimizer proves dead).
///   3. Upstream `#[inline]` fns the collector inlined away but that our lowering
///      emits as a standalone `call @sym` (e.g. `RawTableInner::ctrl_slice`).
/// In every case the emitted module names a symbol with no definition, so the
/// whole-program link dangles. Emit-each closes the gap by BFS-ing this relation and
/// lowering each referenced Item too, under its stable `tcx.symbol_name` (FIX #1) —
/// the exact symbol the caller's extern decl uses — so the references resolve. The
/// pulled-in dead-branch bodies are never executed; the live ones (case 3) run.
///
/// FAIL-SAFE: only `Item` callees that RESOLVE, are NOT foreign, and HAVE MIR are
/// returned, so a later `instance_mir` on them never ICEs. Synthetic shim kinds
/// (DropGlue / ClosureOnceShim / VTableShim / FnPtrShim) are already in the mono set
/// (they were collected as codegen items), so restricting to `Item` here is
/// sufficient and avoids `instance_mir` on a shim def-id that lacks a plain body.
pub fn referenced_item_callees<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
    body: &'tcx Body<'tcx>,
) -> Vec<Instance<'tcx>> {
    let (cx, _ret, _at) = match classify_locals_and_ret_abi(
        tcx,
        instance,
        body,
        /*emit_self_recursion=*/ true,
    ) {
        Ok(v) => v,
        Err(e) => {
            if std::env::var_os("TRUST_IR_PULL_DEBUG").is_some() {
                eprintln!(
                    "PULL-CLASSIFY-FAIL {:?} :: {e}",
                    tcx.def_path_str(instance.def_id())
                );
            }
            return Vec::new();
        }
    };
    let mut out: Vec<Instance<'tcx>> = Vec::new();
    let mut seen: HashSet<String> = HashSet::new();
    // Whether a callee INSTANCE is lowerable HERE: either a real `Item` body with
    // cross-crate MIR (not a foreign `extern "C"` decl — those are true link leaves),
    // or one of the four SYNTHETIC shim kinds whose MIR `instance_mir` fabricates on
    // demand (drop glue, closure-once, vtable, fn-ptr — the set the mono-set loop
    // emits). A shim's `def_id` is the underlying closure/drop/trait-method, for which
    // `is_mir_available` may be false even though the SHIM body is synthesizable, so
    // shim kinds are NOT gated on it — the emit loop's `catch_unwind` + fail-closed
    // shim check is the backstop.
    let pullable = |callee: &Instance<'tcx>| -> bool {
        let did = callee.def_id();
        match callee.def {
            // A variant CTOR used as a fn value (`.map(Some)`): `is_mir_available`
            // is false cross-crate, but `instance_mir` synthesizes the ctor body
            // via `mir_for_ctfe` — emittable like any Item.
            ty::InstanceKind::Item(_) => {
                !tcx.is_foreign_item(did)
                    && (tcx.is_mir_available(did)
                        || matches!(tcx.def_kind(did), rustc_hir::def::DefKind::Ctor(..)))
            }
            // 1.99: the shim variants moved under `InstanceKind::Shim(ShimKind::…)`
            // (DropGlue / ClosureOnce / VTable / FnPtr — same four emittable shims).
            // LANE C: `Clone` (the derived `<T as Clone>::clone` CloneShim) joins
            // them. rustc synthesizes its MIR on demand (`mir_shims`) as a
            // field-by-field clone (a copy of each POD field, a
            // `<FieldT as Clone>::clone` call per non-POD field, then the
            // aggregate re-construction). A `Map<I, F> as Clone>::clone` clones
            // its closure field `F` by calling `<F as Clone>::clone` — the
            // demangle path's `Map<ChunksExact, {HexNibbles closure}>` reaches the
            // `<{closure} as Clone>::clone` CloneShim ONLY this way, so excluding
            // it left the shim's symbol dangling (an abort probe). The shim body
            // is built from constructs the pipeline already lowers.
            ty::InstanceKind::Shim(
                ty::ShimKind::DropGlue(..)
                | ty::ShimKind::ClosureOnce { .. }
                | ty::ShimKind::VTable(_)
                | ty::ShimKind::FnPtr(..)
                | ty::ShimKind::Clone(..),
            ) => true,
            _ => false,
        }
    };
    let push = |callee: Instance<'tcx>,
                out: &mut Vec<Instance<'tcx>>,
                    seen: &mut HashSet<String>| {
        if !pullable(&callee) {
            if std::env::var_os("TRUST_IR_PULL_DEBUG").is_some() {
                eprintln!(
                    "PULL-REJECT {:?} kind={:?} foreign={} mir={}",
                    tcx.def_path_str(callee.def_id()),
                    callee.def,
                    tcx.is_foreign_item(callee.def_id()),
                    tcx.is_mir_available(callee.def_id())
                );
            }
            return;
        }
        let sym = tcx.symbol_name(callee).name.to_string();
        if seen.insert(sym) {
            out.push(callee);
        }
    };
    // (1) Direct `Call`-terminator callees.
    for data in body.basic_blocks.iter() {
        let Some(term) = data.terminator.as_ref() else {
            continue;
        };
        let TerminatorKind::Call { func, args, .. } = &term.kind else {
            continue;
        };
        // These canonical core wrappers are consumed by the caller's inline
        // lane (or rejected there for wrapping semantics). Pulling their
        // cross-crate bodies into an emit closure would reintroduce a dead,
        // unsupported copy after the original call has already disappeared.
        if raw_ptr_method_named(&cx, func, "offset")
            || raw_ptr_method_named(&cx, func, "wrapping_offset")
            || stable_mem_wrapper(&cx, func).is_some()
        {
            continue;
        }
        if let Some(callee) = resolve_call_callee(&cx, func) {
            // UNWIND lane: the `catch_unwind` intrinsic expands to DIRECT calls
            // of its fn-pointer operands (`do_call`/`do_catch`) — enqueue them
            // so their bodies are emitted even when the mono collector only saw
            // the reified constants. Abort lane: unchanged (no expansion).
            if eh_lane(tcx)
                && tcx
                    .intrinsic(callee.def_id())
                    .is_some_and(|i| i.name.as_str() == "catch_unwind")
            {
                for opnd in [args.first(), args.get(2)].into_iter().flatten() {
                    if let Ok(inst) = resolve_fnptr_operand(&cx, body, &opnd.node) {
                        push(inst, &mut out, &mut seen);
                    }
                }
                continue;
            }
            push(callee, &mut out, &mut seen);
        } else if std::env::var_os("TRUST_IR_PULL_DEBUG").is_some() {
            eprintln!(
                "PULL-NORESOLVE in {:?} :: func={func:?}",
                tcx.def_path_str(instance.def_id())
            );
        }
    }
    // (1b) UNWIND lane: the `core::panicking` entry point each supported
    // `Assert` failure path now CALLS (the Assert lowering's rustc-parity
    // panic path). Previously a trap — never a reference — so the mono set /
    // closure has no reason to contain these bodies; pull them explicitly.
    // Abort lane: unchanged (the failure path stays a trap).
    if eh_lane(tcx) {
        for data in body.basic_blocks.iter() {
            let Some(term) = data.terminator.as_ref() else {
                continue;
            };
            let TerminatorKind::Assert { msg, .. } = &term.kind else {
                continue;
            };
            if let Some((lang_item, _, _)) = assert_panic_langcall(msg) {
                let did = tcx.require_lang_item(lang_item, term.source_info.span);
                push(Instance::mono(tcx, did), &mut out, &mut seen);
            }
        }
    }
    // (1c) UNWIND lane: the `core::panicking` TERMINATE entry point each
    // `UnwindAction::Terminate(reason)` edge / `UnwindTerminate(reason)`
    // terminator now CALLS (`panic_cannot_unwind` / `panic_in_cleanup` — the
    // double-panic message + abort). Previously a trap — never a reference —
    // so the mono set has no reason to contain these bodies; pull them
    // explicitly. Abort lane: unchanged (the terminate paths stay traps).
    if eh_lane(tcx) {
        for data in body.basic_blocks.iter() {
            let Some(term) = data.terminator.as_ref() else {
                continue;
            };
            let reason = match &term.kind {
                TerminatorKind::UnwindTerminate(r) => Some(*r),
                _ => term.unwind().and_then(|u| match u {
                    rustc_middle::mir::UnwindAction::Terminate(r) => Some(*r),
                    _ => None,
                }),
            };
            if let Some(reason) = reason {
                let did = tcx.require_lang_item(reason.lang_item(), term.source_info.span);
                push(Instance::mono(tcx, did), &mut out, &mut seen);
            }
        }
    }
    // (2) VTABLE method callees of every to-`dyn` coercion in the body. A `dyn
    // Fn`/`FnMut` closure (hashbrown's erased hasher/eq) is invoked through its vtable,
    // and its concrete method is referenced ONLY as a `SymbolAddr` vtable entry (see
    // `build_dyn_vtable_global`) — never a `Call` — so the scan above misses it. Pull
    // the same method instances `tcx.vtable_entries` installs so their bodies are
    // lowered and the vtable's fn-pointers resolve at whole-program link.
    for (self_ty, dyn_ty) in prescan_dyn_coercions(&cx, body) {
        for callee in dyn_vtable_method_instances(&cx, self_ty, dyn_ty) {
            push(callee, &mut out, &mut seen);
        }
    }
    // (3) REIFIED fn-pointer references: a `closure as fn(..)`
    // (`ClosureFnPointer` -> `resolve_closure(.., FnOnce)`) or `fn_item as fn(..)`
    // (`ReifyFnPointer`) cast produces a `SymbolAddr` relocation to that function's
    // symbol (see the cast lowering), not a `Call`. `reserve_rehash` reifies its
    // non-capturing `make_hasher` closure this way to pass it alongside the `&mut dyn`
    // rehasher; pull the referenced instance so its symbol resolves at link.
    for bdata in body.basic_blocks.iter() {
        for stmt in &bdata.statements {
            let StatementKind::Assign(bx) = &stmt.kind else {
                continue;
            };
            let Rvalue::Cast(kind, op, _) = &bx.1 else {
                continue;
            };
            let inst = match kind {
                CastKind::PointerCoercion(
                    rustc_middle::ty::adjustment::PointerCoercion::ClosureFnPointer(_),
                    _,
                ) => {
                    let op_ty = match op {
                        Operand::Constant(c) => cx.mono(c.const_.ty()),
                        Operand::Copy(p) | Operand::Move(p) => cx.place_concrete_ty(p),
                        Operand::RuntimeChecks(_) => continue,
                    };
                    if let ty::Closure(def_id, args) = op_ty.kind() {
                        Some(Instance::resolve_closure(
                            cx.tcx,
                            *def_id,
                            args,
                            ty::ClosureKind::FnOnce,
                        ))
                    } else {
                        None
                    }
                }
                CastKind::PointerCoercion(
                    rustc_middle::ty::adjustment::PointerCoercion::ReifyFnPointer(_),
                    _,
                ) => resolve_call_callee(&cx, op),
                _ => None,
            };
            if let Some(callee) = inst {
                push(callee, &mut out, &mut seen);
            }
        }
    }
    // (5) CONST-ALLOC provenance FUNCTION targets (THREADS): a constant whose
    // memory image embeds a FUNCTION pointer references that function only
    // through a `SymbolAddr` relocation in the materialized global (see
    // `build_reloc_alloc_init`) — never through a `Call` — so the scans above
    // miss it. The canonical case: the `SPAWN_HOOKS`/`CURRENT` `LocalKey`
    // consts, whose `inner` field is the thread-local ACCESSOR fn. Walk every
    // const operand's allocation graph (nested Memory allocs included) and
    // pull each Function target.
    {
        use rustc_middle::mir::visit::Visitor;
        struct ConstAllocs<'tcx> {
            tcx: TyCtxt<'tcx>,
            instance: Instance<'tcx>,
            ids: Vec<AllocId>,
        }
        impl<'tcx> Visitor<'tcx> for ConstAllocs<'tcx> {
            fn visit_const_operand(
                &mut self,
                constant: &ConstOperand<'tcx>,
                _location: rustc_middle::mir::Location,
            ) {
                // The walked body is the GENERIC MIR: INSTANTIATE the constant
                // with the instance args before evaluating (the exact discipline
                // every lowering-side eval uses). The fallible form — an
                // un-normalizable projection must SKIP this constant, not ICE
                // away the whole body's pull (the addr2line `ResUnits::parse`
                // regression: its entire callee subtree silently degraded to
                // abort probes).
                let Ok(ct) = self
                    .instance
                    .try_instantiate_mir_and_normalize_erasing_regions(
                        self.tcx,
                        ty::TypingEnv::fully_monomorphized(),
                        ty::EarlyBinder::bind(self.tcx, constant.const_),
                    )
                else {
                    return;
                };
                let Ok(cv) = ct.eval(
                    self.tcx,
                    ty::TypingEnv::fully_monomorphized(),
                    constant.span,
                ) else {
                    return;
                };
                match cv {
                    ConstValue::Scalar(Scalar::Ptr(p, _)) => {
                        self.ids.push(p.provenance.alloc_id());
                    }
                    ConstValue::Slice { alloc_id, .. } => self.ids.push(alloc_id),
                    ConstValue::Indirect { alloc_id, .. } => self.ids.push(alloc_id),
                    _ => {}
                }
            }
        }
        let mut v = ConstAllocs { tcx, instance, ids: Vec::new() };
        v.visit_body(body);
        let mut work = v.ids;
        let mut seen_allocs: HashSet<AllocId> = HashSet::new();
        while let Some(aid) = work.pop() {
            if !seen_allocs.insert(aid) {
                continue;
            }
            match tcx.global_alloc(aid) {
                GlobalAlloc::Function { instance } => {
                    push(instance, &mut out, &mut seen);
                }
                GlobalAlloc::Memory(a) => {
                    for (_, prov) in a.inner().provenance().ptrs().iter() {
                        work.push(prov.alloc_id());
                    }
                }
                // LANE C: a const operand that is the ADDRESS of a `static`
                // (`_ = const {addr of OS_FUNCTIONS}`) reaches the static's
                // initializer image, which can itself embed FUNCTION pointers — the
                // `OsFunctions` error-formatting closures stored in `OS_FUNCTIONS`
                // (`get_os_functions`/`set_functions_inner` load it). Those closures
                // are referenced ONLY as `SymbolAddr` relocations inside the static's
                // data image, never as a `Call`, so without following the static's
                // provenance here their `<{closure} as FnOnce>::call_once` bodies
                // dangle at link (cold-path abort probes). Evaluate the initializer
                // (skip TLS / foreign / non-evaluable statics) and enqueue its
                // provenance so the Function targets are pulled. `seen_allocs` guards
                // static→static cycles.
                GlobalAlloc::Static(static_did) => {
                    if !tcx.is_thread_local_static(static_did)
                        && !tcx.is_foreign_item(static_did)
                    {
                        if let Ok(Ok(init)) =
                            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                                tcx.eval_static_initializer(static_did)
                            }))
                        {
                            for (_, prov) in init.inner().provenance().ptrs().iter() {
                                work.push(prov.alloc_id());
                            }
                        }
                    }
                }
                _ => {}
            }
        }
    }
    // (4) DROP-GLUE instances (THREADS): the Drop pre-pass declares
    // `resolve_drop_glue(place_ty)` as the callee of EVERY `Drop { place }`
    // whose type needs drop, but the mono set contains only the glue instances
    // the OPTIMIZED build still calls as glue — rustc's drop elaboration +
    // inlining legitimately erase many (the RwLock read-guard drop inside
    // getenv, the thread-exit `Option<Thread>` TLS destructor chain, ...), so
    // the declared symbol dangled at whole-program link. Pull the same
    // instance the pre-pass names; the BFS then closes over the glue BODY's
    // own callees (`<T as Drop>::drop`, nested field glue) transitively.
    for data in body.basic_blocks.iter() {
        let Some(term) = data.terminator.as_ref() else {
            continue;
        };
        let TerminatorKind::Drop { place, .. } = &term.kind else {
            continue;
        };
        let place_ty = cx.place_concrete_ty(place);
        if !place_ty.needs_drop(cx.tcx, ty::TypingEnv::fully_monomorphized()) {
            continue;
        }
        push(
            Instance::resolve_drop_glue(cx.tcx, place_ty),
            &mut out,
            &mut seen,
        );
    }
    out
}

/// The concrete METHOD instances of the `<self_ty as Trait>` vtable for a to-`dyn`
/// coercion `(self_ty, dyn_ty)` — the fn-pointers `build_dyn_vtable_global` installs
/// as `SymbolAddr` entries. Trait-ref recovery mirrors that function exactly (erase
/// the principal existential's bound regions, re-attach `self_ty`). Returns empty for
/// an auto-trait-only `dyn` (no principal / no methods).
fn dyn_vtable_method_instances<'tcx>(
    cx: &Cx<'tcx, '_>,
    self_ty: Ty<'tcx>,
    dyn_ty: Ty<'tcx>,
) -> Vec<Instance<'tcx>> {
    let ty::Dynamic(preds, _) = dyn_ty.kind() else {
        return Vec::new();
    };
    let Some(principal) = preds
        .principal()
        .map(|p| cx.tcx.instantiate_bound_regions_with_erased(p))
    else {
        return Vec::new();
    };
    let trait_ref = principal.with_self_ty(cx.tcx, self_ty);
    // Walk the vtable-entry TREE: this trait's entries plus, through every
    // `TraitVPtr` (supertrait upcast pointer), the supertrait's own table —
    // the nested tables the synthesis now materializes reference those
    // method symbols, so their bodies must be emitted too.
    let mut out: Vec<Instance<'tcx>> = Vec::new();
    let mut work: Vec<ty::TraitRef<'tcx>> = vec![trait_ref];
    let mut seen: Vec<ty::TraitRef<'tcx>> = Vec::new();
    while let Some(tr) = work.pop() {
        if seen.contains(&tr) {
            continue;
        }
        seen.push(tr);
        for e in cx.tcx.vtable_entries(tr) {
            match e {
                ty::VtblEntry::Method(instance) => out.push(*instance),
                ty::VtblEntry::TraitVPtr(sup) => {
                    work.push(*sup);
                }
                _ => {}
            }
        }
    }
    out
}

/// EMIT-CLOSURE path (`--mir-emit-closure`): starting from the ROOT mono-item fn,
/// compute the call-graph CLOSURE over the crate's OWN fns (root → whnf →
/// instantiate → subst → lift; root → structural_eq; ...), lower EVERY member into
/// ONE shared module, and wire every `Call` whose callee is in the closure to that
/// member's IN-MODULE body `FuncId` (extern decls remain only for the TRUE leaves
/// outside the closure: clone / env_get / is_native_op / Name-eq / level_eq /
/// __rust_alloc / Vec ops). Returns the built module + the validator's errors + the
/// ordered member symbols (for the caller's report). FAIL-LOUD: if any closure
/// member cannot lower, returns `Err` naming WHICH member + why (a real call is
/// never silently dropped).
///
/// Id assignment (the validator matches calls to callees by `FuncId`, NOT by Vec
/// position — see `validate.rs` `functions.iter().find(|f| f.id == callee)`): each
/// member's body id is `base_fid + externs_it_declares`; `base_fid` is the cumulative
/// footprint of the members lowered before it. We learn each member's footprint
/// (externs + 1 body) via a SIZING pass into a scratch builder (member calls are
/// skipped there too, so the footprint is the real one), THEN reserve the body ids,
/// THEN lower for real into the shared mb wiring member calls to those reserved ids.
pub fn lower_closure_for_emit<'tcx>(
    tcx: TyCtxt<'tcx>,
    root: Instance<'tcx>,
    root_body: &'tcx Body<'tcx>,
) -> Result<(trust_ir::Module, Vec<ValidationError>, Vec<String>), String> {
    use std::collections::HashMap as Map;

    // ---- 1. BFS the call-graph closure over crate-local Item callees. ----
    // Members are deduped + ORDERED by symbol (root first, then discovery order) so
    // the id assignment + emitted module are deterministic (no IR drift).
    let root_sym = tcx.symbol_name(root).name.to_string();
    let mut members: Vec<ClosureMember<'tcx>> = Vec::new();
    let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();
    seen.insert(root_sym.clone());
    members.push(ClosureMember {
        instance: root,
        symbol: root_sym,
        body: root_body,
    });
    let mut frontier = 0usize;
    while frontier < members.len() {
        // Build a transient Cx for the frontier member to classify its callees.
        let m_instance = members[frontier].instance;
        let m_body = members[frontier].body;
        let (cx, _ret, _at) =
            classify_locals_and_ret_abi(tcx, m_instance, m_body, /*emit_self_recursion=*/ true)?;
        let callees = eligible_local_callees(&cx, m_body);
        drop(cx);
        for callee in callees {
            let sym = tcx.symbol_name(callee).name.to_string();
            if seen.contains(&sym) {
                continue;
            }
            // `instance_mir` gives the post-mono body; lifetime is the tcx arena.
            let cbody: &'tcx Body<'tcx> = tcx.instance_mir(callee.def);
            seen.insert(sym.clone());
            members.push(ClosureMember {
                instance: callee,
                symbol: sym,
                body: cbody,
            });
        }
        frontier += 1;
    }

    // ---- 2. SIZING pass: footprint (externs + 1 body) of each member. ----
    // A dummy `member_fids` (every member symbol -> FuncId 0) makes member calls be
    // SKIPPED (the count never depends on the id VALUE, only on membership), so the
    // scratch footprint is exactly what the real pass will declare.
    let dummy_fids: Map<String, trust_ir::FuncId> = members
        .iter()
        .map(|m| (m.symbol.clone(), trust_ir::FuncId::new(0)))
        .collect();
    let mut footprints: Vec<u32> = Vec::with_capacity(members.len());
    for m in &members {
        let (mut cx, ret_abi, address_taken) = classify_locals_and_ret_abi(
            tcx,
            m.instance,
            m.body,
            /*emit_self_recursion=*/ true,
        )?;
        let mut scratch = ModuleBuilder::new("mir::__sizing");
        let wiring = ClosureWiring {
            base_fid: 0,
            member_fids: &dummy_fids,
        };
        lower_with_signature(&mut cx, &mut scratch, Some(&wiring), m.body, ret_abi, &address_taken)
            .map_err(|e| format!("closure member `{}` failed to lower: {e}", m.symbol))?;
        let built = scratch.build();
        footprints.push(built.functions.len() as u32);
    }

    // ---- 3. Reserve body ids + base ids. ----
    // member i occupies ids [base_i .. base_i + footprint_i); its BODY is the LAST of
    // those (`base_i + footprint_i - 1` == `base_i + externs_i`).
    let mut base_fids: Vec<u32> = Vec::with_capacity(members.len());
    let mut member_fids: Map<String, trust_ir::FuncId> = Map::new();
    let mut running: u32 = 0;
    for (i, m) in members.iter().enumerate() {
        base_fids.push(running);
        let body_id = running + footprints[i] - 1;
        member_fids.insert(m.symbol.clone(), trust_ir::FuncId::new(body_id));
        running += footprints[i];
    }

    // ---- 4. REAL pass: lower every member into ONE shared mb, wiring member calls. ----
    let root_path = tcx.def_path_str(root.def_id());
    let mut mb = ModuleBuilder::new(format!("mir::closure::{root_path}"));
    for (i, m) in members.iter().enumerate() {
        let (mut cx, ret_abi, address_taken) = classify_locals_and_ret_abi(
            tcx,
            m.instance,
            m.body,
            /*emit_self_recursion=*/ true,
        )?;
        let wiring = ClosureWiring {
            base_fid: base_fids[i],
            member_fids: &member_fids,
        };
        lower_with_signature(&mut cx, &mut mb, Some(&wiring), m.body, ret_abi, &address_taken)
            .map_err(|e| format!("closure member `{}` failed to lower: {e}", m.symbol))?;
    }
    let mut module = mb.build();
    module.target_info = Some(emit_target_info(tcx));
    let errs = validate_module(&module);
    let member_syms: Vec<String> = members.iter().map(|m| m.symbol.clone()).collect();
    Ok((module, errs, member_syms))
}

/// Shared preamble for both the coverage and emit paths: reject synthetic shims,
/// build the `Cx`, classify every MIR local (SSA scalar / memory-backed / ZST), and
/// decide the return ABI (`Scalar` / `Unit` / `Sret`). Returns the populated `Cx`,
/// the `RetAbi`, and the address-taken set the lowering threads through. The
/// `emit_self_recursion` flag is recorded on the `Cx` (it only changes how a
/// self-recursive `Call` is wired during lowering, never the classification).
fn classify_locals_and_ret_abi<'tcx, 'm>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
    body: &'m Body<'tcx>,
    emit_self_recursion: bool,
) -> Result<(Cx<'tcx, 'm>, RetAbi, HashSet<Local>), String> {
    // RUNG R4: synthetic shim BODIES. Several shim kinds synthesize a MIR body built
    // entirely from constructs the existing machinery already lowers, so they flow
    // through the normal pipeline and fail loud (never invalid) on anything they
    // cannot model:
    //   * `DropGlue(T)` — the field-by-field drop sequence: a `discriminant` read +
    //     `switchInt` over the active variant, then a `Drop` terminator per owned
    //     field. Each field `Drop` lowers through the existing drop-glue path (an
    //     extern `drop_in_place::<FieldT>` call, or a no-op branch for a
    //     logic-free/leaking type), and the `<T as Drop>::drop(&mut *self)` call
    //     shape lowers as an ordinary extern call.
    //   * `ClosureOnceShim` — `_0 = <Self as FnMut>::call_mut(&mut self, args)` then
    //     `drop(self)`: a `&mut` of the by-ref-aggregate env plus a resolvable
    //     direct call. (A capture-less ZST closure env has no slot, so `&mut self`
    //     fails loud there — 2/5 land in the ZST bucket, not invalid IR.)
    //   * `VTableShim` — `_0 = <Self as FnOnce>::call_once(move *self, args)`: a
    //     deref-and-forward direct call; this shim's BODY needs no vtable model (the
    //     vtable is where it is *installed*, not what it does). Cases whose receiver
    //     is a by-value aggregate loaded through the deref fail loud on the R3
    //     memory-scalar path, not on any vtable gap.
    // `FnPtrShim` (calls through a fn-pointer local — an indirect call the minimal
    // port does not model) and clone / async-drop shims stay refused below.
    match instance.def {
        ty::InstanceKind::Item(_)
        | ty::InstanceKind::Shim(ty::ShimKind::DropGlue(_, _))
        | ty::InstanceKind::Shim(ty::ShimKind::ClosureOnce { .. })
        | ty::InstanceKind::Shim(ty::ShimKind::VTable(_))
        // R6: `FnPtrShim` is the body of `<fn(..) as FnOnce/FnMut/Fn>::call_*` — it
        // forwards `self` (the fn-POINTER) + the spread args to an indirect call.
        // Its body is built entirely from constructs the pipeline lowers (the
        // fn-pointer INDIRECT call via `CallIndirect`), so it flows through and fails
        // loud on anything it cannot model — never invalid IR.
        | ty::InstanceKind::Shim(ty::ShimKind::FnPtr(_, _))
        // COROUTINE FAMILY (async closures): `ConstructCoroutineInClosure` is the
        // `<{async closure} as AsyncFnOnce>::async_call_once` body
        // (`build_construct_coroutine_by_move_shim`): already-untupled params
        // (self env + each spread call arg), ONE `AggregateKind::Coroutine`
        // construction of the BY-MOVE coroutine (moving the env fields), and a
        // `Return` — every piece flows through the existing aggregate/coroutine
        // lowering and fails loud on anything else.
        | ty::InstanceKind::Shim(ty::ShimKind::ConstructCoroutineInClosure { .. })
        // LANE C: `Clone` — the derived `<T as Clone>::clone` shim body
        // (`build_clone_shim`). rustc synthesizes it as the field-by-field clone:
        // a `discriminant` + `switchInt` for an enum, then per field either a
        // direct copy (a `Copy` POD field) or a `<FieldT as Clone>::clone(&field)`
        // call (the BFS pulls each such callee), and the aggregate
        // re-construction + `Return`. Every construct is already lowered; a shim
        // body that reaches something unmodelable fails loud (never invalid IR).
        | ty::InstanceKind::Shim(ty::ShimKind::Clone(_, _)) => {}
        _ => return Err("shim: synthetic instance (not Item)".to_string()),
    }

    let mut cx = Cx {
        tcx,
        instance,
        body,
        local_ty: HashMap::new(),
        model: HashMap::new(),
        emit_self_recursion,
        str_consts: Vec::new(),
        dyn_vtables: HashMap::new(),
        const_globals: std::cell::RefCell::new(HashMap::new()),
        pending_globals: std::cell::RefCell::new(Vec::new()),
        caller_location: None,
    };

    // RUNG 1 classification: which locals must be MEMORY-BACKED. A local is
    // memory-backed if its address is taken (Ref / RawPtr / CopyForDeref of a
    // place rooted at it) — a scalar then needs a real cell — OR its type is a
    // non-scalar aggregate (the dominant "non-scalar local" bucket).
    let address_taken = compute_address_taken(&cx, body);

    // Classify every local. Local 0 is the return place; 1..=arg_count are params.
    //
    // An SSA scalar is any single-access scalar leaf — int / bool (RUNG 0) OR a
    // THIN reference / raw pointer (RUNG 1: a `&T`/`*T` to a sized T is a single
    // `Ptr`-width register value, e.g. a `&Pair` parameter) — that is NOT
    // address-taken. Everything else (non-scalar aggregate, or any address-taken
    // scalar) is memory-backed.
    for local in body.local_decls.indices() {
        let cty = cx.local_concrete_ty(local);
        match memory_leaf_tir_ty(cx.tcx, cty) {
            Some(t) if !address_taken.contains(&local) => {
                // RUNG 0/1: a pure SSA scalar (int/bool/thin-ptr).
                cx.local_ty.insert(local, t.clone());
                cx.model.insert(local, LocalModel::Ssa(t));
            }
            _ => {
                // RUNG 4: a ZERO-SIZED local (unit / ZST struct/enum / PhantomData /
                // captureless closure env) occupies no storage and no ABI slot —
                // model it as a no-op `Zst` (NOT memory-backed: a ZST has no
                // address, no bytes). This is the biggest failure bucket. A ZST is
                // distinct from an uninitialized non-ZST; we only land here when
                // `layout_of` proves size 0.
                if ty_is_zst(&cx, cty) {
                    cx.model.insert(local, LocalModel::Zst);
                    continue;
                }
                // RUNG 1: memory-backed. Either a non-scalar aggregate, or a
                // scalar whose address is taken (needs a real cell). Require a
                // computable, sized, non-ZST layout up front (so an unmodelable
                // local fails the WHOLE function loud here, keeping buckets honest);
                // the per-projection access paths additionally fail-loud on a
                // non-scalar leaf. The slot `ptr` is filled in once the
                // FunctionBuilder exists (entry-block alloca below).
                // An UNSIZED local (`unsized_fn_params`) gets its 16-byte fat
                // (data, metadata) CARRIER slot instead.
                let (size, align) = match unsized_local_carrier(&cx, cty) {
                    Some(sa) => sa,
                    None => memory_layout_size_align(&cx, cty)?,
                };
                let _ = slot_lane_ty(size, align)?;
                cx.model.insert(
                    local,
                    LocalModel::Memory(MemSlot {
                        ptr: trust_ir::ValueId::new(u32::MAX),
                    }),
                );
            }
        }
    }

    // The return + param trust-ir signature.
    //
    // RUNG 3: by-value aggregate RETURN ABI. When `_0` is a non-scalar aggregate
    // (the dominant "non-scalar return local" bucket, e.g. a `-> E` enum / `-> S`
    // struct ctor — the `whnf`/`def_eq` shape), it is returned via an SRET HIDDEN
    // POINTER: a leading `Ptr` param the callee Stores the result through, and the
    // function `ret`s void. `_0`'s memory slot IS that sret pointer (no separate
    // alloca; the body's Stores into `_0` write the caller's destination). This is
    // the general (any-size) AAPCS64/SysV indirect-result convention, and unlike a
    // lane-tuple return it needs NO by-value tuple value to cross the boundary — so
    // the trust-ir validator's Return-type / field-access rules are satisfied with
    // the existing Load/Store/GEP machinery.
    let ret_local = Local::from_u32(0);
    let ret_abi = match cx.model.get(&ret_local) {
        Some(LocalModel::Ssa(t)) => RetAbi::Scalar(t.clone()),
        // RUNG 4: a ZST return (unit, ZST struct/enum) has zero ABI result values —
        // returned as void, exactly like the unit case.
        Some(LocalModel::Zst) => RetAbi::Unit,
        _ => {
            let cty = cx.local_concrete_ty(ret_local);
            // A unit-returning fn is common; allow it as a zero-result signature.
            if is_unit(cty) {
                RetAbi::Unit
            } else {
                // A non-scalar aggregate return. Require a computable, sized,
                // non-ZST layout up front (so an unmodelable return fails loud
                // here). `_0` must be memory-backed (it is, by classification).
                let _ = memory_layout_size_align(&cx, cty)?;
                if !cx.is_memory_local(ret_local) {
                    return Err(format!(
                        "non-scalar return local: _0 has type {} not memory-backed",
                        ty_family(cty)
                    ));
                }
                // A THIN pointer-wrapper return (`Box<Sized>`/`NonNull`/`Unique`/
                // `Rc`/`Arc`) is a single register-width `Ptr` whose true
                // (AAPCS64/SysV/C) ABI returns it BY VALUE in x0 — NOT through an
                // sret hidden pointer. This is the return-edge dual of the ac3c8ac
                // param-side fix: `_0` keeps its own entry slot (the body Stores the
                // wrapper into it via the ordinary memory-place machinery), and the
                // `Return` edge Loads that slot back to ONE `Ptr` (`RetAbi::Scalar`
                // already Loads a memory-backed `_0`). The caller's `call_return_abi`
                // classifies the destination with the SAME predicate, so both sides of
                // every edge stay in agreement. Restricted to a `Ptr` leaf so a
                // NON-pointer-wrapper return is UNCHANGED: an integer newtype return, a
                // FAT wrapper (`Box<[T]>`/`Box<dyn>` — a `ScalarPair`, `None` here), and
                // a true aggregate all fall through to the pair/sret path below.
                match param_scalar_leaf_tir_ty(&cx, cty) {
                    Some(TIRTy::Ptr) => RetAbi::Scalar(TIRTy::Ptr),
                    // UNWIND lane prerequisite (extern "C" fns only): ANY
                    // single-scalar-repr return — in particular a fieldless
                    // `#[repr(C)]` enum like `_Unwind_Reason_Code` — returns BY
                    // VALUE in w0/x0, per the C ABI the FOREIGN caller uses.
                    // `rust_eh_personality` is CALLED BY LIBUNWIND: an sret
                    // hidden pointer here would shift every argument register.
                    // Restricted to non-Rust-ABI fns so every Rust-ABI module's
                    // historical sret classification is byte-stable.
                    Some(t) if instance_is_extern_c(cx.tcx, cx.instance) => {
                        RetAbi::Scalar(t)
                    }
                    // RUNG 10: a small int/bool-lane struct/tuple pair returns BY
                    // VALUE as one SSA 2-tuple; everything else keeps the general
                    // sret hidden pointer.
                    _ => match pair_ret_model(&cx, cty) {
                        Some(pr) => RetAbi::Pair(pr),
                        None => RetAbi::Sret,
                    },
                }
            }
        }
    };
    Ok((cx, ret_abi, address_taken))
}

/// RUNG 3: how the function returns its result.
#[derive(Clone)]
enum RetAbi {
    /// A `-> ()` unit function: zero ABI result values, `ret []`.
    Unit,
    /// A scalar SSA result of this trust-ir type: `ret [v]`.
    Scalar(TIRTy),
    /// A by-value aggregate result returned through a leading SRET POINTER param:
    /// the callee Stores `_0` through it and `ret`s void. `_0`'s slot pointer IS
    /// the sret param (bound in the entry block before the body runs).
    Sret,
    /// RUNG 10: a SMALL-PAIR aggregate result returned BY VALUE as a single SSA
    /// 2-tuple (see `pair_ret_model`). `_0` keeps its OWN entry-block slot (the
    /// body's aggregate machinery Stores into it unchanged); only the `Return`
    /// edge converts the slot to an SSA value (one whole-aggregate `Load`).
    Pair(PairRet),
}

// ==================== RUNG 10: by-value SMALL-PAIR return ABI ================
//
// The design's remaining "struct/tuple BY-VALUE return ABI" rung, taken for the
// shapes the trust-ir interpreter/validator can execute end-to-end: a `-> S` /
// `-> (A, B)` return whose monomorphic type is
//
//   * a struct or tuple (NOT an enum/union/closure — those keep sret),
//   * laid out `BackendRepr::ScalarPair` by rustc with BOTH lanes fixed-width
//     INT/BOOL scalars (a pointer lane — fat pairs, (ptr,len) — keeps sret: the
//     zero-dep IR has no pointer constant to model such lanes portably yet),
//   * total size <= 16 bytes (the AAPCS64/SysV register-classified band; a
//     larger pair is memory-classed by the pinned `NativeC` policy, so sret IS
//     its faithful ABI),
//
// is returned BY VALUE: the trust-ir signature returns ONE `(laneA, laneB)`
// 2-tuple, the callee `ret`s a single SSA aggregate value, and the caller
// spills it into the destination slot. Lanes are in MEMORY-OFFSET order —
// rustc's ScalarPair invariant places lane `a` at offset 0 and lane `b` at
// `align_to(a.size, b.align)`, which for natural-aligned int/bool lanes is
// EXACTLY the interpreter's C-style `tuple_layout` of `(laneA, laneB)` — so the
// whole-aggregate `Load`/`Store` byte codec agrees with every lane offset the
// layout-faithful field reads/writes use. (For a rustc-REORDERED pair like
// `struct { tag: u8, val: u32 }` — laid out val@0, tag@4 — the emitted tuple is
// the offset-ordered `(u32, u8)`; field reads go through the slot at
// `layout_of` offsets, never through the SSA value, so source-order recovery
// is never needed.) Which REGISTERS carry the
// two lanes (AAPCS64 x0/x1) is trust-cg's realization concern, per the
// `StructPassingPolicy` contract split — the IR states only by-value-ness.
//
// SCOPE — the convention applies where BOTH SIDES of the call edge are lowered
// by THIS frontend: every lowered BODY's own signature
// (`classify_locals_and_ret_abi` on `_0`), and every IN-MODULE call edge (a
// self-recursive call, an emit-closure member edge — `callee_lowered_in_module`).
// A BODYLESS EXTERN declaration keeps the landed conservative sret form: its
// synthesized signature is a claim about FOREIGN code this frontend does not
// yet pin (that is the `byval`/`sret` ParamAttrs classification rung). HONEST
// LIMIT: a cross-MODULE edge to a pair-returning fn that IS separately lowered
// by this frontend would carry the stale sret claim — whole-program
// `--mir-emit-closure` (where such a callee becomes a member) is the supported
// execution path today.
//
// OPT-IN (`--mir-pair-ret-by-value`), default OFF: with the flag off, EVERY
// aggregate return keeps the landed sret
// convention and the emitted bytes are UNCHANGED. The flag is off by default
// because the landed trust-cg byte-verbatim fixture golds pin the sret form
// for in-module pair-returning members too (e.g. the derived `Clone`s of the
// 2-byte `BinderData` in the whnf/eta/infer slices — a default flip drifts
// 11 of the 27 REGEN-able slice modules), and trust-cg's codegen does not yet
// realize tuple-valued call/ret. Flipping the default is a coordinated
// trust-cg rung (tuple-return realization + fixture re-gold), not this one.
//
// Producer/consumer consistency on the applied edges is by construction: the
// callee classification and every in-module caller classification run this
// SAME predicate on the SAME monomorphic type (both behind the same flag).

/// The by-value pair-return model: the two scalar lanes in MEMORY-OFFSET order.
#[derive(Clone)]
struct PairRet {
    /// (trust-ir lane type, byte offset inside the aggregate); `lanes[0]` is at
    /// offset 0 per the ScalarPair invariant.
    lanes: [(TIRTy, u64); 2],
}

impl PairRet {
    /// The trust-ir return type: a single 2-tuple of the offset-ordered lanes.
    fn tuple_ty(&self) -> TIRTy {
        TIRTy::Tuple(vec![self.lanes[0].0.clone(), self.lanes[1].0.clone()])
    }
}

/// Natural size == alignment of an int/bool lane (bytes). The congruence check
/// in `pair_ret_model` compares rustc's lane placement against this table, so a
/// lane the interpreter would place differently fails CLOSED into sret.
fn int_lane_size(t: &TIRTy) -> u64 {
    match t {
        TIRTy::Bool | TIRTy::I8 | TIRTy::U8 => 1,
        TIRTy::I16 | TIRTy::U16 => 2,
        TIRTy::I32 | TIRTy::U32 => 4,
        TIRTy::I64 | TIRTy::U64 => 8,
        TIRTy::I128 | TIRTy::U128 => 16,
        _ => 0,
    }
}

/// Byte width of a SIMD lane element, INCLUDING the float lane types
/// (`F32` -> 4, `F64` -> 8) that `int_lane_size` reports as `0`. The per-lane
/// stride for the float-capable `simd_add`/`simd_mul`/`simd_cast` lowerings and
/// the `vminq_f32`/`vmaxq_f32`/`vcvtq_*` NEON foreign-symbol handlers.
fn simd_lane_bytes(t: &TIRTy) -> u64 {
    match t {
        TIRTy::F32 => 4,
        TIRTy::F64 => 8,
        _ => int_lane_size(t),
    }
}

/// Parse the `v{N}i{W}` element-count / bit-width token out of an LLVM vector
/// intrinsic mangled symbol (e.g. `llvm.aarch64.neon.ld2.v16i8.p0` -> `(16, 1)`
/// — 16 lanes of 1 byte). Returns `(lane_count, lane_bytes)`; `None` if no
/// integer-vector token is present (float `v4f32` forms return `None` — they
/// have their own handlers).
fn parse_vni_shape(sym: &str) -> Option<(u64, u64)> {
    for tok in sym.split('.') {
        if let Some(rest) = tok.strip_prefix('v') {
            if let Some((n_str, w_str)) = rest.split_once('i') {
                if let (Ok(n), Ok(w)) = (n_str.parse::<u64>(), w_str.parse::<u64>()) {
                    if n > 0 && w % 8 == 0 {
                        return Some((n, w / 8));
                    }
                }
            }
        }
    }
    None
}

/// Map a ScalarPair lane to its trust-ir int/bool type; `None` (-> sret) for
/// pointer / float / anything else.
fn pair_lane_tir_ty(scalar: &rustc_abi::Scalar) -> Option<TIRTy> {
    if scalar.is_bool() {
        return Some(TIRTy::Bool);
    }
    match scalar.primitive() {
        Primitive::Int(i, signed) => Some(match (i, signed) {
            (Integer::I8, false) => TIRTy::U8,
            (Integer::I8, true) => TIRTy::I8,
            (Integer::I16, false) => TIRTy::U16,
            (Integer::I16, true) => TIRTy::I16,
            (Integer::I32, false) => TIRTy::U32,
            (Integer::I32, true) => TIRTy::I32,
            (Integer::I64, false) => TIRTy::U64,
            (Integer::I64, true) => TIRTy::I64,
            (Integer::I128, false) => TIRTy::U128,
            (Integer::I128, true) => TIRTy::I128,
        }),
        _ => None,
    }
}

static PAIR_RET_BY_VALUE: std::sync::atomic::AtomicBool =
    std::sync::atomic::AtomicBool::new(false);

/// Enable RUNG 10 before starting rustc. This is intentionally callable only
/// by the sibling driver module; an undocumented ambient variable cannot
/// mutate lowering.
pub(super) fn enable_pair_ret_by_value() {
    PAIR_RET_BY_VALUE.store(true, std::sync::atomic::Ordering::Relaxed);
}

/// The RUNG 10 opt-in switch (see the header above).
fn pair_ret_enabled() -> bool {
    PAIR_RET_BY_VALUE.load(std::sync::atomic::Ordering::Relaxed)
}

/// Classify `ty` for the by-value pair-return ABI. `Some` iff the RUNG 10
/// opt-in is set AND every condition above holds; `None` falls back to the
/// general sret path (never a fail-loud — sret remains a correct general
/// lowering, and the flag-off default emits byte-identical modules).
fn pair_ret_model<'tcx>(cx: &Cx<'tcx, '_>, ty: Ty<'tcx>) -> Option<PairRet> {
    // Gate 0: the opt-in flag (default OFF — the landed sret convention).
    if !pair_ret_enabled() {
        return None;
    }
    // Gate 1: source kind — a struct or tuple only.
    match ty.kind() {
        ty::Tuple(_) => {}
        ty::Adt(adt, _) if adt.is_struct() => {}
        _ => return None,
    }
    // Gate 2: rustc classifies it as a two-scalar-register pair.
    let layout = cx
        .tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(ty))
        .ok()?;
    let BackendRepr::ScalarPair(a, b) = layout.backend_repr else {
        return None;
    };
    // Gate 3: the register-classified size band.
    if layout.size.bytes() > 16 {
        return None;
    }
    // Gate 4: both lanes are int/bool scalars.
    let ta = pair_lane_tir_ty(&a)?;
    let tb = pair_lane_tir_ty(&b)?;
    // Gate 5 (fail-closed congruence): rustc's lane placement must equal the
    // interpreter's C-style layout of `(ta, tb)` — natural size/align lanes,
    // lane b at `align_up(size(ta), align(tb))`. True for every natural int/bool
    // ScalarPair on this target; anything exotic falls back to sret.
    let (sa, sb) = (int_lane_size(&ta), int_lane_size(&tb));
    let b_off = a
        .size(&cx.tcx)
        .align_to(b.default_align(&cx.tcx).abi)
        .bytes();
    if sa == 0 || sb == 0 || a.size(&cx.tcx).bytes() != sa {
        return None;
    }
    if b_off != sa.next_multiple_of(sb) {
        return None;
    }
    Some(PairRet {
        lanes: [(ta, 0), (tb, b_off)],
    })
}

/// RUNG 10: whether this `Call`'s CALLEE body is lowered IN-MODULE by this same
/// run (a self-recursive call in an emit mode, or an emit-closure member), so
/// the by-value pair-return convention applies on this edge. Anything else is a
/// bodyless extern declaration and keeps the landed conservative sret form —
/// see the RUNG 10 header.
fn callee_lowered_in_module<'tcx>(
    cx: &Cx<'tcx, '_>,
    wiring: Option<&ClosureWiring>,
    func: &Operand<'tcx>,
) -> bool {
    if cx.emit_self_recursion && call_is_self_recursive(cx, func) {
        return true;
    }
    if let Some(w) = wiring {
        if let Some(inst) = resolve_call_callee(cx, func) {
            return w.member_fids.contains_key(cx.tcx.symbol_name(inst).name);
        }
    }
    false
}

/// EMIT-CLOSURE mode (`--mir-emit-closure`): how a `Call` whose callee is ANOTHER
/// crate-local closure member is wired to that member's IN-MODULE body `FuncId`
/// (not a 0-block extern stub), so the whole call graph composes inside ONE module.
/// `None` (the single-fn coverage / `--mir-emit` paths) leaves behavior UNCHANGED:
/// every non-self callee becomes an extern, and `body_fid` is 0-based.
struct ClosureWiring<'a> {
    /// The absolute next `FuncId` in the SHARED `ModuleBuilder` at the moment THIS
    /// member's lowering begins. Every `mb.function(..).build()` this member issues
    /// (its externs, then its body) takes ids `base_fid`, `base_fid+1`, ... so the
    /// body's id is `base_fid + (externs declared by this member)`.
    base_fid: u32,
    /// Callee SYMBOL NAME -> the in-module body `FuncId` of the closure member that
    /// IS that symbol. A `Call` resolving to a symbol in this map is wired to that
    /// id (an intra-module edge) instead of declaring an extern. The symbol is the
    /// same `tcx.symbol_name(instance)` the extern dedup uses, so the key is stable
    /// and monomorphization-precise (a different mono-instance is a different symbol).
    member_fids: &'a std::collections::HashMap<String, trust_ir::FuncId>,
}

/// Body of the lowering once the return ABI is decided. Lowers into the provided
/// SHARED `ModuleBuilder` `mb` (the caller owns it: it validates / serializes the
/// built module). The single-fn coverage / `--mir-emit` paths pass a fresh `mb` and
/// `wiring=None`; the `--mir-emit-closure` path passes the shared `mb` and a
/// `ClosureWiring` so a `Call` to another closure member wires in-module.
fn lower_with_signature<'tcx>(
    cx: &mut Cx<'tcx, '_>,
    mb: &mut ModuleBuilder,
    wiring: Option<&ClosureWiring>,
    body: &Body<'tcx>,
    ret_abi: RetAbi,
    _address_taken: &HashSet<Local>,
) -> Result<(), String> {
    // RUNG 3 ABI: the trust-ir param list is, in order:
    //   [sret Ptr]?  ++  for each MIR arg: a scalar of its type, OR a `Ptr`
    //   (by-ref) for a by-value aggregate param.
    // A by-value aggregate parameter is passed BY REFERENCE: the caller hands a
    // pointer to its (immutable copy of the) source aggregate; the param local's
    // memory slot IS that pointer. This needs no by-value lane tuple to cross the
    // boundary, so the existing Load/Store memory-place path reads the parameter.
    let has_sret = matches!(ret_abi, RetAbi::Sret);
    // UNWIND lane (panic=unwind): lower unwind edges faithfully (Invoke /
    // LandingPad / Resume). Under panic=abort this is `false` and every path
    // below is byte-identical to the pre-EH lowering.
    let eh = eh_lane(cx.tcx);
    let mut param_tys: Vec<TIRTy> = Vec::new();
    // RUNG 11 ABI pinning: a positional `ParamAttrs` per signature parameter, built
    // in LOCKSTEP with `param_tys`. Under the opt-in flag we pin `byval` on every
    // by-ref aggregate `Ptr` param and `sret` on the hidden return pointer — the
    // by-value-vs-by-reference classification the abi-pinning contract wants a
    // producer to STATE rather than a consumer to re-invent. With the flag OFF
    // every entry stays `ParamAttrs::default()`, so `FuncAttrs::is_empty()` holds
    // and NO attr comment is emitted — the output is byte-identical to pre-rung.
    let mut param_attrs: Vec<trust_ir::ParamAttrs> = Vec::new();
    let abi_pin = pair_ret_enabled();
    if has_sret {
        param_tys.push(TIRTy::Ptr);
        param_attrs.push(trust_ir::ParamAttrs { sret: abi_pin, ..Default::default() });
    }
    // Which MIR arg locals are by-ref aggregates (memory-backed params).
    let mut agg_param: HashSet<Local> = HashSet::new();
    // Which MIR arg locals are SCALAR-SPILL params: a memory-backed param whose type
    // is a SINGLE scalar leaf (int / bool / THIN pointer like `&T`/`*T`) — it became
    // memory-backed ONLY because its address is taken in the body (e.g. `sz`'s
    // `_1: &T`, where the body forms `&((*_1) as N).0`). Such a param is passed BY
    // VALUE as its scalar (matching how every CALLER passes it — `classify_call_arg`
    // sends the scalar by value, incl. SELF-recursion), then spilled into its
    // entry-allocated slot so the address-taken uses read a real cell. This is the
    // standard "address-taken scalar param" lowering. (If we instead used the by-ref
    // aggregate ABI here, the callee would expect a pointer-TO-the-pointer while every
    // caller passes the pointer by value — an ABI mismatch that crashes the recursion.)
    let mut spill_param: HashSet<Local> = HashSet::new();
    // RUNG 11: MIR arg locals whose monomorphic type is a small int/bool-lane
    // ScalarPair (`pair_ret_model`, opt-in) and so cross the ABI BY VALUE as one
    // SSA 2-tuple param (the dual of the RUNG 10 by-value pair RETURN), spilled
    // into their entry slot so the body's layout-faithful field reads still work.
    let mut pair_param: HashSet<Local> = HashSet::new();
    let mut pair_param_model: HashMap<Local, PairRet> = HashMap::new();
    // THREADS / rust-call ABI: a body with `spread_arg` (the FnOnce/Fn/FnMut
    // family shims, `Box<F>::call_once`, the blanket `impl Fn* for &F` — every
    // `extern "rust-call"` fn whose MIR keeps the trailing ARGS TUPLE as one
    // local) must SPREAD that tuple in its OWN lowered signature: one ABI slot
    // per non-ZST field (scalar by value / aggregate by ref), exactly the
    // caller-side `spread_closure_args` classification. The historical
    // tuple-by-ref lowering agreed with in-repo callers only by accident (a
    // 1-field tuple's address == its field's address) and broke every REIFIED
    // boundary: the thread-local ACCESSOR (`LocalKey.inner`) is called through
    // a plain `fn(Option<..>) -> ..` pointer whose caller passes the Option
    // SCALAR by value, while the tuple-by-ref shim loaded `[x0]` — the NULL
    // deref at thread-spawn. The tuple LOCAL keeps its memory slot; the entry
    // block RECONSTITUTES it by storing each incoming field at its layout
    // offset, so the body is unchanged.
    enum SpreadParamAbi {
        Scalar(TIRTy),
        ByRef { size: u64, align: u64 },
    }
    let spread_local: Option<Local> = body.spread_arg;
    let mut spread_param_fields: Vec<(u64, SpreadParamAbi)> = Vec::new();
    if let Some(sl) = spread_local {
        let tup_ty = cx.local_concrete_ty(sl);
        match cx.model.get(&sl) {
            // A unit `()` args tuple is a Zst local: zero spread slots.
            Some(LocalModel::Zst) | None => {}
            Some(LocalModel::Memory(_)) => {
                let ty::Tuple(elems) = tup_ty.kind() else {
                    return Err(format!(
                        "rust-call spread local is not a tuple ({})",
                        ty_family(tup_ty)
                    ));
                };
                let layout = cx
                    .tcx
                    .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(tup_ty))
                    .map_err(|e| format!("rust-call args-tuple layout_of failed: {e:?}"))?;
                for (i, fty) in elems.iter().enumerate() {
                    let fty = cx.mono(fty);
                    if ty_is_zst(&cx, fty) {
                        continue;
                    }
                    let off = layout.fields.offset(i).bytes();
                    if let Some(t) = spread_field_scalar_leaf(&cx, fty) {
                        spread_param_fields.push((off, SpreadParamAbi::Scalar(t)));
                    } else {
                        let (size, align) = memory_layout_size_align(&cx, fty)?;
                        spread_param_fields.push((off, SpreadParamAbi::ByRef { size, align }));
                    }
                }
            }
            Some(LocalModel::Ssa(_)) => {
                return Err("rust-call spread local unexpectedly SSA".to_string());
            }
        }
    }
    for i in 1..=body.arg_count {
        let l = Local::from_usize(i);
        // The rust-call ARGS-TUPLE param spreads into per-field ABI slots.
        if spread_local == Some(l) {
            for (_off, abi) in &spread_param_fields {
                match abi {
                    SpreadParamAbi::Scalar(t) => param_tys.push(t.clone()),
                    SpreadParamAbi::ByRef { .. } => param_tys.push(TIRTy::Ptr),
                }
                param_attrs.push(trust_ir::ParamAttrs::default());
            }
            continue;
        }
        match cx.model.get(&l) {
            Some(LocalModel::Ssa(t)) => {
                param_tys.push(t.clone());
                param_attrs.push(trust_ir::ParamAttrs::default());
            }
            // RUNG 4: a ZST parameter occupies NO ABI slot (it carries no bytes).
            Some(LocalModel::Zst) => continue,
            Some(LocalModel::Memory(_)) => {
                let cty = cx.local_concrete_ty(l);
                let _ = memory_layout_size_align(cx, cty)?;
                if let Some(leaf) = param_scalar_leaf_tir_ty(cx, cty) {
                    // Address-taken SCALAR param (incl. a transparent int newtype like
                    // `Tag(u8)`): by-value scalar + entry spill.
                    param_tys.push(leaf);
                    param_attrs.push(trust_ir::ParamAttrs::default());
                    spill_param.insert(l);
                } else if let Some(pr) = pair_ret_model(cx, cty) {
                    // RUNG 11: a small int/bool-lane pair param crosses BY VALUE as
                    // ONE SSA 2-tuple (NO by-ref `Ptr`), spilled into its entry slot
                    // at fn entry. `pair_ret_model` is `None` with the flag off, so
                    // this branch (and any emit drift) is opt-in only.
                    param_tys.push(pr.tuple_ty());
                    param_attrs.push(trust_ir::ParamAttrs::default());
                    pair_param.insert(l);
                    pair_param_model.insert(l, pr);
                } else {
                    // A by-value aggregate parameter -> a leading-of-its-position
                    // `Ptr` (by-ref). RUNG 11 pins `byval`: this pointer carries a
                    // by-value aggregate through memory (the caller makes the copy).
                    param_tys.push(TIRTy::Ptr);
                    param_attrs
                        .push(trust_ir::ParamAttrs { byval: abi_pin, ..Default::default() });
                    agg_param.insert(l);
                }
            }
            None => {
                // No model entry: a unit / ZST parameter occupies no ABI slot.
                let cty = cx.local_concrete_ty(l);
                if is_unit(cty) {
                    continue;
                }
                return Err(format!(
                    "non-scalar param local: {:?} has type {} (unmodelable)",
                    l,
                    ty_family(cty)
                ));
            }
        }
    }
    // UNWIND lane, `#[track_caller]` ABI (rustc 1.99 parity): a body that
    // `requires_caller_location` takes ONE extra hidden `&'static Location`
    // param — a thin `Ptr` appended LAST (after every real arg, after spread
    // fields), exactly where rustc's `FnAbi` chains `caller_location`. Every
    // CALLER of such a fn appends the matching argument by the SAME predicate
    // (`callee_needs_caller_location` in `call_signature_params_returns` and
    // at the Call emission site), so definition and every reference stay
    // link-consistent across separately-emitted modules. Not a MIR local: the
    // value is bound as an entry param below, never enters the local model.
    // Under panic=abort this is `false` and the signature is byte-identical.
    let needs_cl_param = eh && cx.instance.def.requires_caller_location(cx.tcx);
    if needs_cl_param {
        param_tys.push(TIRTy::Ptr);
        param_attrs.push(trust_ir::ParamAttrs::default());
    }

    // RUNG 2 cross-block phi: backward liveness over the SSA-scalar locals. Each
    // non-entry block will get a block parameter for every scalar local LIVE AT
    // ITS ENTRY, in stable local order; every edge passes the predecessor's value
    // for each successor live-in. (See the module header for the soundness
    // argument: a successor live-in is live across the edge -> live-out of the
    // predecessor -> a param of, or defined in, the predecessor block.)
    // (RUNG 2 liveness + reachability now run AFTER the Call/Drop pre-passes:
    // under the EH lane they need the per-block faithful-unwind-edge set those
    // pre-passes record. See `compute_scalar_live_in` / `compute_normal_reachable`
    // below — under panic=abort the recorded set is empty and both results are
    // identical to the historical normal-edges-only computation.)

    // RUNG 2 Call pre-pass: declare each call's EXTERN callee in the module BEFORE
    // the FunctionBuilder borrows it. We key the declared `FuncId` by the calling
    // block index (a `Call` is its block's terminator, so at most one per block).
    // The callee's synthesized signature uses the LOWERED arg/dest types (the same
    // type logic the lowering uses), so the validator's arg/return-type checks
    // pass by construction. We fail loud HERE on any call shape the minimal port
    // cannot lower (indirect callee, non-scalar arg/dest), keeping buckets honest.
    let sym = cx.tcx.def_path_str(cx.instance.def_id());
    // The trust-ir text grammar's bare `@name` identifier admits alphanumerics,
    // `_`, and `.` — but NOT `:` `<` `>` `'` etc. A free fn (`sz`) has no `::`, but an
    // inherent / trait IMPL method's `def_path_str` is `Type::method`, whose `::` makes
    // the emitted `@Type::method` UNPARSEABLE (re-parse / JIT both fail). A method on a
    // GENERIC impl (e.g. `MicroChecker::<'e>::whnf`) additionally carries `<'e>`/`<T>`
    // angle/lifetime noise. Sanitize the BODY function's bare name so it round-trips:
    // first `::` -> `__`, then map ANY remaining char outside `[A-Za-z0-9_.]` to `_`.
    // Names WITHOUT generics (`structural_eq_impl`, `subst_at`, `subst`) contain none
    // of these chars, so the second pass is a no-op for them — the already-emitted IR
    // does NOT drift. The module name is a QUOTED string ("mir::..."), so it keeps the
    // readable path.
    let mut fn_name: String = sym
        .replace("::", "__")
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() || c == '_' || c == '.' { c } else { '_' })
        .collect();
    // RUNG 9: a closure-COMBINATOR member (a non-local generic `Option::and_then` /
    // `map` / ... monomorphized at a CLOSURE type) has a `def_path_str` that DROPS
    // the generic args — so two distinct monomorphizations (e.g. `bit_width`'s and
    // `bit_width_with`'s `and_then` closures) collapse to the SAME readable name and
    // the JIT rejects the module with `DuplicateSymbol`. Disambiguate such a member
    // by appending a short, deterministic suffix derived from its UNIQUE mangled
    // symbol (`tcx.symbol_name`), which encodes the full monomorphization. This fires
    // ONLY for a closure-combinator member (the `carries_closure` gate) — every
    // existing member's name is byte-for-byte unchanged (additive). A closure BODY
    // already has a unique `def_path_str` (`..::{closure#N}`), so it is excluded.
    let is_combinator = !cx.instance.def_id().is_local()
        && !matches!(cx.tcx.def_kind(cx.instance.def_id()), rustc_hir::def::DefKind::Closure)
        && cx
            .instance
            .args
            .iter()
            .any(|a| a.as_type().is_some_and(|t| matches!(t.kind(), ty::Closure(..))));
    if is_combinator {
        // A stable 64-bit hash of the mangled symbol -> 16 hex chars. Deterministic
        // (same symbol -> same suffix), so the emitted module does not drift run to
        // run, and distinct monomorphizations get distinct suffixes.
        use std::hash::{Hash, Hasher};
        let mangled = cx.tcx.symbol_name(cx.instance).name;
        let mut h = std::collections::hash_map::DefaultHasher::new();
        mangled.hash(&mut h);
        fn_name = format!("{fn_name}__mono{:016x}", h.finish());
    }
    // WHOLE-PROGRAM LINK FIX: the emitted DEFINITION's function symbol must be the
    // SAME string every CALLER references. A caller lowering a `Call` names its
    // extern callee by `call_extern_signature`'s `tcx.symbol_name(instance).name`
    // (the v0-mangled symbol, e.g. `_RNvMCs..5Level4succ`), while the sanitized
    // def-path name computed above (`Level::succ` -> `Level__succ`) lives in a
    // DISJOINT namespace — so no two per-fn objects co-resolve and the program
    // cannot link. Override the body symbol with the same mangled name on the
    // SINGLE-FN emit paths (`--mir-emit` / `--mir-emit-each`, `wiring.is_none()`),
    // putting definition and reference in ONE namespace. The `--mir-emit-closure`
    // path (`wiring.is_some()`) is deliberately NOT touched: its members are wired
    // by IN-MODULE `FuncId` (not by symbol), and it keeps the readable, JIT-
    // DuplicateSymbol-free name the first-party closure census depends on. The
    // output FILENAME stays sanitized (set by the driver) — only the internal
    // symbol changes.
    if wiring.is_none() {
        fn_name = cx.tcx.symbol_name(cx.instance).name.to_string();
    }
    // `mb` is the SHARED ModuleBuilder (the caller owns it / set its module name).
    let mut callee_ids: HashMap<usize, trust_ir::FuncId> = HashMap::new();
    // R6: per block index, the registered `FuncTy` of a FN-POINTER INDIRECT call —
    // `Some` means the terminator emits `CallIndirect` through the lowered fn-pointer
    // value rather than a direct `Call` to a declared extern.
    let mut indirect_sig_blocks: HashMap<usize, trust_ir::FuncTyId> = HashMap::new();
    // DYN/VIRTUAL dispatch: per block index whose `Call` resolves to a `Virtual`
    // trait method (a `dyn Trait` call), the call's registered `FuncTy` + the vtable
    // SLOT index. `Some` -> the emission loads the concrete method fn-pointer from the
    // receiver's vtable[slot] and emits `CallIndirect`, with the `&dyn` receiver arg
    // replaced by its DATA pointer. (hashbrown erases its hasher/eq closures to `&dyn
    // Fn`/`FnMut` to cut monomorphization, so every insert/get/resize dispatches here.)
    // value = (call signature, vtable slot index, is_rust_call). `is_rust_call` marks
    // a `dyn Fn`/`FnMut`/`FnOnce` dispatch whose args tuple must be SPREAD (its vtable
    // method is the concrete closure body, emitted with spread params).
    let mut virtual_blocks: HashMap<usize, (trust_ir::FuncTyId, usize, bool)> = HashMap::new();
    // Dedup extern callees by symbol across this one function's body.
    let mut extern_by_sym: HashMap<String, trust_ir::FuncId> = HashMap::new();
    // Count of functions THIS member declares into `mb` (its externs, then its body).
    // `FuncId`s are assigned sequentially, one per `.build()`. In single-fn mode the
    // body's id is simply this count (`mb` started empty); in closure mode the body's
    // id is `wiring.base_fid + n_declared` (the absolute next id in the shared mb).
    let mut n_declared: u32 = 0;
    // Absolute base id for THIS member: 0 in single-fn mode, `wiring.base_fid` in
    // closure mode. Added to `n_declared` to compute the body's `FuncId`.
    let base_fid: u32 = wiring.map(|w| w.base_fid).unwrap_or(0);
    // EMIT mode: blocks whose `Call` is a self-recursion to THIS instance, wired to
    // the in-module body `FuncId` (computed once the body is created) so the module
    // is self-contained. Empty in coverage mode (every call declares an extern stub).
    let mut self_call_blocks: Vec<usize> = Vec::new();
    // RUNG 5: blocks whose `Call` is `<Arc<T> as Deref>::deref` over a THIN Arc,
    // inlined to `load ptr + gep <ArcInner-data-offset>` instead of an extern stub.
    // Keyed block -> data offset. (Inlined in BOTH coverage and emit paths: it is
    // pure pointer arithmetic with no cross-fn edge, so a `--mir-lower` count of a
    // walker that touches Arc children no longer fails on the deref shape.)
    let mut arc_deref_blocks: HashMap<usize, u64> = HashMap::new();
    // RUNG 6: blocks whose `Call` is `Arc::<T>::new` over a THIN Arc, inlined to a
    // `heap_alloc` of `ArcInner<T>` + counter/data Stores (the CONSTRUCTION dual of
    // the Arc-deref read). Keyed block -> ArcInner layout. Inlined in BOTH coverage
    // and emit paths (it has no cross-fn edge: the allocator is bound at JIT/link).
    let mut arc_new_blocks: HashMap<usize, ArcInnerLayout> = HashMap::new();
    // RUNG 7: blocks whose `Call` is the `(uN, uN, &str) -> uN` saturating-add
    // diagnostic helper (`checked_add_u32`), inlined to `overflow(Add) + select`
    // (the std `saturating_add`), DROPPING the dead `&str` message. Keyed
    // block -> the unsigned-int lane type. No extern, no `&str` materialization.
    let mut sat_add_blocks: HashMap<usize, TIRTy> = HashMap::new();
    // Both panic lanes: blocks whose `Call` is a size-scaled raw-memory intrinsic
    // mono or stable core/std wrapper (`copy` / `copy_nonoverlapping` /
    // `write_bytes`) lowered inline with its element stride (see
    // `MemIntrinsicInline`).
    let mut mem_intrinsic_blocks: HashMap<usize, MemIntrinsicInline> = HashMap::new();
    // Both panic lanes: blocks whose `Call` is a canonical raw-pointer
    // `offset` / `wrapping_offset` wrapper. Cross-crate MIR can retain these
    // always-inline core methods as real calls rather than expose their MIR
    // intrinsic. Record the faithful inline lane here so a single-function
    // emit cannot leak the wrapper as an opaque bodyless declaration.
    let mut raw_ptr_offset_blocks: HashMap<usize, RawPtrOffsetInline> = HashMap::new();
    // RUNG 8b: blocks whose `Call` is `IntoIterator::into_iter` over a Vec/&Vec/slice,
    // inlined to a `(cur,end)` cursor-init from the source Vec. Keyed block -> model.
    let mut into_iter_blocks: HashMap<usize, IterModel> = HashMap::new();
    // RUNG 8b: blocks whose `Call` is `Iterator::next` over a `vec::IntoIter`/
    // `slice::Iter`, inlined to a cursor index-bump + `Some`/`None` write. Keyed
    // block -> model.
    let mut iter_next_blocks: HashMap<usize, IterModel> = HashMap::new();
    // RUNG 8b: blocks whose `Call` is `Box::<U>::new_uninit()`, inlined to a
    // `heap_alloc` of the pointee buffer. Keyed block -> buffer layout.
    let mut box_new_uninit_blocks: HashMap<usize, BoxNewUninitLayout> = HashMap::new();
    // RUNG 8b: blocks whose `Call` is `box_assume_init_into_vec_unsafe::<T,N>`,
    // inlined to a 3-word `Vec{ptr,N,N}` materialization. Keyed block -> count.
    let mut box_into_vec_blocks: HashMap<usize, BoxIntoVecLayout> = HashMap::new();
    // ADDITIVE (R4 stage 2): blocks whose `Call` is an in-module str/byte shape
    // (`str::as_bytes`/`str::len`/`str::bytes`/`<[u8]>::iter`/blanket-identity
    // `into_iter`), inlined to fat-pair lane reads / cursor writes. Keyed
    // block -> op. No extern.
    let mut str_inline_blocks: HashMap<usize, StrInlineOp> = HashMap::new();
    // RUNG 10: blocks whose `Call`'s callee is lowered IN-MODULE (self-recursion /
    // emit-closure member), so the by-value pair-return convention applies on that
    // edge. The emission-site `call_return_abi` must agree with the signature the
    // pre-pass synthesized, so the decision is recorded here once per block.
    let mut pair_ret_blocks: HashSet<usize> = HashSet::new();
    // UNWIND lane: the faithful-unwind-edge bookkeeping the direct-call branches
    // below record (empty under panic=abort — see `EhEdges`).
    let mut eh_edges = EhEdges::default();
    // UNWIND lane: the per-signature indirect-call THUNKS this module synthesized
    // (fn-pointer / virtual / dyn-drop cleanup-edge carriers), and which blocks'
    // call sites invoke through them. Empty under panic=abort.
    let mut thunk_by_sig: HashMap<trust_ir::FuncTyId, trust_ir::FuncId> = HashMap::new();
    let mut indirect_thunk_blocks: HashMap<usize, trust_ir::FuncId> = HashMap::new();
    // UNWIND lane, `#[track_caller]`: blocks whose `Call` is the
    // `caller_location` intrinsic, lowered INLINE (hidden-param read / span
    // Location const) with NO extern declared. Empty under panic=abort.
    let mut caller_location_blocks: HashSet<usize> = HashSet::new();
    for (bb_raw, data) in body.basic_blocks.iter_enumerated() {
        let term = data
            .terminator
            .as_ref()
            .ok_or_else(|| "block has no terminator".to_string())?;
        if let TerminatorKind::Call {
            func,
            args,
            destination,
            unwind,
            ..
        } = &term.kind
        {
            // RUNG 10: one in-module-edge decision per call, shared by every
            // signature-synthesis branch below AND the emission site (TermCtx).
            let pair_ok = callee_lowered_in_module(cx, wiring, func);
            if pair_ok {
                pair_ret_blocks.insert(bb_raw.as_usize());
            }
            // UNWIND lane: `core::intrinsics::catch_unwind` lowers INLINE as the
            // `__rust_try` invoke/landing-pad shape (rustc's `codegen_gnu_try`,
            // with the fn-pointer operands devirtualized to DIRECT calls — they
            // are constant fn items at every real call site). Pre-declare the
            // `do_call`/`do_catch` callees here and record the expansion; the
            // generic extern-stub declaration is skipped (the intrinsic symbol
            // is never referenced). Under panic=abort this branch is dead and
            // the intrinsic keeps its historical extern-stub lowering.
            if eh {
                if let Some(callee) = resolve_call_callee(cx, func) {
                    if cx
                        .tcx
                        .intrinsic(callee.def_id())
                        .is_some_and(|i| i.name.as_str() == "catch_unwind")
                    {
                        let [try_op, _data_op, catch_op] = &args[..] else {
                            return Err(format!(
                                "catch_unwind intrinsic: expected 3 args, got {}",
                                args.len()
                            ));
                        };
                        let try_inst = resolve_fnptr_operand(cx, body, &try_op.node)?;
                        let catch_inst = resolve_fnptr_operand(cx, body, &catch_op.node)?;
                        let mut declare = |inst: Instance<'tcx>,
                                           params: Vec<TIRTy>|
                         -> trust_ir::FuncId {
                            let dsym = cx.tcx.symbol_name(inst).name.to_string();
                            if let Some(id) = extern_by_sym.get(&dsym) {
                                *id
                            } else {
                                let cty = mb.add_func_type(params, Vec::new());
                                let id = mb.function(dsym.clone(), cty).build();
                                n_declared += 1;
                                extern_by_sym.insert(dsym, id);
                                id
                            }
                        };
                        let try_fid = declare(try_inst, vec![TIRTy::Ptr]);
                        let catch_fid = declare(catch_inst, vec![TIRTy::Ptr, TIRTy::Ptr]);
                        eh_edges
                            .catch_expand
                            .insert(bb_raw.as_usize(), (try_fid, catch_fid));
                        continue;
                    }
                    // UNWIND lane, `#[track_caller]`: `core::intrinsics::
                    // caller_location()` lowers INLINE (rustc's
                    // `get_caller_location`): a track_caller body forwards its
                    // hidden Location param; a non-track_caller body gets the
                    // span's CTFE'd Location const. NO extern is declared (the
                    // harness `_rt_dummy_loc` leaf is dead on this lane). Under
                    // panic=abort the intrinsic keeps its historical
                    // extern-stub lowering byte-for-byte.
                    if cx
                        .tcx
                        .intrinsic(callee.def_id())
                        .is_some_and(|i| i.name.as_str() == "caller_location")
                    {
                        caller_location_blocks.insert(bb_raw.as_usize());
                        continue;
                    }
                }
            }
            // The SIZE-SCALED raw-memory intrinsics (`copy` /
            // `copy_nonoverlapping` / `write_bytes`) whose monos survive as real
            // extern calls. Record the
            // inline plan (element stride from the mono's layout; non-ZST forms
            // declare libc memmove/memset as genuine system leaves, while ZST
            // forms are exact no-ops). NO extern is declared for the intrinsic
            // symbol.
            //
            // HOISTED OUT of the `if eh` gate (bugfix): this MUST run under
            // panic=abort too. The historical extern-stub lowering is
            // STRIDE-ERASED (`@core::intrinsics::copy(ptr, ptr, u64)`), which
            // trust-cg synthesizes as `memmove(dst, src, count)` — using the
            // element COUNT as the BYTE length. For any element wider than 1 byte
            // (e.g. the `NonNull`/`u64` slices in BTreeMap `slice_insert`), an
            // N-element shift moves only N bytes instead of N*stride, corrupting
            // the array (the BTreeMap internal-node NULL-edge SIGSEGV). Append/
            // tail inserts have shift-count 0, so the bug is masked until a
            // mid-array move with a nonzero count occurs.
            if let Some(callee) = resolve_call_callee(cx, func) {
                if let Some(idef) = cx.tcx.intrinsic(callee.def_id()) {
                    let iname = idef.name.as_str();
                    // `arith_offset` (wrapping, negative-capable) lowers inline
                    // at the call site via the C-raw-pointer PtrToInt/IntToPtr
                    // path (see the dedicated arm in terminator dispatch).
                    // Validate the call ABI here, then skip ordinary extern
                    // declaration: leaving an unused intrinsic declaration in
                    // a single-function artifact disguises an authority hole.
                    if iname == "arith_offset" {
                        let _ = call_extern_signature(cx, func, args, destination, pair_ok)?;
                        continue;
                    }
                    if matches!(iname, "copy" | "copy_nonoverlapping" | "write_bytes") {
                        let elem = callee.args.type_at(0);
                        let (stride, _size, _align) = iter_elem_layout(cx, elem)?;
                        let mi = if stride == 0 {
                            // A ZST count denotes zero bytes for every `count`.
                            // Preserve Rust's no-op behavior without introducing
                            // an observable libc call (or requiring its dangling
                            // ZST pointers to satisfy a foreign ABI contract).
                            match iname {
                                "copy" | "copy_nonoverlapping" => MemIntrinsicInline::ZstCopy,
                                _ => MemIntrinsicInline::ZstWriteBytes,
                            }
                        } else {
                            let mut declare_libc =
                                |sym: &str, params: Vec<TIRTy>| -> trust_ir::FuncId {
                                    if let Some(id) = extern_by_sym.get(sym) {
                                        *id
                                    } else {
                                        let cty = mb.add_func_type(params, Vec::new());
                                        let id = mb.function(sym.to_string(), cty).build();
                                        n_declared += 1;
                                        extern_by_sym.insert(sym.to_string(), id);
                                        id
                                    }
                                };
                            match iname {
                                "copy" | "copy_nonoverlapping" => MemIntrinsicInline::Copy {
                                    stride,
                                    memmove: declare_libc(
                                        "memmove",
                                        vec![TIRTy::Ptr, TIRTy::Ptr, TIRTy::U64],
                                    ),
                                    order: CopyOperandOrder::SourceDestination,
                                },
                                _ => MemIntrinsicInline::WriteBytes {
                                    stride,
                                    memset: declare_libc(
                                        "memset",
                                        vec![TIRTy::Ptr, TIRTy::I32, TIRTy::U64],
                                    ),
                                },
                            }
                        };
                        mem_intrinsic_blocks.insert(bb_raw.as_usize(), mi);
                        continue;
                    }
                }
            }
            // Stable `core::ptr`/`std::ptr` APIs and their canonical raw-pointer
            // methods can survive cross-crate MIR as ordinary Item calls rather
            // than expose the intrinsics above. Treating those calls as opaque
            // externs loses the element type and recreates the same stride-erased
            // copy/write bug. Recognize only exact source identities, validate the
            // retained call ABI, derive the stride from its pointer operand, and
            // inline the same libc/no-op plan. `copy_from*` is destination-first;
            // every other copy wrapper is source-first.
            if let Some(wrapper) = stable_mem_wrapper(cx, func) {
                let [pointer_op, _second_op, _count_op] = &args[..] else {
                    return Err(format!(
                        "stable pointer memory wrapper: expected 3 args, got {}",
                        args.len()
                    ));
                };
                let pointer_ty = operand_concrete_ty(cx, &pointer_op.node);
                let pointee = match pointer_ty.kind() {
                    ty::RawPtr(pointee, _) => *pointee,
                    _ => {
                        return Err(format!(
                            "stable pointer memory wrapper: memory operand is not a raw pointer \
                             ({pointer_ty:?})"
                        ));
                    }
                };
                let (stride, _size, _align) = iter_elem_layout(cx, pointee)?;
                let _ = call_extern_signature(cx, func, args, destination, pair_ok)?;
                let mi = if stride == 0 {
                    match wrapper {
                        StableMemWrapper::Copy(_) => MemIntrinsicInline::ZstCopy,
                        StableMemWrapper::WriteBytes => MemIntrinsicInline::ZstWriteBytes,
                    }
                } else {
                    let mut declare_libc =
                        |sym: &str, params: Vec<TIRTy>| -> trust_ir::FuncId {
                            if let Some(id) = extern_by_sym.get(sym) {
                                *id
                            } else {
                                let cty = mb.add_func_type(params, Vec::new());
                                let id = mb.function(sym.to_string(), cty).build();
                                n_declared += 1;
                                extern_by_sym.insert(sym.to_string(), id);
                                id
                            }
                        };
                    match wrapper {
                        StableMemWrapper::Copy(order) => MemIntrinsicInline::Copy {
                            stride,
                            memmove: declare_libc(
                                "memmove",
                                vec![TIRTy::Ptr, TIRTy::Ptr, TIRTy::U64],
                            ),
                            order,
                        },
                        StableMemWrapper::WriteBytes => MemIntrinsicInline::WriteBytes {
                            stride,
                            memset: declare_libc(
                                "memset",
                                vec![TIRTy::Ptr, TIRTy::I32, TIRTy::U64],
                            ),
                        },
                    }
                };
                mem_intrinsic_blocks.insert(bb_raw.as_usize(), mi);
                continue;
            }
            // A stable `ptr.offset(count)` call can survive cross-crate MIR as
            // `core::ptr::{const_ptr,mut_ptr}::<impl ...>::offset`, so handling
            // only the direct MIR `BinOp::Offset` is insufficient. Inline a
            // statically non-negative count with the allocation-relative GEP
            // lane; use the sanctioned integer-pointer lane for a dynamic
            // signed count that may legally step backward. ZST offsets are
            // always zero bytes and return the original pointer.
            if raw_ptr_method_named(cx, func, "offset") {
                let [ptr_op, count_op] = &args[..] else {
                    return Err(format!(
                        "raw pointer offset wrapper: expected 2 args, got {}",
                        args.len()
                    ));
                };
                let ptr_ty = operand_concrete_ty(cx, &ptr_op.node);
                let pointee = match ptr_ty.kind() {
                    ty::RawPtr(pointee, _) => *pointee,
                    _ => {
                        return Err(format!(
                            "raw pointer offset wrapper: arg 0 is not a raw pointer ({ptr_ty:?})"
                        ));
                    }
                };
                let (stride, _size, _align) = iter_elem_layout(cx, pointee)?;
                let statically_nonnegative = match &count_op.node {
                    Operand::Constant(c) => {
                        const_operand_i128(cx, c).is_some_and(|value| value >= 0)
                    }
                    _ => false,
                };
                // Validate the call/destination ABI now, while deliberately
                // discarding its would-be extern symbol.
                let _ = call_extern_signature(cx, func, args, destination, pair_ok)?;
                let inline = if stride == 0 || statically_nonnegative {
                    RawPtrOffsetInline::Gep { stride }
                } else {
                    RawPtrOffsetInline::Integer { stride }
                };
                raw_ptr_offset_blocks.insert(bb_raw.as_usize(), inline);
                continue;
            }
            // Stable `wrapping_offset` is the wrapper form of `arith_offset`.
            // It must use the same modular integer-pointer lane instead of
            // escaping as an opaque core declaration (or being needlessly
            // rejected when cross-crate MIR retains the wrapper call).
            if raw_ptr_method_named(cx, func, "wrapping_offset") {
                let [ptr_op, _count_op] = &args[..] else {
                    return Err(format!(
                        "raw pointer wrapping_offset wrapper: expected 2 args, got {}",
                        args.len()
                    ));
                };
                let ptr_ty = operand_concrete_ty(cx, &ptr_op.node);
                let pointee = match ptr_ty.kind() {
                    ty::RawPtr(pointee, _) => *pointee,
                    _ => {
                        return Err(format!(
                            "raw pointer wrapping_offset wrapper: arg 0 is not a raw pointer \
                             ({ptr_ty:?})"
                        ));
                    }
                };
                let (stride, _size, _align) = iter_elem_layout(cx, pointee)?;
                let _ = call_extern_signature(cx, func, args, destination, pair_ok)?;
                raw_ptr_offset_blocks
                    .insert(bb_raw.as_usize(), RawPtrOffsetInline::Integer { stride });
                continue;
            }
            // RUNG 9 (non-escaping closure): a call whose callee is a CLOSURE BODY or
            // a closure-carrying COMBINATOR is wired straight to its in-module member
            // `FuncId` (or an extern stub when not a member) via the ordinary
            // `call_extern_signature` path — BYPASSING every inline-recognizer below,
            // which `item_name`/`fn_sig` the callee and ICE on a closure def-path (a
            // closure has no `item_name`, and its signature needs
            // `args.as_closure().sig()`). `call_extern_signature` synthesizes the
            // signature from the CALL's arg/dest ABI (not `fn_sig`), so it is
            // closure-safe. ADDITIVE: this fires only for a closure-body / closure-
            // combinator callee — a shape absent from every closure-free module.
            if closure_chain_callee(cx, func).is_some() {
                eh_edges.record(eh, bb_raw.as_usize(), unwind);
                let (callee_sym, params, returns) =
                    call_extern_signature(cx, func, args, destination, pair_ok)?;
                if let Some(w) = wiring {
                    if let Some(&fid) = w.member_fids.get(&callee_sym) {
                        callee_ids.insert(bb_raw.as_usize(), fid);
                        continue;
                    }
                }
                let fid = if let Some(id) = extern_by_sym.get(&callee_sym) {
                    *id
                } else {
                    let cty = mb.add_func_type(params, returns);
                    let id = mb.function(callee_sym.clone(), cty).build();
                    n_declared += 1;
                    extern_by_sym.insert(callee_sym, id);
                    id
                };
                callee_ids.insert(bb_raw.as_usize(), fid);
                continue;
            }
            // RUNG 5: an `<Arc<T> as Deref>::deref` call we can inline as pointer
            // arithmetic. Record its offset and emit NO extern callee (the call is
            // replaced by `load + gep` at the emission site below). Validate its
            // arg/dest ABI here (a thin-ptr arg, a `&T` thin-ptr dest) so an
            // unmodelable Arc-deref still fails loud, then discard the synthesized
            // extern name.
            if let Some(off) = arc_deref_inline_offset(cx, func) {
                let _ = call_extern_signature(cx, func, args, destination, pair_ok)?;
                arc_deref_blocks.insert(bb_raw.as_usize(), off);
                continue;
            }
            // RUNG 6: an `Arc::<T>::new` constructor we inline as a heap allocation
            // + counter/data Stores. Record its ArcInner layout and emit NO extern
            // callee (the call is replaced by `heap_alloc + store`s at the emission
            // site). Validate its arg/dest ABI here so an unmodelable Arc::new still
            // fails loud, then discard the synthesized extern name.
            if let Some(layout) = arc_new_inner_layout(cx, func)? {
                let _ = call_extern_signature(cx, func, args, destination, pair_ok)?;
                arc_new_blocks.insert(bb_raw.as_usize(), layout);
                continue;
            }
            // RUNG 7: the `(uN, uN, &str) -> uN` saturating-add diagnostic helper.
            // Inlined to `overflow(Add) + select`, dropping the `&str`. We do NOT
            // call `call_extern_signature` here (it would reject the `&str` arg);
            // the inline replaces the call entirely, so no extern is declared.
            if let Some(lane) = saturating_add_msg_call(cx, func, args) {
                sat_add_blocks.insert(bb_raw.as_usize(), lane);
                continue;
            }
            // RUNG 8b: `IntoIterator::into_iter` over a Vec/&Vec/slice -> a cursor
            // init. No extern (the call becomes a Vec-read + 2-word cursor store).
            if let Some(model) = into_iter_inline(cx, func)? {
                into_iter_blocks.insert(bb_raw.as_usize(), model);
                continue;
            }
            // RUNG 8b: `Iterator::next` over `vec::IntoIter`/`slice::Iter` -> a cursor
            // index-bump + `Some`/`None` write. No extern.
            if let Some(model) = iter_next_inline(cx, func)? {
                iter_next_blocks.insert(bb_raw.as_usize(), model);
                continue;
            }
            // RUNG 8b: `Box::<U>::new_uninit()` -> a `heap_alloc` of the buffer. No
            // extern.
            if let Some(layout) = box_new_uninit_inline(cx, func)? {
                box_new_uninit_blocks.insert(bb_raw.as_usize(), layout);
                continue;
            }
            // RUNG 8b: `box_assume_init_into_vec_unsafe::<T,N>` -> a 3-word `Vec` header
            // materialization. No extern.
            if let Some(layout) = box_into_vec_inline(cx, func)? {
                box_into_vec_blocks.insert(bb_raw.as_usize(), layout);
                continue;
            }
            // ADDITIVE (R4 stage 2): an in-module str/byte call shape -> fat-pair
            // lane reads / cursor writes. No extern (like RUNG 7, we do NOT run
            // `call_extern_signature` — the emission arm fails loud on any
            // unmodelable arg/dest itself, and a literal receiver needs the
            // materialized pair, not a synthesized extern ABI).
            if let Some(op) = str_inline_op(cx, func)? {
                str_inline_blocks.insert(bb_raw.as_usize(), op);
                continue;
            }
            // EMIT mode: a call that resolves to THIS SAME instance is a self-call.
            // Defer it to the body `FuncId` instead of declaring a 0-block extern
            // stub, so `sz(a)`/`whnf`-style recursion stays intra-module (the JIT
            // and validator both resolve it by id). Validate its arg/dest ABI here
            // (via `call_extern_signature`) so an unmodelable self-call still fails
            // loud — we just discard the synthesized extern name.
            if cx.emit_self_recursion && call_is_self_recursive(cx, func) {
                eh_edges.record(eh, bb_raw.as_usize(), unwind);
                let _ = call_extern_signature(cx, func, args, destination, pair_ok)?;
                self_call_blocks.push(bb_raw.as_usize());
                continue;
            }
            // DYN/VIRTUAL method call: `func` is an `FnDef` resolving to
            // `InstanceKind::Virtual(def, vtable_slot)` — a `<dyn Trait as Trait>::m`
            // call. Lower it as an INDIRECT call through the receiver's vtable: at
            // emission, load the concrete method fn-pointer from `vtable[vtable_slot]`
            // and `CallIndirect` it, with the `&dyn` receiver replaced by its DATA
            // pointer. `&dyn` is passed here as a pointer to the 16-byte {data, vtable}
            // pair (fat pointers pass by pointer), and the concrete method's `self` is
            // a pointer to the env — both a leading `Ptr`, so the call's OWN arg/dest
            // ABI (`call_signature_params_returns`) is exactly the `CallIndirect`
            // signature. Without this, a `dyn Fn`/`FnMut` call (hashbrown erases its
            // hasher/eq closures to `&dyn` to cut monomorphization) would emit a direct
            // call to the abstract virtual-method symbol — which has no body and is
            // undefined at whole-program link.
            if let Some(callee) = resolve_call_callee(cx, func) {
                if let ty::InstanceKind::Virtual(vdef, vslot) = callee.def {
                    // A `dyn Fn`/`FnMut`/`FnOnce` method spreads its args tuple (its
                    // vtable target is the concrete closure body, emitted with spread
                    // params); any other `dyn Trait` method takes its args as declared.
                    let is_rc = is_fn_trait_method(cx, vdef);
                    let (params, returns) = if is_rc {
                        virtual_rustcall_signature(cx, args, destination, pair_ok)?
                    } else {
                        call_signature_params_returns(cx, func, args, destination, pair_ok)?
                    };
                    let sig = mb.add_func_type(params.clone(), returns.clone());
                    virtual_blocks.insert(bb_raw.as_usize(), (sig, vslot, is_rc));
                    // UNWIND lane: a virtual call's cleanup edge is carried
                    // through the per-signature direct THUNK (Invoke is
                    // direct-only by format; the thunk keeps the edge sound).
                    if eh
                        && matches!(
                            unwind,
                            rustc_middle::mir::UnwindAction::Cleanup(_)
                                | rustc_middle::mir::UnwindAction::Terminate(_)
                        )
                    {
                        eh_edges.record(eh, bb_raw.as_usize(), unwind);
                        let tfid = get_or_make_indirect_thunk(
                            mb,
                            &mut thunk_by_sig,
                            &mut n_declared,
                            &fn_name,
                            sig,
                            &params,
                            &returns,
                        )?;
                        indirect_thunk_blocks.insert(bb_raw.as_usize(), tfid);
                    }
                    continue;
                }
            }
            // R6: a FN-POINTER INDIRECT call (`(*fnptr)(args)` — the callee is a
            // `fn(..)` VALUE, not a resolvable `FnDef`). Register the call's `FuncTy`
            // (synthesized from its arg/dest ABI, callee-independent) and record it;
            // the emission site lowers the fn-pointer operand and emits `CallIndirect`.
            if is_fn_ptr_indirect_call(cx, func) {
                let (params, returns) =
                    call_signature_params_returns(cx, func, args, destination, pair_ok)?;
                let sig = mb.add_func_type(params.clone(), returns.clone());
                indirect_sig_blocks.insert(bb_raw.as_usize(), sig);
                // UNWIND lane: same thunk carrier for a fn-pointer call's
                // cleanup edge (see the virtual branch above).
                if eh
                    && matches!(
                        unwind,
                        rustc_middle::mir::UnwindAction::Cleanup(_)
                            | rustc_middle::mir::UnwindAction::Terminate(_)
                    )
                {
                    eh_edges.record(eh, bb_raw.as_usize(), unwind);
                    let tfid = get_or_make_indirect_thunk(
                        mb,
                        &mut thunk_by_sig,
                        &mut n_declared,
                        &fn_name,
                        sig,
                        &params,
                        &returns,
                    )?;
                    indirect_thunk_blocks.insert(bb_raw.as_usize(), tfid);
                }
                continue;
            }
            // UNWIND lane: every branch from here on emits a DIRECT call (including
            // the libm-extern branch below), so a cleanup/terminate unwind action on
            // it becomes a faithful Invoke.
            eh_edges.record(eh, bb_raw.as_usize(), unwind);
            // FLOATS (libm): a BODILESS libm-class float intrinsic (`powf64`,
            // `expf32`, `fmaf64`, ...) becomes a REAL extern call to the C libm
            // symbol (`pow`, `expf`, `fma`, ...) — the boundary native rustc
            // lowers these to, resolved by libSystem at link exactly like `fmod`
            // for `FRem` today. Declared under the C name (never the mangled
            // intrinsic symbol, which nothing defines). An UNMAPPED bodiless
            // float-math intrinsic fails loud right here (fail-closed) instead
            // of dangling at whole-program link.
            if let Some(callee) = resolve_call_callee(cx, func) {
                if let Some(idef) = cx.tcx.intrinsic(callee.def_id()) {
                    if let Some(libm_sym) = libm_intrinsic_extern_symbol(
                        idef.name.as_str(),
                        idef.must_be_overridden,
                    )? {
                        let (params, returns) = call_signature_params_returns(
                            cx,
                            func,
                            args,
                            destination,
                            pair_ok,
                        )?;
                        // The libm boundary is all-float scalars by construction;
                        // anything else is ABI drift — fail loud.
                        if !params
                            .iter()
                            .chain(returns.iter())
                            .all(|t| matches!(t, TIRTy::F32 | TIRTy::F64))
                        {
                            return Err(format!(
                                "libm intrinsic {} lowered to a non-float signature \
                                 {params:?} -> {returns:?}",
                                idef.name
                            ));
                        }
                        let fid = if let Some(id) = extern_by_sym.get(libm_sym) {
                            *id
                        } else {
                            let cty = mb.add_func_type(params, returns);
                            let id = mb.function(libm_sym, cty).build();
                            n_declared += 1;
                            extern_by_sym.insert(libm_sym.to_string(), id);
                            id
                        };
                        callee_ids.insert(bb_raw.as_usize(), fid);
                        continue;
                    }
                }
            }
            let (callee_sym, params, returns) =
                call_extern_signature(cx, func, args, destination, pair_ok)?;
            // EMIT-CLOSURE mode: a `Call` whose callee is ANOTHER closure member is an
            // INTRA-MODULE edge — wire it to that member's reserved body `FuncId`
            // instead of declaring a 0-block extern stub. We validated its arg/dest ABI
            // (via `call_extern_signature` above, same as any other call), then resolve
            // the in-module id by the callee's symbol. (Self-recursion already took the
            // branch above; this covers def_eq->whnf, def_eq->structural_eq,
            // whnf->instantiate, instantiate->subst, subst->lift, whnf->env_get, ...)
            if let Some(w) = wiring {
                if let Some(&fid) = w.member_fids.get(&callee_sym) {
                    callee_ids.insert(bb_raw.as_usize(), fid);
                    continue;
                }
            }
            let fid = if let Some(id) = extern_by_sym.get(&callee_sym) {
                *id
            } else {
                let cty = mb.add_func_type(params, returns);
                // A 0-block function declaration is an extern import.
                let id = mb.function(callee_sym.clone(), cty).build();
                n_declared += 1;
                extern_by_sym.insert(callee_sym, id);
                id
            };
            callee_ids.insert(bb_raw.as_usize(), fid);
        }
    }

    // RUNG 4 Drop pre-pass: declare the drop-glue extern (`core::ptr::drop_in_place
    // ::<T>`, signature `(ptr) -> ()`) for each `Drop { place }` whose place TYPE
    // needs drop, keyed by block index (a Drop is its block's terminator). A place
    // that does not need drop (a `Copy`/scalar/no-drop type — `needs_drop == false`,
    // i.e. `resolve_drop_in_place` would give the noop `DropGlue(_, None)`) emits NO
    // call — just a branch to the target — so it gets no entry here. Every OTHER place
    // gets the REAL `drop_in_place::<T>` glue call, so its destructor runs and its
    // heap memory is freed at scope exit: this is what makes trust-cg-compiled heap
    // programs LEAK-FREE (a dropped `Vec<T>` now calls `drop_in_place::<Vec<T>>`,
    // which frees the buffer via `__rust_dealloc`). Dealloc-only std containers
    // (`Vec`/`Box`/`Arc`/...) are no longer special-cased to a no-op — their glue is
    // exactly the free/refcount code we WANT to run. Callee resolves to the same
    // v0-mangled symbol emit-each emits the `DropGlue` module under, so it co-resolves
    // at whole-program link. We fail loud on a Drop whose place is not addressable in
    // the minimal model (a non-memory, non-deref place), keeping the bucket honest.
    let mut drop_callee_ids: HashMap<usize, trust_ir::FuncId> = HashMap::new();
    // VIRTUAL (dyn) drop: blocks whose `Drop` place is a `dyn Trait` pointee —
    // `drop_glue::<dyn Any>`'s own `Drop((*_1))`. Resolving its glue by symbol
    // would name THIS shim itself (infinite recursion); the faithful lowering
    // dispatches through the fat pointer's vtable SLOT 0 (`drop_in_place` of
    // the concrete type). Value = the `(ptr) -> ()` CallIndirect signature.
    let mut dyn_drop_blocks: HashMap<usize, trust_ir::FuncTyId> = HashMap::new();
    for (bb_raw, data) in body.basic_blocks.iter_enumerated() {
        let term = data.terminator.as_ref().unwrap();
        if let TerminatorKind::Drop { place, unwind, .. } = &term.kind {
            let place_ty = cx.place_concrete_ty(place);
            if !place_ty.needs_drop(cx.tcx, ty::TypingEnv::fully_monomorphized()) {
                continue;
            }
            if matches!(place_ty.kind(), ty::Dynamic(..)) {
                // Virtual dispatch: no glue symbol (see above). UNWIND lane: the
                // vtable-slot-0 dispatch is indirect, so its cleanup edge rides
                // the per-signature THUNK like any other indirect call.
                let sig = mb.add_func_type(vec![TIRTy::Ptr], Vec::new());
                dyn_drop_blocks.insert(bb_raw.as_usize(), sig);
                if eh
                    && matches!(
                        unwind,
                        rustc_middle::mir::UnwindAction::Cleanup(_)
                            | rustc_middle::mir::UnwindAction::Terminate(_)
                    )
                {
                    eh_edges.record(eh, bb_raw.as_usize(), unwind);
                    let tfid = get_or_make_indirect_thunk(
                        mb,
                        &mut thunk_by_sig,
                        &mut n_declared,
                        &fn_name,
                        sig,
                        &[TIRTy::Ptr],
                        &[],
                    )?;
                    indirect_thunk_blocks.insert(bb_raw.as_usize(), tfid);
                }
                continue;
            }
            // UNWIND lane: the drop-glue call is DIRECT, so a cleanup/terminate
            // unwind action on this `Drop` becomes a faithful Invoke.
            eh_edges.record(eh, bb_raw.as_usize(), unwind);
            // LEAK-FREE: no `drop_glue_is_logic_free` no-op skip — every `needs_drop`
            // place emits its REAL drop glue so dealloc/refcount code runs (a dropped
            // `Vec`/`Box`/`Arc` frees its buffer via `__rust_dealloc`). The verification
            // still passes (the returned tree is unchanged) and heap programs no longer
            // leak. `resolve_drop_glue` is the current API (== the retired
            // `resolve_drop_in_place`); it returns the noop only for `needs_drop == false`
            // types, which the guard above already `continue`s past.
            let drop_instance = Instance::resolve_drop_glue(cx.tcx, place_ty);
            let drop_sym = cx.tcx.symbol_name(drop_instance).name.to_string();
            let fid = if let Some(id) = extern_by_sym.get(&drop_sym) {
                *id
            } else {
                // Drop glue ABI: `fn(*mut T)` — one Ptr param, void return.
                let cty = mb.add_func_type(vec![TIRTy::Ptr], Vec::new());
                let id = mb.function(drop_sym.clone(), cty).build();
                n_declared += 1;
                extern_by_sym.insert(drop_sym, id);
                id
            };
            drop_callee_ids.insert(bb_raw.as_usize(), fid);
        }
    }

    // UNWIND lane Assert pre-pass: declare the `core::panicking` entry point
    // each supported `Assert` failure path calls (rustc parity — overflow /
    // bounds / div-by-zero panics UNWIND and are catchable, with cleanup run),
    // and record its cleanup edge so reachability/liveness include it. Under
    // panic=abort this loop is skipped entirely and the Assert failure path
    // keeps its historical shared-trap lowering BYTE-IDENTICALLY.
    let mut assert_panic_blocks: HashMap<usize, AssertPanicCall> = HashMap::new();
    if eh {
        for (bb_raw, data) in body.basic_blocks.iter_enumerated() {
            let term = data.terminator.as_ref().unwrap();
            if let TerminatorKind::Assert { msg, unwind, .. } = &term.kind {
                let Some((lang_item, params, shape)) = assert_panic_langcall(msg) else {
                    continue;
                };
                let did = cx.tcx.require_lang_item(lang_item, term.source_info.span);
                let inst = Instance::mono(cx.tcx, did);
                let sym = cx.tcx.symbol_name(inst).name.to_string();
                let fid = if let Some(id) = extern_by_sym.get(&sym) {
                    *id
                } else {
                    let cty = mb.add_func_type(params, Vec::new());
                    let id = mb.function(sym.clone(), cty).build();
                    n_declared += 1;
                    extern_by_sym.insert(sym, id);
                    id
                };
                eh_edges.record(eh, bb_raw.as_usize(), unwind);
                assert_panic_blocks
                    .insert(bb_raw.as_usize(), AssertPanicCall { fid, args: shape });
            }
        }
    }

    // UNWIND lane TERMINATE pre-pass: declare the `core::panicking` entry point
    // each `UnwindAction::Terminate(reason)` edge / `UnwindTerminate(reason)`
    // terminator calls (rustc parity — `codegen_terminate_terminator` /
    // `terminate_block` call `reason.lang_item()`):
    //   * `Abi`       -> `panic_cannot_unwind` ("panic in a function that
    //                    cannot unwind"),
    //   * `InCleanup` -> `panic_in_cleanup` ("panic in a destructor during
    //                    cleanup" — the double-panic message).
    // Both are `#[rustc_nounwind] fn() -> !` with NO arguments (not even a
    // `#[track_caller]` Location — rustc calls them "directly by the codegen
    // backend"), so the emission is a plain call + `unreachable`. Under
    // panic=abort this loop is skipped and the terminate paths keep their
    // historical trap lowering BYTE-IDENTICALLY.
    let mut terminate_fids: [Option<trust_ir::FuncId>; 2] = [None, None];
    if eh {
        for data in body.basic_blocks.iter() {
            let Some(term) = data.terminator.as_ref() else {
                continue;
            };
            let reason = match &term.kind {
                TerminatorKind::UnwindTerminate(r) => Some(*r),
                _ => term.unwind().and_then(|u| match u {
                    rustc_middle::mir::UnwindAction::Terminate(r) => Some(*r),
                    _ => None,
                }),
            };
            let Some(reason) = reason else { continue };
            let idx = terminate_reason_idx(reason);
            if terminate_fids[idx].is_some() {
                continue;
            }
            let did = cx
                .tcx
                .require_lang_item(reason.lang_item(), term.source_info.span);
            let inst = Instance::mono(cx.tcx, did);
            let sym = cx.tcx.symbol_name(inst).name.to_string();
            let fid = if let Some(id) = extern_by_sym.get(&sym) {
                *id
            } else {
                // `fn() -> !`: no params, no returns (diverging).
                let cty = mb.add_func_type(Vec::new(), Vec::new());
                let id = mb.function(sym.clone(), cty).build();
                n_declared += 1;
                extern_by_sym.insert(sym, id);
                id
            };
            terminate_fids[idx] = Some(fid);
        }
    }

    // RUNG 2 cross-block phi liveness + the emitted-block set. Run AFTER the
    // Call/Drop pre-passes so the EH lane's faithful unwind edges (recorded in
    // `eh_edges` above) extend both computations consistently; under panic=abort
    // `eh_edges` is empty and both are identical to the historical results.
    let live_in = compute_scalar_live_in(cx, body, &eh_edges);
    let normal_reachable = compute_normal_reachable(body, &eh_edges);

    // UNWIND lane: does this body synthesize any landing pad? If so, declare the
    // `rust_eh_personality` MARKER — an external, body-less function declaration
    // trust-cg's adapter detects to select the Rust personality for this module's
    // EH tables (the symbol itself is the REAL `eh_personality` lang-item fn,
    // emitted through this same pipeline and resolved at link). Also the shared
    // exception-pointer slot flag: each pad stores the unwinder-provided
    // exception object into a per-function `Alloca(Ptr)` so `UnwindResume`
    // (`Resume`) can re-raise it — LLVM's classic personality-slot lowering.
    let has_pads = eh && eh_edges.any_pads(&normal_reachable);
    if has_pads && fn_name != "rust_eh_personality" {
        if let std::collections::hash_map::Entry::Vacant(e) =
            extern_by_sym.entry("rust_eh_personality".to_string())
        {
            // The Itanium personality signature:
            //   (version i32, actions i32, exception_class u64,
            //    exception_object ptr, context ptr) -> _Unwind_Reason_Code i32.
            let cty = mb.add_func_type(
                vec![TIRTy::I32, TIRTy::I32, TIRTy::U64, TIRTy::Ptr, TIRTy::Ptr],
                vec![TIRTy::I32],
            );
            let id = mb.function("rust_eh_personality".to_string(), cty).build();
            n_declared += 1;
            e.insert(id);
        }
    }

    // DYN/VTABLE pre-pass: for every `dst = src as &dyn Trait / &mut dyn Trait`
    // (`PointerCoercion(Unsize)` into a trait-object fat pointer) this body
    // performs, synthesize the `<self_ty as Trait>` vtable as a read-only module
    // global (drop/size/align header + the concrete method fn-pointers, from
    // `tcx.vtable_entries`), keyed by `(self_ty, dyn pointee)`. Runs HERE — before
    // `fb` takes the exclusive `mb` borrow — because a global can only be added
    // through the `ModuleBuilder`. `lower_unsize_assign`'s dyn branch then reads
    // the recorded `GlobalId` and stores its address into the fat pointer's
    // metadata (vtable) lane. A body with no to-`dyn` coercion adds nothing.
    let dyn_coercions = prescan_dyn_coercions(cx, body);
    materialize_dyn_vtables(cx, mb, dyn_coercions)?;

    // The function under lowering is created AFTER the extern callees, so it takes
    // the next free `FuncId`. The validator matches calls to callees by `FuncId`
    // (order-independent), so the lowered fn need not be id 0.
    let returns = match &ret_abi {
        RetAbi::Scalar(t) => vec![t.clone()],
        // RUNG 10: a by-value small-pair return is ONE 2-tuple result value.
        RetAbi::Pair(pr) => vec![pr.tuple_ty()],
        // An sret function returns void (the result is written through the hidden
        // pointer); a unit function returns void.
        RetAbi::Sret | RetAbi::Unit => Vec::new(),
    };
    let sig = mb.add_func_type(param_tys.clone(), returns);
    // The body's `FuncId` is the next sequential id in the shared mb: the absolute
    // base (`0` single-fn, `wiring.base_fid` closure) plus the functions THIS member
    // already declared (`n_declared`). Capture it BEFORE `fb` borrows `mb`, so the
    // emit-mode self-call blocks can be wired to the in-module body below. NOTE: a
    // closure member's body id MUST equal the id its callers reserved in
    // `member_fids` — see `lower_closure_for_emit`, which uses this same arithmetic.
    let body_fid = trust_ir::FuncId::new(base_fid + n_declared);
    for &bb in &self_call_blocks {
        callee_ids.insert(bb, body_fid);
    }
    // Span threading: PRE-PASS-intern every source file this body's spans touch
    // (the fn-level `body.span` + each statement's/terminator's `SourceInfo`)
    // into the module's debug-info file table, BEFORE the FunctionBuilder takes
    // the exclusive module borrow. Total: dummy spans skip; macro-expansion
    // spans resolve to their outermost callsite's file.
    let span_map = SpanMap::build(cx.tcx, mb, crate::span_map::mir_body_spans(body));
    // PANIC-CLASS OBLIGATIONS: record one `Pending` `ProofObligation` per
    // Assert this body will lower (see `record_assert_obligations`). Runs in
    // the same pre-`fb` window as the span pre-pass — it needs `mb`, and the
    // interned file table the span pre-pass just built. `peek_next_func_id` is
    // the AUTHORITY on the id `mb.function(..)` is about to assign, and
    // `obligation_fid` below reads it DIRECTLY — so obligation scoping is
    // correct regardless of what the frontend's own `base_fid + n_declared`
    // arithmetic says. (The validator does not check
    // `ProofObligation::function`, so reading the authority rather than
    // recomputing it is what makes the scoping safe.)
    //
    // The assert below therefore protects something else: it is a free
    // consistency check on the PRE-EXISTING closure-emit `base_fid +
    // n_declared` arithmetic, which self-recursion wiring depends on. Note it
    // is a `debug_assert_eq!`, so it is compiled OUT of the `--release` census
    // and emit binaries — it is a development tripwire, not a shipped gate.
    debug_assert_eq!(
        mb.peek_next_func_id(),
        body_fid,
        "body_fid drifted from the ModuleBuilder's next function id"
    );
    let obligation_fid = mb.peek_next_func_id();
    let recorded_obligations =
        record_assert_obligations(cx, mb, body, obligation_fid, &normal_reachable, &span_map);
    // PANIC-CLASS OBLIGATION SITES: filled by the `Assert` arm of
    // `lower_terminator`, drained after `fb.build()` to back-fill each
    // obligation's `ObligationSite`.
    let mut assert_sites: Vec<(usize, trust_ir::BlockId, u32)> = Vec::new();
    let mut fb = mb.function(fn_name.clone(), sig);
    // RUNG 11 ABI pinning: attach the positional `byval`/`sret` attrs built in
    // lockstep with `param_tys` above. Only when at least one is non-default (i.e.
    // under the opt-in flag, on a fn with a by-ref aggregate param or an sret
    // return) — otherwise leave `FuncAttrs::default()` so the emitted text carries
    // no attr comment and stays byte-identical to pre-rung output.
    if param_attrs.iter().any(|pa| !pa.is_empty()) {
        fb.set_attrs(trust_ir::FuncAttrs {
            params: param_attrs.clone(),
            ..Default::default()
        });
    }

    // One trust-ir block per MIR basic block, created up front so terminators can
    // reference forward targets.
    //
    // RUNG 4: only MIR blocks REACHABLE over normal (non-unwind) edges get a
    // trust-ir block. A cleanup block reachable solely through an unwind edge (which
    // we model as a trap, not a real edge) is NOT created — otherwise it would be an
    // orphan with no predecessor, which the validator rejects (`UnreachableBlock`).
    // `blocks[i]` is `Some` iff MIR block `i` is normal-reachable; every emitted edge
    // targets a normal-reachable block, so all `.unwrap()`s below are safe.
    let n_bb = body.basic_blocks.len();
    let mut blocks: Vec<Option<trust_ir::BlockId>> = Vec::with_capacity(n_bb);
    for i in 0..n_bb {
        if normal_reachable.contains(&i) {
            blocks.push(Some(fb.create_block()));
        } else {
            blocks.push(None);
        }
    }
    let entry = blocks[0].expect("entry block is always normal-reachable");
    fb.set_entry(entry);

    // Bind parameters as entry-block params, in the SAME order as `param_tys`:
    //   [sret Ptr]? ++ per MIR arg (scalar value, or a by-ref aggregate Ptr).
    // The sret pointer becomes `_0`'s slot pointer; a by-ref aggregate param's
    // pointer becomes that param local's slot pointer (recorded below into the
    // model, replacing what would otherwise be an entry alloca). The entry params
    // must match the signature EXACTLY (the validator checks this), so we add them
    // here in lockstep with the `param_tys` construction above.
    let mut param_vals: HashMap<Local, trust_ir::ValueId> = HashMap::new();
    // Param locals that are by-ref aggregates: their slot pointer is the entry
    // param value (filled into the model after the param loop, so the entry alloca
    // loop below skips them).
    let mut agg_param_ptr: HashMap<Local, trust_ir::ValueId> = HashMap::new();
    // SCALAR-SPILL params: the incoming by-value scalar + its leaf type. After the
    // entry alloca loop allocates each one's slot, we Store the value into the slot
    // (so the address-taken uses read it back through the slot pointer).
    let mut spill_param_val: HashMap<Local, (trust_ir::ValueId, TIRTy)> = HashMap::new();
    // RUNG 11: by-value pair params: the incoming SSA 2-tuple + its model. After the
    // entry alloca loop allocates the local's (ordinary) slot, we whole-aggregate
    // Store the tuple into it so the body's field reads observe the argument.
    let mut pair_param_val: HashMap<Local, (trust_ir::ValueId, PairRet)> = HashMap::new();
    fb.switch_to_block(entry);
    // Fn-level default span for the entry preamble (slot allocas, scalar-param
    // spills): those instructions have no single originating MIR statement, so
    // they carry the function's own source position.
    span_map.apply(cx.tcx, &mut fb, body.span);
    let sret_ptr = if has_sret {
        Some(fb.add_block_param(entry, TIRTy::Ptr))
    } else {
        None
    };
    // THREADS / rust-call: the spread ARGS-TUPLE's per-field entry params, to be
    // stored into the tuple local's slot once its alloca exists.
    let mut spread_field_vals: Vec<(u64, trust_ir::ValueId)> = Vec::new();
    for i in 1..=body.arg_count {
        let l = Local::from_usize(i);
        if spread_local == Some(l) {
            for (off, abi) in &spread_param_fields {
                let t = match abi {
                    SpreadParamAbi::Scalar(t) => t.clone(),
                    SpreadParamAbi::ByRef { .. } => TIRTy::Ptr,
                };
                let v = fb.add_block_param(entry, t);
                spread_field_vals.push((*off, v));
            }
            continue;
        }
        match cx.model.get(&l) {
            Some(LocalModel::Ssa(t)) => {
                let v = fb.add_block_param(entry, t.clone());
                param_vals.insert(l, v);
            }
            Some(LocalModel::Memory(_)) if spill_param.contains(&l) => {
                // Address-taken scalar param: bind the by-value scalar (its leaf
                // type), to be spilled into the slot once the alloca exists. (Incl. a
                // transparent int newtype like `Tag(u8)` passed by value as `u8`.)
                let leaf = param_scalar_leaf_tir_ty(cx, cx.local_concrete_ty(l))
                    .expect("spill_param is a scalar leaf by construction");
                let v = fb.add_block_param(entry, leaf.clone());
                spill_param_val.insert(l, (v, leaf));
            }
            Some(LocalModel::Memory(_)) if pair_param.contains(&l) => {
                // RUNG 11: bind the by-value 2-tuple param. The local KEEPS its
                // ordinary entry alloca (it is NOT in `agg_param_ptr`), and the
                // incoming tuple is spilled into that slot after the alloca loop.
                let pr = pair_param_model
                    .get(&l)
                    .expect("pair_param has a recorded model")
                    .clone();
                let v = fb.add_block_param(entry, pr.tuple_ty());
                pair_param_val.insert(l, (v, pr));
            }
            Some(LocalModel::Memory(_)) if agg_param.contains(&l) => {
                let p = fb.add_block_param(entry, TIRTy::Ptr);
                agg_param_ptr.insert(l, p);
            }
            _ => {}
        }
    }
    // `#[track_caller]` hidden Location param: LAST entry param, in lockstep
    // with the `param_tys` append above. Defined in the entry block, so it
    // dominates every block (usable anywhere, like the sret pointer / entry
    // allocas); recorded on `cx` for `get_caller_location` to forward.
    if needs_cl_param {
        cx.caller_location = Some(fb.add_block_param(entry, TIRTy::Ptr));
    }

    // RUNG 2 cross-block phi: per NON-ENTRY block, add a block parameter for each
    // scalar local live at its entry (stable local order). Record the binding so
    // the block's env is seeded with these params and so predecessors thread the
    // right values. The entry block's live-in is satisfied by `param_vals`.
    let mut block_param_locals: Vec<Vec<Local>> = vec![Vec::new(); n_bb];
    let mut block_param_vals: Vec<HashMap<Local, trust_ir::ValueId>> =
        vec![HashMap::new(); n_bb];
    for bb_idx in 0..n_bb {
        if bb_idx == 0 {
            continue;
        }
        // Skip blocks that are not normal-reachable (no trust-ir block exists).
        let Some(blk) = blocks[bb_idx] else { continue };
        let mut locals: Vec<Local> = live_in[bb_idx].iter().copied().collect();
        locals.sort_by_key(|l| l.index());
        for &l in &locals {
            let t = match cx.model.get(&l) {
                Some(LocalModel::Ssa(t)) => t.clone(),
                _ => continue,
            };
            let v = fb.add_block_param(blk, t);
            block_param_vals[bb_idx].insert(l, v);
        }
        block_param_locals[bb_idx] = locals;
    }

    // RUNG 1: allocate a stack slot for every memory-backed local, in stable
    // local order, in the entry block. The slot pointer is the local's stable
    // identity (same in every block); it never participates in the per-block SSA
    // env. Record the real `ptr` into the model.
    //
    // RUNG 3 EXCEPTIONS — these two memory-backed locals do NOT get an entry
    // alloca; their slot pointer is an ABI value:
    //   * the return local `_0` under sret: its slot IS the hidden sret pointer
    //     (the caller's destination), so the body's Stores into `_0` write the
    //     result in place.
    //   * a by-ref aggregate parameter: its slot IS the incoming `Ptr` param (a
    //     pointer to the caller's copy of the argument), so the body reads the
    //     parameter through the ordinary memory-place Load path.
    fb.switch_to_block(entry);
    let ret_local = Local::from_u32(0);
    if let Some(sp) = sret_ptr {
        if let Some(LocalModel::Memory(s)) = cx.model.get_mut(&ret_local) {
            s.ptr = sp;
        }
    }
    for (&l, &p) in &agg_param_ptr {
        if let Some(LocalModel::Memory(s)) = cx.model.get_mut(&l) {
            s.ptr = p;
        }
    }
    let mut mem_locals: Vec<Local> = body
        .local_decls
        .indices()
        .filter(|l| cx.is_memory_local(*l))
        .collect();
    mem_locals.sort_by_key(|l| l.index());
    for local in mem_locals {
        // Skip the ABI-bound slots (sret `_0`, by-ref aggregate params).
        if (sret_ptr.is_some() && local == ret_local) || agg_param_ptr.contains_key(&local) {
            continue;
        }
        let cty = cx.local_concrete_ty(local);
        // An UNSIZED local's slot is its 16-byte fat CARRIER (see
        // `unsized_local_carrier`).
        let (size, align) = match unsized_local_carrier(cx, cty) {
            Some(sa) => sa,
            None => memory_layout_size_align(cx, cty)?,
        };
        let slot_ty = slot_lane_ty(size, align)?;
        let ptr = fb.alloca_aligned(slot_ty, align);
        // RUNG 2a: the slot is EXACTLY `size` bytes — `slot_lane_ty` splits that
        // same `size` into `size / lane_width` equal lanes. A multi-lane slot is
        // a `Ty::Tuple`, which has no declared trust-ir layout, so the builder
        // cannot size it on its own; declare it here, where the rustc layout is
        // in hand. This is what lets `gep_byte_offset` discharge `inbounds` for
        // every field/element offset taken off this local.
        fb.note_alloc_extent(ptr, size);
        if let Some(LocalModel::Memory(s)) = cx.model.get_mut(&local) {
            s.ptr = ptr;
        }
    }

    // UNWIND lane: the per-function EXCEPTION-POINTER slot. Every landing pad
    // stores the unwinder-provided exception object here; `UnwindResume` loads
    // it back for `Resume`. One 8-byte entry alloca, only for a body that
    // synthesizes pads — every other function's entry preamble is unchanged.
    let exn_slot: Option<trust_ir::ValueId> =
        if has_pads { Some(fb.alloca(TIRTy::Ptr)) } else { None };

    // RUNG 10: zero-fill the pair-return slot's full span once at entry. The
    // whole-aggregate Load at `Return` reads `_0`'s full byte image — including
    // inter-lane PADDING (e.g. bytes 12..16 of a `(u64, u32)`) — while the
    // body's field Stores initialize only the lanes, so an unwritten padding
    // byte would (rightly) trip the interpreter's uninitialized-read check.
    // Padding content is unobservable; zeros are the canonical choice and are
    // byte-identical to what the caller-side whole-aggregate spill Store writes
    // (the interpreter encodes aggregates over a zeroed image). Emitted ONLY
    // for a pair-returning fn — every other fn's entry preamble is unchanged.
    if matches!(ret_abi, RetAbi::Pair(_)) {
        let slot = cx
            .slot_ptr(ret_local)
            .expect("pair-return _0 slot allocated above");
        let cty = cx.local_concrete_ty(ret_local);
        let (size, align) = memory_layout_size_align(cx, cty)?;
        let lane = slot_lane_ty(align, align)?;
        for off in (0..size).step_by(align as usize) {
            let zero = fb.iconst(lane.clone(), 0);
            let addr = if off == 0 {
                slot
            } else {
                gep_byte_offset(&mut fb, slot, off)
            };
            fb.store(lane.clone(), addr, zero);
        }
    }

    // SCALAR-SPILL params: now that each address-taken scalar param's slot exists,
    // Store the incoming by-value scalar into it, so the body's address-taken reads
    // (Load through the slot pointer) observe the parameter. Done in the entry block,
    // after the allocas, before any body statement runs. Emitted in STABLE LOCAL
    // ORDER (not `HashMap` iteration order) so the emitted IR is deterministic /
    // reproducible run-to-run.
    let mut spill_locals: Vec<Local> = spill_param_val.keys().copied().collect();
    spill_locals.sort_by_key(|l| l.index());
    for l in spill_locals {
        let (v, leaf) = &spill_param_val[&l];
        let slot = cx
            .slot_ptr(l)
            .expect("spill_param has a memory slot allocated above");
        fb.store(leaf.clone(), slot, *v);
    }

    // RUNG 11 by-value pair PARAMS: spill each incoming 2-tuple into its entry slot
    // with ONE whole-aggregate Store. The aggregate encode writes over a zeroed
    // image, so inter-lane padding is initialized too — the body's layout-faithful
    // field reads, and any later whole-aggregate Load of this slot, observe a
    // defined image (the exact dual of the RUNG 10 `_0` entry zero-fill). Lanes are
    // offset-ordered and `pair_ret_model` pins tuple-offset == field-offset, so this
    // Store is byte-congruent with the field reads. Emitted in STABLE LOCAL ORDER.
    let mut pair_spill_locals: Vec<Local> = pair_param_val.keys().copied().collect();
    pair_spill_locals.sort_by_key(|l| l.index());
    for l in pair_spill_locals {
        let (v, pr) = &pair_param_val[&l];
        let slot = cx
            .slot_ptr(l)
            .expect("pair_param has a memory slot allocated above");
        fb.store(pr.tuple_ty(), slot, *v);
    }

    // THREADS / rust-call: RECONSTITUTE the spread ARGS TUPLE — store each
    // incoming per-field param into the tuple local's slot at its layout
    // offset (scalar fields by a typed Store; by-ref aggregate fields by a
    // lane copy from the incoming pointer). The body then reads the tuple
    // local exactly as before.
    if let Some(sl) = spread_local {
        if !spread_field_vals.is_empty() {
            let slot = cx
                .slot_ptr(sl)
                .expect("spread tuple local has a memory slot allocated above");
            for ((off, v), (_, abi)) in
                spread_field_vals.iter().zip(spread_param_fields.iter())
            {
                let addr = if *off == 0 {
                    slot
                } else {
                    gep_byte_offset(&mut fb, slot, *off)
                };
                match abi {
                    SpreadParamAbi::Scalar(t) => fb.store(t.clone(), addr, *v),
                    SpreadParamAbi::ByRef { size, align } => {
                        copy_aggregate_bytes(&mut fb, *v, addr, *size, *align)?;
                    }
                }
            }
        }
    }

    // ADDITIVE (R3 stage 1): materialize every DISTINCT `&'static str` /
    // `&'static [u8]` LITERAL this body consumes (call args / fat-dst Use
    // assigns) ONCE, here in the entry block: an immortal heap byte image + a
    // (ptr,len) fat-pair slot. See the `str_const_bytes` section header for the
    // design and the documented address-identity modeled boundary. A body with
    // no such literals emits NOTHING here (the no-drift guarantee).
    let str_literals = prescan_str_consts(cx, body);
    materialize_str_consts(cx, &mut fb, str_literals)?;

    // A single shared TRAP block for the Assert failure (panic) path: created
    // lazily on first use, threaded through the block loop.
    let mut trap_block: Option<trust_ir::BlockId> = None;
    // UNWIND lane: the shared per-reason TERMINATE pads (a cleanup landing pad
    // that calls the reason's `core::panicking` terminate entry point — the
    // loud double-panic abort), created lazily on first
    // `UnwindAction::Terminate(reason)` invoke and filled after the block loop.
    // Indexed by `terminate_reason_idx` (Abi / InCleanup), like rustc's
    // per-reason `terminate_blocks` cache.
    let mut terminate_pads: [Option<trust_ir::BlockId>; 2] = [None, None];

    // Per-block scalar value environment. Each block's env is seeded with the
    // entry parameters (for the entry block) or its own live-in block parameters
    // (for a non-entry block); statements then add intra-block defs. Memory-backed
    // locals are orthogonal (a stable slot pointer), so they are not in env.
    for (bb_raw, data) in body.basic_blocks.iter_enumerated() {
        let bb_idx = bb_raw.as_usize();
        // Skip non-normal-reachable (cleanup-only) blocks: no trust-ir block exists
        // for them, and the lowering never branches to them.
        let Some(blk) = blocks[bb_idx] else { continue };
        fb.switch_to_block(blk);

        let mut env: HashMap<Local, trust_ir::ValueId> = if bb_idx == 0 {
            param_vals.clone()
        } else {
            block_param_vals[bb_idx].clone()
        };

        for stmt in &data.statements {
            // Thread the statement's own source position onto everything it
            // emits (an unmappable span clears — synthetic statements do not
            // inherit an unrelated predecessor's position).
            span_map.apply(cx.tcx, &mut fb, stmt.source_info.span);
            match &stmt.kind {
                StatementKind::StorageLive(_)
                | StatementKind::StorageDead(_)
                | StatementKind::Nop
                | StatementKind::FakeRead(_)
                | StatementKind::PlaceMention(_)
                | StatementKind::AscribeUserType(_, _)
                | StatementKind::ConstEvalCounter => {}
                StatementKind::Assign(boxed) => {
                    let (place, rvalue) = &**boxed;
                    lower_assign(cx, &mut fb, &mut env, place, rvalue)?;
                }
                // RUNG 3: write a variant's discriminant tag into a memory-backed
                // enum place, at the faithful layout tag offset/width/encoding.
                StatementKind::SetDiscriminant {
                    place,
                    variant_index,
                } => {
                    lower_set_discriminant(cx, &mut fb, &mut env, place, *variant_index)?;
                }
                // R5: the two non-diverging intrinsic STATEMENTS.
                //   * `Assume(cond)` is a pure optimizer HINT (UB if `cond` is
                //     false). Dropping it is SOUND — the lowered program merely
                //     declines to exploit the fact, so every behavior it exhibits is
                //     a valid behavior of the source. (We never invent a fact.)
                //   * `CopyNonOverlapping { src, dst, count }` is a real memcpy of
                //     `count * size_of::<T>()` bytes — lowered faithfully to a
                //     byte-granular copy (loop or unroll).
                StatementKind::Intrinsic(ndi) => match &**ndi {
                    rustc_middle::mir::NonDivergingIntrinsic::Assume(_) => {}
                    rustc_middle::mir::NonDivergingIntrinsic::CopyNonOverlapping(cno) => {
                        lower_copy_nonoverlapping(cx, &mut fb, &mut env, cno)?;
                    }
                },
                other => {
                    return Err(format!("unsupported statement: {}", stmt_name(other)));
                }
            }
        }

        // Terminator.
        let term = data
            .terminator
            .as_ref()
            .ok_or_else(|| "block has no terminator".to_string())?;
        // Thread the terminator's source position (a Call/SwitchInt/Assert may
        // emit several instructions — all carry the terminator's span).
        span_map.apply(cx.tcx, &mut fb, term.source_info.span);
        let mut tcx_term = TermCtx {
            blocks: &blocks,
            block_param_locals: &block_param_locals,
            ret_abi: ret_abi.clone(),
            callee_id: callee_ids.get(&bb_idx).copied(),
            indirect_sig: indirect_sig_blocks.get(&bb_idx).copied(),
            virtual_dispatch: virtual_blocks.get(&bb_idx).copied(),
            pair_ret_ok: pair_ret_blocks.contains(&bb_idx),
            drop_callee_id: drop_callee_ids.get(&bb_idx).copied(),
            dyn_drop_sig: dyn_drop_blocks.get(&bb_idx).copied(),
            arc_deref_offset: arc_deref_blocks.get(&bb_idx).copied(),
            arc_new_layout: arc_new_blocks.get(&bb_idx).cloned(),
            sat_add_lane: sat_add_blocks.get(&bb_idx).cloned(),
            mem_intrinsic: mem_intrinsic_blocks.get(&bb_idx).copied(),
            raw_ptr_offset: raw_ptr_offset_blocks.get(&bb_idx).copied(),
            into_iter_model: into_iter_blocks.get(&bb_idx).cloned(),
            iter_next_model: iter_next_blocks.get(&bb_idx).cloned(),
            box_new_uninit: box_new_uninit_blocks.get(&bb_idx).cloned(),
            box_into_vec: box_into_vec_blocks.get(&bb_idx).cloned(),
            str_inline: str_inline_blocks.get(&bb_idx).cloned(),
            trap_block: &mut trap_block,
            eh,
            cur_blk: blk,
            exn_slot,
            terminate_pads: &mut terminate_pads,
            terminate_fids,
            catch_expand: eh_edges.catch_expand.get(&bb_idx).copied(),
            assert_panic: assert_panic_blocks.get(&bb_idx).copied(),
            indirect_thunk: indirect_thunk_blocks.get(&bb_idx).copied(),
            caller_location_inline: caller_location_blocks.contains(&bb_idx),
            mir_bb: bb_idx,
            assert_sites: &mut assert_sites,
        };
        lower_terminator(cx, &mut fb, &mut env, &mut tcx_term, &term.kind, term.source_info)?;
    }

    // If the Assert path allocated a trap block, fill it with `unreachable`.
    if let Some(tb) = trap_block {
        fb.switch_to_block(tb);
        // The shared trap block belongs to no single statement — give its
        // `unreachable` the fn-level span.
        span_map.apply(cx.tcx, &mut fb, body.span);
        fb.unreachable();
    }

    // UNWIND lane: fill the shared per-reason terminate pads — a cleanup
    // landing pad whose body CALLS the reason's `core::panicking` terminate
    // entry point (`panic_cannot_unwind` / `panic_in_cleanup`), rustc's
    // `terminate_block` shape: the nounwind entry prints the reason message
    // through the panic machinery ("panic in a destructor during cleanup" /
    // "panic in a function that cannot unwind" + "thread caused non-unwinding
    // panic. aborting.") and aborts — the loud abort `UnwindAction::Terminate`
    // denotes, now with native-parity diagnostics. The entry is `fn() -> !`,
    // so the call is followed by `unreachable`.
    for (idx, pad) in terminate_pads.into_iter().enumerate() {
        let Some(tp) = pad else { continue };
        let fid = terminate_fids[idx].ok_or_else(|| {
            "terminate pad allocated without its declared core::panicking entry \
             point (terminate pre-pass bug)"
                .to_string()
        })?;
        fb.switch_to_block(tp);
        span_map.apply(cx.tcx, &mut fb, body.span);
        let (_exn, _sel) = fb.landingpad(true, vec![]);
        fb.call_void(fid, Vec::new());
        fb.unreachable();
    }

    fb.build();
    // PANIC-CLASS OBLIGATION SITES: back-fill each obligation's IR position now
    // that `fb` has released the module borrow.
    //
    // FAILS LOUD on any mismatch rather than emitting a possibly-misaligned
    // site. The pre-pass and the lowering iterate the MIR blocks independently;
    // if they ever disagree, a site attaches to the wrong instruction and every
    // proof downstream is about the wrong check — a silent failure the
    // validator cannot detect, because a wrong-but-in-range site is still
    // well-formed. So the pairing is by MIR block index, and the counts must
    // agree exactly.
    let mut sites_by_mir_bb: HashMap<usize, (trust_ir::BlockId, u32)> = HashMap::new();
    for (mir_bb, block, index) in assert_sites {
        if sites_by_mir_bb.insert(mir_bb, (block, index)).is_some() {
            return Err(format!(
                "Assert lowering recorded two sites for MIR bb{mir_bb}; the obligation \
                 <-> site pairing is not one-to-one"
            ));
        }
    }
    for (id, mir_bb) in &recorded_obligations {
        let Some((block, index)) = sites_by_mir_bb.remove(mir_bb) else {
            return Err(format!(
                "obligation #{} was recorded for MIR bb{mir_bb} but the lowering emitted no \
                 Assert CondBr there (pre-pass / lowering disagreement)",
                id.index()
            ));
        };
        let site = trust_ir::ObligationSite::new(obligation_fid, block, index);
        if !mb.set_obligation_site(*id, site) {
            return Err(format!(
                "obligation #{} vanished from the module table before its site could be \
                 recorded",
                id.index()
            ));
        }
    }
    if !sites_by_mir_bb.is_empty() {
        let mut extra: Vec<usize> = sites_by_mir_bb.keys().copied().collect();
        extra.sort_unstable();
        return Err(format!(
            "the lowering emitted Assert CondBrs at MIR bb(s) {extra:?} for which the \
             obligation pre-pass recorded nothing"
        ));
    }
    // `fb` has released its exclusive `mb` borrow: materialize any globals interned
    // for provenance-bearing constants / thread-local references during lowering
    // (a no-op when the body interned none). Their `GlobalId`s were assigned in
    // `dyn_vtables.len() + pending order`, matching the append order here.
    flush_pending_globals(cx, mb);
    // NOTE: `mb` is now shared/owned by the caller (it builds + validates the final
    // module). The per-fn `TRUST_IR_MIR_DUMP` text dump moved to the callers
    // (`try_lower_minimal` / `lower_module_for_emit` / `lower_closure_for_emit`),
    // which hold the built module — so this lowering can no longer consume `mb`.
    Ok(())
}

/// Lower one `Assign(place, rvalue)`. Splits on whether the destination is a
/// scalar-SSA bare local (RUNG 0: bind the value into `env`) or a memory place
/// (RUNG 1: Store the value at the place address).
fn lower_assign<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    env: &mut HashMap<Local, trust_ir::ValueId>,
    place: &Place<'tcx>,
    rvalue: &Rvalue<'tcx>,
) -> Result<(), String> {
    // RUNG 4: assigning to a ZERO-SIZED destination is a no-op. A ZST place holds
    // no bytes, so there is nothing to store and the rvalue (itself ZST-typed)
    // carries no observable value. This covers `() = ...`, a ZST struct/closure-env
    // assignment, a PhantomData write, etc. (A bare ZST local is classified `Zst`;
    // a projected place whose leaf type is a ZST is also dropped here.) Side
    // effects in MIR live in terminators (Call/Assert), never in an Assign rvalue,
    // so skipping the rvalue is sound.
    if place.projection.is_empty() && cx.is_zst_local(place.local) {
        return Ok(());
    }
    if !place.projection.is_empty() && ty_is_zst(cx, cx.place_concrete_ty(place)) {
        return Ok(());
    }

    // RUNG 4: a FAT-pointer destination (`&[T]`/`&str`/`&dyn`) holds TWO lanes
    // (data ptr + metadata). The single-scalar Store path cannot represent it. We
    // handle the two faithful fat-producing rvalues:
    //   * `dst = &(*src)` / `&raw (*src)` — a fat REBORROW: copy BOTH lanes of the
    //     source fat pointer's slot (the single-ptr `place_address` would drop the
    //     metadata, which is WRONG). The source must be `(*base)` with `base` a fat
    //     pointer, so the source slot is `base`'s slot.
    //   * `dst = Use(Copy/Move(src))` — a whole fat-pointer copy: routed to the
    //     2-lane `lower_aggregate_copy` below (its leaf is non-scalar, non-unit).
    // Any OTHER fat-pointer-producing rvalue is NOT faithfully modelable here, so we
    // fail loud (never emit a length-losing single-ptr store).
    if ty_is_fat_pointer_place(cx, place) {
        return lower_fat_pointer_assign(cx, fb, env, place, rvalue);
    }

    // A `Box<T> -> Box<dyn Trait>` UNSIZE (`Box::new(closure) as Box<dyn Fn>` —
    // the panic-hook shape): the destination is a 16-byte (data, vtable) pair
    // behind an ADT (Box), which the Ref/RawPtr-only fat classification above
    // does not see. Route it through the dyn-unsize lowering (whose
    // classification admits Box on both sides). This shape previously failed
    // loud, so no already-emitted module drifts.
    if let Rvalue::Cast(
        CastKind::PointerCoercion(
            rustc_middle::ty::adjustment::PointerCoercion::Unsize,
            _,
        ),
        src_op,
        _,
    ) = rvalue
    {
        if dyn_unsize_types(cx, cx.place_concrete_ty(place), src_op).is_some() {
            return lower_unsize_assign(cx, fb, env, place, src_op);
        }
        // WRAPPER fat unsize (`Unique<[T; N]> -> Unique<[T]>`,
        // `NonNull<[T; N]> -> NonNull<[T]>` — rustc `unsize_ptr`'s Adt arm):
        // the destination is a 16-byte (ptr, len) pair behind an ADT wrapper.
        // The data lane is the source's THIN pointer value; the len lane is
        // the differing tail's static array length.
        let dst_cty = cx.place_concrete_ty(place);
        if memory_leaf_tir_ty(cx.tcx, dst_cty).is_none() {
            if let Some(n) =
                custom_dst_unsize_len(cx, operand_concrete_ty(cx, src_op), dst_cty)
            {
                let thin = lower_cast_operand(cx, fb, env, src_op, &TIRTy::Ptr)?;
                let dst_addr = place_address(cx, fb, env, place)?;
                fb.store(TIRTy::Ptr, dst_addr, thin);
                let meta_addr = gep_byte_offset(fb, dst_addr, 8);
                let len_v = fb.iconst(TIRTy::U64, n as i128);
                fb.store(TIRTy::U64, meta_addr, len_v);
                return Ok(());
            }
        }
    }

    // UNSIZED destination LOCAL (THREADS / `unsized_fn_params`): the alloc-crate
    // `<Box<dyn FnOnce>>::call_once` body moves the boxed pointee into an
    // unsized local (`_3: dyn FnOnce = move (*_1)`) before the virtual call. In
    // the unsized-local model the local's slot is the 16-byte (data, metadata)
    // CARRIER; the move copies the CARRIER PAIR out of the source fat-pointer
    // cell (`_1`'s Box slot) — ownership of the pointee transfers with the
    // pair, exactly rustc's own by-value-unsized ABI. Only the two faithful
    // shapes are handled; anything else fails loud.
    if place.projection.is_empty()
        && unsized_local_carrier(cx, cx.local_concrete_ty(place.local)).is_some()
    {
        if let Rvalue::Use(Operand::Copy(src) | Operand::Move(src), _) = rvalue {
            let sproj = src.projection.as_ref();
            // `_dst = move (*fat_ptr)`: the carrier IS the fat pointer's pair.
            if sproj.len() == 1
                && matches!(sproj.first(), Some(ProjectionElem::Deref))
                && is_fat_pointer(cx.tcx, cx.local_concrete_ty(src.local))
            {
                let base = Place::from(src.local);
                return lower_fat_lane_copy(cx, fb, env, place, &base);
            }
            // `_dst = move _src` between two unsized locals: carrier-to-carrier.
            if sproj.is_empty()
                && unsized_local_carrier(cx, cx.local_concrete_ty(src.local)).is_some()
            {
                return lower_fat_lane_copy(cx, fb, env, place, src);
            }
        }
        return Err(format!(
            "unsized-local assign shape not modelable [rvalue={rvalue:?}]"
        ));
    }

    // RUNG 2: a CHECKED-OVERFLOW arithmetic rvalue (`AddWithOverflow` /
    // `SubWithOverflow` / `MulWithOverflow`) produces a `(scalar, bool)` pair into
    // a tuple destination. This is the debug-mode `a + b` shape (paired with an
    // `Assert(!overflow)` terminator). We lower it specially: compute
    // `fb.overflow(op, ty, lhs, rhs) -> (result, flag)` and Store each into the
    // destination tuple slot's two fields. (General aggregate construction stays
    // fail-loud; only this 2-field overflow pair is handled.)
    if let Rvalue::BinaryOp(binop, boxed) = rvalue {
        if let Some(ovf) = checked_overflow_op(*binop) {
            return lower_checked_overflow_assign(cx, fb, env, place, ovf, &**boxed);
        }
    }

    // RUNG 3: `dst = Aggregate(kind, operands)` — CONSTRUCT a tuple / struct /
    // array / enum-variant value in the destination's memory slot. Each operand
    // field is Stored at its faithful `layout_of` field offset; for an enum
    // variant the discriminant tag is also written. The destination is therefore
    // a memory place (handled by the construction helper, which addresses through
    // the slot), so this is checked BEFORE the scalar-SSA fast path.
    if let Rvalue::Aggregate(kind, operands) = rvalue {
        return lower_aggregate_assign(cx, fb, env, place, kind, operands);
    }

    // ADDITIVE: `dst = Repeat(elem, N)` — CONSTRUCT a `[T; N]` array all of whose
    // elements are the SAME value `elem`, into the destination's memory slot. This
    // is `[move _3; 8]` in MIR, exactly hashbrown's `repeat` helper
    // (`from_ne_bytes([tag.0; Group::WIDTH])`) — replicating a control-byte tag
    // across the 8-byte group word. We store `elem` at each of the N array strides
    // (the same per-element offsets `store_array_elems` uses for an explicit list),
    // so it is faithful to the array-repeat semantics. Constructed BEFORE the
    // scalar-SSA fast path (the destination is a memory array place).
    if let Rvalue::Repeat(elem, count) = rvalue {
        return lower_repeat_assign(cx, fb, env, place, elem, *count);
    }

    // RUNG 3: `dst = Discriminant(src)` — READ the variant discriminant of a
    // memory-backed enum `src`, yielding the value the guarding `SwitchInt`
    // compares. The destination is a scalar (an `isize`/`iN` tag temp).
    if let Rvalue::Discriminant(src) = rvalue {
        return lower_discriminant_assign(cx, fb, env, place, src);
    }

    // RUNG 3: a WHOLE-AGGREGATE move/copy `dst = Use(Copy/Move(src))` where both
    // sides are by-value aggregates (`_0 = move _1` — the `fn id(e:E)->E { e }`
    // round-trip, and any aggregate-typed temp copy). The single-scalar-leaf path
    // cannot represent a whole aggregate; copy the bytes lane-by-lane from the
    // source slot to the destination slot (both addressed through the memory-place
    // path, so a projected aggregate field copy works too).
    if let Rvalue::Use(Operand::Copy(src) | Operand::Move(src), _) = rvalue {
        let dst_cty = cx.place_concrete_ty(place);
        if memory_leaf_tir_ty(cx.tcx, dst_cty).is_none() && !is_unit(dst_cty) {
            return lower_aggregate_copy(cx, fb, env, place, src);
        }
    }

    // A generic `Reborrow` is a bitwise place copy. Rustc currently guarantees
    // equal source/target layouts even for shared `CoerceShared` reborrows; the
    // aggregate path validates that invariant before copying so a future rustc
    // relaxation fails loud instead of silently using the destination layout.
    if let Rvalue::Reborrow(_, _, src) = rvalue {
        let dst_cty = cx.place_concrete_ty(place);
        if memory_leaf_tir_ty(cx.tcx, dst_cty).is_none() && !is_unit(dst_cty) {
            return lower_aggregate_copy(cx, fb, env, place, src);
        }
    }

    // RUNG R3: a WHOLE-AGGREGATE CONSTANT assign `dst = Use(Constant(c))` where the
    // destination is a by-value aggregate whose leaf is NOT a single memory scalar —
    // e.g. `_10 = const Option::<usize>::None`, a niche/const-evaluated enum value
    // flowing into a memory enum place. The single-scalar Store path
    // (`place_leaf_tir_ty`) rejects the enum/struct/array leaf; instead materialize
    // the constant's EXACT byte image directly into the destination slot, the same
    // pointer-free natural-aligned lane discipline the by-ref call-arg
    // materialization (`materialize_const_aggregate`) uses. Gated on
    // `const_agg_bytes` succeeding, so a constant carrying live POINTER PROVENANCE is
    // NOT materialized here — it falls through and stays a loud failure (never a
    // wrong raw-bytes store of a compile-time address). A fat-pointer / str-slice
    // destination was already handled above, and a scalar/thin-ptr leaf takes the
    // scalar-const Store path below, so this fires exactly for the by-value
    // aggregate-constant case.
    if let Rvalue::Use(Operand::Constant(c), _) = rvalue {
        let dst_cty = cx.place_concrete_ty(place);
        if memory_leaf_tir_ty(cx.tcx, dst_cty).is_none() && !is_unit(dst_cty) {
            if let Ok(bytes) = const_agg_bytes(cx, c) {
                let addr = place_address(cx, fb, env, place)?;
                store_agg_bytes_at(cx, fb, addr, dst_cty, bytes)?;
                return Ok(());
            }
            // A PROVENANCE-BEARING aggregate constant (`_0 = const TypeId` in
            // `<T as Any>::type_id`, a struct holding a `&static`): the
            // relocation-aware writer resolves each pointer slot faithfully
            // (`GlobalAddr` / raw TypeId hash bytes) — never a wrong raw store.
            // Fat-pointer and Slice-value destinations were already routed
            // above; anything unresolvable still fails loud inside.
            if matches!(c.const_.ty().kind(), ty::Adt(..) | ty::Tuple(..) | ty::Array(..))
            {
                let addr = place_address(cx, fb, env, place)?;
                store_const_agg_at(cx, fb, addr, dst_cty, c)?;
                return Ok(());
            }
        }
    }

    // A TRANSMUTE whose DESTINATION leaf is a non-scalar AGGREGATE (`u32::to_ne_bytes`
    // = `transmute::<u32,[u8;4]>`, `usize::to_ne_bytes`, ...): the single-scalar Store
    // path rejects the array/struct leaf. A transmute preserves the exact byte image
    // and size, so store the SOURCE into the destination slot —
    //   * a SCALAR source: one typed Store of its bits (size == dst size), the array
    //     then reads those same bytes back element-by-element;
    //   * an AGGREGATE-PLACE source: a byte lane-copy from the source slot.
    if let Rvalue::Cast(CastKind::Transmute, src_op, _) = rvalue {
        let dst_cty = cx.place_concrete_ty(place);
        if memory_leaf_tir_ty(cx.tcx, dst_cty).is_none() && !is_unit(dst_cty) {
            return lower_transmute_to_aggregate(cx, fb, env, place, src_op);
        }
    }

    // Destination: a bare SSA scalar local with no projection?
    if place.projection.is_empty() {
        if let Some(LocalModel::Ssa(dst_ty)) = cx.model.get(&place.local) {
            let val = lower_rvalue(cx, fb, env, rvalue, dst_ty.clone())?;
            env.insert(place.local, val);
            return Ok(());
        }
    }

    // Otherwise the destination is MEMORY: a memory-backed local (possibly
    // projected). Compute the leaf trust-ir type the place addresses, then Store
    // the rvalue's value at the place address.
    let leaf_ty = place_leaf_tir_ty(cx, place).map_err(|e| {
        let opnd_ty = match rvalue {
            Rvalue::Cast(_, op, _) | Rvalue::Use(op, _) => {
                format!(" src_ty={:?}", operand_concrete_ty(cx, op))
            }
            _ => String::new(),
        };
        format!("{e} [rvalue={rvalue:?}{opnd_ty}]")
    })?;
    let val = lower_rvalue(cx, fb, env, rvalue, leaf_ty.clone())?;
    let addr = place_address(cx, fb, env, place)?;
    fb.store(leaf_ty, addr, val);
    Ok(())
}

/// Whether a destination PLACE's leaf type is a FAT pointer (a 2-lane slot in this
/// model).
fn ty_is_fat_pointer_place<'tcx>(cx: &Cx<'tcx, '_>, place: &Place<'tcx>) -> bool {
    is_fat_pointer(cx.tcx, cx.place_concrete_ty(place))
}

/// RUNG 4: lower an assignment whose DESTINATION is a fat pointer (`&[T]`/`&str`/
/// `&dyn`), copying BOTH lanes (data + metadata) faithfully. Only the two
/// fat-producing rvalues we can model exactly are handled:
///   * `dst = Use(Copy/Move(src))` — copy the source fat pointer's two lanes.
///   * `dst = &(*base)` / `&raw (*base)` — a reborrow: the produced fat pointer IS
///     `base`'s fat pointer (`*base` then `&` reconstitutes data+metadata), so copy
///     `base`'s two lanes. `base` must itself be a fat pointer (so its slot holds
///     both lanes).
/// Anything else fails loud — we never store a single ptr into a 2-lane slot (that
/// would silently drop the metadata = a wrong length / vtable).
fn lower_fat_pointer_assign<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    env: &mut HashMap<Local, trust_ir::ValueId>,
    dst: &Place<'tcx>,
    rvalue: &Rvalue<'tcx>,
) -> Result<(), String> {
    match rvalue {
        // A whole fat-pointer copy: both slots are 16-byte 2-lane; copy lane by lane.
        Rvalue::Use(Operand::Copy(src) | Operand::Move(src), _) => {
            if !is_fat_pointer(cx.tcx, cx.place_concrete_ty(src)) {
                return Err("fat-pointer dst from non-fat source Use (unmodelable)".to_string());
            }
            lower_fat_lane_copy(cx, fb, env, dst, src)
        }
        // ADDITIVE (R3 stage 1): `dst = const "lit"` — a `&'static str` /
        // `&'static [u8]` LITERAL into a fat destination (e.g. `let s: &str =
        // "Tree.rec"`, or `_0 = const ".rec"` returning a literal). The literal's
        // bytes were materialized in the entry block as an IMMORTAL heap image
        // (so this is lifetime-sound even when dst escapes the frame — incl. the
        // sret return slot); store the fat pair into dst's two lanes, mirroring
        // `lower_unsize_assign`'s lane discipline (Ptr at +0, U64 length at +8).
        Rvalue::Use(Operand::Constant(c), _) if str_const_bytes(cx, c).is_some() => {
            let mat = str_const_mat(cx, c)?;
            let (data_ptr, len) = (mat.data_ptr, mat.len);
            let dst_addr = place_address(cx, fb, env, dst)?;
            fb.store(TIRTy::Ptr, dst_addr, data_ptr);
            let meta_addr = gep_byte_offset(fb, dst_addr, 8);
            let len_v = fb.iconst(TIRTy::U64, len as i128);
            fb.store(TIRTy::U64, meta_addr, len_v);
            Ok(())
        }
        // A reborrow `&(*base)` / `&raw (*base)`: the source place must be exactly a
        // single leading Deref of a FAT base; the produced fat pointer equals the
        // base's fat pointer. Copy the base's two lanes.
        Rvalue::Ref(_, _, src) | Rvalue::RawPtr(_, src) => {
            let proj = src.projection.as_ref();
            // GENERAL fat reborrow (THREADS): `&((<prefix>*fat).tail…)` where
            //   * `prefix` (possibly empty, all sized-walk elements, no Deref)
            //     addresses a FAT-POINTER CELL — the bare fat local (`&(*fat)`),
            //     or a fat field of a sized aggregate (a closure env's captured
            //     `&dyn`/`&[u8]` upvar: `[Field(k), Deref]`);
            //   * `suffix` (the elements after the Deref, possibly empty) is a
            //     chain of Fields descending UNSIZED-TAIL structs (`OsStr ->
            //     [u8]`, `CStr -> [c_char]`): each contributes a STATIC byte
            //     offset to the data lane and PRESERVES the metadata lane (an
            //     unsized tail's metadata IS the whole's metadata).
            // The produced fat pointer is (base.data + offset, base.metadata).
            // Anything else (mid-suffix Deref/Index, sized leaf) fails loud.
            if let Some(deref_pos) = proj.iter().position(|e| matches!(e, ProjectionElem::Deref))
            {
                let prefix = &proj[..deref_pos];
                let suffix = &proj[deref_pos + 1..];
                let carrier_ty = cx.mono(
                    Place::ty_from(src.local, prefix, &cx.body.local_decls, cx.tcx).ty,
                );
                let suffix_all_fields = suffix
                    .iter()
                    .all(|e| matches!(e, ProjectionElem::Field(..)));
                if is_fat_pointer(cx.tcx, carrier_ty) && suffix_all_fields {
                    if prefix.is_empty() && suffix.is_empty() {
                        // The historical `&(*fat)` shape: verbatim 2-lane copy.
                        let base = Place::from(src.local);
                        return lower_fat_lane_copy(cx, fb, env, dst, &base);
                    }
                    return lower_fat_tail_reborrow(
                        cx, fb, env, dst, src.local, prefix, suffix, carrier_ty,
                    );
                }
                // SUBSLICE reborrow of a slice/str: `&(*fat)[from..]` /
                // `&(*fat)[..len-to]` / `&(*fat)[from..to]` — the suffix is
                // exactly ONE `Subslice`. The produced fat pointer is
                // (data + from*stride, adjusted length).
                if is_fat_pointer(cx.tcx, carrier_ty) {
                    if let [ProjectionElem::Subslice { from, to, from_end }] = suffix {
                        return lower_fat_subslice_reborrow(
                            cx, fb, env, dst, src.local, prefix, carrier_ty, *from, *to,
                            *from_end,
                        );
                    }
                }
            }
            Err(format!(
                "fat-pointer reborrow shape not modelable (only &(*fat)) [src={src:?} \
                 src_local_ty={} proj={:?}]",
                ty_family(cx.local_concrete_ty(src.local)),
                src.projection
            ))
        }
        // An UNSIZE coercion `dst = src as &[T] / &str (PointerCoercion(Unsize))`
        // from a THIN `&[T; N]` array pointer: the produced fat pointer's data lane
        // is the source thin pointer; the metadata lane is the STATIC array length
        // `N` (a slice/str length is a `usize` known from the source pointee type
        // `[T; N]`). We store both lanes. A `&dyn`/other unsize (vtable metadata) is
        // not modeled — fail loud.
        Rvalue::Cast(
            CastKind::PointerCoercion(
                rustc_middle::ty::adjustment::PointerCoercion::Unsize,
                _,
            ),
            src_op,
            _,
        ) => lower_unsize_assign(cx, fb, env, dst, src_op),
        // R2: a fat -> fat `Transmute` / `PtrToPtr` reinterpret (`*const str` <->
        // `&str`, `*const [T]` <-> `*mut [U]`, ...). Both sides are 16-byte
        // (data, metadata) pairs, so a transmute/ptr-cast between them is
        // BIT-PRESERVING: copy both lanes from the source. This is the fat-dst
        // dual of the thin-dst fat-source cast handled in `lower_cast` — together
        // they cover the `precondition_check` / allocator str-pointer reinterprets.
        Rvalue::Cast(CastKind::Transmute | CastKind::PtrToPtr, src_op, _) => {
            lower_fat_reinterpret_assign(cx, fb, env, dst, src_op)
        }
        // A fat RAW-POINTER built from parts (`AggregateKind::RawPtr` — the
        // `ptr::from_raw_parts(data, meta)` shape): store the data pointer into
        // lane 0 and the metadata into lane 1 (+8).
        Rvalue::Aggregate(kind, ops) if matches!(**kind, AggregateKind::RawPtr(..)) => {
            lower_raw_ptr_from_parts(cx, fb, env, dst, ops)
        }
        _ => Err("fat-pointer dst from unmodelable rvalue".to_string()),
    }
}

/// RUNG 4 + DYN: lower a `dst = src as <unsized> (Unsize)` into `dst`'s 2-lane fat
/// slot (data ptr at +0, metadata at +8). Two coercion families are modeled:
///   * ARRAY-to-slice/str (`&[T; N] -> &[T]/&str`): metadata lane is the static
///     array length `N` (a `usize`), read off the source pointee `[T; N]`.
///   * to-`dyn` (`&T -> &dyn Trait`, `&mut F -> &mut dyn FnMut`): metadata lane is
///     the ADDRESS of the `<self_ty as Trait>` vtable — a read-only module global
///     synthesized in the pre-`fb` pass (`materialize_dyn_vtables`) and recorded in
///     `cx.dyn_vtables`. The data lane is the source thin pointer in both families.
/// Any other unsize (e.g. an auto-trait-only `dyn` with no principal vtable) stays
/// a loud failure.
fn lower_unsize_assign<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    env: &mut HashMap<Local, trust_ir::ValueId>,
    dst: &Place<'tcx>,
    src_op: &Operand<'tcx>,
) -> Result<(), String> {
    // DYN coercion: the destination is a trait-object fat pointer. Its metadata
    // lane carries the vtable pointer (a `Ptr`), synthesized as a module global by
    // the pre-`fb` pass and taken by `global_addr` here. The data lane is the
    // source thin `&self`/`&mut self` pointer value.
    let dst_ty = cx.place_concrete_ty(dst);
    if let Some((self_ty, dyn_ty)) = dyn_unsize_types(cx, dst_ty, src_op) {
        // A dyn -> dyn coercion. Two faithful shapes (rustc `unsized_info`):
        //   * principal-PRESERVING (auto-trait dropping, `&(dyn Any + Send) ->
        //     &dyn Any`): the (data, vtable) pair is UNCHANGED — copy both fat
        //     lanes;
        //   * supertrait UPCAST (`&dyn Error -> &dyn Debug`): the data lane is
        //     unchanged; the vtable lane is adjusted per
        //     `supertrait_vtable_slot` — `Some(idx)` loads the new vtable from
        //     the OLD vtable's TraitVPtr slot at `idx * 8`; `None` (prefix
        //     sharing) keeps the old vtable.
        if matches!(self_ty.kind(), ty::Dynamic(..)) {
            let (Operand::Copy(src) | Operand::Move(src)) = src_op else {
                return Err(
                    "dyn -> dyn coercion source is not a place (const dyn ref)".to_string(),
                );
            };
            if dyn_identity_unsize(cx, self_ty, dyn_ty) {
                return lower_fat_lane_copy(cx, fb, env, dst, src);
            }
            let src_addr = place_address(cx, fb, env, src)?;
            let data = fb.load(TIRTy::Ptr, src_addr);
            let vt_addr = gep_byte_offset(fb, src_addr, 8);
            let vt = fb.load(TIRTy::Ptr, vt_addr);
            let vt2 = match cx.tcx.supertrait_vtable_slot((self_ty, dyn_ty)) {
                Some(idx) => {
                    let slot_addr = gep_byte_offset(fb, vt, (idx as u64) * 8);
                    fb.load(TIRTy::Ptr, slot_addr)
                }
                None => vt,
            };
            let dst_addr = place_address(cx, fb, env, dst)?;
            fb.store(TIRTy::Ptr, dst_addr, data);
            let dst_meta = gep_byte_offset(fb, dst_addr, 8);
            fb.store(TIRTy::Ptr, dst_meta, vt2);
            return Ok(());
        }
        let gid = *cx.dyn_vtables.get(&(self_ty, dyn_ty)).ok_or_else(|| {
            "to-dyn Unsize has no pre-registered vtable (prescan/lower disagreement)".to_string()
        })?;
        let dst_addr = place_address(cx, fb, env, dst)?;
        // Lane 0: the data pointer — the source thin pointer VALUE.
        let data = lower_cast_operand(cx, fb, env, src_op, &TIRTy::Ptr)?;
        fb.store(TIRTy::Ptr, dst_addr, data);
        // Lane 1: the vtable pointer (module global address) at offset 8.
        let vptr = fb.global_addr(gid);
        let meta_addr = gep_byte_offset(fb, dst_addr, 8);
        fb.store(TIRTy::Ptr, meta_addr, vptr);
        return Ok(());
    }

    // The source must be a THIN `&[T; N]` / `*[T; N]` (a sized-array pointer). Its
    // pointee `[T; N]` supplies the static length `N`.
    let src_ty = operand_concrete_ty(cx, src_op);
    let src_pointee = match src_ty.kind() {
        ty::Ref(_, p, _) | ty::RawPtr(p, _) => *p,
        _ => return Err(format!("Unsize source is not a pointer: {}", ty_family(src_ty))),
    };
    let len = match src_pointee.kind() {
        ty::Array(_elem, n) => n
            .try_to_target_usize(cx.tcx)
            .ok_or_else(|| "Unsize: array length is not a concrete usize".to_string())?,
        // CUSTOM-DST unsize (`&S<..[T; N]..> -> &S<..[T]..>` — smallsort's
        // `PolymorphicIter`): same ADT both sides; the metadata is the LENGTH
        // of the differing tail's array leaf (rustc `unsize_ptr`'s Adt arm).
        // A `dyn` unsize (vtable metadata) was already handled above.
        _ => {
            let dstp = fat_pointer_pointee(cx.tcx, dst_ty)
                .or_else(|| dst_ty.boxed_ty())
                .ok_or_else(|| "Unsize destination has no pointee".to_string())?;
            custom_dst_unsize_len(cx, cx.mono(src_pointee), cx.mono(dstp)).ok_or_else(
                || {
                    format!(
                        "Unsize from non-array pointee {} (dyn/vtable not modeled)",
                        ty_family(src_pointee)
                    )
                },
            )?
        }
    };

    // The destination fat slot's two lanes.
    let dst_addr = place_address(cx, fb, env, dst)?;
    // Lane 0: the data pointer — the source thin pointer VALUE (a `Ptr`).
    let data = lower_cast_operand(cx, fb, env, src_op, &TIRTy::Ptr)?;
    fb.store(TIRTy::Ptr, dst_addr, data);
    // Lane 1: the length metadata (`usize`) at offset 8.
    let meta_addr = gep_byte_offset(fb, dst_addr, 8);
    let len_v = fb.iconst(TIRTy::U64, len as i128);
    fb.store(TIRTy::U64, meta_addr, len_v);
    Ok(())
}

// ================= DYN/VTABLE rung: to-`dyn` Unsize coercions ==================
//
// A `&T -> &dyn Trait` / `&mut F -> &mut dyn FnMut` coercion (`PointerCoercion
// (Unsize)` into a trait-object fat pointer) builds a `(data, vtable)` fat pointer:
// the data lane is the source thin `&self` pointer; the vtable lane points at the
// `<self_ty as Trait>` vtable. TrustIr has module globals + `GlobalAddr`, so the
// vtable is a synthesized read-only global whose initializer mirrors rustc's
// `tcx.vtable_entries` layout: the drop/size/align header then the concrete method
// fn-pointers. Method + drop slots are `Constant::SymbolAddr(symbol_name(instance))`
// (a relocatable fn-pointer typed `Ptr` — the exact representation the trust-cg
// backend consumes for a vtable method slot; `Constant::FnDef` is the intra-module
// alternative but would require declaring each concrete method as a module function,
// unnecessary here where the coercion sites never dispatch through the table
// themselves); size/align are `Int` words; null/vacant slots are a null `Ptr`.
//
// The globals must be added through the `ModuleBuilder`, so they are built in a
// pre-`fb` pass (`materialize_dyn_vtables`) and recorded in `cx.dyn_vtables` keyed
// by `(self_ty, dyn pointee)`; `lower_unsize_assign` reads the `GlobalId` back.

/// The static tail LENGTH of a CUSTOM-DST unsize `&S<..[T; N]..> -> &S<..[T]..>`
/// (rustc `unsize_ptr`'s Adt -> Adt arm): both pointees are the SAME struct;
/// descend the (unique) differing field pairwise until the leaf `[T; N] ->
/// [T]`, whose `N` is the fat pointer's metadata. `None` when the pair is not
/// this shape (fail-closed at the caller).
fn custom_dst_unsize_len<'tcx>(
    cx: &Cx<'tcx, '_>,
    src: Ty<'tcx>,
    dst: Ty<'tcx>,
) -> Option<u64> {
    let mut src = src;
    let mut dst = dst;
    loop {
        match (src.kind(), dst.kind()) {
            (ty::Array(_, n), ty::Slice(_)) => return n.try_to_target_usize(cx.tcx),
            // A PATTERN-typed pair (`NonNull.pointer: pattern_type!(*const T
            // is !null)`): unwrap to the base types (rustc `unsize_ptr`'s
            // leading `Pat` arm).
            (ty::Pat(a, _), ty::Pat(b, _)) => {
                src = *a;
                dst = *b;
            }
            // A pointer field pair (`NonNull`'s `*const [T; N]` vs `*const
            // [T]`): the unsize happens through ONE pointer level — recurse
            // into the pointees.
            (
                ty::Ref(_, a, _) | ty::RawPtr(a, _),
                ty::Ref(_, b, _) | ty::RawPtr(b, _),
            ) => {
                src = *a;
                dst = *b;
            }
            (ty::Adt(d1, s1), ty::Adt(d2, s2)) if d1 == d2 && d1.is_struct() => {
                let variant = d1.non_enum_variant();
                let mut differing: Option<(Ty<'tcx>, Ty<'tcx>)> = None;
                for f in variant.fields.iter() {
                    let a = cx.normalize_ty(f.ty(cx.tcx, s1));
                    let b = cx.normalize_ty(f.ty(cx.tcx, s2));
                    // Skip ZST fields (rustc's `unsize_ptr` skips 1-ZSTs): a
                    // `PhantomData<[T; N]>` vs `PhantomData<[T]>` pair also
                    // "differs" but carries no data — the REAL unsizing field
                    // is the pointer (`Unique.pointer: NonNull<..>`).
                    if a != b && !ty_is_zst(cx, a) {
                        differing = Some((a, b));
                    }
                }
                let (a, b) = differing?;
                src = a;
                dst = b;
            }
            _ => return None,
        }
    }
}

/// The `(concrete self type, dyn destination pointee)` of a to-`dyn` Unsize
/// coercion whose destination `dst_ty` is a trait-object fat pointer and whose
/// source `src_op` is a THIN `&self`/`*self` pointer to a sized `self_ty`. Returns
/// `None` for any non-`dyn` unsize (array-to-slice/str) or non-pointer source, so
/// both the prescan and `lower_unsize_assign` classify a coercion identically. All
/// types are monomorphized (`place_concrete_ty` / `operand_concrete_ty`), so the
/// key is a stable `(Ty, Ty)` shared across the two passes.
fn dyn_unsize_types<'tcx>(
    cx: &Cx<'tcx, '_>,
    dst_ty: Ty<'tcx>,
    src_op: &Operand<'tcx>,
) -> Option<(Ty<'tcx>, Ty<'tcx>)> {
    // The destination trait-object pointee: behind a `&dyn`/`*dyn` fat pointer,
    // or behind a `Box<dyn Trait>` (same 16-byte (data, vtable) pair layout).
    let dst_pointee = match fat_pointer_pointee(cx.tcx, dst_ty) {
        Some(p) => p,
        None => dst_ty.boxed_ty()?,
    };
    if !matches!(dst_pointee.kind(), ty::Dynamic(..)) {
        return None;
    }
    let src_ty = operand_concrete_ty(cx, src_op);
    let self_ty = match src_ty.kind() {
        ty::Ref(_, p, _) | ty::RawPtr(p, _) => *p,
        // `Box<T> -> Box<dyn Trait>` (Box::new(closure) as Box<dyn Fn> — the
        // panic-hook / thread-spawn shape): the source data pointer is the thin
        // Box, the self type its pointee.
        _ => match src_ty.boxed_ty() {
            Some(p) => p,
            None => return None,
        },
    };
    Some((self_ty, dst_pointee))
}

/// Pre-scan the body for every to-`dyn` Unsize coercion, returning the DISTINCT
/// `(self_ty, dyn pointee)` keys in first-appearance order. Cleanup blocks are
/// skipped under panic=abort (never lowered there), matching the consumer in
/// `lower_unsize_assign`; the EH lane emits cleanup blocks, so it scans them.
fn prescan_dyn_coercions<'tcx>(
    cx: &Cx<'tcx, '_>,
    body: &Body<'tcx>,
) -> Vec<(Ty<'tcx>, Ty<'tcx>)> {
    let eh = eh_lane(cx.tcx);
    let mut out: Vec<(Ty<'tcx>, Ty<'tcx>)> = Vec::new();
    for (_bb, bdata) in body.basic_blocks.iter_enumerated() {
        if bdata.is_cleanup && !eh {
            continue;
        }
        for stmt in &bdata.statements {
            let StatementKind::Assign(bx) = &stmt.kind else {
                continue;
            };
            let (place, rvalue) = &**bx;
            let Rvalue::Cast(
                CastKind::PointerCoercion(
                    rustc_middle::ty::adjustment::PointerCoercion::Unsize,
                    _,
                ),
                src_op,
                _,
            ) = rvalue
            else {
                continue;
            };
            let dst_ty = cx.place_concrete_ty(place);
            if let Some(key) = dyn_unsize_types(cx, dst_ty, src_op) {
                // A dyn -> dyn coercion (auto-trait dropping OR supertrait
                // upcast) synthesizes NO vtable global: identity reuses the
                // source vtable; an upcast loads the new vtable from the OLD
                // one's TraitVPtr slot at runtime.
                if matches!(key.0.kind(), ty::Dynamic(..)) {
                    continue;
                }
                if !out.contains(&key) {
                    out.push(key);
                }
            }
        }
    }
    out
}

/// Build one vtable module global per distinct to-`dyn` coercion key and record
/// its `GlobalId` in `cx.dyn_vtables`. Globals are added EXCLUSIVELY here over an
/// initially empty table (one per distinct vtable), so the next global's index is
/// `cx.dyn_vtables.len()`. Fails loud (fail-closed, never partial) on a coercion
/// whose vtable cannot be modeled (auto-trait-only `dyn`, unsized self, supertrait
/// vptr) — the coercion then stays an unlowered loud failure at its use site.
fn materialize_dyn_vtables<'tcx>(
    cx: &mut Cx<'tcx, '_>,
    mb: &mut ModuleBuilder,
    keys: Vec<(Ty<'tcx>, Ty<'tcx>)>,
) -> Result<(), String> {
    for (self_ty, dyn_ty) in keys {
        ensure_dyn_vtable(cx, mb, self_ty, dyn_ty)?;
    }
    Ok(())
}

/// Whether a dyn -> dyn Unsize coercion PRESERVES the principal trait (it only
/// drops auto-trait bounds / tightens the region): both pointees are trait
/// objects and their principal `ExistentialTraitRef`s are identical. Such a
/// coercion reuses the source vtable UNCHANGED (rustc emits no new table). A
/// supertrait UPCAST (principal changes) is NOT identity — it reads the
/// `TraitVPtr` slot — and a principal-dropping coercion (to an auto-only dyn)
/// changes the metadata, so neither is admitted here.
fn dyn_identity_unsize<'tcx>(cx: &Cx<'tcx, '_>, self_ty: Ty<'tcx>, dyn_ty: Ty<'tcx>) -> bool {
    let (ty::Dynamic(sp, _), ty::Dynamic(dp, _)) = (self_ty.kind(), dyn_ty.kind()) else {
        return false;
    };
    match (sp.principal(), dp.principal()) {
        (Some(a), Some(b)) => {
            cx.tcx.instantiate_bound_regions_with_erased(a)
                == cx.tcx.instantiate_bound_regions_with_erased(b)
        }
        _ => false,
    }
}

/// Get-or-build the `<self_ty as Trait>` vtable global for a to-`dyn` coercion
/// key, recursing through `TraitVPtr` entries (supertrait upcast pointers) so a
/// trait with supertrait tables (`StringError: Error(+Debug/Display)`) is fully
/// materialized. Ids stay dense by construction: each ensure adds EXACTLY one
/// global per distinct key, nested keys are ensured (added) BEFORE the parent's
/// `add_global`, and this pass runs pre-`fb` (the pending-globals table is
/// empty), so `cx.dyn_vtables.len()` equals the globals-table length at every
/// add.
fn ensure_dyn_vtable<'tcx>(
    cx: &mut Cx<'tcx, '_>,
    mb: &mut ModuleBuilder,
    self_ty: Ty<'tcx>,
    dyn_ty: Ty<'tcx>,
) -> Result<trust_ir::value::GlobalId, String> {
    if let Some(gid) = cx.dyn_vtables.get(&(self_ty, dyn_ty)).copied() {
        return Ok(gid);
    }
    let global = build_dyn_vtable_global(cx, mb, self_ty, dyn_ty)?;
    let gid = trust_ir::value::GlobalId::new(cx.dyn_vtables.len() as u32);
    mb.add_global(global);
    cx.dyn_vtables.insert((self_ty, dyn_ty), gid);
    Ok(gid)
}

/// Synthesize the `<self_ty as Trait>` vtable as a read-only module global (added
/// to `mb`) whose initializer mirrors `tcx.vtable_entries(trait_ref)`:
///   * `MetadataSize` / `MetadataAlign` -> the concrete self layout as an `Int`
///     word (typed `U64`);
///   * `MetadataDropInPlace` -> `SymbolAddr(drop_in_place::<self_ty>)` when the
///     self type needs drop, else a null `Ptr` (matching rustc);
///   * `Method(instance)` -> `SymbolAddr(symbol_name(instance))`, a fn-pointer;
///   * `Vacant` -> a null `Ptr`.
/// The global's type is a positional `Tuple` of the per-entry types, so the
/// `Aggregate` initializer validates element-by-element. `TraitVPtr` (supertrait
/// upcast pointers) and an auto-trait-only `dyn` (no principal) fail closed. The
/// trait ref is recovered exactly as rustc's `vtable_allocation_provider` does:
/// erase the principal existential's bound regions, then re-attach `self_ty`.
fn build_dyn_vtable_global<'tcx>(
    cx: &mut Cx<'tcx, '_>,
    mb: &mut ModuleBuilder,
    self_ty: Ty<'tcx>,
    dyn_ty: Ty<'tcx>,
) -> Result<trust_ir::Global, String> {
    let ty::Dynamic(preds, _) = dyn_ty.kind() else {
        return Err("dyn vtable: destination pointee is not a trait object".to_string());
    };
    let principal = preds
        .principal()
        .map(|p| cx.tcx.instantiate_bound_regions_with_erased(p))
        .ok_or_else(|| {
            "to-dyn Unsize to an auto-trait-only `dyn` (no principal vtable) not modeled"
                .to_string()
        })?;
    let trait_ref = principal.with_self_ty(cx.tcx, self_ty);

    let layout = cx
        .tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(self_ty))
        .map_err(|e| format!("dyn vtable: layout_of({self_ty:?}) failed: {e:?}"))?;
    if !layout.is_sized() {
        return Err(format!("dyn vtable: concrete self type `{self_ty:?}` is unsized"));
    }
    let size = layout.size.bytes();
    let align = layout.align.abi.bytes();

    let entries = cx.tcx.vtable_entries(trait_ref);
    // Emit each pointer-width INTEGER metadata slot (size / align / null drop /
    // vacant) as ONE `Constant::Int` at a `Usize` field type. trust-cg's aggregate
    // initializer encoder (`trust_ir_global_initializer_data`, since the
    // aggregate-`Int`-element-width fix) lays out each `Int` element at its DECLARED
    // type's width — `Usize` -> `ptr_size` — so the following method-pointer
    // (`SymbolAddr`) relocations stay 8-aligned, exactly matching rustc's vtable
    // layout (pointer slots at `slot_index * ptr_size`, read by the `Virtual`
    // dispatch GEP `vtable + vslot * 8`). (This previously flattened each slot to
    // `ptr_size` `U8` bytes to work around a trust-cg bug that laid `Int` aggregate
    // elements at 1 byte each; that bug is now fixed at the source, so the natural
    // per-slot `Int` encoding is used.)
    let mut field_tys: Vec<TIRTy> = Vec::with_capacity(entries.len());
    let mut elems: Vec<Constant> = Vec::with_capacity(entries.len());
    let push_uint_slot = |field_tys: &mut Vec<TIRTy>, elems: &mut Vec<Constant>, v: u128| {
        field_tys.push(TIRTy::Usize);
        elems.push(Constant::Int(v as i128));
    };
    for entry in entries.iter() {
        match entry {
            ty::VtblEntry::MetadataSize => push_uint_slot(&mut field_tys, &mut elems, u128::from(size)),
            ty::VtblEntry::MetadataAlign => push_uint_slot(&mut field_tys, &mut elems, u128::from(align)),
            ty::VtblEntry::MetadataDropInPlace => {
                if self_ty.needs_drop(cx.tcx, ty::TypingEnv::fully_monomorphized()) {
                    let drop_instance = Instance::resolve_drop_glue(cx.tcx, self_ty);
                    let name = cx.tcx.symbol_name(drop_instance).name.to_string();
                    field_tys.push(TIRTy::Ptr);
                    elems.push(Constant::symbol_addr(name));
                } else {
                    // No destructor: rustc stores a null drop pointer (ptr_size zeros).
                    push_uint_slot(&mut field_tys, &mut elems, 0);
                }
            }
            ty::VtblEntry::Method(instance) => {
                field_tys.push(TIRTy::Ptr);
                let name = cx.tcx.symbol_name(*instance).name.to_string();
                elems.push(Constant::symbol_addr(name));
            }
            ty::VtblEntry::Vacant => {
                // A non-dispatchable slot: a null pointer (ptr_size zeros), like rustc.
                push_uint_slot(&mut field_tys, &mut elems, 0);
            }
            ty::VtblEntry::TraitVPtr(sup) => {
                // A supertrait UPCAST pointer: the slot holds the address of
                // the `<self_ty as Supertrait>` vtable. Ensure the nested
                // table exists as its own module global (added BEFORE this
                // one, keeping ids dense) and reference it by its Internal
                // symbol — the same in-object `SymbolAddr` relocation a method
                // slot uses.
                let sup_tr = *sup;
                let sup_ex = ty::ExistentialTraitRef::erase_self_ty(cx.tcx, sup_tr);
                let sup_dyn = Ty::new_dynamic(
                    cx.tcx,
                    cx.tcx.mk_poly_existential_predicates(&[ty::Binder::dummy(
                        ty::ExistentialPredicate::Trait(sup_ex),
                    )]),
                    cx.tcx.lifetimes.re_erased,
                );
                ensure_dyn_vtable(cx, mb, self_ty, sup_dyn)?;
                field_tys.push(TIRTy::Ptr);
                elems.push(Constant::symbol_addr(dyn_vtable_symbol_name(self_ty, sup_tr)));
            }
        }
    }

    let name = dyn_vtable_symbol_name(self_ty, trait_ref);
    Ok(trust_ir::Global {
        name,
        ty: TIRTy::Tuple(field_tys),
        mutable: false,
        initializer: Some(Constant::Aggregate(elems)),
        linkage: trust_ir::Linkage::Internal,
        tls: None,
        // A vtable is pointer-aligned; the Tuple(Ptr, …) type derives that.
        align: None,
    })
}

/// A deterministic, module-local symbol name for the `<self_ty as Trait>` vtable.
/// `Internal` linkage keeps it private to the emitting module, so a content hash of
/// the (self, trait) pair is enough to keep two distinct vtables in one module from
/// colliding.
fn dyn_vtable_symbol_name<'tcx>(self_ty: Ty<'tcx>, trait_ref: ty::TraitRef<'tcx>) -> String {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::Hasher;
    let mut hasher = DefaultHasher::new();
    hasher.write(format!("{self_ty:?}|{trait_ref:?}").as_bytes());
    format!("vtable.{:016x}", hasher.finish())
}

/// SUBSLICE fat reborrow: `dst = &(*fat)[from..]` / `&(*fat)[..len-to]` /
/// `&(*fat)[from..to]` — the source is a fat slice/str CELL (addressed by
/// `base_local` + the sized `prefix` walk) and the single `Subslice`
/// projection adjusts BOTH lanes:
///   * data' = data + `from` * element stride (a static byte offset);
///   * len'  = `from_end` ? len - (from + to)   (a runtime subtract)
///             : to - from                       (a compile-time constant).
/// Stores the adjusted (data, len) pair into `dst`'s 2-lane slot. Only
/// slice/str pointees carry a countable length; anything else fails loud.
#[allow(clippy::too_many_arguments)]
fn lower_fat_subslice_reborrow<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    env: &mut HashMap<Local, trust_ir::ValueId>,
    dst: &Place<'tcx>,
    base_local: Local,
    prefix: &[ProjectionElem<Local, Ty<'tcx>>],
    carrier_ty: Ty<'tcx>,
    from: u64,
    to: u64,
    from_end: bool,
) -> Result<(), String> {
    // Address the fat CELL, then load both lanes.
    let base_addr = place_address(cx, fb, env, &Place::from(base_local))?;
    let cell_addr = if prefix.is_empty() {
        base_addr
    } else {
        walk_projection_address(
            cx,
            fb,
            env,
            base_addr,
            cx.local_concrete_ty(base_local),
            prefix,
            None,
        )?
    };
    let data = fb.load(TIRTy::Ptr, cell_addr);
    let meta_addr = gep_byte_offset(fb, cell_addr, 8);
    let len = fb.load(TIRTy::U64, meta_addr);
    // The element stride, from the slice/str pointee.
    let pointee = fat_pointer_pointee(cx.tcx, carrier_ty)
        .ok_or_else(|| "subslice reborrow: carrier has no pointee".to_string())?;
    let stride = match cx.mono(pointee).kind() {
        ty::Str => 1u64,
        ty::Slice(el) => {
            let tal = cx
                .tcx
                .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(cx.mono(*el)))
                .map_err(|e| format!("subslice element layout_of failed: {e:?}"))?;
            tal.size.align_to(tal.align.abi).bytes()
        }
        other => {
            return Err(format!(
                "subslice reborrow of non-slice pointee: {other:?}"
            ))
        }
    };
    // data' = data + from * stride.
    let data2 = if from == 0 {
        data
    } else {
        gep_byte_offset(fb, data, from * stride)
    };
    // len' per MIR Subslice semantics.
    let len2 = if from_end {
        let k = fb.iconst(TIRTy::U64, (from + to) as i128);
        fb.sub(TIRTy::U64, len, k)
    } else {
        let n = to
            .checked_sub(from)
            .ok_or_else(|| "subslice reborrow: to < from".to_string())?;
        fb.iconst(TIRTy::U64, n as i128)
    };
    let dst_addr = place_address(cx, fb, env, dst)?;
    fb.store(TIRTy::Ptr, dst_addr, data2);
    let dst_meta = gep_byte_offset(fb, dst_addr, 8);
    fb.store(TIRTy::U64, dst_meta, len2);
    Ok(())
}

/// Copy a 16-byte fat pointer's two pointer-width lanes from `src`'s slot to `dst`'s
/// slot (data ptr at offset 0, metadata at offset 8). Both places are addressed
/// through the memory-place path.
fn lower_fat_lane_copy<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    env: &HashMap<Local, trust_ir::ValueId>,
    dst: &Place<'tcx>,
    src: &Place<'tcx>,
) -> Result<(), String> {
    let dst_addr = place_address(cx, fb, env, dst)?;
    let src_addr = place_address(cx, fb, env, src)?;
    // Lane 0 (data ptr) at offset 0; lane 1 (metadata) at offset 8. Copy both as
    // I64 (pointer-width; the bits are preserved regardless of Ptr/usize typing).
    for off in [0u64, 8] {
        let sa = if off == 0 { src_addr } else { gep_byte_offset(fb, src_addr, off) };
        let da = if off == 0 { dst_addr } else { gep_byte_offset(fb, dst_addr, off) };
        let v = fb.load(TIRTy::I64, sa);
        fb.store(TIRTy::I64, da, v);
    }
    Ok(())
}

/// GENERAL fat reborrow (THREADS): store `(base.data + tail_offset, base.metadata)`
/// into `dst`'s 2-lane fat slot, where the fat-pointer CELL is addressed by
/// `base_local` + the sized `prefix` projection walk, and `suffix` is a chain of
/// Field descents through UNSIZED-TAIL structs in the pointee (each a static byte
/// offset; the tail's metadata equals the whole's). Fail-closed when the final
/// leaf is SIZED — a sized leaf has no metadata, so this 2-lane store would
/// fabricate one.
#[allow(clippy::too_many_arguments)]
fn lower_fat_tail_reborrow<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    env: &mut HashMap<Local, trust_ir::ValueId>,
    dst: &Place<'tcx>,
    base_local: Local,
    prefix: &[ProjectionElem<Local, Ty<'tcx>>],
    suffix: &[ProjectionElem<Local, Ty<'tcx>>],
    carrier_ty: Ty<'tcx>,
) -> Result<(), String> {
    // Address the fat CELL: the base local's slot, then the sized prefix walk.
    let base_addr = place_address(cx, fb, env, &Place::from(base_local))?;
    let cell_addr = if prefix.is_empty() {
        base_addr
    } else {
        walk_projection_address(
            cx,
            fb,
            env,
            base_addr,
            cx.local_concrete_ty(base_local),
            prefix,
            None,
        )?
    };
    // Load both lanes of the fat pointer.
    let data = fb.load(TIRTy::Ptr, cell_addr);
    let meta_addr = gep_byte_offset(fb, cell_addr, 8);
    let meta = fb.load(TIRTy::I64, meta_addr);
    // Accumulate the static byte offsets of the unsized-tail Field descents.
    let pointee = fat_pointer_pointee(cx.tcx, carrier_ty)
        .ok_or_else(|| "fat reborrow: carrier has no pointee".to_string())?;
    let lcx = LayoutCx::new(cx.tcx, ty::TypingEnv::fully_monomorphized());
    let mut layout = cx
        .tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(cx.mono(pointee)))
        .map_err(|e| format!("fat reborrow pointee layout_of failed: {e:?}"))?;
    let mut tail_off: u64 = 0;
    for elem in suffix {
        match elem {
            ProjectionElem::Field(field, _) => {
                tail_off += layout.fields.offset(field.index()).bytes();
                layout = layout.field(&lcx, field.index());
            }
            other => {
                return Err(format!(
                    "fat reborrow suffix element {other:?} not supported"
                ))
            }
        }
    }
    if layout.is_sized() {
        return Err(format!(
            "fat reborrow leaf is SIZED ({}) — metadata lane would be fabricated",
            ty_family(layout.ty)
        ));
    }
    let data = if tail_off == 0 {
        data
    } else {
        gep_byte_offset(fb, data, tail_off)
    };
    // Store the (data, metadata) pair into dst's 2-lane slot.
    let dst_addr = place_address(cx, fb, env, dst)?;
    fb.store(TIRTy::Ptr, dst_addr, data);
    let dst_meta = gep_byte_offset(fb, dst_addr, 8);
    fb.store(TIRTy::I64, dst_meta, meta);
    Ok(())
}

/// R2: lower a fat-pointer DESTINATION produced by a bit-preserving `Transmute` /
/// `PtrToPtr` cast (`*const str` <-> `&str`, `*const [T]` <-> `*mut [U]`, a
/// 16-byte 2-field struct <-> a fat raw pointer). Both carrier types are the same
/// size, so the reinterpret copies bytes verbatim:
///   * a str/byte LITERAL source stores the materialized (ptr, len) pair;
///   * a PLACE source copies the source slot's bytes (guarded: src size == dst
///     size, so the copy reads exactly the 2-lane fat image and never over-reads).
/// Any other source (a non-str constant, an unsized/size-mismatched value) fails
/// loud — we never store a truncated / over-read image into a fat slot.
fn lower_fat_reinterpret_assign<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    env: &mut HashMap<Local, trust_ir::ValueId>,
    dst: &Place<'tcx>,
    src_op: &Operand<'tcx>,
) -> Result<(), String> {
    match src_op {
        // A str/byte LITERAL reinterpreted into a fat pointer: store its
        // materialized (ptr, len) pair — identical to the `Use(Constant)` str arm.
        Operand::Constant(c) if str_const_bytes(cx, c).is_some() => {
            let mat = str_const_mat(cx, c)?;
            let (data_ptr, len) = (mat.data_ptr, mat.len);
            let dst_addr = place_address(cx, fb, env, dst)?;
            fb.store(TIRTy::Ptr, dst_addr, data_ptr);
            let meta_addr = gep_byte_offset(fb, dst_addr, 8);
            let len_v = fb.iconst(TIRTy::U64, len as i128);
            fb.store(TIRTy::U64, meta_addr, len_v);
            Ok(())
        }
        // A PLACE source of the SAME size as the fat destination: byte-preserving
        // lane copy of the whole 2-lane image.
        Operand::Copy(src) | Operand::Move(src) => {
            let (dsize, dalign) = memory_layout_size_align(cx, cx.place_concrete_ty(dst))?;
            let (ssize, _salign) = memory_layout_size_align(cx, cx.place_concrete_ty(src))?;
            if ssize != dsize {
                return Err(format!(
                    "fat reinterpret size mismatch: src {ssize} != dst {dsize}"
                ));
            }
            let dst_addr = place_address(cx, fb, env, dst)?;
            let src_addr = place_address(cx, fb, env, src)?;
            copy_aggregate_bytes(fb, src_addr, dst_addr, dsize, dalign)
        }
        _ => Err("fat-pointer reinterpret source not a place / str literal".to_string()),
    }
}

/// Lower `dst = Aggregate(RawPtr, [data, meta])` into a fat raw-pointer slot: the
/// data pointer (op 0) at lane 0, the metadata (op 1, a `usize` slice length or a
/// vtable `*const ()`) at lane 1 (+8). This is the `ptr::from_raw_parts` shape a
/// fat raw pointer is constructed by. A ZST/absent metadata operand is treated as
/// a thin construction (no lane-1 store); fails loud if the operand list is not
/// the expected (data, meta) pair.
fn lower_raw_ptr_from_parts<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    env: &mut HashMap<Local, trust_ir::ValueId>,
    dst: &Place<'tcx>,
    ops: &rustc_index::IndexVec<rustc_abi::FieldIdx, Operand<'tcx>>,
) -> Result<(), String> {
    if ops.len() != 2 {
        return Err(format!(
            "RawPtr aggregate has {} operands (expected data + metadata)",
            ops.len()
        ));
    }
    let mut it = ops.iter();
    let data_op = it.next().expect("checked len == 2");
    let meta_op = it.next().expect("checked len == 2");
    let dst_addr = place_address(cx, fb, env, dst)?;
    // Lane 0: the data pointer.
    let (data, _dt) = lower_operand(cx, fb, env, data_op)?;
    fb.store(TIRTy::Ptr, dst_addr, data);
    // Lane 1: the metadata (`usize` length / vtable ptr) at +8.
    let (meta, mt) = lower_operand(cx, fb, env, meta_op)?;
    let meta_addr = gep_byte_offset(fb, dst_addr, 8);
    let store_ty = if is_ptr_tir(&mt) { TIRTy::Ptr } else { TIRTy::U64 };
    fb.store(store_ty, meta_addr, meta);
    Ok(())
}

// ================= ADDITIVE (R3 stage 1): &str-CONSTANT lowering ==============
//
// A `&'static str` / `&'static [u8]` LITERAL is a FAT-POINTER CONSTANT: a
// (data ptr into rodata, byte length) pair, `ConstValue::Slice` after const-eval.
// Until now every such constant failed loud ("call arg constant of non-scalar
// type ref" / "fat-pointer dst from unmodelable rvalue") because the lowering had
// nowhere to put the bytes: trust-ir HAS module globals + `GlobalAddr` (and the
// OBJECT/link path lowers them, `e2e_aarch64_read_global.rs`), but the in-process
// JIT that executes every verification round-trip resolves ONLY Branch26 code
// fixups — an ADRP/Page21 DATA relocation is unresolvable there today (trust-cg
// `jit.rs::patch_fixup` = `patch_branch26`). So rodata-by-symbol cannot round-trip.
//
// DESIGN: materialize each DISTINCT literal ONCE per function, in the ENTRY
// block, as
//   * an IMMORTAL heap byte image — `heap_alloc(I8, len, align 1, RustHeap)` +
//     one byte-Store per literal byte (literals in the verified kernel surfaces
//     are short: ".rec", overflow-context messages, name segments); heap, never
//     freed, so ESCAPING references (returned literals, literals stored into
//     outliving structures) remain valid exactly like `&'static` rodata — the
//     same `__rust_alloc` trust boundary as the landed `Arc::new` lowering;
//   * a 16-byte (ptr,len) FAT-PAIR SLOT (stack alloca, [Ptr at +0, U64 len at
//     +8]) whose ADDRESS is the `ArgAbi::AggByRef` call-arg value — precisely
//     the convention a lowered callee already models a fat `&str` param with.
//
// MODELED BOUNDARY (documented for every consumer): ADDRESS IDENTITY and
// ALLOCATION COUNT. Native Rust places a literal in rodata (one stable address
// for the program's life; zero allocations). This lowering allocates one image
// per (function, literal) per INVOCATION and leaks it. Value semantics — the
// bytes and the length — are exact; a program that COMPARES literal ADDRESSES
// across calls or counts allocator traffic would diverge. No verified surface
// does either. When the JIT gains data-relocation support, these literals should
// move to true module globals (`ModuleBuilder::add_global` + `fb.global_addr`).

/// The literal BYTES of a `&'static str` / `&'static [u8]` CONSTANT operand, or
/// `None` when `c` is not such a constant. Type-gated by `is_str_or_byteslice_ref`
/// (a fat `&str`/`&[u8]` only — a thin `&[u8; N]` array ref is NOT admitted), then
/// const-evaluated; only a slice-repr value (`ConstValue::Slice` / `Indirect`)
/// carries literal bytes (`try_get_slice_bytes_for_diagnostics` reads the exact
/// allocation bytes; the variant guard keeps its Scalar/ZeroSized `bug!` path
/// unreachable).
fn str_const_bytes<'tcx>(cx: &Cx<'tcx, '_>, c: &ConstOperand<'tcx>) -> Option<Vec<u8>> {
    let cty = cx.mono(c.const_.ty());
    if !is_str_or_byteslice_ref(cty) {
        return None;
    }
    let ct = cx.instance.instantiate_mir_and_normalize_erasing_regions(
        cx.tcx,
        ty::TypingEnv::fully_monomorphized(),
        ty::EarlyBinder::bind(cx.tcx, c.const_),
    );
    let cv = ct
        .eval(cx.tcx, ty::TypingEnv::fully_monomorphized(), c.span)
        .ok()?;
    if !matches!(cv, ConstValue::Slice { .. } | ConstValue::Indirect { .. }) {
        return None;
    }
    cv.try_get_slice_bytes_for_diagnostics(cx.tcx)
        .map(|b| b.to_vec())
}

/// Pre-scan the body for every `&'static str` / `&'static [u8]` LITERAL the
/// lowering will consume, in FIRST-APPEARANCE order, deduped by CONTENT. Covers
/// exactly the two consumer sites this stage lowers: (a) a `Call` terminator's
/// constant args, (b) a `Use(Constant)` assign into a fat-pointer destination.
/// Cleanup blocks are skipped under panic=abort (the lowering never emits them
/// there); the EH lane emits cleanup blocks, so it scans them too. Any OTHER
/// appearance of a fat constant still fails loud at its consumer, so the scan
/// and the consumers agree by construction.
fn prescan_str_consts<'tcx>(cx: &Cx<'tcx, '_>, body: &Body<'tcx>) -> Vec<Vec<u8>> {
    let eh = eh_lane(cx.tcx);
    let mut out: Vec<Vec<u8>> = Vec::new();
    for (_bb, data) in body.basic_blocks.iter_enumerated() {
        if data.is_cleanup && !eh {
            continue;
        }
        for stmt in &data.statements {
            if let StatementKind::Assign(bx) = &stmt.kind {
                let (place, rvalue) = &**bx;
                // The two literal-consuming assign shapes:
                //   * `fat_place = const "lit"` (`Rvalue::Use`), and
                //   * `fat_place = const "lit" as *const str / transmute` — the
                //     bit-preserving CAST route `lower_fat_reinterpret_assign`
                //     consumes (same guard as that consumer: literal + fat dst).
                let cast_or_use_const = match rvalue {
                    Rvalue::Use(Operand::Constant(c), _) => Some(c),
                    Rvalue::Cast(_, Operand::Constant(c), _) => Some(c),
                    _ => None,
                };
                if let Some(c) = cast_or_use_const {
                    if ty_is_fat_pointer_place(cx, place) {
                        if let Some(b) = str_const_bytes(cx, c) {
                            if !out.contains(&b) {
                                out.push(b);
                            }
                        }
                    }
                }
            }
        }
        if let Some(term) = &data.terminator {
            if let TerminatorKind::Call { args, .. } = &term.kind {
                for a in args.iter() {
                    if let Operand::Constant(c) = &a.node {
                        if let Some(b) = str_const_bytes(cx, c) {
                            if !out.contains(&b) {
                                out.push(b);
                            }
                        }
                    }
                }
            }
        }
    }
    out
}

/// Materialize each pre-scanned literal in the ENTRY block (the caller has `fb`
/// switched there, after the memory-local allocas): the immortal heap byte image,
/// its byte Stores, and the (ptr,len) fat-pair slot. Records each into
/// `cx.str_consts`. A function with no literals emits NOTHING (no-drift).
fn materialize_str_consts<'tcx>(
    cx: &mut Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    literals: Vec<Vec<u8>>,
) -> Result<(), String> {
    for bytes in literals {
        let len = bytes.len() as u64;
        // Lower the literal's bytes to a READ-ONLY module global (rodata) and take
        // its ADDRESS, rather than a runtime `heap_alloc` + per-byte Stores. A
        // `&'static str` / `&'static [u8]` is immutable static data with 'static
        // lifetime — a frozen `Bytes` global (Internal linkage) models that exactly,
        // with NO allocation. The old heap materialization forced an UNCONDITIONAL
        // `__rust_alloc` at entry of every fn mentioning a literal (e.g. the
        // `debug_assert!` message string in `RawVecInner::grow_amortized`), which
        // both leaked and perturbed the allocator happy path.
        let gid = intern_str_literal_global(cx, &bytes);
        let img = fb.global_addr(gid);
        // The (ptr,len) fat-pair slot: the standard 16-byte 2-lane fat slot shape
        // (`slot_lane_ty(16, 8)`), lane 0 = data Ptr, lane 1 = U64 length — the
        // exact lane discipline `lower_unsize_assign` established.
        let pair_ptr = fb.alloca_aligned(slot_lane_ty(16, 8)?, 8);
        fb.note_alloc_extent(pair_ptr, 16);
        fb.store(TIRTy::Ptr, pair_ptr, img);
        let meta_addr = gep_byte_offset(fb, pair_ptr, 8);
        let len_v = fb.iconst(TIRTy::U64, len as i128);
        fb.store(TIRTy::U64, meta_addr, len_v);
        cx.str_consts.push((
            bytes,
            StrConstMat {
                data_ptr: img,
                pair_ptr,
                len,
            },
        ));
    }
    Ok(())
}

/// Look up the materialized image/pair for a literal constant operand. Fails
/// loud if the operand is not a str/byte-slice literal or the pre-scan missed it
/// (a scan/consumer disagreement would be a bug — never silent).
fn str_const_mat<'a, 'tcx>(
    cx: &'a Cx<'tcx, '_>,
    c: &ConstOperand<'tcx>,
) -> Result<&'a StrConstMat, String> {
    let bytes = str_const_bytes(cx, c)
        .ok_or_else(|| "str-const: operand is not a str/byte-slice literal".to_string())?;
    cx.str_consts
        .iter()
        .find(|(b, _)| *b == bytes)
        .map(|(_, m)| m)
        .ok_or_else(|| "str-const literal not materialized (pre-scan bug)".to_string())
}

/// Map a MIR checked-overflow `BinOp` to a trust-ir `OverflowOp`, or `None` for a
/// non-checked op.
fn checked_overflow_op(op: MirBinOp) -> Option<OverflowOp> {
    match op {
        MirBinOp::AddWithOverflow => Some(OverflowOp::AddOverflow),
        MirBinOp::SubWithOverflow => Some(OverflowOp::SubOverflow),
        MirBinOp::MulWithOverflow => Some(OverflowOp::MulOverflow),
        _ => None,
    }
}

/// Lower a `dest = <op>WithOverflow(lhs, rhs)` into a `(scalar, bool)` tuple
/// destination: compute `(result, flag)` via `fb.overflow`, then Store `result`
/// at the destination's field-0 address and `flag` at field-1. The destination
/// MUST be a memory-backed 2-field tuple `(scalar, bool)` whose fields are
/// single-scalar leaves (the canonical debug checked-arith temp); anything else
/// fails loud (RUNG 3 aggregate). The result/flag scalar widths are taken from
/// the destination's two field leaf types so the Store types match.
fn lower_checked_overflow_assign<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    env: &mut HashMap<Local, trust_ir::ValueId>,
    place: &Place<'tcx>,
    ovf: OverflowOp,
    operands: &(Operand<'tcx>, Operand<'tcx>),
) -> Result<(), String> {
    let (lhs_op, rhs_op) = operands;
    // The destination tuple's layout (field 0 = scalar result, field 1 = bool
    // overflow flag) — used both for the result width and the field byte offsets.
    let dst_ty = cx.place_concrete_ty(place);
    let (res_ty, flag_ty, off0, off1) = checked_tuple_layout(cx, dst_ty)?;
    if !matches!(flag_ty, TIRTy::Bool) {
        return Err(format!("checked-overflow dest field 1 is not bool: {flag_ty:?}"));
    }
    let (lhs, _lt) = lower_operand(cx, fb, env, lhs_op)?;
    let (rhs, _rt) = lower_operand(cx, fb, env, rhs_op)?;
    let (result, flag) = fb.overflow(ovf, res_ty.clone(), lhs, rhs);

    // The destination tuple's BASE address (a memory-backed local, possibly itself
    // projected). Then byte-offset GEP to each field and Store.
    let base = place_address(cx, fb, env, place)?;
    let a0 = if off0 == 0 { base } else { gep_byte_offset(fb, base, off0) };
    fb.store(res_ty, a0, result);
    let a1 = if off1 == 0 { base } else { gep_byte_offset(fb, base, off1) };
    fb.store(TIRTy::Bool, a1, flag);
    Ok(())
}

/// The result/flag leaf types and the two field BYTE OFFSETS of a 2-field tuple
/// `(scalar, bool)` checked-overflow destination, from `layout_of`. Fails loud on
/// anything that is not a 2-element tuple of single-scalar leaves.
fn checked_tuple_layout<'tcx>(
    cx: &Cx<'tcx, '_>,
    dst_ty: Ty<'tcx>,
) -> Result<(TIRTy, TIRTy, u64, u64), String> {
    let ty::Tuple(elems) = dst_ty.kind() else {
        return Err(format!(
            "checked-overflow dest is not a tuple: {}",
            ty_family(dst_ty)
        ));
    };
    if elems.len() != 2 {
        return Err(format!(
            "checked-overflow dest tuple has {} fields (expected 2)",
            elems.len()
        ));
    }
    let res_ty = memory_leaf_tir_ty(cx.tcx, cx.mono(elems[0])).ok_or_else(|| {
        format!(
            "checked-overflow result field not a scalar leaf: {}",
            ty_family(elems[0])
        )
    })?;
    let flag_ty = memory_leaf_tir_ty(cx.tcx, cx.mono(elems[1])).ok_or_else(|| {
        format!(
            "checked-overflow flag field not a scalar leaf: {}",
            ty_family(elems[1])
        )
    })?;
    let layout = cx
        .tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(dst_ty))
        .map_err(|e| format!("checked-overflow tuple layout_of failed: {e:?}"))?;
    let off0 = layout.fields.offset(0).bytes();
    let off1 = layout.fields.offset(1).bytes();
    Ok((res_ty, flag_ty, off0, off1))
}

// ============================ RUNG 3: faithful enum layout ===================
//
// A self-contained re-derivation (in the `trust_ir_mir` BINARY crate, which does
// not link the `trust_ir_frontend` lib's `enum_layout_of`) of the M6 FAITHFUL
// enum layout: the tag READ offset + width, the Direct/Niche encoding, and each
// variant's Switch discriminant VALUE + per-field byte offsets, all from
// `tcx.layout_of` + `rustc_abi::{Variants, TagEncoding}` — never hand-coded.

/// How a variant's discriminant is encoded in memory.
#[derive(Clone)]
enum MirTagEncoding {
    /// The tag word holds the discriminant directly. Every variant has a Switch
    /// value (its discriminant).
    Direct,
    /// The discriminant is encoded as a niche in a payload field: the
    /// `untagged_variant` writes NO niche (Switch default); each niche variant `v`
    /// writes `niche_start + (v - niche_variants_start)` (wrapping, tag-width
    /// masked).
    Niche {
        untagged_variant: VariantIdx,
        niche_variants_start: VariantIdx,
        niche_start: u128,
    },
}

/// The faithful in-memory enum layout (the subset RUNG 3 needs).
struct MirEnumLayout {
    /// Byte offset the tag/niche is READ/written at.
    tag_offset: u64,
    /// trust-ir integer type to Load/Store the tag with (I8/I16/I32/I64).
    tag_ir_ty: TIRTy,
    /// Whether reading the discriminant may sign-extend the loaded tag. FALSE only
    /// when rustc's tag is UNSIGNED *and* some discriminant, truncated to the tag
    /// width, has its high bit set — the [F5] case (e.g. a >128-variant no-repr enum:
    /// discriminant 201 in a 1-byte tag sign-extends to −55 and misses its unsigned
    /// SwitchInt key 201, so the arm aborts). Then the tag must ZERO-extend. For every
    /// enum whose discriminants fit the tag's signed range, sext and zext are identical,
    /// so this stays TRUE and the emit is byte-unchanged (no-drift gate preserved).
    read_signed: bool,
    encoding: MirTagEncoding,
    /// Per-variant: the Switch VALUE (None for the niche untagged variant) and the
    /// per-field byte offsets (variant-relative, == whole-struct offsets since
    /// `for_variant` offsets are absolute).
    variants: Vec<(Option<i128>, Vec<u64>)>,
}

/// Map a tag scalar's byte width to the trust-ir integer Load/Store type.
fn tag_ir_ty_for_bytes(bytes: u64) -> Result<TIRTy, String> {
    match bytes {
        1 => Ok(TIRTy::I8),
        2 => Ok(TIRTy::I16),
        4 => Ok(TIRTy::I32),
        8 => Ok(TIRTy::I64),
        // ADDITIVE (Option<u128>/Option<i128> class): a u128/i128 payload has no
        // niche, so rustc lays the enum out with a SEPARATE 16-byte Direct tag
        // field. trust-cg carries i128 values (register-pair Load/Store/Icmp/Const,
        // VERIFIED), so a 16-byte tag lowers as an i128 Load + i128 Switch — the
        // discriminant is then truncated to the destination width by `cast_int`,
        // exactly as the 1/2/4/8 cases are widened/narrowed. The 1/2/4/8 arms above
        // are untouched (byte-identical re-emit gate).
        16 => Ok(TIRTy::I128),
        other => Err(format!(
            "enum discriminant tag is {other} bytes wide (no trust-ir Load width 1/2/4/8/16)"
        )),
    }
}

/// Sign-extend a tag-width-masked `u128` to the `i128` the trust-ir Switch /
/// Constant::Int carries (matching a signed-int typed Load of width `tag_bytes`).
fn tag_u128_to_i128(masked: u128, tag_bytes: u64) -> Result<i128, String> {
    // ADDITIVE (16-byte tag): a full-width 16-byte tag carries the whole 128-bit
    // pattern; a signed i128 Load reinterprets those bits verbatim, so the Switch
    // value is `masked as i128` (no sign-extend from a sub-128 width). `masked` was
    // already truncated to 16 bytes (the full width), so this is lossless. The
    // sub-16-byte path below is unchanged (byte-identical re-emit gate).
    if tag_bytes >= 16 {
        if tag_bytes == 16 {
            return Ok(masked as i128);
        }
        return Err(format!("enum tag is {tag_bytes} bytes (>16-byte tag unsupported)"));
    }
    Ok(Size::from_bytes(tag_bytes).sign_extend(masked))
}

/// Compute the faithful `MirEnumLayout` for an enum ADT type via `tcx.layout_of`.
/// Mirrors the M6 `enum_layout_of` in lib.rs (Direct + Niche), restricted to what
/// RUNG 3 SetDiscriminant / Discriminant / Aggregate construction need.
fn mir_enum_layout<'tcx>(cx: &Cx<'tcx, '_>, enum_ty: Ty<'tcx>) -> Result<MirEnumLayout, String> {
    let ty::Adt(adt, _) = enum_ty.kind() else {
        return Err(format!("enum layout of non-ADT: {}", ty_family(enum_ty)));
    };
    if !adt.is_enum() {
        return Err(format!("enum layout of non-enum ADT: {}", ty_family(enum_ty)));
    }
    let lcx = LayoutCx::new(cx.tcx, ty::TypingEnv::fully_monomorphized());
    let tal = cx
        .tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(enum_ty))
        .map_err(|e| format!("enum layout_of failed: {e:?}"))?;

    let variant_field_offsets = |idx: VariantIdx| -> Vec<u64> {
        let vlayout = tal.for_variant(&lcx, idx);
        let vdef = adt.variant(idx);
        (0..vdef.fields.len())
            .map(|i| vlayout.fields.offset(i).bytes())
            .collect()
    };

    match &tal.variants {
        // A single-inhabited-variant enum: no tag word; the one variant is always
        // selected (degenerate Switch value 0 at offset 0). Construction needs only
        // the field offsets; SetDiscriminant of the single variant writes nothing.
        Variants::Single { index } => {
            let idx = *index;
            let mut variants = Vec::with_capacity(adt.variants().len());
            for (vidx, _v) in adt.variants().iter_enumerated() {
                if vidx == idx {
                    variants.push((Some(0i128), variant_field_offsets(idx)));
                } else {
                    variants.push((None, Vec::new()));
                }
            }
            Ok(MirEnumLayout {
                tag_offset: 0,
                tag_ir_ty: TIRTy::I8,
                // Single-variant enum: the sole discriminant is materialized as an
                // iconst (no tag load), so signedness is moot; default to signed.
                read_signed: true,
                encoding: MirTagEncoding::Direct,
                variants,
            })
        }
        Variants::Multiple {
            tag,
            tag_encoding,
            tag_field,
            ..
        } => {
            let tag_offset = tal.fields.offset(tag_field.index()).bytes();
            let tag_bytes = tag.size(&cx.tcx).bytes();
            let tag_ir_ty = tag_ir_ty_for_bytes(tag_bytes)?;
            // [F5] read-signedness: a discriminant read may sign-extend UNLESS rustc's
            // tag is unsigned AND some discriminant, truncated to the tag width, has its
            // high bit set (then sext would read it negative and miss the unsigned
            // SwitchInt key — the >128-variant no-repr enum miscompile). Values within
            // the tag's signed range extend identically either way, so this leaves the
            // emit byte-unchanged for every existing slice (no-drift gate preserved).
            let tag_is_signed = match tag.primitive() {
                Primitive::Int(_, signed) => signed,
                _ => true,
            };
            let sign_bit: u128 = 1u128 << (tag_bytes * 8 - 1);
            let has_high_bit_discr = adt.variants().iter_enumerated().any(|(idx, _)| {
                let discr = adt.discriminant_for_variant(cx.tcx, idx).val;
                Size::from_bytes(tag_bytes).truncate(discr) & sign_bit != 0
            });
            let read_signed = tag_is_signed || !has_high_bit_discr;

            let mut variants: Vec<(Option<i128>, Vec<u64>)> =
                Vec::with_capacity(adt.variants().len());
            for (idx, _v) in adt.variants().iter_enumerated() {
                variants.push((None, variant_field_offsets(idx)));
            }

            let encoding = match tag_encoding {
                TagEncoding::Direct => {
                    for (idx, _) in adt.variants().iter_enumerated() {
                        let discr = adt.discriminant_for_variant(cx.tcx, idx).val;
                        let masked = Size::from_bytes(tag_bytes).truncate(discr);
                        variants[idx.as_usize()].0 = Some(tag_u128_to_i128(masked, tag_bytes)?);
                    }
                    MirTagEncoding::Direct
                }
                TagEncoding::Niche {
                    untagged_variant,
                    niche_variants,
                    niche_start,
                } => {
                    let start = niche_variants.start.as_u32();
                    for (idx, _) in adt.variants().iter_enumerated() {
                        if idx == *untagged_variant {
                            continue;
                        }
                        if !niche_variants.contains(&idx) {
                            return Err(
                                "niche enum: variant neither untagged nor in niche range"
                                    .to_string(),
                            );
                        }
                        let rel = idx.as_u32().wrapping_sub(start) as u128;
                        let raw = rel.wrapping_add(*niche_start);
                        let masked = Size::from_bytes(tag_bytes).truncate(raw);
                        variants[idx.as_usize()].0 = Some(tag_u128_to_i128(masked, tag_bytes)?);
                    }
                    MirTagEncoding::Niche {
                        untagged_variant: *untagged_variant,
                        niche_variants_start: niche_variants.start,
                        niche_start: *niche_start,
                    }
                }
            };

            Ok(MirEnumLayout {
                tag_offset,
                tag_ir_ty,
                read_signed,
                encoding,
                variants,
            })
        }
        Variants::Empty => Err("enum layout is Variants::Empty (uninhabited)".to_string()),
    }
}

/// Compute a `MirEnumLayout` for a COROUTINE type (an `async fn` body or a
/// `gen`/coroutine closure). rustc lays a coroutine out exactly like a tagged
/// enum: a state DISCRIMINANT plus per-variant saved-local fields, over a common
/// prefix of the captured upvars. Coroutines carry NO explicit discriminant
/// values — the discriminant of variant `v` IS the variant index `v`
/// (`CoroutineArgs::discriminant_for_variant`: "Coroutines don't support explicit
/// discriminant values, so they are the same as the variant index"). So the
/// Direct tag values are the variant indices and the niche decode keys on the
/// index, byte-for-byte the same shape the enum layout produces — the only
/// difference is that variant metadata comes from the coroutine layout
/// (`for_variant` / the `Variants::Multiple` variant list), not an `AdtDef`.
fn mir_coroutine_layout<'tcx>(
    cx: &Cx<'tcx, '_>,
    coro_ty: Ty<'tcx>,
) -> Result<MirEnumLayout, String> {
    if !matches!(coro_ty.kind(), ty::Coroutine(..)) {
        return Err(format!(
            "coroutine layout of non-coroutine: {}",
            ty_family(coro_ty)
        ));
    }
    let lcx = LayoutCx::new(cx.tcx, ty::TypingEnv::fully_monomorphized());
    let tal = cx
        .tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(coro_ty))
        .map_err(|e| format!("coroutine layout_of failed: {e:?}"))?;

    let variant_field_offsets = |idx: VariantIdx| -> Vec<u64> {
        let vlayout = tal.for_variant(&lcx, idx);
        (0..vlayout.fields.count())
            .map(|i| vlayout.fields.offset(i).bytes())
            .collect()
    };

    match &tal.variants {
        // A single-state coroutine (no reachable suspend states) is tagless — the
        // one variant is always selected. (Rare; async fns with awaits are always
        // `Variants::Multiple`.)
        Variants::Single { index } => {
            let idx = *index;
            let mut variants: Vec<(Option<i128>, Vec<u64>)> =
                vec![(None, Vec::new()); idx.as_usize() + 1];
            variants[idx.as_usize()] = (Some(0i128), variant_field_offsets(idx));
            Ok(MirEnumLayout {
                tag_offset: 0,
                tag_ir_ty: TIRTy::I8,
                read_signed: true,
                encoding: MirTagEncoding::Direct,
                variants,
            })
        }
        Variants::Multiple {
            tag,
            tag_encoding,
            tag_field,
            variants: variant_layouts,
        } => {
            let tag_offset = tal.fields.offset(tag_field.index()).bytes();
            let tag_bytes = tag.size(&cx.tcx).bytes();
            let tag_ir_ty = tag_ir_ty_for_bytes(tag_bytes)?;
            let n_variants = variant_layouts.len();
            // The coroutine state discriminant is unsigned (a `u32`), and states are
            // small non-negative indices; the [F5] high-bit rule still applies if a
            // masked index sets the tag's sign bit (only for an implausibly wide
            // state count), so mirror the enum layout's read-signedness choice.
            let tag_is_signed = match tag.primitive() {
                Primitive::Int(_, signed) => signed,
                _ => true,
            };
            let sign_bit: u128 = 1u128 << (tag_bytes * 8 - 1);
            let has_high_bit_discr = (0..n_variants)
                .any(|v| Size::from_bytes(tag_bytes).truncate(v as u128) & sign_bit != 0);
            let read_signed = tag_is_signed || !has_high_bit_discr;

            let mut variants: Vec<(Option<i128>, Vec<u64>)> = Vec::with_capacity(n_variants);
            for i in 0..n_variants {
                variants.push((None, variant_field_offsets(VariantIdx::from_usize(i))));
            }

            let encoding = match tag_encoding {
                TagEncoding::Direct => {
                    for i in 0..n_variants {
                        // discriminant == variant index for coroutines.
                        let masked = Size::from_bytes(tag_bytes).truncate(i as u128);
                        variants[i].0 = Some(tag_u128_to_i128(masked, tag_bytes)?);
                    }
                    MirTagEncoding::Direct
                }
                TagEncoding::Niche {
                    untagged_variant,
                    niche_variants,
                    niche_start,
                } => {
                    let start = niche_variants.start.as_u32();
                    for i in 0..n_variants {
                        let idx = VariantIdx::from_usize(i);
                        if idx == *untagged_variant {
                            continue;
                        }
                        if !niche_variants.contains(&idx) {
                            return Err(
                                "niche coroutine: variant neither untagged nor in niche range"
                                    .to_string(),
                            );
                        }
                        let rel = idx.as_u32().wrapping_sub(start) as u128;
                        let raw = rel.wrapping_add(*niche_start);
                        let masked = Size::from_bytes(tag_bytes).truncate(raw);
                        variants[i].0 = Some(tag_u128_to_i128(masked, tag_bytes)?);
                    }
                    MirTagEncoding::Niche {
                        untagged_variant: *untagged_variant,
                        niche_variants_start: niche_variants.start,
                        niche_start: *niche_start,
                    }
                }
            };

            Ok(MirEnumLayout {
                tag_offset,
                tag_ir_ty,
                read_signed,
                encoding,
                variants,
            })
        }
        Variants::Empty => {
            Err("coroutine layout is Variants::Empty (uninhabited)".to_string())
        }
    }
}

/// Whether an enum type's layout is `Variants::Empty` — a fully UNINHABITED
/// enum (`Infallible`, `!`-carrying `Result` monos). No value of it can exist,
/// so every runtime operation on one is dynamically dead: rustc codegens a
/// discriminant read of one as `poison` and never materializes a construction.
fn enum_layout_is_empty<'tcx>(cx: &Cx<'tcx, '_>, ty: Ty<'tcx>) -> bool {
    match cx
        .tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(ty))
    {
        Ok(tal) => matches!(tal.variants, Variants::Empty),
        Err(_) => false,
    }
}

// ============================ RUNG 3: SetDiscriminant ========================

/// Lower `SetDiscriminant { place, variant_index }` — write the variant's tag/
/// niche into a memory-backed enum place at the faithful layout offset/width. The
/// place is a bare memory-backed enum LOCAL or a `(*ptr)` deref; the enum's
/// `MirEnumLayout` supplies the offset/width/encoding + the discriminant value.
fn lower_set_discriminant<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    env: &HashMap<Local, trust_ir::ValueId>,
    place: &Place<'tcx>,
    variant_index: VariantIdx,
) -> Result<(), String> {
    // The enum TYPE the place addresses (the whole enum, before the Downcast a
    // sibling Field projection would add — SetDiscriminant's place is the enum
    // itself, possibly through a single leading Deref).
    let enum_ty = cx.place_concrete_ty(place);
    // A fully-uninhabited enum (`Variants::Empty`): the statement is
    // dynamically dead (no value of the type exists to set a tag on) — rustc
    // parity is to emit nothing.
    if enum_layout_is_empty(cx, enum_ty) {
        return Ok(());
    }
    // A coroutine `SetDiscriminant` (`discriminant((*self)) = N`) writes the state
    // tag at each suspend/return point; it uses the coroutine layout, which — like
    // the enum layout — records the per-variant Direct/niche tag value to store.
    let layout = if matches!(enum_ty.kind(), ty::Coroutine(..)) {
        mir_coroutine_layout(cx, enum_ty)?
    } else {
        mir_enum_layout(cx, enum_ty)?
    };
    // The enum's base address (the slot, or the loaded pointer for `(*r)`).
    let base = place_address(cx, fb, env, place)?;

    match &layout.encoding {
        MirTagEncoding::Direct => {
            let Some(disc) = layout.variants.get(variant_index.as_usize()).and_then(|v| v.0) else {
                // A single-variant enum (Variants::Single): no tag to write.
                return Ok(());
            };
            store_tag(fb, base, layout.tag_offset, &layout.tag_ir_ty, disc);
            Ok(())
        }
        MirTagEncoding::Niche {
            untagged_variant, ..
        } => {
            if variant_index == *untagged_variant {
                // The untagged (default) variant writes NO niche — its payload's
                // own value occupies the niche field. Nothing to store.
                return Ok(());
            }
            let Some(disc) = layout.variants.get(variant_index.as_usize()).and_then(|v| v.0) else {
                return Err("SetDiscriminant niche variant has no encoded value".to_string());
            };
            store_tag(fb, base, layout.tag_offset, &layout.tag_ir_ty, disc);
            Ok(())
        }
    }
}

/// Store a tag value of width `tag_ir_ty` at `base + tag_offset` (a byte-offset
/// GEP then a typed Store).
fn store_tag(
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    base: trust_ir::ValueId,
    tag_offset: u64,
    tag_ir_ty: &TIRTy,
    value: i128,
) {
    let addr = if tag_offset == 0 {
        base
    } else {
        gep_byte_offset(fb, base, tag_offset)
    };
    let v = fb.iconst(tag_ir_ty.clone(), value);
    fb.store(tag_ir_ty.clone(), addr, v);
}

// ============================ RUNG 3: Discriminant read ======================

/// Lower `dst = Discriminant(src)` — read the variant discriminant of a memory-
/// backed enum `src` into a scalar destination. For a Direct encoding the loaded
/// tag IS the discriminant the guarding `SwitchInt` compares (zero/sign-extended
/// to the destination width). A Niche encoding is decoded with the standard niche
/// formula. A single-variant (tagless) enum yields the static discriminant 0.
fn lower_discriminant_assign<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    env: &mut HashMap<Local, trust_ir::ValueId>,
    dst: &Place<'tcx>,
    src: &Place<'tcx>,
) -> Result<(), String> {
    // The destination scalar type (the `isize`/`iN` tag temp).
    let dst_ty = dst_scalar_ty(cx, dst)?;
    let enum_ty = cx.place_concrete_ty(src);
    // MIR semantics (THREADS): `Discriminant` of a type WITHOUT a discriminant
    // (a tuple / struct / primitive — e.g. the `(A, B)` state pair inside
    // `Zip::size` and `IntoIter::as_raw_mut_slice`) is defined as ZERO — the
    // same rule rustc's own codegen applies. Only enum/coroutine ADTs carry a
    // real tag; everything else short-circuits to `0` here so the enum-layout
    // machinery below stays enum-only and fail-loud.
    // A COROUTINE also carries a (state) discriminant — the resume state machine's
    // opening `SwitchInt(discriminant((*self)))` dispatch reads it. A coroutine is
    // laid out like a Direct-tagged enum (discriminant == variant index), so the
    // read is the enum Direct path over the coroutine layout: load the state tag
    // and extend it to the destination width.
    if matches!(enum_ty.kind(), ty::Coroutine(..)) {
        let layout = mir_coroutine_layout(cx, enum_ty)?;
        let result = if !multi_variant_has_tag(&layout) {
            // A single-state coroutine is tagless; the discriminant is statically 0.
            fb.iconst(dst_ty.clone(), 0)
        } else {
            match &layout.encoding {
                MirTagEncoding::Direct => {
                    let base = place_address(cx, fb, env, src)?;
                    let tag = load_tag(fb, base, layout.tag_offset, &layout.tag_ir_ty);
                    cast_int_ext(fb, tag, &layout.tag_ir_ty, &dst_ty, layout.read_signed)
                }
                MirTagEncoding::Niche {
                    untagged_variant,
                    niche_variants_start,
                    niche_start,
                } => {
                    // A niche-encoded coroutine state tag decodes with the SAME
                    // formula as a niche enum, and the decode's discriminant ==
                    // variant-index requirement holds BY CONSTRUCTION for
                    // coroutines (`CoroutineArgs::discriminant_for_variant`), so
                    // reuse the shared select-chain decode keyed on the coroutine
                    // layout. NOTE: rustc 1.99 hardcodes `TagEncoding::Direct`
                    // for every coroutine layout (rustc_abi/src/layout/
                    // coroutine.rs, `tag_encoding: TagEncoding::Direct`) — even a
                    // `&T` held across an `.await` keeps a 1-byte Direct tag
                    // (verified via `-Zprint-type-sizes` on the wholeprog19
                    // borrow-across-await corpus). This arm is faithful-parity
                    // insurance for a future rustc that niches coroutine tags,
                    // not a shape today's layouts can produce.
                    let (uv, nvs, ns) = (*untagged_variant, *niche_variants_start, *niche_start);
                    lower_niche_discriminant(
                        cx, fb, env, src, &layout, &dst_ty, uv, nvs, ns,
                    )?
                }
            }
        };
        if dst.projection.is_empty() {
            if let Some(LocalModel::Ssa(_)) = cx.model.get(&dst.local) {
                env.insert(dst.local, result);
                return Ok(());
            }
        }
        let leaf = place_leaf_tir_ty(cx, dst)?;
        let addr = place_address(cx, fb, env, dst)?;
        fb.store(leaf, addr, result);
        return Ok(());
    }
    // A fully-uninhabited enum (`Variants::Empty` — `Infallible` / `!`-carrying
    // monos): the read is dynamically dead (rustc codegens `poison` here). Any
    // constant is a faithful lowering of a poison the program can never
    // observe; bind 0 like the no-discriminant case below.
    if matches!(enum_ty.kind(), ty::Adt(adt, _) if adt.is_enum())
        && enum_layout_is_empty(cx, enum_ty)
    {
        let zero = fb.iconst(dst_ty.clone(), 0);
        if dst.projection.is_empty() {
            if let Some(LocalModel::Ssa(_)) = cx.model.get(&dst.local) {
                env.insert(dst.local, zero);
                return Ok(());
            }
        }
        let leaf = place_leaf_tir_ty(cx, dst)?;
        let addr = place_address(cx, fb, env, dst)?;
        fb.store(leaf, addr, zero);
        return Ok(());
    }
    let is_enum_like = matches!(enum_ty.kind(), ty::Adt(adt, _) if adt.is_enum());
    if !is_enum_like {
        let zero = fb.iconst(dst_ty.clone(), 0);
        if dst.projection.is_empty() {
            if let Some(LocalModel::Ssa(_)) = cx.model.get(&dst.local) {
                env.insert(dst.local, zero);
                return Ok(());
            }
        }
        let leaf = place_leaf_tir_ty(cx, dst)?;
        let addr = place_address(cx, fb, env, dst)?;
        fb.store(leaf, addr, zero);
        return Ok(());
    }
    let layout = mir_enum_layout(cx, enum_ty)?;

    let result = match &layout.encoding {
        MirTagEncoding::Direct => {
            // A single-variant (tagless) enum: the discriminant is the static value
            // of the one inhabited variant. `Variants::Single` records the sole
            // variant's switch_value as 0 and no others, but a multi-variant Direct
            // enum (the common case) loads the tag.
            if is_single_variant_enum(cx, enum_ty) {
                let disc = single_variant_discr(cx, enum_ty)?;
                fb.iconst(dst_ty.clone(), disc)
            } else {
                let base = place_address(cx, fb, env, src)?;
                let tag = load_tag(fb, base, layout.tag_offset, &layout.tag_ir_ty);
                // Widen/narrow the loaded tag to the destination scalar width. The
                // tag is a discriminant compared by value; extend per the tag's TRUE
                // signedness. An UNSIGNED tag (no-repr fieldless enum, discriminants
                // 0..N-1) must ZERO-extend: a discriminant >= 128 in a 1-byte tag has
                // the high bit set, and sign-extending it ([F5]) made it negative so it
                // missed its positive SwitchInt key -> the arm fell through to the
                // unreachable default and the machine code aborted. Signed tags (rare,
                // e.g. explicit negative discriminants) still sign-extend.
                cast_int_ext(fb, tag, &layout.tag_ir_ty, &dst_ty, layout.read_signed)
            }
        }
        MirTagEncoding::Niche {
            untagged_variant,
            niche_variants_start,
            niche_start,
        } => {
            // The MIR `discriminant` of a niche enum yields the VARIANT-INDEX-based
            // discriminant the SwitchInt compares. Decode it from the loaded niche:
            //   if niche in [niche_start, niche_start + N): variant =
            //       niche_variants_start + (niche - niche_start)
            //   else: untagged_variant.
            // The trust-ir `Discriminant`-faithful decode is a branchful select.
            // For RUNG 3 we support the COMMON two-variant niche (e.g. Option<&T>,
            // Option<Box<T>>): a single comparison against the untagged value.
            lower_niche_discriminant(
                cx,
                fb,
                env,
                src,
                &layout,
                &dst_ty,
                *untagged_variant,
                *niche_variants_start,
                *niche_start,
            )?
        }
    };

    // Bind the discriminant into the destination (scalar SSA local, or a Store to
    // a memory cell).
    if dst.projection.is_empty() {
        if let Some(LocalModel::Ssa(_)) = cx.model.get(&dst.local) {
            env.insert(dst.local, result);
            return Ok(());
        }
    }
    let leaf = place_leaf_tir_ty(cx, dst)?;
    let addr = place_address(cx, fb, env, dst)?;
    fb.store(leaf, addr, result);
    Ok(())
}

/// Decode a niche-encoded enum's discriminant. Handles the GENERAL N-variant niche
/// (one untagged default + any number of niche variants), the shape rustc produces
/// for a multi-variant enum whose largest variant donates a niche (e.g. a 10-variant
/// `MicroCert` whose `Box`-carrying variant is untagged and sits in the MIDDLE of the
/// index range, leaving a gap in the niche-tag space) as well as the 2-variant
/// `Option<&T>` / `Box`-niche case.
///
/// The MIR `Discriminant` rvalue yields each variant's own discriminant value, which
/// the guarding `SwitchInt` compares. For an enum WITHOUT explicit `= N` discriminants
/// (the only shape this fires on — asserted below), every variant's discriminant
/// equals its variant index. We decode the loaded niche scalar `raw` by matching it
/// against the exact per-variant encoded tag value the faithful layout recorded
/// (`layout.variants[v].0`) and yielding that variant's index, defaulting to the
/// untagged variant when `raw` matches none — a SELECT CHAIN that is correct for any
/// gap/ordering and never traps. We FAIL LOUD if the enum carries explicit
/// discriminants (discriminant != variant index), so no silent miscompile.
#[allow(clippy::too_many_arguments)]
fn lower_niche_discriminant<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    env: &HashMap<Local, trust_ir::ValueId>,
    src: &Place<'tcx>,
    layout: &MirEnumLayout,
    dst_ty: &TIRTy,
    untagged_variant: VariantIdx,
    niche_variants_start: VariantIdx,
    niche_start: u128,
) -> Result<trust_ir::ValueId, String> {
    // The niche variants: every inhabited variant other than the untagged default.
    let niche_variant_idxs: Vec<usize> = layout
        .variants
        .iter()
        .enumerate()
        .filter(|(i, v)| *i != untagged_variant.as_usize() && v.0.is_some())
        .map(|(i, _)| i)
        .collect();
    if niche_variant_idxs.is_empty() {
        return Err("niche discriminant with no niche variants".to_string());
    }

    let enum_ty = cx.place_concrete_ty(src);
    // The MIR `Discriminant` rvalue yields each variant's own discriminant value,
    // which the guarding `SwitchInt` compares. Require those discriminants to equal
    // the variant INDEX (the only shape this decode handles — no explicit `= N`
    // discriminants), failing loud otherwise so a custom-discriminant enum never
    // silently miscompiles. (Result/Option/MicroCert/MicroError all satisfy this.)
    match enum_ty.kind() {
        ty::Adt(adt, _) => {
            for (i, _) in layout.variants.iter().enumerate() {
                let disc = adt
                    .discriminant_for_variant(cx.tcx, VariantIdx::from_usize(i))
                    .val as i128;
                if disc != i as i128 {
                    return Err(format!(
                        "niche enum variant {i} has explicit discriminant {disc} != index \
                         (RUNG 4 niche decode needs discriminant == variant index)"
                    ));
                }
            }
        }
        // A COROUTINE's state discriminant IS its variant index by construction
        // ("Coroutines don't support explicit discriminant values" —
        // `CoroutineArgs::discriminant_for_variant`), so the decode requirement
        // holds without an ADT to interrogate. (Unreachable from rustc 1.99
        // layouts — coroutine tags are hardcoded `TagEncoding::Direct` — see the
        // coroutine Niche arm in `lower_discriminant_assign`.)
        ty::Coroutine(..) => {}
        _ => return Err("niche discriminant of non-ADT".to_string()),
    }
    let untagged_discr = untagged_variant.as_usize() as i128;
    // The select-chain reads the per-variant encoded tag values from `layout.variants`
    // directly, so the raw `niche_variants_start` / `niche_start` are not re-derived.
    let _ = (niche_variants_start, niche_start);

    let base = place_address(cx, fb, env, src)?;
    let niche = load_tag(fb, base, layout.tag_offset, &layout.tag_ir_ty);

    // 2-variant fast path (Option-like): one niche variant, one equality compare +
    // select. Emits the SAME IR as before (constant = the niche variant's index),
    // so the prior Option/Box-niche tests stay byte-identical.
    if niche_variant_idxs.len() == 1 {
        let niche_idx = niche_variant_idxs[0];
        let niche_switch = layout.variants[niche_idx].0.unwrap();
        let niche_const = fb.iconst(layout.tag_ir_ty.clone(), niche_switch);
        let is_niche = fb.icmp(ICmpOp::Eq, layout.tag_ir_ty.clone(), niche, niche_const);
        let niche_d = fb.iconst(dst_ty.clone(), niche_idx as i128);
        let untagged_d = fb.iconst(dst_ty.clone(), untagged_discr);
        return Ok(fb.select(dst_ty.clone(), is_niche, niche_d, untagged_d));
    }

    // General N-variant decode (the multi-variant niche, e.g. a 10-variant MicroCert
    // whose untagged `Box`-carrying variant sits in the middle of the index range).
    // Each niche variant `v` was assigned the tag value `layout.variants[v].0`; the
    // untagged variant's slot is unused (its payload occupies the niche field). We
    // decode by a SELECT CHAIN over the exact (tag_value -> variant_index) pairs the
    // faithful layout recorded, defaulting to the untagged variant when `raw` matches
    // none — fully faithful regardless of gaps/ordering, and trap-free.
    let mut result = fb.iconst(dst_ty.clone(), untagged_discr);
    for &vi in &niche_variant_idxs {
        let tag_val = layout.variants[vi]
            .0
            .ok_or_else(|| "niche variant missing encoded tag value".to_string())?;
        let tag_const = fb.iconst(layout.tag_ir_ty.clone(), tag_val);
        let is_match = fb.icmp(ICmpOp::Eq, layout.tag_ir_ty.clone(), niche, tag_const);
        let vi_const = fb.iconst(dst_ty.clone(), vi as i128);
        result = fb.select(dst_ty.clone(), is_match, vi_const, result);
    }
    Ok(result)
}

/// Whether an enum type has a single inhabited variant (a tagless `Variants::Single`
/// layout — no runtime tag to read).
fn is_single_variant_enum<'tcx>(cx: &Cx<'tcx, '_>, enum_ty: Ty<'tcx>) -> bool {
    cx.tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(enum_ty))
        .map(|tal| matches!(tal.variants, Variants::Single { .. }))
        .unwrap_or(false)
}

/// The static discriminant of the sole inhabited variant of a single-variant enum.
fn single_variant_discr<'tcx>(cx: &Cx<'tcx, '_>, enum_ty: Ty<'tcx>) -> Result<i128, String> {
    let tal = cx
        .tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(enum_ty))
        .map_err(|e| format!("single-variant enum layout_of failed: {e:?}"))?;
    let Variants::Single { index } = tal.variants else {
        return Err("single_variant_discr on multi-variant enum".to_string());
    };
    let ty::Adt(adt, _) = enum_ty.kind() else {
        return Err("single_variant_discr of non-ADT".to_string());
    };
    Ok(adt.discriminant_for_variant(cx.tcx, index).val as i128)
}

/// Load a tag of width `tag_ir_ty` at `base + tag_offset`.
fn load_tag(
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    base: trust_ir::ValueId,
    tag_offset: u64,
    tag_ir_ty: &TIRTy,
) -> trust_ir::ValueId {
    let addr = if tag_offset == 0 {
        base
    } else {
        gep_byte_offset(fb, base, tag_offset)
    };
    fb.load(tag_ir_ty.clone(), addr)
}

/// Cast an integer value from `src` to `dst` trust-ir type via sign-extend /
/// truncate / no-op. Tag values are small non-negative discriminants, so the
/// sign-extend widening is value-preserving.
fn cast_int(
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    val: trust_ir::ValueId,
    src: &TIRTy,
    dst: &TIRTy,
) -> trust_ir::ValueId {
    // Default (existing callers): sign-extend on widening.
    cast_int_ext(fb, val, src, dst, true)
}

/// Like `cast_int`, but widening uses `signed` to pick sign- vs zero-extend. An
/// UNSIGNED source (e.g. a no-repr enum's unsigned tag) must ZERO-extend so a
/// high-bit-set byte reads back as its positive value ([F5]).
fn cast_int_ext(
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    val: trust_ir::ValueId,
    src: &TIRTy,
    dst: &TIRTy,
    signed: bool,
) -> trust_ir::ValueId {
    if src == dst {
        return val;
    }
    let sw = int_bit_width(src);
    let dw = int_bit_width(dst);
    match (sw, dw) {
        (Some(s), Some(d)) if s < d => {
            if signed {
                fb.sext(src.clone(), dst.clone(), val)
            } else {
                fb.zext(src.clone(), dst.clone(), val)
            }
        }
        (Some(s), Some(d)) if s > d => fb.trunc(src.clone(), dst.clone(), val),
        // Equal width, different trust-ir type: a same-width Bitcast retypes it.
        _ => fb.cast(CastOp::Bitcast, src.clone(), dst.clone(), val),
    }
}

/// The trust-ir scalar type of a Discriminant destination place (a bare SSA scalar
/// local, or a memory scalar leaf).
fn dst_scalar_ty<'tcx>(cx: &Cx<'tcx, '_>, dst: &Place<'tcx>) -> Result<TIRTy, String> {
    if dst.projection.is_empty() {
        if let Some(LocalModel::Ssa(t)) = cx.model.get(&dst.local) {
            return Ok(t.clone());
        }
    }
    place_leaf_tir_ty(cx, dst)
}

// ============================ RUNG 3: Aggregate construction =================

/// ADDITIVE: lower `dst = Repeat(elem, N)` — construct a `[T; N]` array all of
/// whose elements equal `elem`, into `dst`'s memory slot. Stores `elem` at each
/// of the N per-element strides (the same offsets `store_array_elems` uses), so
/// it is faithful to MIR's `[elem; N]` array-repeat. This is hashbrown's
/// `repeat` helper (`from_ne_bytes([tag.0; Group::WIDTH])`): an 8-element
/// `[u8; 8]` of the same control-byte tag, later reinterpreted to a u64 word.
fn lower_repeat_assign<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    env: &mut HashMap<Local, trust_ir::ValueId>,
    dst: &Place<'tcx>,
    elem: &Operand<'tcx>,
    count: ty::Const<'tcx>,
) -> Result<(), String> {
    let agg_ty = cx.place_concrete_ty(dst);
    if !matches!(agg_ty.kind(), ty::Array(_, _)) {
        return Err(format!("Rvalue::Repeat into non-array place {}", ty_family(agg_ty)));
    }
    // Monomorphize the repeat count first: a CONST-GENERIC length
    // (`truncate_cstr::<MAX_WITH_NUL>`'s `[0; MAX_WITH_NUL]`) is an
    // unevaluated param until the instance's args are substituted in.
    let count = cx.instance.instantiate_mir_and_normalize_erasing_regions(
        cx.tcx,
        ty::TypingEnv::fully_monomorphized(),
        ty::EarlyBinder::bind(cx.tcx, count),
    );
    let n = count
        .try_to_target_usize(cx.tcx)
        .ok_or_else(|| "Rvalue::Repeat: non-const array length".to_string())?;
    let base = place_address(cx, fb, env, dst)?;
    // The array's faithful per-element offsets (stride = size.align_to(align)).
    let layout = cx
        .tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(agg_ty))
        .map_err(|e| format!("Repeat array layout_of failed: {e:?}"))?;
    for i in 0..n as usize {
        let off = layout.fields.offset(i).bytes();
        store_one_field(cx, fb, env, base, off, elem)?;
    }
    Ok(())
}

/// Lower `dst = Aggregate(kind, operands)` — construct a tuple / struct / array /
/// enum-variant value in `dst`'s memory slot. Each operand is Stored at its
/// faithful `layout_of` field offset; an enum variant also writes the
/// discriminant tag. The destination must be a memory-backed aggregate place.
fn lower_aggregate_assign<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    env: &mut HashMap<Local, trust_ir::ValueId>,
    dst: &Place<'tcx>,
    kind: &AggregateKind<'tcx>,
    operands: &rustc_index::IndexVec<rustc_abi::FieldIdx, Operand<'tcx>>,
) -> Result<(), String> {
    // The aggregate's concrete TYPE (and its base address: the destination slot,
    // possibly projected).
    let agg_ty = cx.place_concrete_ty(dst);
    let base = place_address(cx, fb, env, dst)?;

    match kind {
        AggregateKind::Tuple => {
            store_aggregate_fields(cx, fb, env, agg_ty, base, 0, operands)
        }
        AggregateKind::Array(_elem) => {
            // An array `[e0, e1, ..]`: store each element at index*stride. The
            // element leaf type sizes the stride.
            store_array_elems(cx, fb, env, agg_ty, base, operands)
        }
        AggregateKind::Adt(_def_id, variant_index, _args, _user_ty, _field_idx) => {
            let adt = match agg_ty.kind() {
                ty::Adt(adt, _) => *adt,
                _ => return Err(format!("Aggregate ADT of non-ADT type {}", ty_family(agg_ty))),
            };
            if adt.is_union() {
                // RUNG 4: a union construction writes exactly ONE active field's
                // value; every union field is laid out at offset 0 (overlapping
                // storage), so store the single operand at `base + 0`.
                // `store_one_field` handles a scalar leaf, a ZST active field
                // (`MaybeUninit::<T>::uninit()` writes the `uninit: ()` field — no
                // bytes, slot stays uninitialized), or a nested aggregate (byte
                // copy). The union's other fields alias this storage and are read
                // back via a field place at offset 0 (`place_address`). This is the
                // sanctioned byte-overlap union model (two-producer-coverage.md).
                let op = operands
                    .iter()
                    .next()
                    .ok_or_else(|| "union aggregate has no operand".to_string())?;
                return store_one_field(cx, fb, env, base, 0, op);
            }
            if adt.is_enum() {
                // UNINHABITED-variant construction (THREADS): `?` on a
                // `Result<T, !>` desugars to a `Err(e: !)` aggregate in a block
                // that can never execute (its operand type is uninhabited — no
                // value of it can ever be produced). rustc keeps the statement
                // in optimized MIR (`OnceCell::<Thread>::try_init` via
                // `get_or_init`'s `Ok::<_, !>` closure); the faithful lowering
                // of a dynamically-dead construction is NO stores at all.
                let lcx = LayoutCx::new(cx.tcx, ty::TypingEnv::fully_monomorphized());
                let full_tal = cx
                    .tcx
                    .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(agg_ty))
                    .map_err(|e| format!("aggregate enum layout_of failed: {e:?}"))?;
                // A fully-uninhabited enum (`Variants::Empty`) short-circuits
                // BEFORE the per-variant view (which has no variants to view).
                if full_tal.is_uninhabited()
                    || full_tal.for_variant(&lcx, *variant_index).is_uninhabited()
                {
                    return Ok(());
                }
                // Enum variant: write the variant's fields at their VARIANT-relative
                // offsets, then the discriminant tag.
                let layout = mir_enum_layout(cx, agg_ty)?;
                let (_sv, field_offsets) = layout
                    .variants
                    .get(variant_index.as_usize())
                    .ok_or_else(|| "Aggregate enum variant index out of range".to_string())?;
                let field_offsets = field_offsets.clone();
                store_variant_fields(cx, fb, env, adt, *variant_index, base, &field_offsets, operands)?;
                // The discriminant tag (Direct: the tag value; Niche: niche or
                // nothing for untagged).
                set_discriminant_at(fb, base, &layout, *variant_index)?;
                Ok(())
            } else {
                // A struct: a single-variant ADT; store each field at its layout
                // offset.
                store_aggregate_fields(cx, fb, env, agg_ty, base, 0, operands)
            }
        }
        AggregateKind::Closure(_def_id, _args) => {
            // RUNG 9 (non-escaping closure): a closure VALUE is constructed by
            // capturing its upvars into a struct-like capture environment. The
            // closure type (`agg_ty`) is an ADT-like type whose `tcx.layout_of`
            // lays out one field per captured upvar (by-value or by-ref per the
            // capture mode); the operands ARE those upvars, in field order. This
            // is byte-identical to a struct aggregate: store each upvar at its
            // faithful `layout.fields.offset(i)`. A non-escaping closure (one
            // constructed and immediately consumed by a combinator) never has its
            // env stored/returned, so the captured struct lives only across the
            // combinator call — the same lifetime a struct temporary has. The
            // combinator later calls `<{closure} as FnOnce>::call_once(env, args)`,
            // which `Instance::try_resolve` collapses to the closure's OWN MIR body
            // taking this same capture struct by-ref (pulled in by
            // `closure_chain_callee`).
            store_aggregate_fields(cx, fb, env, agg_ty, base, 0, operands)
        }
        AggregateKind::Coroutine(_def_id, _args) => {
            // A coroutine VALUE (`_0 = {coroutine} { upvar0: .., .. }`, what an
            // `async fn` / `gen` body constructs on entry) is built in its UNRESUMED
            // state (variant 0). The captured upvars are the coroutine's common
            // PREFIX fields — laid out at the top-level `layout.fields` offsets,
            // exactly like a closure capture env — so store each operand there via
            // `store_aggregate_fields`, then write the Unresumed state discriminant.
            // The per-variant saved-local fields stay uninitialized until the first
            // suspend point writes them, matching rustc's own construction.
            store_aggregate_fields(cx, fb, env, agg_ty, base, 0, operands)?;
            let layout = mir_coroutine_layout(cx, agg_ty)?;
            set_discriminant_at(fb, base, &layout, VariantIdx::from_u32(0))?;
            Ok(())
        }
        AggregateKind::CoroutineClosure(_, _) => {
            // RUNG 4 (async closures): an ASYNC-CLOSURE VALUE (`let f = async
            // |..| { .. }`) captures its upvars into a struct-like env, exactly
            // like an ordinary closure: `tcx.layout_of` on the
            // `ty::CoroutineClosure` lays out one field per captured upvar
            // (UNIVARIANT — the coroutine-closure itself is NOT a state machine;
            // only the coroutine its CALL returns is, so there is no
            // discriminant to write). Calling the closure resolves to its own
            // MIR body (`Instance::new_raw(coroutine_closure_def_id)` for the
            // kind-matching `Fn`/`FnMut`/`AsyncFn`/`AsyncFnMut` paths —
            // rustc_ty_utils/src/instance.rs `resolve_associated_item`), an
            // ordinary `DefKind::Closure` rust-call Item body that reads this
            // env by ref and constructs the child coroutine via the
            // `AggregateKind::Coroutine` arm above. (The `AsyncFnOnce` path on
            // a by-ref closure routes through the
            // `Shim(ConstructCoroutineInClosure)` synthetic instead, which the
            // Item-only shim gate refuses loudly — unchanged here.) Store each
            // capture at its faithful `layout.fields.offset(i)` — byte-identical
            // to the `Closure` arm.
            store_aggregate_fields(cx, fb, env, agg_ty, base, 0, operands)
        }
        AggregateKind::RawPtr(_, _) => Err("Aggregate RawPtr construction (RUNG 4)".to_string()),
    }
}

/// Store each operand of a struct/tuple aggregate at its `layout_of` field offset
/// (relative to `base + base_off`). Each field must be a single scalar leaf.
fn store_aggregate_fields<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    env: &mut HashMap<Local, trust_ir::ValueId>,
    agg_ty: Ty<'tcx>,
    base: trust_ir::ValueId,
    base_off: u64,
    operands: &rustc_index::IndexVec<rustc_abi::FieldIdx, Operand<'tcx>>,
) -> Result<(), String> {
    let layout = cx
        .tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(agg_ty))
        .map_err(|e| format!("aggregate layout_of failed: {e:?}"))?;
    for (i, op) in operands.iter_enumerated() {
        let off = base_off + layout.fields.offset(i.index()).bytes();
        store_one_field(cx, fb, env, base, off, op)?;
    }
    Ok(())
}

/// Store each ENUM-VARIANT field at its variant-relative byte offset.
fn store_variant_fields<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    env: &mut HashMap<Local, trust_ir::ValueId>,
    _adt: ty::AdtDef<'tcx>,
    _variant_index: VariantIdx,
    base: trust_ir::ValueId,
    field_offsets: &[u64],
    operands: &rustc_index::IndexVec<rustc_abi::FieldIdx, Operand<'tcx>>,
) -> Result<(), String> {
    if operands.len() != field_offsets.len() {
        return Err(format!(
            "enum variant has {} operands but {} field offsets",
            operands.len(),
            field_offsets.len()
        ));
    }
    for (i, op) in operands.iter_enumerated() {
        let off = field_offsets[i.index()];
        store_one_field(cx, fb, env, base, off, op)?;
    }
    Ok(())
}

/// Copy a WHOLE aggregate value from `src`'s slot into `dst`'s slot, lane by lane
/// (`dst = move/copy src` for a by-value aggregate). Both places are addressed
/// through the memory-place path; the byte copy uses the aggregate's natural-
/// alignment lane width so it is byte- and alignment-accurate.
fn lower_aggregate_copy<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    env: &HashMap<Local, trust_ir::ValueId>,
    dst: &Place<'tcx>,
    src: &Place<'tcx>,
) -> Result<(), String> {
    let cty = cx.place_concrete_ty(dst);
    let (size, align) = memory_layout_size_align(cx, cty)?;
    let src_cty = cx.place_concrete_ty(src);
    let (src_size, src_align) = memory_layout_size_align(cx, src_cty)?;
    if (src_size, src_align) != (size, align) {
        return Err(format!(
            "aggregate copy layout mismatch: src size/align {src_size}/{src_align}, \
             dst size/align {size}/{align}"
        ));
    }
    // Cap the copy lane width at 16 bytes (I128). An aggregate OVER-aligned to
    // 32/64 — e.g. the portable `Simd<u8, 32>` interleave that `vst2q_u8` stores
    // through `ptr::write_unaligned` (a 32-byte, align-32 value) — still copies
    // byte-exact in 16-byte lanes. Mirrors `slot_lane_ty`'s cap: the LANE type
    // maxes at I128 (the widest integer access this model emits); the aggregate's
    // full ABI alignment rides on the place, not the copy stride. For align <= 16
    // this is the original behavior unchanged.
    let lane_align = align.min(16);
    let lane = lane_ty_for_align(lane_align)?;
    if size % lane_align != 0 {
        return Err(format!(
            "aggregate copy size {size} not a multiple of lane width {lane_align} \
             (align {align})"
        ));
    }
    let dst_addr = place_address(cx, fb, env, dst)?;
    let src_addr = place_address(cx, fb, env, src)?;
    let lanes = size / lane_align;
    for i in 0..lanes {
        let off = i * lane_align;
        let sa = if off == 0 { src_addr } else { gep_byte_offset(fb, src_addr, off) };
        let da = if off == 0 { dst_addr } else { gep_byte_offset(fb, dst_addr, off) };
        let v = fb.load(lane.clone(), sa);
        fb.store(lane.clone(), da, v);
    }
    Ok(())
}

/// Copy `size` bytes from `src_addr` to `dst_addr` lane-by-lane at width `align`
/// (the natural-alignment lane width, so the copy is byte- and alignment-accurate).
/// The raw-address analog of `lower_aggregate_copy`, used by RUNG 6 to move an
/// aggregate `Arc::new` payload into the freshly allocated ArcInner data slot.
fn copy_aggregate_bytes(
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    src_addr: trust_ir::ValueId,
    dst_addr: trust_ir::ValueId,
    size: u64,
    align: u64,
) -> Result<(), String> {
    // Cap the copy lane at 16 bytes (I128) so an OVER-aligned payload (align
    // 32/64, e.g. the `Simd<u8, 32>` interleave `vst2q_u8` stores through
    // `ptr::write_unaligned`) copies byte-exact in 16-byte lanes. `slot_lane_ty`
    // makes the same cap; align <= 16 is unchanged.
    let lane_align = align.min(16);
    let lane = lane_ty_for_align(lane_align)?;
    if size % lane_align != 0 {
        return Err(format!(
            "aggregate payload size {size} not a multiple of lane width {lane_align} \
             (align {align})"
        ));
    }
    let lanes = size / lane_align;
    for i in 0..lanes {
        let off = i * lane_align;
        let sa = if off == 0 { src_addr } else { gep_byte_offset(fb, src_addr, off) };
        let da = if off == 0 { dst_addr } else { gep_byte_offset(fb, dst_addr, off) };
        let v = fb.load(lane.clone(), sa);
        fb.store(lane.clone(), da, v);
    }
    Ok(())
}

/// Lower a `dst_aggregate = transmute(src)` whose destination leaf is a non-scalar
/// aggregate (an array / struct). A transmute is bit- and size-preserving, so the
/// destination slot receives the source's exact bytes:
///   * a SCALAR source -> one typed Store of its scalar bits into the slot (the
///     slot is exactly `size_of(scalar)` bytes; a later element read observes the
///     same little-endian bytes — `u32::to_ne_bytes` reads back its 4 bytes);
///   * an AGGREGATE-PLACE source -> a byte lane-copy from the source slot.
fn lower_transmute_to_aggregate<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    env: &mut HashMap<Local, trust_ir::ValueId>,
    dst: &Place<'tcx>,
    src_op: &Operand<'tcx>,
) -> Result<(), String> {
    let dst_cty = cx.place_concrete_ty(dst);
    let (dsize, _dalign) = memory_layout_size_align(cx, dst_cty)?;
    let src_ty = operand_concrete_ty(cx, src_op);
    let dst_addr = place_address(cx, fb, env, dst)?;
    // A SCALAR source (int / bool / thin ptr / single-scalar wrapper): store its
    // bits. The transmute guarantees `size_of(src) == size_of(dst)`, so the store
    // fills the slot exactly.
    if scalar_or_ptr_wrapper_leaf(cx, src_ty).is_some() {
        let (v, t) = lower_operand(cx, fb, env, src_op)?;
        fb.store(t, dst_addr, v);
        return Ok(());
    }
    // An AGGREGATE-PLACE source: copy its byte image (same size) lane-by-lane.
    if let Operand::Copy(sp) | Operand::Move(sp) = src_op {
        let src_addr = place_address(cx, fb, env, sp)?;
        copy_aggregate_bytes(fb, src_addr, dst_addr, dsize, 1)?;
        return Ok(());
    }
    // A CONSTANT aggregate source: materialize its exact (pointer-free) byte image
    // into the destination slot — same fail-closed discipline as the whole-aggregate
    // constant assign (a constant carrying live pointer provenance stays a loud
    // failure, never a raw-bytes store of a compile-time address).
    if let Operand::Constant(c) = src_op {
        let bytes = const_agg_bytes(cx, c)?;
        store_agg_bytes_at(cx, fb, dst_addr, dst_cty, bytes)?;
        return Ok(());
    }
    Err(format!(
        "transmute to aggregate from non-scalar, non-place source: {}",
        ty_family(src_ty)
    ))
}

/// R5: lower `copy_nonoverlapping::<T>(src, dst, count)` (the MIR
/// `NonDivergingIntrinsic::CopyNonOverlapping` statement) to a byte-granular copy
/// of `count * size_of::<T>()` bytes from `src` to `dst`. `src`/`dst` are pointer
/// operands (`*const T` / `*mut T`); `count` is a `usize` ELEMENT count.
///
/// The copy is BYTE-GRANULAR (`I8` lanes), so it is correct for the UNALIGNED
/// targets `ptr::write_unaligned` / `read_unaligned` produce (it assumes no
/// alignment). A COMPILE-TIME-CONSTANT small byte count is UNROLLED; a runtime
/// count emits a counted forward byte-copy loop. The regions are non-overlapping
/// by the intrinsic's contract, so a forward copy is faithful.
fn lower_copy_nonoverlapping<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    env: &mut HashMap<Local, trust_ir::ValueId>,
    cno: &rustc_middle::mir::CopyNonOverlapping<'tcx>,
) -> Result<(), String> {
    // The element type T: `src` is `*const T` / `&T`; its pointee gives size_of::<T>.
    let src_ty = operand_concrete_ty(cx, &cno.src);
    let elem = match src_ty.kind() {
        ty::RawPtr(p, _) | ty::Ref(_, p, _) => *p,
        _ => {
            return Err(format!(
                "copy_nonoverlapping src is not a pointer: {}",
                ty_family(src_ty)
            ))
        }
    };
    let elem_size = cx
        .tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(elem))
        .map_err(|e| format!("copy_nonoverlapping elem layout_of failed: {e:?}"))?
        .size
        .bytes();

    // `src` / `dst` pointer values.
    let (src_v, src_tir) = lower_operand(cx, fb, env, &cno.src)?;
    let (dst_v, dst_tir) = lower_operand(cx, fb, env, &cno.dst)?;
    if !matches!(src_tir, TIRTy::Ptr) || !matches!(dst_tir, TIRTy::Ptr) {
        return Err("copy_nonoverlapping src/dst did not lower to Ptr".to_string());
    }

    // A ZST element copies zero bytes.
    if elem_size == 0 {
        return Ok(());
    }

    // A COMPILE-TIME-CONSTANT element count -> a fixed byte count; UNROLL when small.
    if let Operand::Constant(c) = &cno.count {
        if let Some(n) = const_operand_u64(cx, c) {
            let nbytes = n.saturating_mul(elem_size);
            if nbytes <= 64 {
                for i in 0..nbytes {
                    let sa = if i == 0 { src_v } else { gep_byte_offset(fb, src_v, i) };
                    let da = if i == 0 { dst_v } else { gep_byte_offset(fb, dst_v, i) };
                    let b = fb.load(TIRTy::I8, sa);
                    fb.store(TIRTy::I8, da, b);
                }
                return Ok(());
            }
        }
    }

    // RUNTIME count (or a large constant): a counted byte-copy loop.
    let (count_v, count_tir) = lower_operand(cx, fb, env, &cno.count)?;
    let count_i = to_i64_value(fb, count_v, &count_tir)?;
    let nbytes = if elem_size == 1 {
        count_i
    } else {
        let sz = fb.iconst(TIRTy::I64, elem_size as i128);
        fb.binop(BinOp::Mul, TIRTy::I64, count_i, sz)
    };
    emit_byte_copy_loop(fb, src_v, dst_v, nbytes);
    Ok(())
}

/// Emit a counted forward BYTE-COPY loop copying `nbytes` (`I64`) bytes from `src`
/// to `dst`, leaving `fb` switched to the loop-EXIT continuation block. The loop
/// index is a `check`-block PARAMETER (the merge-point phi over `{entry 0, body
/// i+1}`); the pre-loop SSA values (`src`/`dst`/`nbytes`) dominate every loop block,
/// so they flow by dominance and need no threading.
fn emit_byte_copy_loop(
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    src: trust_ir::ValueId,
    dst: trust_ir::ValueId,
    nbytes: trust_ir::ValueId,
) {
    let check = fb.create_block();
    let body = fb.create_block();
    let exit = fb.create_block();
    let i = fb.add_block_param(check, TIRTy::I64);
    // entry -> check(0)
    let i0 = fb.iconst(TIRTy::I64, 0);
    fb.br(check, vec![i0]);
    // check(i): if i < nbytes goto body else exit
    fb.switch_to_block(check);
    let cond = fb.icmp(ICmpOp::Slt, TIRTy::I64, i, nbytes);
    fb.condbr(cond, body, vec![], exit, vec![]);
    // body: dst[i] = src[i]; check(i+1)
    fb.switch_to_block(body);
    let sa = fb.gep(TIRTy::I8, src, vec![i]);
    let da = fb.gep(TIRTy::I8, dst, vec![i]);
    let b = fb.load(TIRTy::I8, sa);
    fb.store(TIRTy::I8, da, b);
    let one = fb.iconst(TIRTy::I64, 1);
    let i2 = fb.add(TIRTy::I64, i, one);
    fb.br(check, vec![i2]);
    // exit: the continuation for the rest of the enclosing block.
    fb.switch_to_block(exit);
}

/// Const-eval a scalar-int constant operand to a `u64` (a compile-time element
/// COUNT / length). `None` if it is not a single-scalar-int constant.
fn const_operand_u64<'tcx>(cx: &Cx<'tcx, '_>, c: &ConstOperand<'tcx>) -> Option<u64> {
    let ct = cx.instance.instantiate_mir_and_normalize_erasing_regions(
        cx.tcx,
        ty::TypingEnv::fully_monomorphized(),
        ty::EarlyBinder::bind(cx.tcx, c.const_),
    );
    let cv = ct
        .eval(cx.tcx, ty::TypingEnv::fully_monomorphized(), c.span)
        .ok()?;
    match cv {
        ConstValue::Scalar(Scalar::Int(si)) => Some(si.to_uint(si.size()) as u64),
        _ => None,
    }
}

/// Const-eval a scalar integer operand with its Rust signedness preserved.
/// Used to admit only demonstrably non-negative signed pointer offsets into
/// TrustIR GEP, whose semantics reject negative indices.
fn const_operand_i128<'tcx>(cx: &Cx<'tcx, '_>, c: &ConstOperand<'tcx>) -> Option<i128> {
    let ct = cx.instance.instantiate_mir_and_normalize_erasing_regions(
        cx.tcx,
        ty::TypingEnv::fully_monomorphized(),
        ty::EarlyBinder::bind(cx.tcx, c.const_),
    );
    let cty = cx.mono(c.const_.ty());
    let cv = ct
        .eval(cx.tcx, ty::TypingEnv::fully_monomorphized(), c.span)
        .ok()?;
    const_value_to_i128(cv, cty)
}

/// Normalize a 64-bit-or-narrower integer value to `I64` (the loop-index / byte-
/// offset width): `I64` passes through, `U64` bit-reinterprets, a narrower unsigned
/// zero-extends. A count / length is non-negative, so this preserves its value.
fn to_i64_value(
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    v: trust_ir::ValueId,
    tir: &TIRTy,
) -> Result<trust_ir::ValueId, String> {
    match tir {
        TIRTy::I64 => Ok(v),
        TIRTy::U64 => Ok(fb.cast(CastOp::Bitcast, TIRTy::U64, TIRTy::I64, v)),
        TIRTy::U32 => Ok(fb.cast(CastOp::ZExt, TIRTy::U32, TIRTy::I64, v)),
        TIRTy::U16 => Ok(fb.cast(CastOp::ZExt, TIRTy::U16, TIRTy::I64, v)),
        TIRTy::U8 => Ok(fb.cast(CastOp::ZExt, TIRTy::U8, TIRTy::I64, v)),
        other => Err(format!("count value type {other:?} not 64-bit-convertible")),
    }
}

/// The trust-ir integer lane type for a given alignment (1/2/4/8/16 -> I8/I16/I32/
/// I64/I128). The byte-copy / slot-lane width.
fn lane_ty_for_align(align: u64) -> Result<TIRTy, String> {
    match align {
        1 => Ok(TIRTy::I8),
        2 => Ok(TIRTy::I16),
        4 => Ok(TIRTy::I32),
        8 => Ok(TIRTy::I64),
        16 => Ok(TIRTy::I128),
        other => Err(format!("aggregate lane alignment {other} unsupported")),
    }
}

/// Store one aggregate field operand at `base + off`.
///
/// A SINGLE-SCALAR-LEAF field (an int/bool/thin-ptr, or a single-pointer-width
/// wrapper such as `Arc<T>`) is lowered to its value and Stored with one typed
/// access. RUNG 7: a field whose type is itself a NESTED AGGREGATE (an enum /
/// struct passed by value — e.g. `MicroExpr::Sort(level)`'s `level: MicroLevel`)
/// is written by COPYING its bytes from the source operand's slot into the
/// field's slot at `base + off`, lane-by-lane via `copy_aggregate_bytes`, using
/// `tcx.layout_of` for the inner aggregate's size/align. This is the nested-
/// aggregate generalization of the scalar/Box-child field construction.
fn store_one_field<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    env: &mut HashMap<Local, trust_ir::ValueId>,
    base: trust_ir::ValueId,
    off: u64,
    op: &Operand<'tcx>,
) -> Result<(), String> {
    let fty = operand_concrete_ty(cx, op);
    // RUNG 4: a ZST field (unit, PhantomData, a ZST marker) stores no bytes — skip
    // it. Its operand carries no value, so there is nothing to lower or store.
    if ty_is_zst(cx, fty) {
        return Ok(());
    }
    // A single-access scalar leaf (int / bool / thin-ptr / single-pointer-width
    // wrapper like `Arc<T>`): lower its VALUE first, then the field address, then
    // Store — the same emission order as the original scalar-only path (so the
    // already-emitted structural_eq/subst_at IR does not drift).
    if let Some(leaf) = scalar_or_ptr_wrapper_leaf(cx, fty) {
        let (val, _vty) = lower_operand(cx, fb, env, op)?;
        let addr = if off == 0 { base } else { gep_byte_offset(fb, base, off) };
        fb.store(leaf, addr, val);
        return Ok(());
    }
    // RUNG 7: a NESTED-AGGREGATE field (an enum/struct by value, e.g. the
    // `MicroLevel` payload of `MicroExpr::Sort(level)`). It has no single-scalar
    // leaf; copy its bytes from the source operand's slot into the field slot.
    // The source must be a PLACE (a copy/move of an aggregate value) — a constant
    // aggregate field is not modeled (fail loud).
    let addr = if off == 0 { base } else { gep_byte_offset(fb, base, off) };
    // A CONSTANT nested-aggregate field (a compile-time struct/array constant held
    // in a field, e.g. a monomorphized `TableLayout`, or `RawTableInner::NEW` inside
    // `fallible_with_capacity` / `HashMap::new`): materialize its byte image into the
    // field slot. `store_const_agg_at` resolves any pointer PROVENANCE the constant
    // carries (a relocation -> `GlobalAddr` of the interned static); a pointer-free
    // constant takes the identical byte-image path.
    if let Operand::Constant(c) = op {
        store_const_agg_at(cx, fb, addr, fty, c)?;
        return Ok(());
    }
    let (Operand::Copy(place) | Operand::Move(place)) = op else {
        return Err(format!(
            "aggregate field operand is not a place (constant aggregate field): {}",
            ty_family(fty)
        ));
    };
    let (size, align) = memory_layout_size_align(cx, fty)?;
    let src_addr = place_address(cx, fb, env, place)?;
    copy_aggregate_bytes(fb, src_addr, addr, size, align)?;
    Ok(())
}

/// The concrete (monomorphized) type of an operand.
fn operand_concrete_ty<'tcx>(cx: &Cx<'tcx, '_>, op: &Operand<'tcx>) -> Ty<'tcx> {
    match op {
        Operand::Copy(place) | Operand::Move(place) => cx.place_concrete_ty(place),
        Operand::Constant(c) => cx.mono(c.const_.ty()),
        Operand::RuntimeChecks(_) => cx.tcx.types.unit,
    }
}

/// Store each array element at `base + index*stride`.
///
/// The element STRIDE is the array layout's per-element offset (`size.align_to(align)`,
/// which `tcx.layout_of(agg_ty).fields.offset(i)` reports exactly), so an over-aligned
/// or padded element is placed faithfully. Each element is written via `store_one_field`,
/// which handles BOTH a single scalar leaf (int/bool/thin-ptr/`Arc<T>`) AND a NESTED
/// AGGREGATE element (e.g. a `MicroExpr` enum by value — the `vec![a.clone()]` spine
/// seed: a `[MicroExpr; 1]` array whose one element is the 32-byte enum, byte-copied
/// from its source slot). This is the RUNG-8 generalization that unblocks the `vec!`
/// macro's `[elem]` array temporary over an aggregate element type.
fn store_array_elems<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    env: &mut HashMap<Local, trust_ir::ValueId>,
    agg_ty: Ty<'tcx>,
    base: trust_ir::ValueId,
    operands: &rustc_index::IndexVec<rustc_abi::FieldIdx, Operand<'tcx>>,
) -> Result<(), String> {
    if !matches!(agg_ty.kind(), ty::Array(_, _)) {
        return Err(format!("Aggregate Array of non-array type {}", ty_family(agg_ty)));
    }
    // The array's faithful per-element offsets (stride = size.align_to(align)).
    let layout = cx
        .tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(agg_ty))
        .map_err(|e| format!("array layout_of failed: {e:?}"))?;
    for (i, op) in operands.iter_enumerated() {
        let off = layout.fields.offset(i.index()).bytes();
        store_one_field(cx, fb, env, base, off, op)?;
    }
    Ok(())
}

/// Write a variant's discriminant tag at the enum layout's tag offset (used by
/// Aggregate construction; the SetDiscriminant statement reuses this via
/// `lower_set_discriminant`). For a single-variant (tagless) enum, nothing is
/// written; for a Niche untagged variant, nothing is written.
fn set_discriminant_at(
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    base: trust_ir::ValueId,
    layout: &MirEnumLayout,
    variant_index: VariantIdx,
) -> Result<(), String> {
    match &layout.encoding {
        MirTagEncoding::Direct => {
            if let Some(disc) = layout.variants.get(variant_index.as_usize()).and_then(|v| v.0) {
                // A `Variants::Single` records exactly one Some(0); a tagless enum
                // has tag_bytes==1 sentinel but we only write a real tag for a
                // multi-variant layout. Detect the single-variant tagless case: if
                // ALL other variants are None and this one is Some, and there is
                // genuinely no tag, the write is harmless (offset 0, the payload).
                // To stay sound we skip the write for a single-inhabited-variant
                // layout (no tag field exists).
                if multi_variant_has_tag(layout) {
                    store_tag(fb, base, layout.tag_offset, &layout.tag_ir_ty, disc);
                }
            }
            Ok(())
        }
        MirTagEncoding::Niche {
            untagged_variant, ..
        } => {
            if variant_index == *untagged_variant {
                return Ok(());
            }
            if let Some(disc) = layout.variants.get(variant_index.as_usize()).and_then(|v| v.0) {
                store_tag(fb, base, layout.tag_offset, &layout.tag_ir_ty, disc);
            }
            Ok(())
        }
    }
}

/// Whether a layout genuinely has a runtime tag field (more than one variant
/// carries a Direct Switch value). A `Variants::Single` layout records exactly one
/// `Some(0)` and is tagless.
fn multi_variant_has_tag(layout: &MirEnumLayout) -> bool {
    layout.variants.iter().filter(|v| v.0.is_some()).count() > 1
}

/// Statement discriminant name for an unsupported-statement bail message.
fn stmt_name(s: &StatementKind<'_>) -> &'static str {
    match s {
        StatementKind::Assign(_) => "Assign",
        StatementKind::SetDiscriminant { .. } => "SetDiscriminant",
        StatementKind::Coverage(_) => "Coverage",
        StatementKind::Intrinsic(_) => "Intrinsic",
        StatementKind::BackwardIncompatibleDropHint { .. } => "BackwardIncompatibleDropHint",
        _ => "Other",
    }
}

/// A coarse type-family label for the bail message (so the bucket is stable).
fn ty_family(ty: Ty<'_>) -> &'static str {
    match ty.kind() {
        ty::Tuple(t) if t.is_empty() => "unit",
        ty::Tuple(_) => "tuple",
        ty::Adt(adt, _) => {
            if adt.is_enum() {
                "enum-adt"
            } else if adt.is_union() {
                "union-adt"
            } else {
                "struct-adt"
            }
        }
        ty::Ref(_, _, _) => "ref",
        ty::RawPtr(_, _) => "rawptr",
        ty::Float(_) => "float",
        ty::Array(_, _) => "array",
        ty::Slice(_) => "slice",
        ty::Str => "str",
        ty::Closure(_, _) => "closure",
        ty::FnDef(_, _) => "fndef",
        ty::FnPtr(_, _) => "fnptr",
        ty::Char => "char",
        ty::Never => "never",
        ty::Param(_) => "param",
        _ => "other",
    }
}

fn is_unit(ty: Ty<'_>) -> bool {
    matches!(ty.kind(), ty::Tuple(t) if t.is_empty())
}

// ============================ RUNG 1: classification =========================

/// Locals whose ADDRESS is taken anywhere in the body (`Rvalue::Ref` /
/// `Rvalue::RawPtr` / `Rvalue::CopyForDeref` of a place rooted at the local). A
/// scalar whose address is taken must be MEMORY-BACKED (it needs a real cell so
/// `&local` is a stable runtime address). Non-scalar locals are memory-backed
/// regardless; this set only PROMOTES otherwise-SSA scalars.
fn compute_address_taken<'tcx>(_cx: &Cx<'tcx, '_>, body: &Body<'tcx>) -> HashSet<Local> {
    let mut taken: HashSet<Local> = HashSet::new();
    for data in body.basic_blocks.iter() {
        for stmt in &data.statements {
            if let StatementKind::Assign(boxed) = &stmt.kind {
                let (_dst, rvalue) = &**boxed;
                match rvalue {
                    Rvalue::Ref(_, _, place)
                    | Rvalue::RawPtr(_, place)
                    | Rvalue::CopyForDeref(place) => {
                        taken.insert(place.local);
                    }
                    _ => {}
                }
            }
        }
    }
    taken
}

// ============================ RUNG 2: cross-block phi (liveness) ==============

/// Whether a MIR Local is realized as an SSA scalar (the only locals that need
/// block-parameter phi threading; memory-backed locals thread via a stable slot
/// pointer).
fn is_ssa(cx: &Cx<'_, '_>, local: Local) -> bool {
    matches!(cx.model.get(&local), Some(LocalModel::Ssa(_)))
}

/// Collect the SSA-scalar locals READ by an operand (a bare scalar local use; a
/// projected/memory place reads through the slot pointer, not an SSA scalar).
fn operand_scalar_uses(cx: &Cx<'_, '_>, op: &Operand<'_>, out: &mut BTreeSet<Local>) {
    match op {
        Operand::Copy(place) | Operand::Move(place) => {
            if place.projection.is_empty() && is_ssa(cx, place.local) {
                out.insert(place.local);
            } else {
                // A projected read (Index uses the index local; a Deref of an SSA
                // pointer uses that pointer local). Capture any SSA-scalar local
                // referenced by a projection (the Index local), plus the base if
                // the base itself is an SSA pointer used by a leading Deref.
                place_scalar_uses(cx, place, out);
            }
        }
        Operand::Constant(_) | Operand::RuntimeChecks(_) => {}
    }
}

/// SSA-scalar locals referenced by a PLACE's projections / base. The base local
/// is an SSA use only when it is itself an SSA scalar (a non-projected read, or a
/// leading-`Deref` of an SSA pointer local). `Index(local)` always references its
/// index local.
fn place_scalar_uses(cx: &Cx<'_, '_>, place: &Place<'_>, out: &mut BTreeSet<Local>) {
    // A leading Deref of an SSA-pointer base reads that base pointer value.
    if matches!(place.projection.as_ref().first(), Some(ProjectionElem::Deref))
        && is_ssa(cx, place.local)
    {
        out.insert(place.local);
    }
    // A bare (non-projected) SSA scalar base is a value read.
    if place.projection.is_empty() && is_ssa(cx, place.local) {
        out.insert(place.local);
    }
    for elem in place.projection.iter() {
        if let ProjectionElem::Index(idx) = elem {
            if is_ssa(cx, idx) {
                out.insert(idx);
            }
        }
    }
}

/// SSA-scalar locals read by one Rvalue.
fn rvalue_scalar_uses(cx: &Cx<'_, '_>, rv: &Rvalue<'_>, out: &mut BTreeSet<Local>) {
    match rv {
        Rvalue::Use(op, _) | Rvalue::UnaryOp(_, op) | Rvalue::Repeat(op, _) => {
            operand_scalar_uses(cx, op, out)
        }
        Rvalue::Cast(_, op, _) => operand_scalar_uses(cx, op, out),
        Rvalue::BinaryOp(_, boxed) => {
            let (a, b) = &**boxed;
            operand_scalar_uses(cx, a, out);
            operand_scalar_uses(cx, b, out);
        }
        Rvalue::Ref(_, _, place)
        | Rvalue::RawPtr(_, place)
        | Rvalue::CopyForDeref(place)
        | Rvalue::Reborrow(_, _, place) => {
            place_scalar_uses(cx, place, out)
        }
        Rvalue::Discriminant(place) => place_scalar_uses(cx, place, out),
        Rvalue::Aggregate(_, ops) => {
            for op in ops.iter() {
                operand_scalar_uses(cx, op, out);
            }
        }
        Rvalue::ThreadLocalRef(_) | Rvalue::WrapUnsafeBinder(_, _) => {}
    }
}

/// SSA-scalar locals read by a terminator (the switch/assert/call operands, the
/// return place, the call args, and any projected destination's index locals).
fn terminator_scalar_uses(cx: &Cx<'_, '_>, kind: &TerminatorKind<'_>, out: &mut BTreeSet<Local>) {
    match kind {
        TerminatorKind::Return => {
            let ret = Local::from_u32(0);
            if is_ssa(cx, ret) {
                out.insert(ret);
            }
        }
        TerminatorKind::SwitchInt { discr, .. } => operand_scalar_uses(cx, discr, out),
        TerminatorKind::Assert { cond, msg, .. } => {
            operand_scalar_uses(cx, cond, out);
            // UNWIND lane: the failure arm CALLS the core::panicking entry
            // point with the message's VALUE operands (BoundsCheck index/len,
            // Misaligned required/found) — those reads must be live. Under
            // panic=abort the failure path is a trap that reads nothing, so
            // the scan is unchanged (byte-stable).
            if eh_lane(cx.tcx) && assert_panic_langcall(msg).is_some() {
                match &**msg {
                    AssertKind::BoundsCheck { len, index } => {
                        operand_scalar_uses(cx, len, out);
                        operand_scalar_uses(cx, index, out);
                    }
                    AssertKind::MisalignedPointerDereference { required, found } => {
                        operand_scalar_uses(cx, required, out);
                        operand_scalar_uses(cx, found, out);
                    }
                    // The `CheckEnums` shape defines the widened `u128` source
                    // in the GUARD block and asserts on it in the failure
                    // block — a genuinely cross-block read.
                    AssertKind::InvalidEnumConstruction(source) => {
                        operand_scalar_uses(cx, source, out);
                    }
                    _ => {}
                }
            }
        }
        TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } => {
            operand_scalar_uses(cx, func, out);
            for a in args.iter() {
                operand_scalar_uses(cx, &a.node, out);
            }
            // A projected destination addresses through the slot; capture any
            // Index local it uses.
            if !destination.projection.is_empty() {
                place_scalar_uses(cx, destination, out);
            }
        }
        // RUNG 4: a Drop reads its place (the address to destruct) — capture any
        // SSA-pointer base / Index local the place projection references.
        TerminatorKind::Drop { place, .. } => place_scalar_uses(cx, place, out),
        _ => {}
    }
}

/// SSA-scalar locals DEFINED in a block (an Assign to a bare SSA scalar local, or
/// a Call whose destination is a bare SSA scalar local).
fn block_scalar_defs(cx: &Cx<'_, '_>, data: &rustc_middle::mir::BasicBlockData<'_>) -> BTreeSet<Local> {
    let mut defs = BTreeSet::new();
    for stmt in &data.statements {
        if let StatementKind::Assign(boxed) = &stmt.kind {
            let (place, _) = &**boxed;
            if place.projection.is_empty() && is_ssa(cx, place.local) {
                defs.insert(place.local);
            }
        }
    }
    if let Some(term) = &data.terminator {
        if let TerminatorKind::Call { destination, .. } = &term.kind {
            if destination.projection.is_empty() && is_ssa(cx, destination.local) {
                defs.insert(destination.local);
            }
        }
    }
    defs
}

/// SSA-scalar locals USED in a block before any (re)definition in that block — the
/// block's upward-exposed uses (`gen` set for liveness).
fn block_scalar_upward_uses(
    cx: &Cx<'_, '_>,
    data: &rustc_middle::mir::BasicBlockData<'_>,
) -> BTreeSet<Local> {
    let mut defined: BTreeSet<Local> = BTreeSet::new();
    let mut uses: BTreeSet<Local> = BTreeSet::new();
    let add_uses = |from: &BTreeSet<Local>, defined: &BTreeSet<Local>, uses: &mut BTreeSet<Local>| {
        for &l in from {
            if !defined.contains(&l) {
                uses.insert(l);
            }
        }
    };
    for stmt in &data.statements {
        match &stmt.kind {
            StatementKind::Assign(boxed) => {
                let (place, rvalue) = &**boxed;
                let mut rv_uses = BTreeSet::new();
                rvalue_scalar_uses(cx, rvalue, &mut rv_uses);
                // A projected destination addresses through the slot; its Index local
                // is read, not defined.
                if !place.projection.is_empty() {
                    place_scalar_uses(cx, place, &mut rv_uses);
                }
                add_uses(&rv_uses, &defined, &mut uses);
                // Now the def (a bare SSA scalar).
                if place.projection.is_empty() && is_ssa(cx, place.local) {
                    defined.insert(place.local);
                }
            }
            // R5: `copy_nonoverlapping(src, dst, count)` READS src/dst/count (its
            // lowering `lower_copy_nonoverlapping` reads exactly these), so their SSA
            // locals are upward-exposed uses — needed for the cross-block block-param
            // (phi) of a source/dest pointer defined in a predecessor block. (An
            // `Assume` is lowered to nothing, so it reads nothing.)
            StatementKind::Intrinsic(ndi) => {
                if let rustc_middle::mir::NonDivergingIntrinsic::CopyNonOverlapping(cno) = &**ndi {
                    let mut rv_uses = BTreeSet::new();
                    operand_scalar_uses(cx, &cno.src, &mut rv_uses);
                    operand_scalar_uses(cx, &cno.dst, &mut rv_uses);
                    operand_scalar_uses(cx, &cno.count, &mut rv_uses);
                    add_uses(&rv_uses, &defined, &mut uses);
                }
            }
            // `SetDiscriminant((*ptr)) = N` (the coroutine state machine's
            // per-suspend/return state write, and any enum-tag write through a
            // pointer) READS the place's base pointer — capture any SSA-pointer
            // base / Index local so a pointer defined in a predecessor block is
            // threaded here as a block parameter (phi). `lower_set_discriminant`
            // reads exactly this place via `place_address`.
            StatementKind::SetDiscriminant { place, .. } => {
                let mut u = BTreeSet::new();
                place_scalar_uses(cx, place, &mut u);
                add_uses(&u, &defined, &mut uses);
            }
            _ => {}
        }
    }
    if let Some(term) = &data.terminator {
        let mut t_uses = BTreeSet::new();
        terminator_scalar_uses(cx, &term.kind, &mut t_uses);
        add_uses(&t_uses, &defined, &mut uses);
    }
    uses
}

/// UNWIND (panic=unwind) lane: whether this compilation session lowers unwind edges
/// FAITHFULLY — `Call`/`Drop` cleanup edges become `Invoke` + `LandingPad`
/// pads, cleanup blocks are emitted, and `UnwindResume` becomes `Resume`.
/// Under panic=abort (every pre-existing lane) NOTHING changes: cleanup is
/// modeled as a trap and unwind edges stay elided, byte-for-byte.
fn eh_lane(tcx: TyCtxt<'_>) -> bool {
    // `.unwinds()` == `PanicStrategy::Unwind` (avoids naming rustc_target).
    tcx.sess.panic_strategy().unwinds()
}

/// Whether an instance is an `extern "C"`-family function — a FOREIGN item
/// (`_Unwind_RaiseException`), or a Rust fn DEFINED with a non-Rust ABI
/// (`rust_eh_personality`, `exception_cleanup`). Such a boundary uses the C
/// calling convention: a single-scalar-repr return (a fieldless `#[repr(C)]`
/// enum like `_Unwind_Reason_Code`) crosses BY VALUE in w0/x0, never via an
/// sret hidden pointer. Shims and closures are Rust-ABI by construction.
fn instance_is_extern_c<'tcx>(tcx: TyCtxt<'tcx>, instance: Instance<'tcx>) -> bool {
    if !matches!(instance.def, ty::InstanceKind::Item(_)) {
        return false;
    }
    let did = instance.def_id();
    if tcx.is_foreign_item(did) {
        return true;
    }
    if !matches!(
        tcx.def_kind(did),
        rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn
    ) {
        return false;
    }
    !tcx.fn_sig(did).skip_binder().abi().is_rustic_abi()
}

/// Whether a `Call`'s resolved callee is an `extern "C"`-family fn (see
/// `instance_is_extern_c`) — the caller-side twin: the call's RETURN
/// classification must then use the C scalar convention.
fn callee_is_extern_c<'tcx>(cx: &Cx<'tcx, '_>, func: &Operand<'tcx>) -> bool {
    resolve_call_callee(cx, func)
        .map(|i| instance_is_extern_c(cx.tcx, i))
        .unwrap_or(false)
}

/// UNWIND lane: which VALUE operands an assert-failure panic entry point takes
/// before the trailing `&'static Location` argument (rustc's
/// `codegen_assert_terminator` argument shapes).
#[derive(Clone, Copy)]
enum AssertPanicArgs {
    /// `fn panic_...( &Location )` — the `panic_const_*` family, div/rem-zero,
    /// null-pointer-deref: location only.
    LocationOnly,
    /// `fn panic_bounds_check(index: usize, len: usize, &Location)`.
    BoundsCheck,
    /// `fn panic_misaligned_pointer_dereference(required, found, &Location)`.
    Misaligned,
    /// `fn panic_invalid_enum_construction(source: u128, &Location)` — the
    /// `CheckEnums` ub-check (`-Zub-checks` / debug-assertions sessions; the
    /// battery's default-O0 emit lane is such a session). The source value
    /// rides as ONE `U128` (rustc widens + masks the discriminant to `u128`
    /// in MIR before the assert, so the operand is already `u128`-typed).
    InvalidEnum,
}

/// Both panic lanes: a SIZE-SCALED raw-memory intrinsic mono (`copy` /
/// `write_bytes`) whose call site lowers INLINE with the element
/// stride baked in from the mono's layout. These intrinsics reach call sites
/// as REAL extern monos when the collector keeps the un-inlined intrinsic
/// call; the historical byte-scaled C harness leaves are silently wrong for
/// any element with size != 1 (the wp20 smallsort merge corruption over
/// `(&[u8], u64)`), so the lowering scales the count itself and never
/// references the intrinsic symbol. A zero-sized mono is a true no-op and
/// declares no foreign leaf.
#[derive(Clone, Copy)]
enum MemIntrinsicInline {
    /// `copy<Zst>`: exactly zero bytes for every element count. This remains a
    /// frontend no-op and does not declare/call libc `memmove`.
    ZstCopy,
    /// `write_bytes<Zst>`: exactly zero bytes for every element count. This
    /// remains a frontend no-op and does not declare/call libc `memset`.
    ZstWriteBytes,
    /// `copy<T>(src, dst, count)`: overlap-tolerant — a libc `memmove(dst,
    /// src, count * stride)` call (genuine system leaf).
    Copy {
        stride: u64,
        memmove: trust_ir::FuncId,
        order: CopyOperandOrder,
    },
    /// `write_bytes<T>(dst, val, count)`: libc `memset(dst, val, count *
    /// stride)` (genuine system leaf).
    WriteBytes {
        stride: u64,
        memset: trust_ir::FuncId,
    },
}

/// Faithful lowering lane for a stable raw-pointer offset wrapper retained as
/// a call in cross-crate MIR. `Gep` is reserved for a proven non-negative
/// in-allocation step. `Integer` models the general signed / wrapping address
/// operation without imposing TrustIR GEP's negative-index UB.
#[derive(Clone, Copy)]
enum RawPtrOffsetInline {
    Gep { stride: u64 },
    Integer { stride: u64 },
}

/// UNWIND lane: an `Assert` failure path lowered as the REAL `core::panicking`
/// call (rustc parity — the panic UNWINDS and is catchable) instead of the
/// abort-lane trap. `fid` is the declared extern entry point; `args` selects
/// which message operands it takes.
#[derive(Clone, Copy)]
struct AssertPanicCall {
    fid: trust_ir::FuncId,
    args: AssertPanicArgs,
}

/// The `core::panicking` entry point for an assert failure — the EXACT mapping
/// rustc's `codegen_assert_terminator` + `AssertKind::panic_function` use, for
/// the assert kinds this lowering supports. Returns the lang item, the value
/// params BEFORE the trailing `&Location` (always appended), and the arg shape.
/// `None` -> keep the historical trap lowering. Every assert kind now maps to a
/// `core::panicking` entry (the coroutine-resume kinds included, since coroutine
/// bodies lower as of this tranche), so `None` is currently unreachable — it is
/// retained so a future assert kind added upstream fails closed to a trap rather
/// than silently miscompiling.
fn assert_panic_langcall(
    msg: &AssertKind<Operand<'_>>,
) -> Option<(rustc_hir::LangItem, Vec<TIRTy>, AssertPanicArgs)> {
    use rustc_hir::LangItem;
    let loc_only = |li: LangItem| Some((li, vec![TIRTy::Ptr], AssertPanicArgs::LocationOnly));
    match msg {
        AssertKind::BoundsCheck { .. } => Some((
            LangItem::PanicBoundsCheck,
            vec![TIRTy::U64, TIRTy::U64, TIRTy::Ptr],
            AssertPanicArgs::BoundsCheck,
        )),
        AssertKind::MisalignedPointerDereference { .. } => Some((
            LangItem::PanicMisalignedPointerDereference,
            vec![TIRTy::U64, TIRTy::U64, TIRTy::Ptr],
            AssertPanicArgs::Misaligned,
        )),
        AssertKind::NullPointerDereference => loc_only(LangItem::PanicNullPointerDereference),
        AssertKind::NullReferenceConstructed => {
            loc_only(LangItem::PanicNullReferenceConstructed)
        }
        AssertKind::Overflow(..)
        | AssertKind::OverflowNeg(_)
        | AssertKind::DivisionByZero(_)
        | AssertKind::RemainderByZero(_) => loc_only(msg.panic_function()),
        // `CheckEnums` ub-check (present in the battery's default-O0 emit
        // sessions): `fn panic_invalid_enum_construction(source: u128) -> !`
        // (`#[track_caller]` + `#[rustc_nounwind]`; the MIR assert carries
        // `unwind: Unreachable`, so the emission's plain-call arm applies).
        AssertKind::InvalidEnumConstruction(_) => Some((
            LangItem::PanicInvalidEnumConstruction,
            vec![TIRTy::U128, TIRTy::Ptr],
            AssertPanicArgs::InvalidEnum,
        )),
        // Coroutine-resume asserts: `assert(const false, "resumed after
        // completion")` guarding the Returned/Panicked/Dropped states of a lowered
        // coroutine state machine. Now that coroutine bodies lower, route them to
        // their `panic_const_{async_fn,coroutine,..}_resumed{,_panic,_drop}` entry
        // points — each a `#[track_caller] fn() -> !` (LocationOnly), exactly like
        // the other diverging assert kinds. `panic_function()` picks the entry per
        // the coroutine's desugaring kind.
        AssertKind::ResumedAfterReturn(_)
        | AssertKind::ResumedAfterPanic(_)
        | AssertKind::ResumedAfterDrop(_) => loc_only(msg.panic_function()),
    }
}

// ===== PANIC-CLASS PROOF OBLIGATIONS (rustc `Assert` -> `ProofObligation`) ====
//
// rustc inserts a `TerminatorKind::Assert` exactly where a property MUST hold or
// the program panics: index-in-bounds, arithmetic overflow, division by zero,
// misaligned/null pointer deref, invalid enum construction, coroutine resume.
// The lowering above is faithful about the CONTROL FLOW (condbr to a
// `core::panicking` call under the unwind lane, or to a trap under
// panic=abort) but historically recorded NOTHING about the CLAIM: every
// panic-freedom property rustc handed the producer was silently dropped.
//
// This pass records them, and ONLY records them. Each lowered Assert mints one
// module-level `ProofObligation` with `ProofStatus::Pending` — a stated,
// undischarged obligation, B4-scoped to the function that carries the check and
// carrying the source range so a human can find it. Deliberately NOT done here:
//
//   * no `ProofAnnotation` on any node or function — an annotation CLAIMS the
//     property holds, and nothing in this frontend has established it;
//   * no `ProofAnnotation::ProofRef` linkage — the validator rejects a
//     ProofRef to a non-discharged obligation, and rightly so;
//   * no `PublicObligationIdentity` — that demands a real semantic digest,
//     and there is nothing here to digest it from.
//
// The obligation identity (`source_id` + `assertion_id`) IS the linkage back to
// the check; it round-trips through all four wire formats.

/// The stable `source_id` every obligation this pass mints carries. Versioned
/// so a consumer can tell this schema from a future one.
const ASSERT_OBLIGATION_SOURCE_ID: &str = "trust-ir-frontend/mir-assert@1";

/// Classify one rustc `AssertKind` into (a) the trust-ir obligation kind it
/// routes to, (b) a stable slug for the assertion id, and (c) a human phrase
/// naming what must be proved.
///
/// The two panic-class kinds mirror `trust_verifier_api`'s split:
/// `BoundsCheck` for index-in-bounds and `ArithmeticSafety` for the
/// overflow / div-by-zero family (shift-amount overflow arrives as
/// `Overflow(BinOp::Shl | Shr, ..)`, so this matches on the AssertKind VARIANT
/// and never on the inner `BinOp`).
///
/// The alignment and non-null kinds are `MemorySafety`, NOT `PanicFreedom`.
/// An earlier revision of this function filed them as `PanicFreedom` on the
/// stated grounds that "`MemorySafety` routes to borrow-checking ... would send
/// a panic-freedom VC to the wrong router". That rationale was FALSE — no such
/// router exists (an exhaustive search of the trust-cg backend finds zero
/// production matches on `ObligationKind`, and `trust-ir-ay`'s
/// `vc_addressable_kind` treats `MemorySafety` / `PanicFreedom` /
/// `ArithmeticSafety` / `BoundsCheck` identically). The kind is not a routing
/// hint; it is the obligation's TAXONOMY, and trust-ir's own canonical routing
/// table is `ProofAnnotation::obligation_kind()`
/// (`crates/trust-ir/src/proof/annotations.rs`), which sends `NotNull` and
/// `Aligned(_)` — the exact facts these two AssertKinds encode — to
/// `MemorySafety`.
///
/// The consequence of getting it wrong is not cosmetic: `proof_ref_kind_can_back`
/// (`crates/trust-ir-build/src/validate.rs`) is a real behavioral gate, and it
/// REJECTS a `ProofAnnotation::NotNull` / `Aligned(_)` claim referencing a
/// `PanicFreedom` obligation (`ProofRefKindMismatch`). Filing these rows as
/// `PanicFreedom` therefore makes them structurally impossible to ever
/// discharge-and-link, which is the entire point of recording them.
///
/// The coroutine-resume kinds stay `PanicFreedom`: their natural claim is
/// `NoPanic`, which routes to `PanicFreedom` and which `proof_ref_kind_can_back`
/// accepts. `InvalidEnumConstruction` also stays `PanicFreedom` for now —
/// `TypeInvariant` is arguably the principled fit, but no corpus has yet
/// produced one, so there is no measured evidence to move it on.
///
/// Exhaustive on purpose, matching `assert_panic_langcall` directly above: a
/// new upstream `AssertKind` must fail the BUILD here rather than silently
/// fall into a wildcard bucket and be misclassified.
fn assert_obligation_class(
    msg: &AssertKind<Operand<'_>>,
) -> (trust_ir::ObligationKind, &'static str, &'static str) {
    use trust_ir::ObligationKind as Kind;
    match msg {
        AssertKind::BoundsCheck { .. } => (Kind::BoundsCheck, "bounds_check", "index is in bounds"),
        AssertKind::Overflow(..) => (
            Kind::ArithmeticSafety,
            "overflow",
            "arithmetic does not overflow",
        ),
        AssertKind::OverflowNeg(_) => (
            Kind::ArithmeticSafety,
            "overflow_neg",
            "negation does not overflow",
        ),
        AssertKind::DivisionByZero(_) => {
            (Kind::ArithmeticSafety, "div_by_zero", "divisor is nonzero")
        }
        AssertKind::RemainderByZero(_) => (
            Kind::ArithmeticSafety,
            "rem_by_zero",
            "remainder divisor is nonzero",
        ),
        AssertKind::MisalignedPointerDereference { .. } => (
            Kind::MemorySafety,
            "misaligned_ptr",
            "pointer is sufficiently aligned",
        ),
        AssertKind::NullPointerDereference => {
            (Kind::MemorySafety, "null_ptr", "pointer is nonnull")
        }
        AssertKind::NullReferenceConstructed => {
            (Kind::MemorySafety, "null_ref", "reference is nonnull")
        }
        AssertKind::InvalidEnumConstruction(_) => (
            Kind::PanicFreedom,
            "invalid_enum",
            "discriminant is a valid variant",
        ),
        AssertKind::ResumedAfterReturn(_) => (
            Kind::PanicFreedom,
            "resumed_after_return",
            "coroutine is not resumed after returning",
        ),
        AssertKind::ResumedAfterPanic(_) => (
            Kind::PanicFreedom,
            "resumed_after_panic",
            "coroutine is not resumed after panicking",
        ),
        AssertKind::ResumedAfterDrop(_) => (
            Kind::PanicFreedom,
            "resumed_after_drop",
            "coroutine is not resumed after dropping",
        ),
    }
}

/// Make an arbitrary frontend string safe as a `ProofObligation` source or
/// assertion id: control chars become `_`, the result is trimmed and truncated
/// to the format's byte cap on a char boundary, and an empty result degrades to
/// `fallback`. Makes `validate_module`'s `InvalidProofObligationSourceTextId`
/// unconstructible regardless of what a mangled symbol contains.
fn clamp_proof_text_id(value: &str, fallback: &'static str) -> String {
    let cleaned: String = value
        .chars()
        .map(|c| if c.is_control() { '_' } else { c })
        .collect();
    let trimmed = cleaned.trim();
    let mut out = String::new();
    for (offset, ch) in trimmed.char_indices() {
        if offset + ch.len_utf8() > trust_ir::PROOF_OBLIGATION_SOURCE_TEXT_ID_MAX_BYTES {
            break;
        }
        out.push(ch);
    }
    // Truncation can expose trailing whitespace the pre-truncation trim removed.
    let out = out.trim().to_string();
    if out.is_empty() {
        fallback.to_string()
    } else {
        out
    }
}

/// Build an assert's `assertion_id` so it stays under the source-text-id byte
/// cap WITHOUT losing the tail that makes it unique.
///
/// The identity is `{symbol}#bb{index}#{slug}`, and the `#bb{index}#{slug}`
/// suffix is the ONLY part distinguishing two asserts in the same function. A
/// naive length clamp truncates the tail, so a sufficiently long mangled symbol
/// would collapse every assert in that function onto ONE id. That collision is
/// invisible to the validator, which checks obligation `id` uniqueness
/// (`DuplicateProofObligationId`) but never `assertion_id`. So clamp the
/// SYMBOL and always keep the suffix.
///
/// Not reachable on today's corpora (max observed 391 bytes against a 1024-byte
/// cap), but the failure mode is silent, so it is closed structurally rather
/// than left to headroom.
fn assert_assertion_id(symbol: &str, index: usize, slug: &'static str) -> String {
    let max = trust_ir::PROOF_OBLIGATION_SOURCE_TEXT_ID_MAX_BYTES;
    let suffix = format!("#bb{index}#{slug}");
    // Degenerate guard: if the suffix alone cannot fit there is no identity to
    // preserve, so fall back to the plain clamp over it.
    if suffix.len() >= max {
        return clamp_proof_text_id(&suffix, slug);
    }
    let budget = max - suffix.len();
    let cleaned: String = symbol
        .chars()
        .map(|c| if c.is_control() { '_' } else { c })
        .collect();
    let mut head = String::new();
    for (offset, ch) in cleaned.trim().char_indices() {
        if offset + ch.len_utf8() > budget {
            break;
        }
        head.push(ch);
    }
    clamp_proof_text_id(&format!("{}{suffix}", head.trim_end()), slug)
}

/// Keep an obligation `description` on one line and free of the text format's
/// string delimiters. (`Display` writes it with `{:?}`, so a quote or backslash
/// would round-trip fine but makes the emitted `.trust_ir` far less greppable;
/// a newline would break the one-obligation-per-line shape entirely.)
fn clamp_proof_description(value: &str) -> String {
    value
        .chars()
        .map(|c| match c {
            '"' | '\\' => '\'',
            c if c.is_control() => ' ',
            c => c,
        })
        .collect()
}

/// PRE-PASS (runs BEFORE the `FunctionBuilder` takes the module's exclusive
/// borrow): record one `Pending` `ProofObligation` per Assert this lowering
/// will actually emit. Returns how many were recorded.
///
/// `fid` must be the id the body about to be built will occupy — the caller
/// reads it from `ModuleBuilder::peek_next_func_id`, which is the authority.
/// Only NORMAL-REACHABLE blocks are considered: a block this lowering does not
/// emit carries no claim we are entitled to state.
fn record_assert_obligations<'tcx>(
    cx: &Cx<'tcx, '_>,
    mb: &mut ModuleBuilder,
    body: &Body<'tcx>,
    fid: trust_ir::FuncId,
    normal_reachable: &HashSet<usize>,
    span_map: &SpanMap,
) -> Vec<(trust_ir::ProofId, usize)> {
    // IDENTITY vs. READABILITY, deliberately split:
    //   * `symbol` — the mono-precise, ASCII, stable mangled symbol — keys the
    //     machine-readable `assertion_id`, so two monomorphizations of the same
    //     generic never collide;
    //   * `path` — the source-level def path — goes in the human `description`,
    //     because `trust-ir dump` output naming `_RNvCs..12probe_bounds` tells a
    //     reader nothing.
    let symbol = cx.tcx.symbol_name(cx.instance).name.to_string();
    let path = cx.tcx.def_path_str(cx.instance.def_id());
    let mut recorded: Vec<(trust_ir::ProofId, usize)> = Vec::new();
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        let index = bb.as_usize();
        if !normal_reachable.contains(&index) {
            continue;
        }
        let Some(term) = &data.terminator else {
            continue;
        };
        let TerminatorKind::Assert { msg, .. } = &term.kind else {
            continue;
        };
        let (kind, slug, phrase) = assert_obligation_class(msg);
        let mut source = trust_ir::ProofObligationSourceIdentity::new(
            ASSERT_OBLIGATION_SOURCE_ID,
            assert_assertion_id(&symbol, index, slug),
        );
        if let Some(range) = span_map.to_ir_range(cx.tcx, term.source_info.span) {
            source = source.with_range(range);
        }
        let description = clamp_proof_description(&format!(
            "rustc MIR Assert ({slug}) at bb{index} of `{path}`: {phrase}. \
             RECORDED BY THE FRONTEND, NOT PROVED."
        ));
        let id = mb.add_proof_obligation(|id| {
            trust_ir::ProofObligation::new(id, kind, trust_ir::ProofStatus::Pending, description)
                .with_function(fid)
                .with_source(source)
        });
        recorded.push((id, index));
    }
    recorded
}

/// Record the `(mir_bb, block, inst_index)` of the lowered-`Assert` `CondBr`
/// the caller JUST emitted.
///
/// Reads the position back out of the builder rather than recomputing it: the
/// only correctness property that matters here is that the site names the
/// instruction the obligation is about, and a producer-side recomputation is
/// exactly the kind of bookkeeping that drifts silently under refactoring.
/// A builder that cannot report a position is a hard error, not a skipped site.
fn record_assert_site(
    fb: &trust_ir_build::FunctionBuilder<'_>,
    tc: &mut TermCtx<'_>,
) -> Result<(), String> {
    let (block, index) = fb.last_emitted_position().ok_or_else(|| {
        "Assert lowering emitted a CondBr but the builder reports no last position".to_string()
    })?;
    tc.assert_sites.push((tc.mir_bb, block, index));
    Ok(())
}

/// Per-kind tally of the `Pending` panic-class obligations a lowered module
/// carries. Reported by the coverage driver so the census states how many
/// panic-freedom claims the Rust producer is now recording (and was previously
/// dropping) rather than leaving it to be inferred.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct ObligationTally {
    pub total: usize,
    pub bounds_check: usize,
    pub arithmetic_safety: usize,
    pub panic_freedom: usize,
    /// Alignment (`misaligned_ptr`) and non-nullness (`null_ptr` / `null_ref`)
    /// rows. A named bucket rather than the `_ => {}` wildcard on purpose: they
    /// are the DOMINANT class on real corpora, and letting them fall through
    /// would print `panic_freedom=0` next to `total=70` — a silently misleading
    /// census.
    pub memory_safety: usize,
    /// Rows whose kind is none of the four named buckets. Never silently
    /// dropped: a nonzero value here means the classifier grew a kind the
    /// banner does not name yet.
    pub other_kind: usize,
    /// Rows whose source identity carries a resolved source range.
    pub with_range: usize,
    /// Rows carrying a v34 `ObligationSite` — the IR-position backref a
    /// verifier needs to bind the obligation to the ONE condition that can back
    /// it. A row without one is unbindable and fail-closed downstream, so the
    /// census reports it rather than leaving it to be assumed.
    pub with_site: usize,
    /// Rows carrying a status OTHER than `Pending`. Must always be 0 for this
    /// frontend: it records claims, it never discharges them.
    pub non_pending: usize,
    /// Per-`AssertKind` breakdown, keyed by the `assert_obligation_class` slug
    /// recovered from the assertion id's trailing `#`-segment. Says WHICH
    /// checks the panic-freedom bucket is made of (a bucket dominated by
    /// alignment checks is a different fact than one dominated by coroutine
    /// resume guards), so the mapping stays reviewable.
    pub by_check: BTreeMap<String, usize>,
}

impl ObligationTally {
    pub fn of_module(module: &trust_ir::Module) -> Self {
        let mut tally = Self::default();
        for oblig in &module.proof_obligations {
            tally.total += 1;
            match oblig.kind {
                trust_ir::ObligationKind::BoundsCheck => tally.bounds_check += 1,
                trust_ir::ObligationKind::ArithmeticSafety => tally.arithmetic_safety += 1,
                trust_ir::ObligationKind::PanicFreedom => tally.panic_freedom += 1,
                trust_ir::ObligationKind::MemorySafety => tally.memory_safety += 1,
                _ => tally.other_kind += 1,
            }
            if oblig.status != trust_ir::ProofStatus::Pending {
                tally.non_pending += 1;
            }
            if oblig.site.is_some() {
                tally.with_site += 1;
            }
            if let Some(source) = &oblig.source {
                if source.range.is_some() {
                    tally.with_range += 1;
                }
                if source.source_id == ASSERT_OBLIGATION_SOURCE_ID {
                    let slug = source
                        .assertion_id
                        .rsplit('#')
                        .next()
                        .unwrap_or("unknown")
                        .to_string();
                    *tally.by_check.entry(slug).or_insert(0) += 1;
                }
            }
        }
        tally
    }

    pub fn add(&mut self, other: Self) {
        self.total += other.total;
        self.bounds_check += other.bounds_check;
        self.arithmetic_safety += other.arithmetic_safety;
        self.panic_freedom += other.panic_freedom;
        self.memory_safety += other.memory_safety;
        self.other_kind += other.other_kind;
        self.with_range += other.with_range;
        self.with_site += other.with_site;
        self.non_pending += other.non_pending;
        for (slug, count) in other.by_check {
            *self.by_check.entry(slug).or_insert(0) += count;
        }
    }
}

/// UNWIND lane pre-pass bookkeeping: which blocks' terminators will be emitted
/// as a FAITHFUL `Invoke` with a real unwind edge. Recorded by the Call/Drop
/// pre-passes in `lower_with_signature` — the branches whose emission produces
/// a DIRECT call, the `Assert` failure paths that call a `core::panicking`
/// entry point, and the INDIRECT/virtual/dyn-drop call sites whose cleanup
/// edge is carried through a synthesized per-signature THUNK (trust-ir
/// `Invoke` is direct-only by format; `Invoke(thunk, fnptr, args..)` keeps the
/// format untouched while the unwind propagates through the pad-less thunk
/// frame into this caller's real cleanup pad).
#[derive(Default)]
struct EhEdges {
    /// block index -> its `UnwindAction::Cleanup` target (a real pad edge).
    cleanup: HashMap<usize, usize>,
    /// blocks whose call/drop has `UnwindAction::Terminate` (shared trap pad).
    terminate: HashSet<usize>,
    /// blocks whose `Call` is the `catch_unwind` intrinsic, pre-lowered to the
    /// inline `__rust_try` invoke/pad shape: (do_call FuncId, do_catch FuncId).
    catch_expand: HashMap<usize, (trust_ir::FuncId, trust_ir::FuncId)>,
}

/// The fixed index of an `UnwindTerminateReason` in the per-reason terminate
/// fid/pad arrays: 0 = `Abi` (`panic_cannot_unwind`), 1 = `InCleanup`
/// (`panic_in_cleanup`). Mirrors `UnwindTerminateReason::lang_item()`.
fn terminate_reason_idx(reason: rustc_middle::mir::UnwindTerminateReason) -> usize {
    match reason {
        rustc_middle::mir::UnwindTerminateReason::Abi => 0,
        rustc_middle::mir::UnwindTerminateReason::InCleanup => 1,
    }
}

impl EhEdges {
    /// Record a faithful direct call/drop's unwind action (EH lane only).
    fn record(&mut self, eh: bool, bb: usize, unwind: &rustc_middle::mir::UnwindAction) {
        if !eh {
            return;
        }
        match unwind {
            rustc_middle::mir::UnwindAction::Cleanup(t) => {
                self.cleanup.insert(bb, t.as_usize());
            }
            rustc_middle::mir::UnwindAction::Terminate(_) => {
                self.terminate.insert(bb);
            }
            _ => {}
        }
    }

    /// Does any block in `reachable` synthesize a landing pad?
    fn any_pads(&self, reachable: &HashSet<usize>) -> bool {
        reachable.iter().any(|b| {
            self.cleanup.contains_key(b)
                || self.terminate.contains(b)
                || self.catch_expand.contains_key(b)
        })
    }
}

/// UNWIND lane: get-or-synthesize the per-signature INDIRECT-CALL THUNK for
/// `sig` — the sound carrier of a cleanup edge on an indirect (fn-pointer /
/// dyn-dispatch / dyn-drop) call site. trust-ir `Invoke` is direct-only BY
/// FORMAT, so the call site becomes `Invoke(thunk, fnptr, args.., pad)` where
/// the thunk is a tiny DIRECT fn `(fnptr: Ptr, args..) -> rets` whose body is
/// exactly one `CallIndirect(fnptr)(args..)` + `Return`. The thunk has NO
/// landing pads: a panic in the real callee unwinds straight through the
/// thunk frame (its always-emitted unwind tables) and phase-2 lands in the
/// INVOKING frame's pad — the caller's cleanup runs, faithfully.
///
/// One thunk per DISTINCT signature, shared across this module's call sites
/// (`cache`). The symbol is suffixed with the host body's mangled symbol so
/// two modules' thunks never collide at whole-program link.
fn get_or_make_indirect_thunk(
    mb: &mut ModuleBuilder,
    cache: &mut HashMap<trust_ir::FuncTyId, trust_ir::FuncId>,
    n_declared: &mut u32,
    host_sym: &str,
    sig: trust_ir::FuncTyId,
    params: &[TIRTy],
    returns: &[TIRTy],
) -> Result<trust_ir::FuncId, String> {
    if let Some(&fid) = cache.get(&sig) {
        return Ok(fid);
    }
    if returns.len() > 1 {
        return Err(format!(
            "indirect-call thunk: multi-return signature not modeled ({} returns)",
            returns.len()
        ));
    }
    let mut thunk_params = Vec::with_capacity(params.len() + 1);
    thunk_params.push(TIRTy::Ptr);
    thunk_params.extend(params.iter().cloned());
    let thunk_ty = mb.add_func_type(thunk_params, returns.to_vec());
    // `cache.len()` disambiguates multiple thunks within one module; `host_sym`
    // (the body's unique mangled symbol) disambiguates across modules.
    let name = format!("__tir_ithunk{}__{host_sym}", cache.len());
    let mut fbt = mb.function(name, thunk_ty);
    let entry = fbt.create_block();
    fbt.set_entry(entry);
    fbt.switch_to_block(entry);
    let fnptr = fbt.add_block_param(entry, TIRTy::Ptr);
    let mut args = Vec::with_capacity(params.len());
    for t in params {
        args.push(fbt.add_block_param(entry, t.clone()));
    }
    if returns.is_empty() {
        fbt.call_indirect_void(fnptr, sig, args);
        fbt.ret(Vec::new());
    } else {
        let r = fbt.call_indirect(fnptr, sig, args);
        fbt.ret(vec![r]);
    }
    let fid = fbt.build();
    *n_declared += 1;
    cache.insert(sig, fid);
    Ok(fid)
}

/// UNWIND lane: the `&'static core::panic::Location` value for a panic entry
/// call / `caller_location()` intrinsic — rustc's `FunctionCx::
/// get_caller_location`, faithfully: walk the inlined scopes
/// (`caller_location_span`); if the walk stops inside an inlined
/// non-track_caller frame the Location is that span's CTFE'd const; if it
/// reaches this body's root and the body IS `#[track_caller]`, FORWARD the
/// hidden Location parameter (`cx.caller_location` — bound at entry); a
/// non-track_caller root materializes its own span (rustc semantics for a
/// plain caller of `caller_location()`).
fn get_caller_location<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    source_info: rustc_middle::mir::SourceInfo,
) -> Result<trust_ir::ValueId, String> {
    cx.body
        .caller_location_span(source_info, cx.caller_location.map(Ok), cx.tcx, |span| {
            span_caller_location_const(cx, fb, span)
        })
}

/// Materialize the CTFE'd `Location` allocation for `span` as a read-only
/// module global (bytes + the file-name `&str` relocation), yielding its
/// address (`span_as_caller_location` + `intern_alloc_global`).
fn span_caller_location_const<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    span: rustc_span::Span,
) -> Result<trust_ir::ValueId, String> {
    let cv = cx.tcx.span_as_caller_location(span);
    let ConstValue::Scalar(Scalar::Ptr(ptr, _)) = cv else {
        return Err(format!(
            "span_as_caller_location did not yield a const pointer ({cv:?})"
        ));
    };
    let (prov, offset) = ptr.prov_and_relative_offset();
    let gid = intern_alloc_global(cx, prov.alloc_id())?;
    let base = fb.global_addr(gid);
    let off = offset.bytes();
    Ok(if off == 0 {
        base
    } else {
        gep_byte_offset(fb, base, off)
    })
}

/// UNWIND lane, `#[track_caller]` ABI: whether this `Call`'s resolved callee
/// takes the hidden trailing `&'static Location` parameter
/// (`InstanceKind::requires_caller_location` — `Item`/`Virtual`/`VTableShim`
/// with the TRACK_CALLER codegen attr, or a `ClosureOnce` shim carrying the
/// flag). The SAME predicate drives the signature synthesis
/// (`call_signature_params_returns`), the arg push at the Call emission site,
/// and the callee BODY's own param append (`lower_with_signature`), so every
/// edge agrees by construction. Always `false` under panic=abort (byte
/// stability) and for an unresolvable (fn-pointer) callee — a reified
/// `fn()` pointer never carries the location ABI (rustc routes those through
/// `ReifyShim`).
fn callee_needs_caller_location<'tcx>(cx: &Cx<'tcx, '_>, func: &Operand<'tcx>) -> bool {
    eh_lane(cx.tcx)
        && resolve_call_callee(cx, func)
            .is_some_and(|i| i.def.requires_caller_location(cx.tcx))
}

/// The successors of a MIR terminator AS THIS LOWERING EMITS THEM: the normal
/// (happy-path) edges always, plus — under the EH lane — the faithful cleanup
/// edge the pre-pass recorded for this block (`EhEdges.cleanup`), which becomes
/// a real `Invoke` unwind edge through a synthesized landing pad. Drives both
/// reachability (which MIR blocks get a trust-ir block) and scalar liveness
/// (which locals thread as block params), so the two stay consistent by
/// construction. Under panic=abort the recorded set is empty and this is
/// exactly `normal_successors`.
fn successors_for_lowering(
    kind: &TerminatorKind<'_>,
    bb_idx: usize,
    eh_edges: &EhEdges,
) -> Vec<usize> {
    let mut s = normal_successors(kind);
    if let Some(&u) = eh_edges.cleanup.get(&bb_idx) {
        s.push(u);
    }
    s
}

/// The NORMAL (non-unwind, non-cleanup) successors of a MIR terminator — the edges
/// this minimal lowering actually emits. A `Drop`/`Call`/`Assert`/`FalseUnwind`'s
/// unwind/cleanup edge is EXCLUDED (we model the cleanup path as a trap, not a real
/// edge), so a block reachable ONLY through unwind edges is not emitted at all. The
/// happy-path edges (`target`, switch arms, goto) are the ones we keep.
fn normal_successors(kind: &TerminatorKind<'_>) -> Vec<usize> {
    match kind {
        TerminatorKind::Goto { target } => vec![target.as_usize()],
        TerminatorKind::SwitchInt { targets, .. } => {
            targets.all_targets().iter().map(|t| t.as_usize()).collect()
        }
        TerminatorKind::Call { target, .. } => target.iter().map(|t| t.as_usize()).collect(),
        TerminatorKind::Drop { target, .. } => vec![target.as_usize()],
        TerminatorKind::Assert { target, .. } => vec![target.as_usize()],
        TerminatorKind::FalseUnwind { real_target, .. } => vec![real_target.as_usize()],
        TerminatorKind::FalseEdge { real_target, .. } => vec![real_target.as_usize()],
        TerminatorKind::Yield { resume, .. } => vec![resume.as_usize()],
        // No normal successor: Return / Unreachable / UnwindResume / UnwindTerminate
        // / CoroutineDrop / TailCall / InlineAsm (the last fails loud anyway).
        _ => Vec::new(),
    }
}

/// The set of MIR block indices REACHABLE from the entry block over the edges
/// this lowering emits (`successors_for_lowering`): normal edges always, plus
/// `Call`/`Drop` cleanup edges under the EH lane. A block reachable solely via
/// an excluded edge (any unwind edge under abort; an assert unwind edge under
/// EH) is not emitted, so it never becomes an orphan (validation-error) block.
/// Soundness: an emitted terminator's target is, by construction, in this set,
/// so every edge the lowering emits points at an emitted block.
fn compute_normal_reachable(body: &Body<'_>, eh_edges: &EhEdges) -> HashSet<usize> {
    let mut reachable: HashSet<usize> = HashSet::new();
    let mut stack: Vec<usize> = vec![0];
    reachable.insert(0);
    while let Some(b) = stack.pop() {
        let data = &body.basic_blocks[BasicBlock::from_usize(b)];
        if let Some(term) = &data.terminator {
            for s in successors_for_lowering(&term.kind, b, eh_edges) {
                if reachable.insert(s) {
                    stack.push(s);
                }
            }
        }
    }
    reachable
}

/// Backward liveness over the SSA-scalar locals: returns, per block index, the
/// set of SSA-scalar locals LIVE AT ENTRY. Standard iterative dataflow:
///   live_in[B]  = use[B] ∪ (live_out[B] \ def[B])
///   live_out[B] = ⋃ live_in[S] for S in successors(B)
/// over the `gen`/`kill` sets above. Memory-backed locals are excluded (they are
/// never SSA, so never appear in any set). Drives the per-block phi parameters.
fn compute_scalar_live_in(
    cx: &Cx<'_, '_>,
    body: &Body<'_>,
    eh_edges: &EhEdges,
) -> Vec<BTreeSet<Local>> {
    let n = body.basic_blocks.len();
    let mut gen: Vec<BTreeSet<Local>> = Vec::with_capacity(n);
    let mut kill: Vec<BTreeSet<Local>> = Vec::with_capacity(n);
    let mut succs: Vec<Vec<usize>> = Vec::with_capacity(n);
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        gen.push(block_scalar_upward_uses(cx, data));
        kill.push(block_scalar_defs(cx, data));
        // Liveness flows only over the successors this lowering actually emits
        // (`successors_for_lowering`). Under panic=abort a cleanup/unwind block is
        // NOT emitted (it is a trap), so a scalar used ONLY inside cleanup (e.g. a
        // drop-elaboration flag that the unwind path's `switchInt` reads) is DEAD in
        // the emitted code and must not be threaded as a block parameter into normal
        // blocks. Under the EH lane the `Call`/`Drop` cleanup edge IS emitted (an
        // `Invoke` through a synthesized pad that forwards the target's live-ins),
        // so liveness must flow across it — the invoke block's live-out then feeds
        // the pad's `br cleanup_bb(args)`. A scalar used on ANY emitted path stays
        // live via that path, so this is liveness-correct in both lanes.
        let s: Vec<usize> = if let Some(term) = &data.terminator {
            successors_for_lowering(&term.kind, bb.as_usize(), eh_edges)
        } else {
            Vec::new()
        };
        succs.push(s);
    }
    let mut live_in: Vec<BTreeSet<Local>> = vec![BTreeSet::new(); n];
    let mut changed = true;
    while changed {
        changed = false;
        // Reverse block order tends to converge faster for backward dataflow.
        for b in (0..n).rev() {
            let mut live_out: BTreeSet<Local> = BTreeSet::new();
            for &s in &succs[b] {
                for &l in &live_in[s] {
                    live_out.insert(l);
                }
            }
            let mut new_in = gen[b].clone();
            for &l in &live_out {
                if !kill[b].contains(&l) {
                    new_in.insert(l);
                }
            }
            if new_in != live_in[b] {
                live_in[b] = new_in;
                changed = true;
            }
        }
    }
    live_in
}

// ============================ RUNG 2: Call callee signature ===================

/// Resolve a call-`func` operand to its monomorphized callee `Instance` (for the
/// stable symbol name). `None` for an indirect call or a callee that does not
/// resolve. Mirrors trust-cg's `resolve_call_callee`.
fn resolve_call_callee<'tcx>(
    cx: &Cx<'tcx, '_>,
    func: &Operand<'tcx>,
) -> Option<Instance<'tcx>> {
    // The callee is statically known when the `func` operand's TYPE is a `FnDef` —
    // either an `FnDef` CONSTANT (`f(x)`), or a `Copy`/`Move` of a `FnDef`-typed
    // ZST value (`(move _self)(x)` inside a `FnPtrShim` body, where `_self:
    // FnDef(g)` uniquely identifies `g`). A ZST `FnDef` carries no runtime data — it
    // IS the function's identity — so calling it is a DIRECT call to that instance.
    let func_ty = match func {
        Operand::Constant(c) => cx.mono(c.const_.ty()),
        Operand::Copy(p) | Operand::Move(p) => cx.place_concrete_ty(p),
        Operand::RuntimeChecks(_) => return None,
    };
    let ty::FnDef(def_id, args) = *func_ty.kind() else {
        return None;
    };
    Instance::try_resolve(cx.tcx, ty::TypingEnv::fully_monomorphized(), def_id, args)
        .ok()
        .flatten()
}

/// Extract the trust-ir memory `Ordering` from an atomic intrinsic's `AtomicOrdering`
/// CONST GENERIC (`core::intrinsics::{atomic_xadd,atomic_xsub,atomic_fence}<.., const
/// ORD: AtomicOrdering>`). The ordering is the sole const arg; its evaluated
/// discriminant is `Relaxed=0`/`Release=1`/`Acquire=2`/`AcqRel=3`/`SeqCst=4` (pinned in
/// `core::intrinsics::AtomicOrdering`). Fail-closed (`Err`) if no const arg is present
/// or its value is not a resolvable leaf in `0..=4`.
/// THREADS: ALL `AtomicOrdering` const generics of an atomic intrinsic, in
/// declaration order — `atomic_cxchg`/`atomic_cxchgweak` carry TWO (success,
/// failure); every other atomic intrinsic carries one.
fn atomic_orderings_from_args<'tcx>(
    args: ty::GenericArgsRef<'tcx>,
) -> Result<Vec<TIROrdering>, String> {
    let mut out = Vec::new();
    for a in args.iter() {
        let Some(c) = a.as_const() else { continue };
        let si = c
            .try_to_branch()
            .and_then(|b| b.first().and_then(|cc| cc.try_to_leaf()))
            .or_else(|| c.try_to_leaf())
            .ok_or_else(|| {
                "atomic intrinsic ordering is not a resolved const value".to_string()
            })?;
        let disc = si.to_uint(si.size());
        out.push(match disc {
            0 => TIROrdering::Relaxed,
            1 => TIROrdering::Release,
            2 => TIROrdering::Acquire,
            3 => TIROrdering::AcqRel,
            4 => TIROrdering::SeqCst,
            n => {
                return Err(format!(
                    "atomic intrinsic ordering discriminant {n} out of range 0..=4"
                ))
            }
        });
    }
    if out.is_empty() {
        return Err("atomic intrinsic has no AtomicOrdering const generic".to_string());
    }
    Ok(out)
}

/// THREADS: the INTEGER lane an atomic intrinsic's `T` computes in, plus
/// whether `T` is a POINTER (so values bridge with PtrToInt/IntToPtr around
/// the integer-lane atomic — `AtomicPtr` CAS in the rwlock queue). Fail-closed
/// on any `T` that is not a 1/2/4/8-byte integer/pointer scalar.
fn atomic_int_lane<'tcx>(cx: &Cx<'tcx, '_>, t: Ty<'tcx>) -> Result<(TIRTy, bool), String> {
    let leaf = cast_scalar_tir_ty(cx, t)
        .ok_or_else(|| format!("atomic intrinsic T is not a scalar ({})", ty_family(t)))?;
    if matches!(leaf, TIRTy::Ptr) {
        return Ok((TIRTy::U64, true));
    }
    if int_bit_width(&leaf).is_none()
        || matches!(leaf, TIRTy::I128 | TIRTy::U128 | TIRTy::Bool)
    {
        return Err(format!("atomic intrinsic T lane not supported ({leaf:?})"));
    }
    Ok((leaf, false))
}

fn atomic_ordering_from_args<'tcx>(
    args: ty::GenericArgsRef<'tcx>,
) -> Result<TIROrdering, String> {
    let ord_const = args
        .iter()
        .find_map(|a| a.as_const())
        .ok_or_else(|| "atomic intrinsic has no AtomicOrdering const generic".to_string())?;
    // `AtomicOrdering` is a fieldless enum: its valtree is a BRANCH whose first
    // element is the variant discriminant leaf (mirrors rustc_codegen_ssa's
    // `parse_atomic_ordering`: `ord.to_branch()[0].to_leaf()`). A defensive leaf
    // fallback covers a scalar-repr representation.
    let si = ord_const
        .try_to_branch()
        .and_then(|b| b.first().and_then(|c| c.try_to_leaf()))
        .or_else(|| ord_const.try_to_leaf())
        .ok_or_else(|| "atomic intrinsic ordering is not a resolved const value".to_string())?;
    let disc = si.to_uint(si.size());
    match disc {
        0 => Ok(TIROrdering::Relaxed),
        1 => Ok(TIROrdering::Release),
        2 => Ok(TIROrdering::Acquire),
        3 => Ok(TIROrdering::AcqRel),
        4 => Ok(TIROrdering::SeqCst),
        n => Err(format!("atomic intrinsic ordering discriminant {n} out of range 0..=4")),
    }
}

/// FLOATS (libm): the C libm symbol a BODILESS float-math intrinsic lowers to —
/// the exact boundary native rustc uses (LLVM legalizes `llvm.pow.f64` & friends
/// to libm calls), so the extern leaf resolves against libSystem at link exactly
/// like `fmod` for `FRem` today.
///   * `Ok(Some(sym))` — declare + call the C symbol (`powf64` -> `pow`, ...).
///   * `Ok(None)`      — not a libm extern: either lowered NATIVELY at the
///     terminator site (the sqrt/floor/ceil/trunc/fabs unary ops, FMin/FMax,
///     the powi loop) or not a float-math intrinsic at all.
///   * `Err`           — a BODILESS float-math intrinsic with NO mapping (the
///     f16/f128 widths): fail loud at emit time, never a silently-undefined
///     mangled extern at whole-program link.
/// `fma`/`fmaf` are the correctly-rounded C99 fused ops — the same
/// single-rounding contract as the intrinsics. `fmuladd` (fused-OR-separate by
/// contract) maps to the fused form, exactly the choice native rustc's
/// `llvm.fmuladd` makes on aarch64 (FMADD). `round_ties_even` == C `rint` under
/// the default nearest-even rounding mode (never changed by us or the runtime).
fn libm_intrinsic_extern_symbol(
    iname: &str,
    must_be_overridden: bool,
) -> Result<Option<&'static str>, String> {
    let mapped = match iname {
        "powf64" => Some("pow"),
        "powf32" => Some("powf"),
        "expf64" => Some("exp"),
        "expf32" => Some("expf"),
        "exp2f64" => Some("exp2"),
        "exp2f32" => Some("exp2f"),
        "logf64" => Some("log"),
        "logf32" => Some("logf"),
        "log2f64" => Some("log2"),
        "log2f32" => Some("log2f"),
        "log10f64" => Some("log10"),
        "log10f32" => Some("log10f"),
        "sinf64" => Some("sin"),
        "sinf32" => Some("sinf"),
        "cosf64" => Some("cos"),
        "cosf32" => Some("cosf"),
        "fmaf64" => Some("fma"),
        "fmaf32" => Some("fmaf"),
        "fmuladdf64" => Some("fma"),
        "fmuladdf32" => Some("fmaf"),
        "copysignf64" => Some("copysign"),
        "copysignf32" => Some("copysignf"),
        "roundf64" => Some("round"),
        "roundf32" => Some("roundf"),
        "round_ties_even_f64" => Some("rint"),
        "round_ties_even_f32" => Some("rintf"),
        _ => None,
    };
    if mapped.is_some() {
        return Ok(mapped);
    }
    // NATIVE terminator-site lowerings: not libm externs, never fail here.
    if matches!(
        iname,
        "sqrtf32"
            | "sqrtf64"
            | "floorf32"
            | "floorf64"
            | "ceilf32"
            | "ceilf64"
            | "truncf32"
            | "truncf64"
            | "fabs"
            | "powif32"
            | "powif64"
            | "minimum_number_nsz_f32"
            | "minimum_number_nsz_f64"
            | "maximum_number_nsz_f32"
            | "maximum_number_nsz_f64"
    ) {
        return Ok(None);
    }
    // FAIL-CLOSED: any OTHER bodiless float-math intrinsic (the f16/f128 widths
    // of the families below) has no lowering — a loud emit-time error, not a
    // dangling mangled extern. Body-carrying float intrinsics (the
    // NaN-propagating `minimumf64`/`maximumf64`, the nsz f16/f128 fallbacks)
    // keep their reference-MIR-body path (`must_be_overridden == false`).
    if must_be_overridden && is_float_math_intrinsic_name(iname) {
        return Err(format!(
            "unmapped libm-class float intrinsic `{iname}` (fail-closed; add a \
             libm mapping or a native lowering)"
        ));
    }
    Ok(None)
}

/// Name test for the bodiless float-math intrinsic FAMILIES (width-suffixed
/// transcendentals + rounding/copysign/fma + the generic `fabs`).
fn is_float_math_intrinsic_name(iname: &str) -> bool {
    const FAMILIES: &[&str] = &[
        "sqrtf",
        "powif",
        "powf",
        "expf",
        "exp2f",
        "logf",
        "log2f",
        "log10f",
        "sinf",
        "cosf",
        "fmaf",
        "fmuladdf",
        "copysignf",
        "floorf",
        "ceilf",
        "truncf",
        "roundf",
        "round_ties_even_f",
        "fabs",
    ];
    FAMILIES.iter().any(|f| iname.starts_with(f))
}

/// Whether a `Call`'s callee resolves to THIS SAME monomorphic instance — a
/// self-recursive call (e.g. `sz(a)` inside `sz`, the `whnf`-style recursion). We
/// compare the resolved callee `Instance` (def_id + monomorphized generic args)
/// against `cx.instance`: equal def_id AND equal args means the very same function,
/// so the emit path wires the call to the in-module body `FuncId` rather than a
/// 0-block extern stub. A DIFFERENT monomorphization of the same generic fn (e.g.
/// `f::<i32>` calling `f::<i64>`) is NOT self-recursion (distinct args) — it stays an
/// extern, which is correct (it is a distinct mono-item, not this body).
fn call_is_self_recursive<'tcx>(cx: &Cx<'tcx, '_>, func: &Operand<'tcx>) -> bool {
    match resolve_call_callee(cx, func) {
        // THREADS fix: compare the WHOLE instance (`def` includes the
        // `InstanceKind`), not just `def_id + args`. A `VTableShim` of
        // `FnOnce::call_once` calls `<{closure} as FnOnce>::call_once`, which
        // resolves to the `ClosureOnce` SHIM of the SAME `def_id` and SAME
        // args — a DIFFERENT function (different shim kind, different symbol).
        // The def_id-only comparison bound that call back to the wrapper
        // itself, emitting a bogus self-call whose dropped-ZST-receiver arg
        // list can never match the wrapper's own signature
        // (`CallArgCountMismatch expected 3 actual 2`).
        Some(callee) => callee == cx.instance,
        None => false,
    }
}

/// Recognize one canonical inherent method on raw pointers by source identity,
/// not by a bare method name. Cross-crate MIR may retain these `#[inline(always)]`
/// core wrappers as calls, so their pointer semantics must not escape the
/// frontend's intrinsic/MIR-domain checks as opaque extern declarations.
fn raw_ptr_method_named<'tcx>(
    cx: &Cx<'tcx, '_>,
    func: &Operand<'tcx>,
    method: &str,
) -> bool {
    let Some(callee) = resolve_call_callee(cx, func) else {
        return false;
    };
    let path = cx.tcx.def_path_str(callee.def_id());
    if std::env::var_os("TRUST_IR_PULL_DEBUG").is_some() {
        eprintln!("RAW-PTR-METHOD? method={method} path={path}");
    }
    path.ends_with(&format!("::{method}"))
        && (path.starts_with("core::ptr::const_ptr::")
            || path.starts_with("core::ptr::mut_ptr::")
            || path.starts_with("std::ptr::const_ptr::")
            || path.starts_with("std::ptr::mut_ptr::"))
}

/// Operand order presented by a copy-shaped MIR call. The core intrinsic,
/// free `ptr::copy*`, and `*const T::copy_to*` APIs are source-first;
/// `*mut T::copy_from*` is destination-first.
#[derive(Clone, Copy)]
enum CopyOperandOrder {
    SourceDestination,
    DestinationSource,
}

/// Exact stable core/std pointer-memory wrapper retained as an Item call.
#[derive(Clone, Copy)]
enum StableMemWrapper {
    Copy(CopyOperandOrder),
    WriteBytes,
}

fn stable_mem_wrapper<'tcx>(
    cx: &Cx<'tcx, '_>,
    func: &Operand<'tcx>,
) -> Option<StableMemWrapper> {
    let callee = resolve_call_callee(cx, func)?;
    let path = cx.tcx.def_path_str(callee.def_id());
    let free = |name: &str| {
        path == format!("core::ptr::{name}") || path == format!("std::ptr::{name}")
    };
    let raw_method = |namespace: &str, name: &str| {
        path.ends_with(&format!("::{name}"))
            && (path.starts_with(&format!("core::ptr::{namespace}::"))
                || path.starts_with(&format!("std::ptr::{namespace}::")))
    };

    if free("copy")
        || free("copy_nonoverlapping")
        || raw_method("const_ptr", "copy_to")
        || raw_method("const_ptr", "copy_to_nonoverlapping")
    {
        Some(StableMemWrapper::Copy(CopyOperandOrder::SourceDestination))
    } else if raw_method("mut_ptr", "copy_from")
        || raw_method("mut_ptr", "copy_from_nonoverlapping")
    {
        Some(StableMemWrapper::Copy(CopyOperandOrder::DestinationSource))
    } else if free("write_bytes") || raw_method("mut_ptr", "write_bytes") {
        Some(StableMemWrapper::WriteBytes)
    } else {
        None
    }
}

/// RUNG 5 (Arc-deref inline): recognize a `Call` to `<Arc<T> as Deref>::deref`
/// (a THIN `Arc<T>`, `T: Sized`) and return the ArcInner DATA offset to inline it.
///
/// Unlike `Box<T>` — whose `*box` is a COMPILER-BUILTIN primitive deref the MIR
/// lowers to direct pointer arithmetic (so the child read is already an inline
/// `load ptr` / `gep` in our place machinery) — `Arc<T>`'s `Deref` is a real
/// user trait impl, so MIR emits an opaque `Call` to `Arc::deref`. Left as an
/// extern that callee is a 0-block stub and the module is NOT executable. The
/// `structural_eq_impl`/`whnf` micro-checker walkers traverse `Arc<MicroExpr>`
/// children EXCLUSIVELY through this call, so inlining it is what makes them
/// executable end-to-end.
///
/// FAITHFUL lowering: an `Arc<T>` value is a thin pointer to
/// `ArcInner<T> { strong: AtomicUsize, weak: AtomicUsize, data: T }`, and
/// `Arc::deref(&self) -> &T` returns `&(*self.ptr).data`. The two `AtomicUsize`
/// counters precede `data`, so the data offset is
/// `align_up(2 * pointer_size, align_of::<T>())` — computed here via
/// `tcx.layout_of(T)` (no hardcoded 16; correct for any over-aligned `T`).
/// The call's argument is `&Arc<T>` (the ADDRESS holding the thin pointer), so
/// the inline emits: `arc = load ptr, arg; ret = gep i8, arc, offset`.
///
/// FAIL-LOUD: returns `None` (callee stays an extern stub, behavior unchanged)
/// unless ALL hold — the trait is the `Deref` lang-item trait, the receiver Adt
/// is the `Arc` diagnostic item, and the pointee `T` is `Sized` (a fat
/// `Arc<str>`/`Arc<[T]>` is a DIFFERENT, 2-word shape we do NOT inline here).
fn arc_deref_inline_offset<'tcx>(cx: &Cx<'tcx, '_>, func: &Operand<'tcx>) -> Option<u64> {
    let callee = resolve_call_callee(cx, func)?;
    let did = callee.def_id();
    // `did` is the IMPL method `<Arc<T, A> as Deref>::deref`. Map it back to the
    // TRAIT method (`trait_item_def_id`), then to its container TRAIT, and require
    // that to be the `Deref` lang-item trait — NOT a bare `deref` method name (a
    // user method literally named `deref` on a non-Deref trait must not be
    // misclassified into pointer arithmetic).
    let trait_method = cx.tcx.opt_associated_item(did)?.trait_item_def_id()?;
    let trait_did = cx.tcx.opt_associated_item(trait_method)?.trait_container(cx.tcx)?;
    if Some(trait_did) != cx.tcx.lang_items().deref_trait() {
        return None;
    }
    // The impl's Self type must be the `Arc` diagnostic item (the canonical, stable
    // identifier rustc itself uses for `alloc::sync::Arc`). We read it from the
    // impl's `Self` (`impl_of_method` -> `type_of`), instantiated with the call's
    // generic args, so a different `Deref` impl (Rc, Box, &T, a user smart pointer)
    // is rejected.
    let impl_did = cx.tcx.opt_associated_item(did)?.impl_container(cx.tcx)?;
    let self_ty = cx.normalize_ty(
        cx.tcx
            .type_of(impl_did)
            .instantiate(cx.tcx, callee.args),
    );
    let ty::Adt(adt_def, adt_args) = self_ty.kind() else {
        return None;
    };
    let is_arc = cx
        .tcx
        .get_diagnostic_name(adt_def.did())
        .is_some_and(|s| s.as_str() == "Arc");
    if !is_arc {
        return None;
    }
    // The pointee `T = Arc<T>`'s first type arg. Require `T: Sized` (a thin Arc:
    // size_of::<Arc<T>>() == pointer_size). A fat `Arc<str>`/`Arc<[T]>` is a
    // 2-word pointer+metadata value with a different deref — fail loud (extern).
    let pointee = adt_args.type_at(0);
    let pointee_layout = cx
        .tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(pointee))
        .ok()?;
    if pointee_layout.is_unsized() {
        return None;
    }
    let ptr_size = cx.tcx.data_layout.pointer_size().bytes();
    let pointee_align = pointee_layout.align.abi.bytes();
    // ArcInner data offset = align_up(2 * pointer_size, align_of::<T>()).
    let two_words = 2 * ptr_size;
    let offset = two_words.next_multiple_of(pointee_align);
    Some(offset)
}

/// The faithful `ArcInner<T>` heap-block layout an `Arc::new(x)` allocates: the data
/// offset (where `x` lives), the total block size to allocate, and the block's
/// alignment. RUNG 6 (Arc-WRITE) emits a `heap_alloc` of `total_size` bytes (align
/// `block_align`), Stores the two reference counters at offsets `0`/`pointer_size`
/// and `x` at `data_offset`, and the constructed `Arc<T>` value IS the block base.
#[derive(Clone)]
struct ArcInnerLayout {
    /// Byte offset of `data: T` inside `ArcInner<T>` (the same offset the Arc-READ
    /// rung adds to deref). `align_up(2 * pointer_size, align_of::<T>())`.
    data_offset: u64,
    /// Total bytes of `ArcInner<T>` to allocate (data_offset + size_of::<T>, padded
    /// to the block alignment).
    total_size: u64,
    /// Alignment of the whole block: `max(align_of::<AtomicUsize>, align_of::<T>())`.
    block_align: u64,
    /// The trust-ir leaf type of `x` (the pointee) when it is a single scalar (so
    /// the data Store is a typed scalar Store); `None` for an aggregate pointee
    /// (Stored by a typed-field memcpy from the source slot).
    data_scalar: Option<TIRTy>,
    /// The pointee `T`'s natural size/align (bytes) — used for the aggregate
    /// data-copy path (`copy_aggregate_bytes`).
    data_size: u64,
    data_align: u64,
}

/// RUNG 6 (Arc-WRITE inline): recognize a `Call` to the INHERENT `Arc::<T>::new`
/// constructor (a THIN `Arc<T>`, `T: Sized`) and return the `ArcInner<T>` layout so
/// the call lowers to a real heap allocation + counter/data Stores instead of an
/// opaque extern stub.
///
/// This is the CONSTRUCTION dual of `arc_deref_inline_offset` (RUNG 5, the read).
/// `subst`/`instantiate`/`lift`/`whnf` rebuild a `MicroExpr` tree exclusively via
/// `MicroExpr::App(Arc::new(..), Arc::new(..))` etc.; left as an extern, `Arc::new`
/// is a 0-block stub and the constructed value is opaque (so the +16 read on the
/// result reads garbage and the function is NOT executable). Lowering it faithfully
/// is what makes a constructed-then-read `Arc<MicroExpr>` graph execute.
///
/// FAITHFUL lowering: `Arc::new(x)` allocates `ArcInner<T> { strong: AtomicUsize=1,
/// weak: AtomicUsize=1, data: x }` (`#[repr(C, align(2))]`) and returns a thin
/// pointer to that block. `data` sits at `align_up(2 * pointer_size, align_of::<T>)`
/// — the SAME offset RUNG 5 reads — and the block size is that offset plus
/// `size_of::<T>`, padded to the block alignment (`max(align AtomicUsize, align T)`),
/// matching `arcinner_layout_for_value_layout` in `alloc::sync`. All derived from
/// `tcx.layout_of(T)` (no hardcoded 16).
///
/// FAIL-LOUD: returns `None` (callee stays an extern stub, behavior unchanged)
/// unless ALL hold — the callee is an INHERENT (non-trait) associated `new`, its
/// impl `Self` is the `Arc` diagnostic ADT, and the pointee `T` is `Sized` (a fat
/// `Arc<str>`/`Arc<[T]>` has a different, 2-word construction we do NOT inline).
fn arc_new_inner_layout<'tcx>(
    cx: &Cx<'tcx, '_>,
    func: &Operand<'tcx>,
) -> Result<Option<ArcInnerLayout>, String> {
    let Some(callee) = resolve_call_callee(cx, func) else {
        return Ok(None);
    };
    let did = callee.def_id();
    let Some(assoc) = cx.tcx.opt_associated_item(did) else {
        return Ok(None);
    };
    // Must be an INHERENT associated fn named `new` (NOT a trait method): a user
    // trait method literally named `new`, or `Rc::new`/`Box::new`, must not be
    // misclassified into Arc construction.
    if assoc.trait_container(cx.tcx).is_some() {
        return Ok(None);
    }
    if cx.tcx.item_name(did).as_str() != "new" {
        return Ok(None);
    }
    let Some(impl_did) = assoc.impl_container(cx.tcx) else {
        return Ok(None);
    };
    // The impl's `Self` (instantiated with the call's generic args) must be the
    // `Arc` diagnostic ADT — the canonical, stable identifier for `alloc::sync::Arc`.
    let self_ty = cx.normalize_ty(
        cx.tcx
            .type_of(impl_did)
            .instantiate(cx.tcx, callee.args),
    );
    let ty::Adt(adt_def, adt_args) = self_ty.kind() else {
        return Ok(None);
    };
    let is_arc = cx
        .tcx
        .get_diagnostic_name(adt_def.did())
        .is_some_and(|s| s.as_str() == "Arc");
    if !is_arc {
        return Ok(None);
    }
    // The pointee `T = Arc<T>`'s first type arg. Require `T: Sized` (a thin Arc); a
    // fat `Arc<str>`/`Arc<[T]>` is constructed differently — fail loud (extern stub).
    let pointee = adt_args.type_at(0);
    let pointee_layout = cx
        .tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(pointee))
        .map_err(|e| format!("Arc::new pointee layout_of failed: {e:?}"))?;
    if pointee_layout.is_unsized() {
        return Ok(None);
    }
    let ptr_size = cx.tcx.data_layout.pointer_size().bytes();
    let data_size = pointee_layout.size.bytes();
    let data_align = pointee_layout.align.abi.bytes();
    // `ArcInner<()>` is two `AtomicUsize` (each `pointer_size`, align `pointer_size`).
    // `arcinner_layout_for_value_layout` = `Layout::new::<ArcInner<()>>().extend(T)
    // .pad_to_align()`: data at `align_up(2*ptr_size, align_of::<T>)`, total padded to
    // the block align (`max(ptr_size, align_of::<T>)`). `#[repr(C, align(2))]` cannot
    // raise the align above `ptr_size` here (usize align == ptr_size >= 2).
    let block_align = ptr_size.max(data_align);
    let data_offset = (2 * ptr_size).next_multiple_of(data_align);
    let total_size = (data_offset + data_size).next_multiple_of(block_align);
    // The pointee's data Store form: a single scalar (typed Store) or an aggregate
    // (typed-field memcpy from the source slot). A ZST pointee Stores nothing.
    let data_scalar = scalar_tir_ty(pointee).or_else(|| memory_leaf_tir_ty(cx.tcx, pointee));
    Ok(Some(ArcInnerLayout {
        data_offset,
        total_size,
        block_align,
        data_scalar,
        data_size,
        data_align,
    }))
}

// ===================== RUNG 7: &str-message saturating-add helper ============
//
// The clean-kernel `subst`/`lift` bump a de-Bruijn depth/cutoff via the helper
//
//     fn checked_add_u32(a: u32, b: u32, _context: &'static str) -> u32 {
//         a.saturating_add(b)
//     }
//
// where the third argument is a `&'static str` overflow-diagnostic message that
// the body NEVER reads (`_context` is unused). MIR lowers each call site as
//   `_n = checked_add_u32(copy a, const 1_u32, const "subst lam depth")`
// passing the `&str` as a fat-pointer const operand. Two facts let us lower it
// without ever materializing the `&str` (the const-data / global-relocation that
// the in-process JIT cannot resolve): the `&str` is DEAD in the callee, and the
// callee's whole observable effect is `a.saturating_add(b)`.
//
// RECOGNITION (by SHAPE / type, never the user fn's bare name):
//   * a direct call to a resolvable INHERENT/FREE fn (not a trait method),
//   * signature `(uN, uN, &str) -> uN` — first two args and the return are the
//     SAME unsigned integer; exactly one trailing `&str` (or `&[u8]`) message arg,
//   * the message parameter is NEVER read in the callee body (a dead diagnostic),
//   * the body's arithmetic is the STD `saturating_add` primitive — confirmed by a
//     call to the std `saturating_add` item inside the callee body.
// If ALL hold we return the unsigned-int lane type and inline the call to a real
// `saturating_add` (overflow-add + select-to-max). Otherwise `None` — the call
// stays an extern, which then fails loud on its `&str` arg (no silent miscompile).
fn saturating_add_msg_call<'tcx>(
    cx: &Cx<'tcx, '_>,
    func: &Operand<'tcx>,
    args: &[rustc_span::Spanned<Operand<'tcx>>],
) -> Option<TIRTy> {
    let callee = resolve_call_callee(cx, func)?;
    let did = callee.def_id();
    // Must be a free / inherent fn we can fetch MIR for — NOT a trait method (a
    // user trait method of the same shape must not be misclassified).
    if let Some(assoc) = cx.tcx.opt_associated_item(did) {
        if assoc.trait_container(cx.tcx).is_some() {
            return None;
        }
    }
    if !matches!(callee.def, ty::InstanceKind::Item(_)) {
        return None;
    }
    // Only a real NAMED fn item carries a `tcx.fn_sig` — closure/coroutine
    // bodies and the AsyncFnOnce BY-MOVE coroutine body (an `InstanceKind::Item`
    // over a `DefKind::SyntheticCoroutineBody`, reached by a direct
    // `Future::poll` call once `coroutine_by_move_body_def_id` resolution picks
    // it) keep their signature in their type's args, and `tcx.fn_sig` ICEs on
    // them ("unexpected sort of node in fn_sig(): Synthetic"). The recognizer
    // only ever targets a named helper fn, so anything else is `None` by
    // definition.
    if !matches!(
        cx.tcx.def_kind(did),
        rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn
    ) {
        return None;
    }
    // Signature `(uN, uN, &str|&[u8]) -> uN` with the SAME unsigned-int lane on the
    // two value args and the return.
    let sig = cx
        .tcx
        .normalize_erasing_regions(
            ty::TypingEnv::fully_monomorphized(),
            cx.tcx.fn_sig(did).instantiate(cx.tcx, callee.args),
        )
        .skip_binder();
    if sig.inputs().len() != 3 {
        return None;
    }
    let a0 = cx.mono(sig.inputs()[0]);
    let a1 = cx.mono(sig.inputs()[1]);
    let a2 = cx.mono(sig.inputs()[2]);
    let ret = cx.mono(sig.output());
    let lane = uint_lane_tir(a0)?;
    if uint_lane_tir(a1) != Some(lane.clone()) || uint_lane_tir(ret) != Some(lane.clone()) {
        return None;
    }
    if !is_str_or_byteslice_ref(a2) {
        return None;
    }
    // The argument list must match: two value args + one `&str`/`&[u8]` const.
    if args.len() != 3 {
        return None;
    }
    if !matches!(&args[2].node, Operand::Constant(_)) {
        return None;
    }
    // The callee body: the `&str` parameter (_3) is never read, AND the body's
    // arithmetic is the std `saturating_add` primitive (a call to an item named
    // `saturating_add`). Both confirmed structurally — fail loud (None) otherwise.
    let body = cx.tcx.instance_mir(callee.def);
    let msg_local = Local::from_u32(3);
    if local_is_read(body, msg_local) {
        return None;
    }
    if !body_calls_saturating_add(cx, body) {
        return None;
    }
    Some(lane)
}

/// Materialize the unsigned MAX value of a trust-ir unsigned-int lane.
///
/// `U8..U64` fit in the builder's `iconst` carrier. The upper half of the
/// `u128` domain does not: v24 requires `Constant::U128`, reached through
/// `uconst`, rather than a negative `Constant::Int` raw-bit spelling.
fn uint_max_const(
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    lane: &TIRTy,
) -> Result<trust_ir::ValueId, String> {
    match lane {
        TIRTy::U8 => Ok(fb.iconst(lane.clone(), u8::MAX as i128)),
        TIRTy::U16 => Ok(fb.iconst(lane.clone(), u16::MAX as i128)),
        TIRTy::U32 => Ok(fb.iconst(lane.clone(), u32::MAX as i128)),
        TIRTy::U64 => Ok(fb.iconst(lane.clone(), u64::MAX as i128)),
        TIRTy::U128 => Ok(fb.uconst(lane.clone(), u128::MAX)),
        other => Err(format!(
            "saturating-add recognizer produced non-unsigned lane {other:?}"
        )),
    }
}

/// The trust-ir lane type of an UNSIGNED fixed-width integer (`u8..u128`/`usize`),
/// or `None` for anything else (signed / non-integer).
fn uint_lane_tir(ty: Ty<'_>) -> Option<TIRTy> {
    match ty.kind() {
        ty::Uint(u) => Some(match u {
            ty::UintTy::U8 => TIRTy::U8,
            ty::UintTy::U16 => TIRTy::U16,
            ty::UintTy::U32 => TIRTy::U32,
            ty::UintTy::U64 => TIRTy::U64,
            ty::UintTy::U128 => TIRTy::U128,
            ty::UintTy::Usize => TIRTy::U64,
        }),
        _ => None,
    }
}

/// Whether `ty` is a shared reference to `str` or `[u8]` — a diagnostic-message
/// fat pointer (`&'static str` / `&[u8]`).
fn is_str_or_byteslice_ref(ty: Ty<'_>) -> bool {
    let ty::Ref(_, pointee, _) = ty.kind() else {
        return false;
    };
    match pointee.kind() {
        ty::Str => true,
        ty::Slice(elem) => matches!(elem.kind(), ty::Uint(ty::UintTy::U8)),
        _ => false,
    }
}

/// Whether a MIR `Body` ever READS the given local (as an operand `Copy`/`Move`,
/// a `Ref`/`RawPtr`, or a place projected off it). Used to confirm the `&str`
/// message parameter is a dead diagnostic before we drop it.
fn local_is_read(body: &Body<'_>, target: Local) -> bool {
    use rustc_middle::mir::visit::{PlaceContext, Visitor};
    struct ReadFinder {
        target: Local,
        found: bool,
    }
    impl<'tcx> Visitor<'tcx> for ReadFinder {
        fn visit_local(
            &mut self,
            local: Local,
            context: PlaceContext,
            _loc: rustc_middle::mir::Location,
        ) {
            if local != self.target {
                return;
            }
            // A non-use context (StorageLive/Dead, a NonUse marker) is not a read.
            // Any Copy/Move/Borrow/AddressOf/projection use of the local IS.
            if !matches!(context, PlaceContext::NonUse(_)) {
                self.found = true;
            }
        }
    }
    let mut f = ReadFinder {
        target,
        found: false,
    };
    f.visit_body(body);
    f.found
}

/// Whether the callee body's arithmetic is the std `saturating_add` primitive:
/// it contains a `Call` whose resolved callee's item name is `saturating_add`.
/// This pins the recognized helper to genuine saturating add (not an arbitrary
/// `(uN,uN,&str)->uN`), so the inline lowering is faithful.
fn body_calls_saturating_add<'tcx>(cx: &Cx<'tcx, '_>, body: &Body<'tcx>) -> bool {
    for bb in body.basic_blocks.iter() {
        let Some(term) = &bb.terminator else { continue };
        if let TerminatorKind::Call { func, .. } = &term.kind {
            if let Operand::Constant(c) = func {
                if let ty::FnDef(callee_did, _) = c.const_.ty().kind() {
                    if cx.tcx.item_name(*callee_did).as_str() == "saturating_add" {
                        return true;
                    }
                }
            }
        }
    }
    false
}

// ===================== RUNG 8b: Vec/slice iteration -> INDEX loop ============
//
// The clean-kernel `whnf_impl` SPINE / DELTA-apply / STUCK-rebuild loops are
// `for arg in args { .. }` and `for arg in &args { .. }`. rustc desugars each to
//   `let mut it = IntoIterator::into_iter(<vec or &vec>);`
//   `loop { match Iterator::next(&mut it) { Some(x) => body, None => break } }`
// where `into_iter`/`next` are real (opaque) trait-method `Call`s over std's
// iterator state machines (`vec::IntoIter<T>` / `slice::Iter<'_,T>`). Left as
// externs they are 0-block stubs (iterator-state + Option-niche ABIs we cannot
// faithfully bind), so the loop never executes. We LOWER them faithfully + INLINE:
// model the iterator value as a `(cur_ptr, end_ptr)` cursor (which FITS inside the
// real iterator slot `tcx.layout_of` allocates — `slice::Iter` is exactly 2 words,
// `vec::IntoIter` is 4 words), make `into_iter` initialize the cursor from the
// source Vec's `{ptr@0, len@<2*ptr_size>}`, and make `next` an index/pointer-bump
// that yields `Some(elem)` / `None` into the destination `Option<..>` slot (the
// surrounding match/loop already lowers via the gateway loop-SSA). Faithful element
// stride via `tcx.layout_of(T)`. Fail-loud if `T`'s layout can't derive or the
// iterator isn't a recognized Vec/slice shape (so an unmodelable iterator stays an
// extern — no silent miscompile).

/// Which iterator shape a recognized `into_iter`/`next` is over.
#[derive(Clone, Copy, PartialEq, Eq)]
enum IterKind {
    /// `vec::IntoIter<T>`: OWNED iteration. `next` yields `Some(T)` BY VALUE (a
    /// `size_of::<T>` aggregate move via `copy_aggregate_bytes`).
    VecIntoIter,
    /// `slice::Iter<'_,T>`: BORROWED iteration. `next` yields `Some(&T)` — a thin
    /// pointer, no aggregate move.
    SliceIter,
    /// ADDITIVE (R4 stage 2): `core::str::iter::Bytes<'_>` — the str BYTE
    /// iterator (`str::bytes`). `Bytes` wraps `Copied<slice::Iter<'_, u8>>`, so
    /// its cursor is the same two pointer words (`cur@0`, `end@8`) and `next`
    /// yields `Some(u8)` BY VALUE — the single byte at `cur`. Its element type
    /// is `u8` BY DEFINITION (`Iterator<Item = u8>`), not a generic arg
    /// (`Bytes<'a>` carries only a lifetime — the round-1 T3 gap (3) shape
    /// "next inline: iterator has no element type arg").
    StrBytes,
}

/// The faithful per-iterator cursor model + element layout, derived from the
/// element type's `tcx.layout_of`. The cursor lives in the iterator local's
/// memory slot as two pointer words: `cur_ptr @ 0`, `end_ptr @ 8`.
#[derive(Clone)]
struct IterModel {
    kind: IterKind,
    /// Per-element stride in bytes: `size.align_to(align)` — the same value
    /// `tcx.layout_of(Vec<T>)`'s buffer uses and `[T;N]`'s element offset uses.
    stride: u64,
    /// Element `T`'s natural size (bytes) — the by-value move width for
    /// `VecIntoIter::next` (`copy_aggregate_bytes`). 0 for a ZST element.
    elem_size: u64,
    /// Element `T`'s natural alignment (bytes) — the by-value move lane width.
    elem_align: u64,
    /// The source `Vec<T>`'s `ptr`/`len` byte offsets (from `tcx.layout_of`), used
    /// by `into_iter` to read the buffer base + element count. `None` for an
    /// `into_iter` over a fat `&[T]` slice (which carries `(ptr, len)` directly, not
    /// a Vec) — currently the recognized borrowed case is `&Vec`, so this is Some.
    vec_ptr_off: u64,
    vec_len_off: u64,
    /// THREADS: the CURSOR words' byte offsets INSIDE the iterator slot. For
    /// `slice::Iter`/`Bytes` the iterator IS the two words (`cur@0`, `end@8`).
    /// For `vec::IntoIter` these are the REAL `ptr`/`end` FIELD offsets from
    /// `tcx.layout_of` — the inlined `next` and every REAL `IntoIter` body the
    /// program also runs (`size_hint`, `as_raw_mut_slice`, the drop glue that
    /// frees the buffer) then read/write the SAME state. The old synthetic
    /// `(cur@0, end@8)` cursor was garbage to those real bodies.
    cur_off: u64,
    end_off: u64,
    /// THREADS (owned `vec::IntoIter` only): the REAL `buf` / `cap` field
    /// offsets the cursor-init must ALSO initialize (the drop glue deallocates
    /// through them), plus the SOURCE Vec's `cap` offset to copy from.
    init_buf_off: Option<u64>,
    init_cap_off: Option<u64>,
    vec_cap_off: u64,
}

/// The faithful byte offsets of a `Vec<T>`'s three words — `ptr`, `cap`, `len` —
/// derived from `tcx.layout_of`, NOT hardcoded. A `Vec<T>` is `{ buf: RawVec<T>,
/// len: usize }`; `RawVec` nests `{ cap, ptr }` (whose ORDER is an internal detail
/// that varies by std version — e.g. `{cap, ptr}` vs `{ptr, cap}`), so we cannot
/// assume `ptr@0`. We walk the layout's leaf scalars: the single POINTER-primitive
/// leaf is `ptr`; `len` is `Vec`'s own field #1 (`usize`); the remaining integer
/// leaf inside `buf` is `cap`. Fail-loud if the shape is not the expected
/// one-pointer + two-usize triple.
struct VecFieldOffsets {
    ptr_off: u64,
    cap_off: u64,
    len_off: u64,
}

/// Recursively collect `(byte_offset, is_pointer)` for every SCALAR leaf of `ty`'s
/// layout (a `BackendRepr::Scalar` leaf, recursing into aggregates). Used to locate
/// a `Vec`'s `ptr`/`cap`/`len` words faithfully.
fn collect_scalar_leaves<'tcx>(
    cx: &Cx<'tcx, '_>,
    ty: Ty<'tcx>,
    base: u64,
    out: &mut Vec<(u64, bool)>,
) -> Result<(), String> {
    let layout = cx
        .tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(ty))
        .map_err(|e| format!("Vec field layout_of failed: {e:?}"))?;
    if layout.size.bytes() == 0 {
        return Ok(());
    }
    if let BackendRepr::Scalar(scalar) = layout.backend_repr {
        let is_ptr = matches!(scalar.primitive(), Primitive::Pointer(_));
        out.push((base, is_ptr));
        return Ok(());
    }
    // An aggregate: recurse into each field at its layout offset.
    match ty.kind() {
        ty::Adt(adt, adt_args) => {
            // Single-variant struct/union; walk its fields.
            let variant = adt.non_enum_variant();
            for (i, field) in variant.fields.iter().enumerate() {
                let off = base + layout.fields.offset(i).bytes();
                let fty = cx.normalize_ty(field.ty(cx.tcx, adt_args));
                collect_scalar_leaves(cx, fty, off, out)?;
            }
            Ok(())
        }
        ty::Tuple(elems) => {
            for (i, e) in elems.iter().enumerate() {
                let off = base + layout.fields.offset(i).bytes();
                collect_scalar_leaves(cx, e, off, out)?;
            }
            Ok(())
        }
        _ => Err(format!("Vec field has unexpected aggregate leaf: {}", ty_family(ty))),
    }
}

/// Derive a `Vec<T>`'s `{ptr, cap, len}` byte offsets faithfully from its layout.
fn vec_field_offsets<'tcx>(cx: &Cx<'tcx, '_>, vec_ty: Ty<'tcx>) -> Result<VecFieldOffsets, String> {
    let mut leaves: Vec<(u64, bool)> = Vec::new();
    collect_scalar_leaves(cx, vec_ty, 0, &mut leaves)?;
    // Expect exactly one pointer leaf + two integer leaves (cap, len).
    let ptr_leaves: Vec<u64> = leaves.iter().filter(|(_, p)| *p).map(|(o, _)| *o).collect();
    let mut int_leaves: Vec<u64> = leaves.iter().filter(|(_, p)| !*p).map(|(o, _)| *o).collect();
    if ptr_leaves.len() != 1 || int_leaves.len() != 2 {
        return Err(format!(
            "Vec layout is not the expected 1-ptr + 2-usize triple ({} ptr, {} int leaves)",
            ptr_leaves.len(),
            int_leaves.len()
        ));
    }
    let ptr_off = ptr_leaves[0];
    int_leaves.sort_unstable();
    // `len` is `Vec`'s OWN field #1 (the top-level `usize`), which sits at the
    // HIGHEST offset (after `buf`); `cap` lives inside `buf` at a lower offset.
    let cap_off = int_leaves[0];
    let len_off = int_leaves[1];
    Ok(VecFieldOffsets {
        ptr_off,
        cap_off,
        len_off,
    })
}

/// The element `T`'s per-element stride / size / align from `tcx.layout_of(T)`.
/// Fail-loud if the layout cannot be derived.
fn iter_elem_layout<'tcx>(cx: &Cx<'tcx, '_>, elem: Ty<'tcx>) -> Result<(u64, u64, u64), String> {
    let layout = cx
        .tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(elem))
        .map_err(|e| format!("iterator element layout_of failed: {e:?}"))?;
    if !layout.is_sized() {
        return Err(format!("iterator element is unsized: {}", ty_family(elem)));
    }
    let size = layout.size.bytes();
    let align = layout.align.abi.bytes();
    let stride = size.next_multiple_of(align.max(1));
    Ok((stride, size, align))
}

/// RUNG 8b (into_iter inline): recognize a `Call` to `IntoIterator::into_iter`
/// whose Self is `Vec<T>` (-> `vec::IntoIter<T>`, OWNED) or `&Vec<T>` / `[T]`
/// (-> `slice::Iter<'_,T>`, BORROWED), by the `IntoIterator` lang/diagnostic trait
/// + the Self ADT being the `Vec` diagnostic item (or a slice). Returns the iterator
/// model so the call lowers to a cursor-init.
///
/// FAIL-LOUD: `None` (callee stays an extern) unless the trait is `IntoIterator`,
/// the receiver is a recognized Vec/&Vec/slice shape, and the element layout derives.
fn into_iter_inline<'tcx>(
    cx: &Cx<'tcx, '_>,
    func: &Operand<'tcx>,
) -> Result<Option<IterModel>, String> {
    let Some(callee) = resolve_call_callee(cx, func) else {
        return Ok(None);
    };
    let did = callee.def_id();
    // The impl method `<X as IntoIterator>::into_iter` -> its TRAIT method -> the
    // container TRAIT, required to be the `IntoIterator` diagnostic trait (NOT a
    // bare `into_iter` name on some user trait).
    let Some(assoc) = cx.tcx.opt_associated_item(did) else {
        return Ok(None);
    };
    let Some(trait_method) = assoc.trait_item_def_id() else {
        return Ok(None);
    };
    let Some(trait_did) = cx.tcx.opt_associated_item(trait_method).and_then(|a| a.trait_container(cx.tcx)) else {
        return Ok(None);
    };
    if !cx
        .tcx
        .get_diagnostic_name(trait_did)
        .is_some_and(|s| s.as_str() == "IntoIterator")
    {
        return Ok(None);
    }
    // The impl's Self type (instantiated with the call's args): `Vec<T>` (owned) or
    // `&Vec<T>` / `&[T]` (borrowed). We read the ELEMENT type and the OUTPUT iterator
    // type from the resolved instance's generics / Self.
    let Some(impl_did) = assoc.impl_container(cx.tcx) else {
        return Ok(None);
    };
    let self_ty = cx.normalize_ty(
        cx.tcx
            .type_of(impl_did)
            .instantiate(cx.tcx, callee.args),
    );
    // Peel a leading shared reference: `&Vec<T>` / `&[T]` -> borrowed slice iter.
    let (recv_ty, borrowed) = match self_ty.kind() {
        ty::Ref(_, inner, _) => (*inner, true),
        _ => (self_ty, false),
    };
    // The element type from the receiver: a `Vec<T>` ADT's first arg, or a `[T]`
    // slice / `[T;N]` array element.
    let (elem, is_vec) = match recv_ty.kind() {
        ty::Adt(adt, adt_args) => {
            let is_vec = cx
                .tcx
                .get_diagnostic_name(adt.did())
                .is_some_and(|s| s.as_str() == "Vec");
            if !is_vec {
                return Ok(None);
            }
            (adt_args.type_at(0), true)
        }
        ty::Slice(elem) | ty::Array(elem, _) => (*elem, false),
        _ => return Ok(None),
    };
    // OWNED iteration only applies to a by-value `Vec<T>` (-> `vec::IntoIter`).
    // Borrowed (`&Vec<T>`/`&[T]`/`[T]`) -> `slice::Iter`.
    let kind = if borrowed || !is_vec {
        IterKind::SliceIter
    } else {
        IterKind::VecIntoIter
    };
    // The source of the cursor is a `Vec<T>` (`recv_ty`). A borrowed `&[T]`/`[T]`
    // (no Vec) is NOT modeled here (whnf iterates `&Vec`/`Vec`); fail loud.
    if !is_vec {
        return Ok(None);
    }
    let vfo = vec_field_offsets(cx, recv_ty)?;
    let (stride, elem_size, elem_align) = iter_elem_layout(cx, elem)?;
    // THREADS: for OWNED iteration the destination is a real `vec::IntoIter`
    // whose OTHER readers (`size_hint`, `as_raw_mut_slice`, the buffer-freeing
    // drop glue) run as REAL bodies — the cursor must live at the REAL
    // `ptr`/`end` field offsets, and `buf`/`cap` must be initialized too.
    let (cur_off, end_off, init_buf_off, init_cap_off) = match kind {
        IterKind::VecIntoIter => {
            let sig = cx.tcx.normalize_erasing_regions(
                ty::TypingEnv::fully_monomorphized(),
                cx.tcx.fn_sig(did).instantiate(cx.tcx, callee.args),
            );
            let out_ty = sig.skip_binder().output();
            let (p, e, b, c) = vec_into_iter_offsets(cx, out_ty)?;
            (p, e, Some(b), Some(c))
        }
        _ => (0, 8, None, None),
    };
    Ok(Some(IterModel {
        kind,
        stride,
        elem_size,
        elem_align,
        vec_ptr_off: vfo.ptr_off,
        vec_len_off: vfo.len_off,
        cur_off,
        end_off,
        init_buf_off,
        init_cap_off,
        vec_cap_off: vfo.cap_off,
    }))
}


/// THREADS: the REAL `vec::IntoIter<T, A>` field offsets — `(ptr, end, buf,
/// cap)` — from `tcx.layout_of` + the ADT's FIELD NAMES (robust to layout
/// reorder). The inlined cursor ops and every REAL `IntoIter` body then share
/// one state. Fail-loud if the expected fields are missing.
fn vec_into_iter_offsets<'tcx>(
    cx: &Cx<'tcx, '_>,
    iter_ty: Ty<'tcx>,
) -> Result<(u64, u64, u64, u64), String> {
    let ty::Adt(adt, _) = iter_ty.kind() else {
        return Err("vec::IntoIter model: iterator type is not an ADT".to_string());
    };
    let layout = cx
        .tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(iter_ty))
        .map_err(|e| format!("vec::IntoIter layout_of failed: {e:?}"))?;
    let (mut ptr_o, mut end_o, mut buf_o, mut cap_o) = (None, None, None, None);
    for (i, f) in adt.non_enum_variant().fields.iter().enumerate() {
        let off = layout.fields.offset(i).bytes();
        match f.name.as_str() {
            "ptr" => ptr_o = Some(off),
            "end" => end_o = Some(off),
            "buf" => buf_o = Some(off),
            "cap" => cap_o = Some(off),
            _ => {}
        }
    }
    match (ptr_o, end_o, buf_o, cap_o) {
        (Some(p), Some(e), Some(b), Some(c)) => Ok((p, e, b, c)),
        _ => Err("vec::IntoIter model: expected fields ptr/end/buf/cap not all found".to_string()),
    }
}

/// RUNG 8b (next inline): recognize a `Call` to `Iterator::next` whose Self is
/// `vec::IntoIter<T>` or `slice::Iter<'_,T>` (by the `Iterator` diagnostic trait +
/// the Self ADT diagnostic item), and return the iterator model so the call lowers
/// to a cursor index-bump + `Some`/`None` write.
///
/// FAIL-LOUD: `None` unless the trait is `Iterator`, the Self is a recognized
/// `vec::IntoIter`/`slice::Iter`, and the element layout derives.
fn iter_next_inline<'tcx>(
    cx: &Cx<'tcx, '_>,
    func: &Operand<'tcx>,
) -> Result<Option<IterModel>, String> {
    let Some(callee) = resolve_call_callee(cx, func) else {
        return Ok(None);
    };
    let did = callee.def_id();
    let Some(assoc) = cx.tcx.opt_associated_item(did) else {
        return Ok(None);
    };
    let Some(trait_method) = assoc.trait_item_def_id() else {
        return Ok(None);
    };
    let Some(trait_did) = cx.tcx.opt_associated_item(trait_method).and_then(|a| a.trait_container(cx.tcx)) else {
        return Ok(None);
    };
    if !cx
        .tcx
        .get_diagnostic_name(trait_did)
        .is_some_and(|s| s.as_str() == "Iterator")
    {
        return Ok(None);
    }
    // THREADS: the inline models `next` and ONLY `next`. Any other Iterator
    // method on a modeled iterator (`size_hint` on `IntoIter<JoinHandle>` in
    // `as_raw_mut_slice`, `advance_by`, ...) is an ordinary call to its real
    // MIR body — routing it here read the destination as an Option and died
    // on `size_hint`'s `(usize, Option<usize>)` tuple.
    if cx.tcx.item_name(trait_method).as_str() != "next" {
        return Ok(None);
    }
    // The impl's Self (instantiated): `vec::IntoIter<T>` or `slice::Iter<'_,T>`.
    let Some(impl_did) = assoc.impl_container(cx.tcx) else {
        return Ok(None);
    };
    let self_ty = cx.normalize_ty(
        cx.tcx
            .type_of(impl_did)
            .instantiate(cx.tcx, callee.args),
    );
    let ty::Adt(adt, adt_args) = self_ty.kind() else {
        return Ok(None);
    };
    let is_slice_iter_diag = cx
        .tcx
        .get_diagnostic_name(adt.did())
        .is_some_and(|s| s.as_str() == "SliceIter");
    // `vec::IntoIter` has no stable diagnostic item; recognize it by its def-path
    // (`alloc::vec::into_iter::IntoIter`). `slice::Iter` is `core::slice::iter::Iter`.
    let path = cx.tcx.def_path_str(adt.did());
    // ADDITIVE (R4 stage 2): `<core::str::iter::Bytes<'_> as Iterator>::next` —
    // the str BYTES iterator. Recognized BEFORE the element-type-arg extraction
    // below because `Bytes<'a>` has NO type generic arg: its element is `u8` BY
    // DEFINITION (`impl Iterator for Bytes<'_> { type Item = u8; .. }`). Cursor
    // shape: `Bytes` wraps `Copied<slice::Iter<'_, u8>>` = the same (cur,end)
    // pointer pair at +0/+8 the `str::bytes` cursor-init inline writes. Any
    // OTHER no-type-arg iterator (e.g. `Chars`) still fails loud below.
    if path == "core::str::iter::Bytes"
        || path.ends_with("str::iter::Bytes")
        || path == "core::str::Bytes"
        || path == "std::str::Bytes"
    {
        return Ok(Some(IterModel {
            kind: IterKind::StrBytes,
            stride: 1,
            elem_size: 1,
            elem_align: 1,
            // `next` reads only the (cur,end) cursor — no source Vec fields.
            vec_ptr_off: 0,
            vec_len_off: 0,
            cur_off: 0,
            end_off: 8,
            init_buf_off: None,
            init_cap_off: None,
            vec_cap_off: 0,
        }));
    }
    // The element `T` is the FIRST TYPE generic arg (skip the erased lifetime that
    // `slice::Iter<'a, T>` carries at index 0; `vec::IntoIter<T, A=Global>` has it
    // at index 0). Fail loud if there is no type arg.
    // THREADS: an iterator WITHOUT a type arg (`Chars`) is simply NOT modeled —
    // fall through to the ordinary extern call of its real `next` body (its
    // state was built by real code too, so both sides stay extern-consistent).
    // This was a hard error, which needlessly killed whole fmt bodies.
    let Some(elem) = adt_args.iter().find_map(|a| a.as_type()) else {
        return Ok(None);
    };
    let kind = if is_slice_iter_diag
        || path.ends_with("slice::Iter")
        || path == "std::slice::Iter"
        || path == "core::slice::Iter"
    {
        IterKind::SliceIter
    } else if path.ends_with("vec::IntoIter")
        || path == "std::vec::IntoIter"
        || path == "alloc::vec::IntoIter"
    {
        IterKind::VecIntoIter
    } else {
        return Ok(None);
    };
    let (stride, elem_size, elem_align) = iter_elem_layout(cx, elem)?;
    // THREADS: `next` on an owned `vec::IntoIter` bumps the REAL `ptr` field
    // (see `vec_into_iter_offsets`); the slice/bytes cursors stay `(0, 8)`.
    let (cur_off, end_off) = match kind {
        IterKind::VecIntoIter => {
            let (p, e, _b, _c) = vec_into_iter_offsets(cx, self_ty)?;
            (p, e)
        }
        _ => (0, 8),
    };
    Ok(Some(IterModel {
        kind,
        stride,
        elem_size,
        elem_align,
        // `next` reads only the iterator's own `(cur,end)` cursor, never the source
        // Vec's `ptr`/`len` fields — these offsets are unused here.
        vec_ptr_off: 0,
        vec_len_off: 0,
        cur_off,
        end_off,
        init_buf_off: None,
        init_cap_off: None,
        vec_cap_off: 0,
    }))
}

// ============ ADDITIVE (R4 stage 2): in-module str BYTE ACCESS ================
//
// Stage 1 (R3) materialized `&'static str` literals as (ptr,len) pairs; their
// BYTES could only be observed by crossing an extern boundary (host shims for
// `String::as_bytes` etc.). Stage 2 lowers the str byte-access surface
// IN-MODULE, so the JIT machine code itself walks the bytes:
//   * `str::as_bytes(&self) -> &[u8]` — in core this is a transmute: IDENTITY
//     on the (ptr,len) fat pair. Inlined as a 2-lane copy into the fat dest.
//   * `str::len(&self) -> usize` — the fat pair's METADATA lane. Inlined as a
//     single load at +8.
//   * `str::bytes(&self) -> str::Bytes<'_>` — a cursor init: `cur = data ptr`,
//     `end = ptr + len` (stride 1), stored at +0/+8 of the `Bytes` slot —
//     exactly the convention the landed slice-iterator model established
//     (`into_iter` cursor-init / `lower_iter_next`).
//   * `<[u8]>::iter(&self) -> slice::Iter<'_, u8>` — the same cursor init from
//     a `&[u8]` fat pair. GATED to element `u8` (the str-bytes program's
//     scope): landed fixtures declare `<[Constant]>::iter` as an extern
//     (trust_value_matches_slice), and a general `[T]::iter` inline would
//     drift their re-emits.
//   * the BLANKET `impl<I: Iterator> IntoIterator for I` `into_iter` — the
//     for-loop desugar's identity hop (`fn into_iter(self) -> I { self }`).
//     Inlined as a `size_of::<I>` aggregate copy, GATED to the two modeled
//     u8-iterator states (`slice::Iter<'_, u8>`, `str::iter::Bytes<'_>`).
//     The gate keys on the impl's UNINSTANTIATED Self being a bare type PARAM,
//     which is true of core's blanket impl and FALSE of every concrete
//     `IntoIterator` impl (`&[T]`/`&Vec<T>`/`Vec<T>`) — so the landed extern
//     declarations for those (e.g. `<&[MicroExpr] as IntoIterator>::into_iter`
//     in the round-trip fixtures) are untouched, byte-for-byte.
//
// FAITHFULNESS: the (ptr,len) pair IS the fat-pointer value the rest of the
// lowering already models (`lower_unsize_assign` lane discipline; sret pairs);
// `as_bytes`/`len` read it exactly as native does. The iterator cursor layout
// (`cur@0,end@8`) is internal to the module: it is written and read ONLY by
// these inlines + `lower_iter_next` — an iterator state never crosses an
// extern boundary on any emitted surface (same discipline as the landed
// slice-iterator model).
//
// FAIL-LOUD: every recognizer returns `None` for any other shape (those keep
// their extern/fail-loud behavior); the emission arms error on non-fat args.

/// A recognized in-module str/byte call shape (see the section header above).
#[derive(Clone)]
enum StrInlineOp {
    /// `str::as_bytes` — identity on the fat pair: copy both lanes into the
    /// fat `&[u8]` destination slot.
    AsBytes,
    /// `str::len` — load the metadata lane (+8) of the arg pair.
    Len,
    /// `str::bytes` / `<[u8]>::iter` — cursor init: `cur = ptr@0`,
    /// `end = ptr + len` (stride 1 byte), stored at +0/+8 of the destination
    /// iterator slot.
    ByteCursorInit,
    /// The blanket `IntoIterator::into_iter` identity over a modeled
    /// u8-iterator state: copy `size` bytes (lane width `align`) from the arg
    /// slot to the destination slot.
    IterIdentity { size: u64, align: u64 },
}

/// Whether `ty` is one of the two MODELED u8-iterator states whose blanket
/// `into_iter` identity we inline: `core::slice::iter::Iter<'_, u8>` or
/// `core::str::iter::Bytes<'_>`. Recognition mirrors `iter_next_inline`
/// (diagnostic item / def-path), plus the `u8` element gate for `Iter`.
fn is_modeled_u8_iter_state<'tcx>(cx: &Cx<'tcx, '_>, ty: Ty<'tcx>) -> bool {
    let ty::Adt(adt, adt_args) = ty.kind() else {
        return false;
    };
    let path = cx.tcx.def_path_str(adt.did());
    if path == "core::str::iter::Bytes"
        || path.ends_with("str::iter::Bytes")
        || path == "core::str::Bytes"
        || path == "std::str::Bytes"
    {
        return true;
    }
    let is_slice_iter = cx
        .tcx
        .get_diagnostic_name(adt.did())
        .is_some_and(|s| s.as_str() == "SliceIter")
        || path.ends_with("slice::Iter")
        || path == "std::slice::Iter"
        || path == "core::slice::Iter";
    if !is_slice_iter {
        return false;
    }
    adt_args
        .iter()
        .find_map(|a| a.as_type())
        .is_some_and(|t| matches!(t.kind(), ty::Uint(ty::UintTy::U8)))
}

/// ADDITIVE (R4 stage 2): recognize the in-module str/byte call shapes (see the
/// section header). Returns `None` for every other callee — including the
/// String INHERENT methods (`String::len`/`String::as_bytes`/...), which stay
/// externs exactly as the landed fixtures embed them.
fn str_inline_op<'tcx>(
    cx: &Cx<'tcx, '_>,
    func: &Operand<'tcx>,
) -> Result<Option<StrInlineOp>, String> {
    let Some(callee) = resolve_call_callee(cx, func) else {
        return Ok(None);
    };
    let did = callee.def_id();
    let Some(assoc) = cx.tcx.opt_associated_item(did) else {
        return Ok(None);
    };
    let Some(impl_did) = assoc.impl_container(cx.tcx) else {
        return Ok(None);
    };
    match assoc.trait_item_def_id() {
        // INHERENT methods: `str::{as_bytes,len,bytes}` and `<[u8]>::iter`.
        None => {
            let self_ty = cx.normalize_ty(
                cx.tcx
                    .type_of(impl_did)
                    .instantiate(cx.tcx, callee.args),
            );
            if self_ty.is_str() {
                return Ok(match cx.tcx.item_name(did).as_str() {
                    "as_bytes" => Some(StrInlineOp::AsBytes),
                    "len" => Some(StrInlineOp::Len),
                    "bytes" => Some(StrInlineOp::ByteCursorInit),
                    _ => None,
                });
            }
            if let ty::Slice(elem) = self_ty.kind() {
                if matches!(elem.kind(), ty::Uint(ty::UintTy::U8))
                    && cx.tcx.item_name(did).as_str() == "iter"
                {
                    return Ok(Some(StrInlineOp::ByteCursorInit));
                }
            }
            Ok(None)
        }
        // The BLANKET `impl<I: Iterator> IntoIterator for I` identity.
        Some(trait_method) => {
            let Some(trait_did) = cx
                .tcx
                .opt_associated_item(trait_method)
                .and_then(|a| a.trait_container(cx.tcx))
            else {
                return Ok(None);
            };
            if !cx
                .tcx
                .get_diagnostic_name(trait_did)
                .is_some_and(|s| s.as_str() == "IntoIterator")
            {
                return Ok(None);
            }
            // The blanket identity impl's UNINSTANTIATED Self is the bare type
            // param `I`; every concrete impl (`&[T]`, `&Vec<T>`, `Vec<T>`, ...)
            // has a constructed Self and is NOT touched here.
            if !matches!(
                cx.tcx.type_of(impl_did).skip_binder().kind(),
                ty::Param(_)
            ) {
                return Ok(None);
            }
            let self_ty = cx.normalize_ty(
                cx.tcx
                    .type_of(impl_did)
                    .instantiate(cx.tcx, callee.args),
            );
            if !is_modeled_u8_iter_state(cx, self_ty) {
                return Ok(None);
            }
            let layout = cx
                .tcx
                .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(self_ty))
                .map_err(|e| format!("into_iter identity: layout_of failed: {e:?}"))?;
            Ok(Some(StrInlineOp::IterIdentity {
                size: layout.size.bytes(),
                align: layout.align.abi.bytes(),
            }))
        }
    }
}

/// The ADDRESS of a call arg's (ptr,len) fat-pair slot, for the str-inline
/// emission arms: a str/byte-slice LITERAL uses its materialized pair slot
/// (`materialize_str_consts`); a fat PLACE uses its slot address. Anything else
/// fails loud.
fn str_call_arg_pair_addr<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    env: &HashMap<Local, trust_ir::ValueId>,
    op: &Operand<'tcx>,
) -> Result<trust_ir::ValueId, String> {
    match op {
        Operand::Constant(c) => Ok(str_const_mat(cx, c)?.pair_ptr),
        Operand::Copy(place) | Operand::Move(place) => {
            if !is_fat_pointer(cx.tcx, cx.place_concrete_ty(place)) {
                return Err("str inline: arg place is not a fat pointer".to_string());
            }
            place_address(cx, fb, env, place)
        }
        other => Err(format!("str inline: unmodelable arg operand {other:?}")),
    }
}

// ===================== RUNG 8b: the `vec![x]` macro box->Vec path ============
//
// `vec![a.clone()]` lowers (post the store_array_elems rung that built the
// `[MicroExpr;1]` into the box buffer) via
//   `_box = Box::<[T;N]>::new_uninit();`   // alloc N*size_of::<T>() bytes
//   `(*_box).<array> = [elems];`           // store_array_elems (already lowered)
//   `_vec = box_assume_init_into_vec_unsafe::<T,N>(_box);`  // -> Vec{ptr,N,N}
// `new_uninit` is a plain heap allocation; `box_assume_init_into_vec_unsafe` just
// reinterprets the box's buffer pointer as a `Vec{ptr, cap=N, len=N}`. We inline
// BOTH faithfully (alloc + 3-word Vec header materialization); the array store
// between them is the existing aggregate-array path. Fail-loud on an unrecognized
// vec-construction shape (no silent miscompile).

/// The faithful buffer layout a `Box::<[T;N]>::new_uninit()` allocates: the total
/// byte size and the buffer alignment.
#[derive(Clone)]
struct BoxNewUninitLayout {
    /// `N * size_of::<T>` padded to `align_of::<T>` — the buffer byte size.
    total_size: u64,
    /// `align_of::<[T;N]>` = `align_of::<T>`.
    align: u64,
}

/// RUNG 8b (Box::new_uninit inline): recognize `Box::<U>::new_uninit()` (an
/// INHERENT `new_uninit` on the `Box` diagnostic ADT) and return the buffer layout
/// of its pointee `U` (here `MaybeUninit<[T;N]>`) so the call lowers to a
/// `heap_alloc` returning the buffer pointer.
///
/// FAIL-LOUD: `None` unless the callee is the inherent `new_uninit` on the `Box`
/// diagnostic ADT and the pointee `U` layout derives.
fn box_new_uninit_inline<'tcx>(
    cx: &Cx<'tcx, '_>,
    func: &Operand<'tcx>,
) -> Result<Option<BoxNewUninitLayout>, String> {
    let Some(callee) = resolve_call_callee(cx, func) else {
        return Ok(None);
    };
    let did = callee.def_id();
    let Some(assoc) = cx.tcx.opt_associated_item(did) else {
        return Ok(None);
    };
    // INHERENT `new_uninit` (not a trait method).
    if assoc.trait_container(cx.tcx).is_some() {
        return Ok(None);
    }
    if cx.tcx.item_name(did).as_str() != "new_uninit" {
        return Ok(None);
    }
    let Some(impl_did) = assoc.impl_container(cx.tcx) else {
        return Ok(None);
    };
    let self_ty = cx.normalize_ty(
        cx.tcx
            .type_of(impl_did)
            .instantiate(cx.tcx, callee.args),
    );
    // `Box<T>` is the `owned_box` LANG item (not a diagnostic item) — check the
    // resolved Self via `Ty::is_box` (it inspects the `owned_box` lang-item ADT),
    // so a user struct named `Box` or `Rc`/`Arc` is rejected.
    if !self_ty.is_box() {
        return Ok(None);
    }
    let ty::Adt(_adt_def, adt_args) = self_ty.kind() else {
        return Ok(None);
    };
    // The pointee `T` = `Box<T>`'s first type arg. `new_uninit` allocates a buffer
    // for `MaybeUninit<T>`, which has the SAME size/align as `T`, so the buffer
    // layout is `tcx.layout_of(T)`.
    let pointee = adt_args.type_at(0);
    let layout = cx
        .tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(pointee))
        .map_err(|e| format!("Box::new_uninit pointee layout_of failed: {e:?}"))?;
    if !layout.is_sized() {
        return Ok(None);
    }
    Ok(Some(BoxNewUninitLayout {
        total_size: layout.size.bytes(),
        align: layout.align.abi.bytes(),
    }))
}

/// The faithful `Vec<T>` header a `box_assume_init_into_vec_unsafe::<T,N>(box)`
/// materializes: the element count `N` (= cap = len). The Vec's `ptr` is the box's
/// buffer pointer (the single arg).
#[derive(Clone)]
struct BoxIntoVecLayout {
    /// The const `N` element count: written into both `cap` and `len`.
    count: u64,
}

/// RUNG 8b (box->Vec inline): recognize `box_assume_init_into_vec_unsafe::<T,N>` (a
/// FREE `alloc::boxed` fn) and return the `Vec` count so the call lowers to a 3-word
/// `Vec{ptr=<box buffer>, cap=N, len=N}` materialization.
///
/// FAIL-LOUD: `None` unless the callee is a resolvable FREE fn whose item name is
/// `box_assume_init_into_vec_unsafe` and the const generic `N` reads.
fn box_into_vec_inline<'tcx>(
    cx: &Cx<'tcx, '_>,
    func: &Operand<'tcx>,
) -> Result<Option<BoxIntoVecLayout>, String> {
    let Some(callee) = resolve_call_callee(cx, func) else {
        return Ok(None);
    };
    let did = callee.def_id();
    // A FREE fn (no trait/impl container) named `box_assume_init_into_vec_unsafe`.
    // Only a NAMED free fn (`DefKind::Fn`) can match — a closure / coroutine /
    // synthetic-coroutine-body def has no `item_name` (`tcx.item_name` ICEs on
    // it), and can never be the helper. (Belt-and-braces: the closure-safe
    // `closure_chain_callee` bypass normally routes those away before the
    // recognizers run.)
    if !matches!(cx.tcx.def_kind(did), rustc_hir::def::DefKind::Fn) {
        return Ok(None);
    }
    if let Some(assoc) = cx.tcx.opt_associated_item(did) {
        if assoc.trait_container(cx.tcx).is_some() || assoc.impl_container(cx.tcx).is_some() {
            return Ok(None);
        }
    }
    if cx.tcx.item_name(did).as_str() != "box_assume_init_into_vec_unsafe" {
        return Ok(None);
    }
    // Generic args: `[T, N]` — `N` is the const element count.
    let count = callee
        .args
        .iter()
        .find_map(|a| a.as_const())
        .and_then(|c| c.try_to_target_usize(cx.tcx))
        .ok_or_else(|| "box->Vec: const element count N not resolvable".to_string())?;
    Ok(Some(BoxIntoVecLayout { count }))
}

// ===================== RUNG 8b (RETIRED): logic-free drop no-op ==============
//
// HISTORICAL: this pipeline once modeled the drop glue of purely-deallocating std
// containers (`Vec`/`Box`/`Arc`/`IntoIter`/...) as a NO-OP — the `drop_glue_is_logic_free`
// / `is_known_dealloc_only_adt` guard skipped emitting the `drop_in_place::<T>` call at a
// `Drop` site whose glue "only" freed memory / decremented a refcount. That LEAKED every
// heap buffer (a `Vec`'s allocation was never `__rust_dealloc`'d). The guard is now
// RETIRED: the RUNG-4 Drop pre-pass emits the real drop glue call for EVERY `needs_drop`
// place, so dealloc/refcount glue runs and trust-cg-compiled heap programs are LEAK-FREE.
// (The only remaining no-op case is `needs_drop == false`, which has no glue at all.)

/// RUNG 9 (rust-call ABI): whether `func` resolves to a CLOSURE BODY invoked via
/// the `"rust-call"` ABI — `<{closure} as FnOnce/FnMut/Fn>::call*(self, args_tuple)`
/// which `Instance::try_resolve` collapses to the closure body. At the MIR call site
/// the trailing argument is the ARGS TUPLE `(a0, a1, ..)`; the closure body's own
/// signature is the UNTUPLED `(self, a0, a1, ..)`. So a call to a closure body must
/// SPREAD its last tuple argument into the tuple's fields. Returns `true` iff the
/// callee is a closure body (`def_kind == Closure`); the spread is applied by
/// `spread_closure_args`. Non-closure calls return `false` and are untouched
/// (additive).
fn is_closure_rust_call<'tcx>(cx: &Cx<'tcx, '_>, func: &Operand<'tcx>) -> bool {
    let Some(callee) = resolve_call_callee(cx, func) else {
        return false;
    };
    match cx.tcx.def_kind(callee.def_id()) {
        rustc_hir::def::DefKind::Closure => {
            // A COROUTINE (an `async fn` body / `gen` block) is also
            // `DefKind::Closure`, but its resume/poll entry is NOT the untupled
            // `rust-call` shape: it is called `(Pin<&mut Self>, resume_arg)` with
            // the resume argument (e.g. `&mut Context<'_>` for an async coroutine)
            // passed AS-IS — a single value, never a spread args-tuple. Only a real
            // Fn-trait closure body untuples. Detect the coroutine by its kind and
            // route it through the normal (non-spread) call path.
            cx.tcx.coroutine_kind(callee.def_id()).is_none()
        }
        // THREADS: every `extern "rust-call"` fn spreads its trailing args
        // tuple — the FnOnce/Fn/FnMut method shims (`ClosureOnce`, `VTable`,
        // `FnPtr`), `Box<F>::call_once`, and the blanket `impl Fn* for &F`
        // Items. Their lowered signatures now spread (`body.spread_arg`), so
        // every DIRECT caller must classify args with the same spread rule.
        // (`Virtual` dyn calls never reach here — the pre-pass routes them.)
        rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn => {
            cx.tcx.fn_sig(callee.def_id()).skip_binder().abi()
                == rustc_abi::ExternAbi::RustCall
        }
        _ => false,
    }
}

/// Whether a trait method `def_id` is one of the `Fn` / `FnMut` / `FnOnce` trait
/// methods (`call` / `call_mut` / `call_once`) — the "rust-call" ABI methods whose
/// LAST parameter is an ARGS TUPLE that the callee UNTUPLES (spreads). A `dyn Fn`
/// vtable's method slot points at the concrete closure body, which our lowering emits
/// with SPREAD parameters (`spread_closure_args`), so a virtual call through it must
/// spread the args tuple too — exactly as a direct closure call does.
fn is_fn_trait_method<'tcx>(cx: &Cx<'tcx, '_>, def_id: rustc_hir::def_id::DefId) -> bool {
    // A trait method's parent DefId is its trait.
    let trait_did = cx.tcx.parent(def_id);
    let li = cx.tcx.lang_items();
    Some(trait_did) == li.fn_trait()
        || Some(trait_did) == li.fn_mut_trait()
        || Some(trait_did) == li.fn_once_trait()
}

/// The `CallIndirect` signature for a rust-call VIRTUAL dispatch (`dyn Fn`/`FnMut`/
/// `FnOnce`): the concrete closure body's SPREAD parameter list — the receiver (the
/// closure env, a leading `Ptr`) then each args-tuple field spread by value / by-ref
/// (`spread_closure_args`), returning the call's own return ABI. This is the exact
/// signature the emitted closure-body module carries, so the indirect call is
/// wire-compatible with the vtable's method pointer.
fn virtual_rustcall_signature<'tcx>(
    cx: &Cx<'tcx, '_>,
    args: &[rustc_span::Spanned<Operand<'tcx>>],
    destination: &Place<'tcx>,
    pair_value_ok: bool,
) -> Result<(Vec<TIRTy>, Vec<TIRTy>), String> {
    // A dyn Fn/FnMut/FnOnce dispatch is always a Rust-ABI edge.
    let ret = call_return_abi(cx, destination, pair_value_ok, false)?;
    let mut params: Vec<TIRTy> = Vec::new();
    if matches!(ret, CallRet::Sret) {
        params.push(TIRTy::Ptr);
    }
    for slot in spread_closure_args(cx, args)? {
        let abi = match &slot {
            SpreadSlot::Whole(_, abi) => abi,
            SpreadSlot::TupleField { abi, .. } => abi,
        };
        match abi {
            ArgAbi::Scalar(t) => params.push(t.clone()),
            ArgAbi::AggByRef => params.push(TIRTy::Ptr),
            ArgAbi::Zst => {}
            ArgAbi::PairByValue(pr) => params.push(pr.tuple_ty()),
        }
    }
    let returns = match ret {
        CallRet::Direct(v) => v,
        CallRet::Sret => Vec::new(),
        CallRet::Pair(pr) => vec![pr.tuple_ty()],
    };
    Ok((params, returns))
}

/// RUNG 9: the per-ABI-slot classification of a closure-body call's arguments AFTER
/// rust-call untupling. The receiver (`self` = the closure env) is the first MIR arg
/// (passed as a by-ref `Ptr` to the capture struct, or `Zst` for a captureless
/// closure). The trailing MIR arg is the ARGS TUPLE; it is SPREAD into one ABI slot
/// per tuple field (each field classified by `classify_field_abi`). The result lists
/// every slot in callee-signature order, each tagged with the SOURCE it is read from
/// (a whole operand, or a field of the tuple operand) so the emission site can load
/// it. FAIL-LOUD if the call shape is not `(self, args_tuple)`.
enum SpreadSlot<'tcx> {
    /// A whole call operand (the receiver `self`).
    Whole(Operand<'tcx>, ArgAbi),
    /// Field `idx` (at byte `off`) of the args-tuple operand `tuple` — a spread
    /// element. `abi` is the field's own ABI form (scalar by value / aggregate
    /// by-ref); ZST fields are dropped (not listed).
    TupleField {
        tuple: Operand<'tcx>,
        off: u64,
        abi: ArgAbi,
    },
}

/// RUNG 9: classify a closure-body call's args into per-slot `SpreadSlot`s (untupling
/// the trailing args tuple). `args` is the MIR call's argument list: `[self,
/// args_tuple]` (or just `[args_tuple]` for some shims — handled by treating a single
/// non-tuple arg as the receiver and a tuple as the spread). FAIL-LOUD on an
/// unexpected shape.
fn spread_closure_args<'tcx>(
    cx: &Cx<'tcx, '_>,
    args: &[rustc_span::Spanned<Operand<'tcx>>],
) -> Result<Vec<SpreadSlot<'tcx>>, String> {
    // The closure call is `call_once(self, (a0, a1, ..))` -> exactly two MIR args:
    // the receiver and the args tuple.
    let [recv, tup] = args else {
        return Err(format!(
            "closure rust-call: expected (self, args_tuple), got {} args",
            args.len()
        ));
    };
    let mut out: Vec<SpreadSlot<'tcx>> = Vec::new();
    // The receiver `self` (the capture struct): a by-ref aggregate, or Zst for a
    // captureless closure.
    // The closure receiver (a capture struct) is always by-ref; it is never a
    // by-value pair, so `pair_value_ok = false` here.
    out.push(SpreadSlot::Whole(
        recv.node.clone(),
        classify_call_arg(cx, &recv.node, false)?,
    ));
    // The args tuple: spread each field into its own ABI slot at the tuple layout's
    // field offset.
    let tup_ty = operand_concrete_ty(cx, &tup.node);
    let ty::Tuple(elems) = tup_ty.kind() else {
        // A captureless / 0-arg closure can take a unit `()` args tuple — Zst, no
        // slots. Any other non-tuple final arg is unexpected.
        if is_unit(tup_ty) || ty_is_zst(cx, tup_ty) {
            return Ok(out);
        }
        return Err(format!(
            "closure rust-call: args operand is not a tuple ({})",
            ty_family(tup_ty)
        ));
    };
    let layout = cx
        .tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(tup_ty))
        .map_err(|e| format!("closure args-tuple layout_of failed: {e:?}"))?;
    for (i, fty) in elems.iter().enumerate() {
        let fty = cx.mono(fty);
        if ty_is_zst(cx, fty) {
            continue;
        }
        let off = layout.fields.offset(i).bytes();
        let abi = if let Some(t) = spread_field_scalar_leaf(cx, fty) {
            ArgAbi::Scalar(t)
        } else {
            // A by-value aggregate tuple field crosses by-ref (a Ptr to the field's
            // slot inside the tuple). Validate it is sized.
            let _ = memory_layout_size_align(cx, fty)?;
            ArgAbi::AggByRef
        };
        out.push(SpreadSlot::TupleField {
            tuple: tup.node.clone(),
            off,
            abi,
        });
    }
    Ok(out)
}

/// How one call ARGUMENT crosses the ABI boundary.
enum ArgAbi {
    /// A scalar value of this trust-ir type (SSA scalar / memory leaf / constant).
    Scalar(TIRTy),
    /// A by-value aggregate passed BY REFERENCE: a `Ptr` to the source aggregate's
    /// slot (RUNG 3, matching the callee's by-ref aggregate parameter ABI).
    AggByRef,
    /// A unit / ZST argument: occupies no ABI slot.
    Zst,
    /// RUNG 11: a small int/bool-lane pair passed BY VALUE as ONE SSA 2-tuple
    /// (the caller mirror of the callee's by-value pair PARAM). Only classified on
    /// an IN-MODULE edge (`pair_value_ok`), so a bodyless extern keeps the by-ref
    /// aggregate ABI. The call site emits a single whole-aggregate Load of the
    /// source slot to produce the tuple value.
    PairByValue(PairRet),
}

/// Classify a call argument operand into its ABI form (scalar / by-ref aggregate /
/// ZST / by-value pair). A bare SSA scalar / memory scalar-leaf / scalar constant is
/// a Scalar; a small int/bool-lane pair place on an in-module edge (`pair_value_ok`,
/// RUNG 11) is PairByValue; any other by-value aggregate place is AggByRef; a unit is
/// Zst. The type/value lowering at the call site mirrors this classification exactly,
/// so both sides of the edge agree by construction.
fn classify_call_arg<'tcx>(
    cx: &Cx<'tcx, '_>,
    op: &Operand<'tcx>,
    pair_value_ok: bool,
) -> Result<ArgAbi, String> {
    match op {
        Operand::Copy(place) | Operand::Move(place) => {
            if place.projection.is_empty() {
                match cx.model.get(&place.local) {
                    Some(LocalModel::Ssa(t)) => return Ok(ArgAbi::Scalar(t.clone())),
                    // RUNG 4: a ZST local argument crosses the ABI as zero values.
                    Some(LocalModel::Zst) => return Ok(ArgAbi::Zst),
                    Some(LocalModel::Memory(_)) => {
                        // A bare memory-backed local: a single-scalar leaf is passed
                        // by value (its loaded scalar); a true aggregate is by-ref.
                        // `param_scalar_leaf_tir_ty` ALSO admits a transparent int
                        // newtype (`Group(u64)` / `Tag(u8)`), so a `group.match_tag(..)`
                        // receiver passes the inner scalar BY VALUE — matching the
                        // callee's by-value scalar param (the `Scalar` emission Loads
                        // the inner scalar from the slot).
                        let cty = cx.local_concrete_ty(place.local);
                        if let Some(t) = param_scalar_leaf_tir_ty(cx, cty) {
                            return Ok(ArgAbi::Scalar(t));
                        }
                        if is_unit(cty) {
                            return Ok(ArgAbi::Zst);
                        }
                        // RUNG 11: on an IN-MODULE edge, a small int/bool-lane pair
                        // arg crosses BY VALUE as one SSA 2-tuple (matching the
                        // callee's SSA-tuple param); off such an edge (or with the
                        // flag off — `pair_ret_model` is `None`) it stays by-ref.
                        if pair_value_ok {
                            if let Some(pr) = pair_ret_model(cx, cty) {
                                return Ok(ArgAbi::PairByValue(pr));
                            }
                        }
                        // An UNSIZED local argument (`unsized_fn_params`: the
                        // by-value `dyn FnOnce` receiver of the virtual
                        // `call_once`) passes the ADDRESS of its 16-byte fat
                        // carrier slot — the same pointer-to-(data,vtable) form
                        // the virtual-dispatch emission reads through.
                        if unsized_local_carrier(cx, cty).is_some() {
                            return Ok(ArgAbi::AggByRef);
                        }
                        // A by-value aggregate argument -> by-ref.
                        let _ = memory_layout_size_align(cx, cty)?;
                        return Ok(ArgAbi::AggByRef);
                    }
                    None => {
                        let cty = cx.local_concrete_ty(place.local);
                        if is_unit(cty) {
                            return Ok(ArgAbi::Zst);
                        }
                    }
                }
            }
            // RUNG 4: a projected place whose leaf type is a ZST passes nothing.
            if ty_is_zst(cx, cx.place_concrete_ty(place)) {
                return Ok(ArgAbi::Zst);
            }
            // RUNG 11: a projected place of small-pair type crosses BY VALUE on an
            // in-module edge (its address is a whole-aggregate Load at the emission
            // site). Off such an edge / with the flag off this is skipped.
            if pair_value_ok {
                if let Some(pr) = pair_ret_model(cx, cx.place_concrete_ty(place)) {
                    return Ok(ArgAbi::PairByValue(pr));
                }
            }
            // A projected place that bottoms out at a scalar leaf is a Scalar.
            if let Ok(t) = place_leaf_tir_ty(cx, place) {
                return Ok(ArgAbi::Scalar(t));
            }
            // An UNSIZED arg place (THREADS / `unsized_fn_params`): the
            // alloc-crate `<Box<dyn FnOnce>>::call_once` passes `move (*_8)`
            // (`_8: *const dyn FnOnce`) as the by-value unsized receiver of the
            // virtual `call_once`. It crosses as a `Ptr` TO ITS FAT (data,
            // metadata) CARRIER — the emission site passes the fat CELL's
            // address (`_8`'s own slot), which is exactly the pointer-to-pair
            // form the virtual-dispatch emission dereferences. Only the bare
            // `(*fat_local)` shape is emittable; deeper unsized places fail
            // loud at emission.
            let leaf_ty = cx.place_concrete_ty(place);
            if unsized_local_carrier(cx, leaf_ty).is_some() {
                return Ok(ArgAbi::AggByRef);
            }
            // Otherwise the projected place's leaf is a by-value AGGREGATE — pass it
            // BY REF (a `Ptr` to the leaf's address). This is the `VTableShim` body
            // `_0 = <Self as FnOnce>::call_once(move (*_1), move _2)` where `_1: *mut
            // Self` and `Self` is a (non-ZST) CLOSURE / ENUM: the aggregate receiver
            // `(*_1)` is passed by reference, and `place_address` computes its address
            // as the loaded pointer `_1` (the by-ref ABI a lowered callee models its
            // own by-value aggregate param with). Require a computable sized layout so
            // an unmodelable leaf still fails loud.
            let _ = memory_layout_size_align(cx, leaf_ty)?;
            Ok(ArgAbi::AggByRef)
        }
        Operand::Constant(c) => {
            let cty = cx.mono(c.const_.ty());
            // RUNG 4: a ZST constant (unit, a ZST struct/fndef value) passes nothing.
            if is_unit(cty) || ty_is_zst(cx, cty) {
                return Ok(ArgAbi::Zst);
            }
            // A bare scalar constant (int / bool) is a Scalar arg.
            if let Some(t) = scalar_tir_ty(cty) {
                return Ok(ArgAbi::Scalar(t));
            }
            // ADDITIVE: a constant whose type is a transparent single-scalar-field
            // newtype (`#[repr(transparent)] struct Tag(u8)`) has a `BackendRepr::
            // Scalar` layout and is passed by value AS that inner scalar in the ABI.
            // `cast_scalar_tir_ty` already maps such a layout-scalar ADT to its inner
            // trust-ir int/ptr type (the same admission the Cast path makes). The
            // const VALUE is read at the inner scalar width by `lower_const_operand`.
            // This is what `repeat(Tag(0x01))` in the SwissTable group scan needs.
            if let Some(t) = cast_scalar_tir_ty(cx, cty) {
                return Ok(ArgAbi::Scalar(t));
            }
            // ADDITIVE (R3 stage 1): a `&'static str` / `&'static [u8]` LITERAL
            // call arg (a fat-pointer constant, e.g. `String::from("Tree.rec")`,
            // `push_str(".rec")`). Its bytes are materialized once per function
            // in the entry block (`materialize_str_consts`: immortal heap image
            // + 16-byte (ptr,len) pair slot); the call passes the PAIR SLOT's
            // address — the same AggByRef convention a lowered callee models its
            // own fat `&str` param with, so both sides agree by construction.
            if str_const_bytes(cx, c).is_some() {
                return Ok(ArgAbi::AggByRef);
            }
            // ADDITIVE (R1): a CONSTANT AGGREGATE call arg (an enum / struct / tuple
            // value passed BY VALUE — e.g. `Option::<Arguments>::None` on a nounwind
            // panic path, a monomorphized `Layout` / `TableLayout` allocator arg).
            // Its byte image is materialized into a fresh stack slot at the call site
            // and passed BY REF as a `Ptr` (the `AggByRef` convention). We admit it
            // here only when `const_agg_bytes` proves it materializable (a
            // pointer-free in-memory / scalar-repr aggregate); a provenance-bearing
            // or unevaluable const still fails loud below.
            if const_agg_bytes(cx, c).is_ok() {
                return Ok(ArgAbi::AggByRef);
            }
            Err(format!("call arg constant of non-scalar type {}", ty_family(cty)))
        }
        Operand::RuntimeChecks(_) => Err("call arg: RuntimeChecks".to_string()),
    }
}

/// Compute the EXTERN declaration of a call's callee: its stable symbol name and
/// a trust-ir signature SYNTHESIZED from the lowered arg/dest ABI (so the
/// validator's by-construction arg/return checks pass). RUNG 3: a callee that
/// returns a by-value aggregate gets a leading SRET `Ptr` param + a void return;
/// a by-value aggregate ARG is passed by-ref as a `Ptr`. Fails loud on an
/// indirect callee.
fn call_extern_signature<'tcx>(
    cx: &Cx<'tcx, '_>,
    func: &Operand<'tcx>,
    args: &[rustc_span::Spanned<Operand<'tcx>>],
    destination: &Place<'tcx>,
    pair_value_ok: bool,
) -> Result<(String, Vec<TIRTy>, Vec<TIRTy>), String> {
    let instance = resolve_call_callee(cx, func).ok_or_else(|| {
        let shape = match func {
            Operand::Constant(c) => format!("FnDef-const {:?}", cx.mono(c.const_.ty()).kind()),
            Operand::Copy(_) | Operand::Move(_) => {
                format!("fn-ptr value {:?}", operand_concrete_ty(cx, func).kind())
            }
            Operand::RuntimeChecks(_) => "runtime-checks".to_string(),
        };
        format!("Call: indirect / unresolved callee (RUNG 3) [{shape}]")
    })?;
    let name = cx.tcx.symbol_name(instance).name.to_string();
    let (params, returns) =
        call_signature_params_returns(cx, func, args, destination, pair_value_ok)?;
    Ok((name, params, returns))
}

/// The trust-ir `(params, returns)` a call implies — the callee-INDEPENDENT part
/// of `call_extern_signature`, shared with the fn-pointer INDIRECT-call path (which
/// has no resolvable callee symbol). Params/returns are synthesized from the call's
/// arg/dest ABI (a by-value aggregate arg -> `Ptr`, an sret return -> a leading
/// `Ptr` param + void return, a small pair -> one 2-tuple), so the caller and any
/// lowered callee classify identically by construction.
fn call_signature_params_returns<'tcx>(
    cx: &Cx<'tcx, '_>,
    func: &Operand<'tcx>,
    args: &[rustc_span::Spanned<Operand<'tcx>>],
    destination: &Place<'tcx>,
    pair_value_ok: bool,
) -> Result<(Vec<TIRTy>, Vec<TIRTy>), String> {
    let call_ret = call_return_abi(cx, destination, pair_value_ok, callee_is_extern_c(cx, func))?;
    let returns = call_ret.signature_returns();
    // `#[track_caller]` ABI: the callee's signature ends with the hidden
    // `&'static Location` `Ptr` (appended after ALL real args on both return
    // paths below — the position rustc's `FnAbi` gives it). The lowered BODY
    // of such a callee appends the same param by the same predicate.
    let needs_cl = callee_needs_caller_location(cx, func);
    let mut params: Vec<TIRTy> = Vec::with_capacity(args.len() + 2);
    if call_ret.has_sret() {
        params.push(TIRTy::Ptr);
    }
    // RUNG 9: a closure-body callee uses the `"rust-call"` ABI — the trailing args
    // tuple is UNTUPLED into the closure body's trailing params. Synthesize the
    // signature over the SPREAD slots (receiver `self` + one slot per tuple field),
    // matching how the closure body's own signature is classified.
    if is_closure_rust_call(cx, func) {
        for slot in spread_closure_args(cx, args)? {
            let abi = match slot {
                SpreadSlot::Whole(_, abi) => abi,
                SpreadSlot::TupleField { abi, .. } => abi,
            };
            match abi {
                ArgAbi::Scalar(t) => params.push(t),
                ArgAbi::AggByRef => params.push(TIRTy::Ptr),
                ArgAbi::Zst => {}
                // A closure spread field is classified via `scalar_or_ptr_wrapper_leaf`
                // (never by-value pair), so this is unreachable.
                ArgAbi::PairByValue(_) => {
                    return Err("closure spread arg unexpectedly a by-value pair (RUNG 11)"
                        .to_string())
                }
            }
        }
        if needs_cl {
            params.push(TIRTy::Ptr);
        }
        return Ok((params, returns));
    }
    for a in args {
        match classify_call_arg(cx, &a.node, pair_value_ok)? {
            ArgAbi::Scalar(t) => params.push(t),
            ArgAbi::AggByRef => params.push(TIRTy::Ptr),
            ArgAbi::Zst => {}
            // RUNG 11: a by-value pair arg contributes ONE 2-tuple param (matching
            // the in-module callee's SSA-tuple param), NOT a by-ref `Ptr`.
            ArgAbi::PairByValue(pr) => params.push(pr.tuple_ty()),
        }
    }
    if needs_cl {
        params.push(TIRTy::Ptr);
    }
    Ok((params, returns))
}

/// Whether a `Call`'s callee is a genuine FN-POINTER VALUE (an `Operand::Copy/Move`
/// of a `fn(..)`-typed place) rather than a resolvable `FnDef` constant — the
/// indirect-call shape lowered via `CallIndirect`. A `dyn`/virtual method call
/// (whose `func` is an `FnDef` constant that resolves to a `Virtual` instance) is
/// NOT this — that needs a vtable model and stays a loud failure.
fn is_fn_ptr_indirect_call<'tcx>(cx: &Cx<'tcx, '_>, func: &Operand<'tcx>) -> bool {
    if resolve_call_callee(cx, func).is_some() {
        return false;
    }
    match func {
        // A fn-pointer VALUE (`(*fnptr)(args)`).
        Operand::Copy(_) | Operand::Move(_) => {
            matches!(operand_concrete_ty(cx, func).kind(), ty::FnPtr(..))
        }
        // A fn-pointer CONSTANT (quicksort's const-propagated
        // `partition_lomuto_.. as fn(..)` callee): the operand lowers to a
        // `SymbolAddr` fn pointer; the call is the same `CallIndirect`. (The
        // reference-closure const-alloc scan pulls the pointee fn's body.)
        Operand::Constant(c) => matches!(cx.mono(c.const_.ty()).kind(), ty::FnPtr(..)),
        Operand::RuntimeChecks(_) => false,
    }
}

/// How a call's result crosses back to its destination (the caller-side mirror
/// of `RetAbi`, computed from the destination PLACE's type — the callee's `_0`
/// type — so both sides classify identically by construction).
enum CallRet {
    /// Zero or one scalar return value(s), bound directly to the destination.
    Direct(Vec<TIRTy>),
    /// The result is written through the leading hidden sret pointer; the call
    /// itself returns void.
    Sret,
    /// RUNG 10: a by-value small-pair result — the call returns ONE SSA 2-tuple
    /// the caller spills into the destination slot.
    Pair(PairRet),
}

impl CallRet {
    /// The trust-ir signature `returns` list this form implies.
    fn signature_returns(&self) -> Vec<TIRTy> {
        match self {
            CallRet::Direct(returns) => returns.clone(),
            CallRet::Sret => Vec::new(),
            CallRet::Pair(pr) => vec![pr.tuple_ty()],
        }
    }

    /// Whether the signature takes the leading hidden sret `Ptr` param.
    fn has_sret(&self) -> bool {
        matches!(self, CallRet::Sret)
    }
}

/// The return form for a call's destination. A scalar dest -> `Direct([scalar])`;
/// a unit / diverging dest -> `Direct([])`; a small int/bool pair dest ->
/// `Pair` (RUNG 10, by value) — but ONLY on an in-module edge
/// (`pair_value_ok`, see `callee_lowered_in_module`); any other aggregate dest
/// -> `Sret` (the result is written through the leading hidden pointer).
fn call_return_abi<'tcx>(
    cx: &Cx<'tcx, '_>,
    destination: &Place<'tcx>,
    pair_value_ok: bool,
    // The callee is `extern "C"`-family (`callee_is_extern_c`): a single-
    // scalar-repr destination (fieldless repr(C) enum — `_Unwind_Reason_Code`)
    // is returned BY VALUE per the C ABI, never via sret. `false` on every
    // Rust-ABI edge keeps the historical classification byte-stable.
    c_scalar_ret: bool,
) -> Result<CallRet, String> {
    if destination.projection.is_empty() {
        match cx.model.get(&destination.local) {
            Some(LocalModel::Ssa(t)) => return Ok(CallRet::Direct(vec![t.clone()])),
            // RUNG 4: a ZST call destination has no ABI return value.
            Some(LocalModel::Zst) => return Ok(CallRet::Direct(Vec::new())),
            Some(LocalModel::Memory(_)) => {
                // A bare memory-backed destination: a single-scalar leaf is returned
                // by value; a THIN pointer-wrapper is returned by value as one `Ptr`;
                // a small int/bool pair is returned by value as one 2-tuple (RUNG 10);
                // a true aggregate destination uses sret.
                let cty = cx.local_concrete_ty(destination.local);
                if let Some(leaf) = memory_leaf_tir_ty(cx.tcx, cty) {
                    return Ok(CallRet::Direct(vec![leaf]));
                }
                // The return-edge dual of the ac3c8ac param-side fix: a thin
                // pointer-wrapper (`Box<Sized>`/`NonNull`/`Unique`/`Rc`/`Arc`) crosses
                // BY VALUE as one `Ptr` in x0 — the same predicate the CALLEE's
                // `classify_locals_and_ret_abi` uses for `_0`, so both edge sides
                // agree by construction (unconditional, like the by-value ARG fix: a
                // bodyless extern callee that returns a wrapper uses the real by-value
                // C ABI). Restricted to `Ptr` so a fat wrapper / integer newtype /
                // true aggregate stays on the pair/sret path below (fail-closed).
                if let Some(TIRTy::Ptr) = param_scalar_leaf_tir_ty(cx, cty) {
                    return Ok(CallRet::Direct(vec![TIRTy::Ptr]));
                }
                // extern "C" callee: ANY single-scalar-repr destination returns
                // by value (see the `c_scalar_ret` doc above) — the caller-side
                // twin of the callee's `instance_is_extern_c` RetAbi widening.
                if c_scalar_ret {
                    if let Some(t) = param_scalar_leaf_tir_ty(cx, cty) {
                        return Ok(CallRet::Direct(vec![t]));
                    }
                }
                if pair_value_ok {
                    if let Some(pr) = pair_ret_model(cx, cty) {
                        return Ok(CallRet::Pair(pr));
                    }
                }
                let _ = memory_layout_size_align(cx, cty)?;
                return Ok(CallRet::Sret);
            }
            None => {}
        }
        // No model entry: a unit / ZST destination (no ABI return value).
        let cty = cx.local_concrete_ty(destination.local);
        if is_unit(cty) {
            return Ok(CallRet::Direct(Vec::new()));
        }
        return Err(format!(
            "Call: non-scalar destination local {} (unmodelable)",
            ty_family(cty)
        ));
    }
    // RUNG 4: a projected ZST destination has no ABI return value.
    if ty_is_zst(cx, cx.place_concrete_ty(destination)) {
        return Ok(CallRet::Direct(Vec::new()));
    }
    // RUNG 10: a projected destination of small-pair type receives the by-value
    // 2-tuple (spilled at the projected address, same as the bare-local case).
    if pair_value_ok {
        if let Some(pr) = pair_ret_model(cx, cx.place_concrete_ty(destination)) {
            return Ok(CallRet::Pair(pr));
        }
    }
    // A projected destination whose leaf is a by-ref AGGREGATE (a call whose
    // result lands in an aggregate FIELD — `Map::map(..)` written into
    // `(_17.0)` while building a nested-iterator struct): sret through the
    // PROJECTED address, exactly like the bare-local aggregate case (the sret
    // arg emission takes `place_address(destination)`, which handles the
    // projection).
    {
        let cty = cx.place_concrete_ty(destination);
        if memory_leaf_tir_ty(cx.tcx, cty).is_none()
            && cast_scalar_tir_ty(cx, cty).is_none()
            && !is_unit(cty)
        {
            if pair_value_ok {
                if let Some(pr) = pair_ret_model(cx, cty) {
                    return Ok(CallRet::Pair(pr));
                }
            }
            let _ = memory_layout_size_align(cx, cty)?;
            return Ok(CallRet::Sret);
        }
    }
    // A projected destination: a scalar leaf returned by value.
    let leaf = place_leaf_tir_ty(cx, destination)?;
    Ok(CallRet::Direct(vec![leaf]))
}

/// Per-block terminator-lowering context (the cross-block phi edge args + Call /
/// Assert wiring).
struct TermCtx<'a> {
    /// trust-ir block per MIR block index — `None` for a non-normal-reachable
    /// (cleanup-only) block that this lowering never emits.
    blocks: &'a [Option<trust_ir::BlockId>],
    /// Per block index, the SSA-scalar locals that became its block parameters
    /// (stable local order) — the values an edge into that block must supply.
    block_param_locals: &'a [Vec<Local>],
    /// How the function returns its result (scalar value / unit-void / sret).
    ret_abi: RetAbi,
    /// The declared extern `FuncId` for this block's `Call` terminator (if any).
    callee_id: Option<trust_ir::FuncId>,
    /// R6: the registered `FuncTy` when this block's `Call` is a FN-POINTER INDIRECT
    /// call. `Some` -> emit `CallIndirect` through the lowered fn-pointer VALUE (the
    /// `func` operand) with this signature, instead of a direct `Call` to `callee_id`.
    indirect_sig: Option<trust_ir::FuncTyId>,
    /// DYN/VIRTUAL dispatch: when this block's `Call` resolves to a `Virtual` trait
    /// method, the call's `FuncTy` + the vtable SLOT index. `Some` -> emit a vtable
    /// load (`data`/`vtable`/`fnptr`) + `CallIndirect`, with the `&dyn` receiver arg
    /// replaced by its data pointer.
    virtual_dispatch: Option<(trust_ir::FuncTyId, usize, bool)>,
    /// RUNG 10: whether this block's `Call` edge is IN-MODULE (self-recursion /
    /// emit-closure member), so a small-pair destination receives the by-value
    /// 2-tuple. MUST agree with the pre-pass signature synthesis (both read the
    /// same `pair_ret_blocks` decision).
    pair_ret_ok: bool,
    /// The declared drop-glue `FuncId` for this block's `Drop` terminator (if its
    /// place needs drop; `None` for a no-drop place = just a branch).
    drop_callee_id: Option<trust_ir::FuncId>,
    /// VIRTUAL (dyn) drop: this block's `Drop` place is a `dyn Trait` pointee —
    /// dispatch through the fat pointer's vtable slot 0 with this `(ptr) -> ()`
    /// signature instead of a (self-recursive) glue symbol call.
    dyn_drop_sig: Option<trust_ir::FuncTyId>,
    /// RUNG 5: when this block's `Call` is an `<Arc<T> as Deref>::deref` we inline,
    /// the ArcInner data offset to add to the (loaded) thin Arc pointer. `Some`
    /// here means the terminator emits `load + gep` instead of a `call`.
    arc_deref_offset: Option<u64>,
    /// RUNG 6: when this block's `Call` is an `Arc::<T>::new` we inline, the
    /// `ArcInner<T>` layout. `Some` here means the terminator emits a `heap_alloc`
    /// + counter/data Stores instead of a `call`.
    arc_new_layout: Option<ArcInnerLayout>,
    /// RUNG 7: when this block's `Call` is the `(uN, uN, &str) -> uN` saturating-add
    /// diagnostic helper we inline, the unsigned-int lane type. `Some` here means
    /// the terminator emits `overflow(Add) + select` (dropping the `&str`) instead
    /// of a `call`.
    sat_add_lane: Option<TIRTy>,
    /// Both panic lanes: this block's `Call` is a size-scaled raw-memory intrinsic
    /// mono (`copy` / `write_bytes`) lowered inline with the
    /// element stride from the pre-pass (see `MemIntrinsicInline`).
    mem_intrinsic: Option<MemIntrinsicInline>,
    /// Both panic lanes: this block's `Call` is a canonical raw-pointer
    /// `offset` / `wrapping_offset` wrapper retained by cross-crate MIR. The
    /// recorded mode chooses an admitted GEP or general integer-pointer path;
    /// either way, the wrapper cannot survive as an opaque call.
    raw_ptr_offset: Option<RawPtrOffsetInline>,
    /// RUNG 8b: when this block's `Call` is `IntoIterator::into_iter` we inline, the
    /// iterator cursor model. `Some` -> emit a `(cur,end)` cursor-init from the Vec.
    into_iter_model: Option<IterModel>,
    /// RUNG 8b: when this block's `Call` is `Iterator::next` we inline, the iterator
    /// cursor model. `Some` -> emit a cursor index-bump + `Some`/`None` write.
    iter_next_model: Option<IterModel>,
    /// RUNG 8b: when this block's `Call` is `Box::<U>::new_uninit()` we inline, the
    /// buffer layout. `Some` -> emit a `heap_alloc` of the buffer.
    box_new_uninit: Option<BoxNewUninitLayout>,
    /// RUNG 8b: when this block's `Call` is `box_assume_init_into_vec_unsafe::<T,N>`
    /// we inline, the element count. `Some` -> emit a 3-word `Vec{ptr,N,N}` header.
    box_into_vec: Option<BoxIntoVecLayout>,
    /// ADDITIVE (R4 stage 2): when this block's `Call` is an in-module str/byte
    /// shape we inline (`str::as_bytes`/`str::len`/`str::bytes`/`<[u8]>::iter`/
    /// blanket-identity `into_iter`). `Some` -> emit fat-pair lane reads /
    /// cursor writes instead of a `call`.
    str_inline: Option<StrInlineOp>,
    /// The shared Assert-failure trap block, allocated lazily on first use.
    trap_block: &'a mut Option<trust_ir::BlockId>,
    /// UNWIND lane: whether this compilation session lowers unwind edges faithfully
    /// (`eh_lane`). `false` under panic=abort — every EH field below is inert.
    eh: bool,
    /// The trust-ir block of the MIR block currently being lowered — the block
    /// the pad-synthesis helper switches back to after filling a landing pad.
    cur_blk: trust_ir::BlockId,
    /// The per-function exception-pointer slot (entry `Alloca(Ptr)`), present
    /// iff this body synthesizes pads. Pads store the exception object here;
    /// `UnwindResume` loads it back for `Resume`.
    exn_slot: Option<trust_ir::ValueId>,
    /// The shared per-reason TERMINATE pads (double-panic -> the reason's
    /// `core::panicking` terminate entry + abort), allocated lazily on first
    /// `UnwindAction::Terminate(reason)` invoke and filled after the block
    /// loop. Indexed by `terminate_reason_idx`.
    terminate_pads: &'a mut [Option<trust_ir::BlockId>; 2],
    /// The declared `core::panicking` terminate entry points (`fn() -> !`),
    /// indexed by `terminate_reason_idx`: `panic_cannot_unwind` (Abi) /
    /// `panic_in_cleanup` (InCleanup). `Some` for every reason that appears in
    /// this body's MIR (terminate pre-pass).
    terminate_fids: [Option<trust_ir::FuncId>; 2],
    /// UNWIND lane: this block's `Call` is the `catch_unwind` intrinsic,
    /// pre-lowered to the inline `__rust_try` shape with these DIRECT
    /// (do_call, do_catch) callees.
    catch_expand: Option<(trust_ir::FuncId, trust_ir::FuncId)>,
    /// UNWIND lane: this block's `Assert` failure path calls this declared
    /// `core::panicking` entry point (rustc parity) instead of trapping.
    assert_panic: Option<AssertPanicCall>,
    /// UNWIND lane: this block's indirect (fn-pointer / virtual / dyn-drop)
    /// call carries its cleanup edge through this synthesized direct THUNK:
    /// the site emits `Invoke(thunk, fnptr, args.., pad)`.
    indirect_thunk: Option<trust_ir::FuncId>,
    /// UNWIND lane, `#[track_caller]`: this block's `Call` is the
    /// `caller_location` intrinsic, pre-lowered INLINE (no extern declared) —
    /// the emission binds `get_caller_location` to the destination.
    caller_location_inline: bool,
    /// The MIR block index this terminator belongs to. Carried so the `Assert`
    /// arm can key the site it records back to the obligation the pre-pass
    /// minted for the same MIR block.
    mir_bb: usize,
    /// PANIC-CLASS OBLIGATION SITES: `(mir_bb, trust-ir block, inst index)` of
    /// each lowered-`Assert` `CondBr` this body emits. Recorded BY THE ARM THAT
    /// EMITS IT, read back from the builder — never recomputed — because a site
    /// that names the wrong instruction would silently bind an obligation to a
    /// different check.
    assert_sites: &'a mut Vec<(usize, trust_ir::BlockId, u32)>,
}

impl<'a> TermCtx<'a> {
    /// The edge arguments to pass into successor block `target`: the current
    /// `env` value of each SSA-scalar local that is a parameter of `target`, in
    /// the target's stable parameter order. (Soundness: a target parameter local
    /// is live-in to the target, hence live-out of this block, hence present in
    /// `env`; if absent that is a real bug and we fail loud rather than thread an
    /// undefined value.)
    fn edge_args(
        &self,
        env: &HashMap<Local, trust_ir::ValueId>,
        target: BasicBlock,
    ) -> Result<Vec<trust_ir::ValueId>, String> {
        let mut out = Vec::new();
        for &l in &self.block_param_locals[target.as_usize()] {
            let v = env.get(&l).copied().ok_or_else(|| {
                "cross-block phi: live-in local not bound at edge (liveness bug)".to_string()
            })?;
            out.push(v);
        }
        Ok(out)
    }

    fn target_block(&self, bb: BasicBlock) -> trust_ir::BlockId {
        // A normal edge always targets a normal-reachable block (see
        // `compute_normal_reachable`), so this `Some` holds by construction.
        self.blocks[bb.as_usize()].expect("normal edge targets an emitted block")
    }

    /// The shared trap block, created on first use (filled with `unreachable`
    /// after the block loop).
    fn trap(&mut self, fb: &mut FunctionBuilder<'_>) -> trust_ir::BlockId {
        if let Some(tb) = *self.trap_block {
            tb
        } else {
            let tb = fb.create_block();
            *self.trap_block = Some(tb);
            tb
        }
    }
}

/// Size + alignment (bytes) of a memory-backed local's slot, from `layout_of`.
fn memory_layout_size_align<'tcx>(cx: &Cx<'tcx, '_>, ty: Ty<'tcx>) -> Result<(u64, u64), String> {
    let layout = cx
        .tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(ty))
        .map_err(|e| format!("memory local layout_of failed: {e:?}"))?;
    if !layout.is_sized() {
        return Err(format!(
            "memory local is unsized: {} [ty={ty:?}]",
            ty_family(ty)
        ));
    }
    let size = layout.size.bytes();
    let align = layout.align.abi.bytes();
    if size == 0 {
        return Err(format!("memory local is zero-sized: {}", ty_family(ty)));
    }
    Ok((size, align))
}

/// A flat integer-lane tuple covering `size` bytes at `align` (1/2/4/8/16). This
/// is the `Alloca` element type: a slot of natural-aligned lanes that is byte-
/// and alignment-accurate. A single-scalar leaf (size==align) collapses to the
/// bare lane type (not a 1-tuple) so a scalar cell's slot type is the scalar.
fn slot_lane_ty(size: u64, align: u64) -> Result<TIRTy, String> {
    let lane = match align {
        1 => TIRTy::I8,
        2 => TIRTy::I16,
        4 => TIRTy::I32,
        8 => TIRTy::I64,
        // 16-byte lanes cover every alignment >= 16: the LANE type caps at
        // I128 (the widest integer access this model emits); the slot's FULL
        // 32-/64-byte ABI alignment is carried by the `alloca_aligned`
        // alignment attribute (portable-simd `Simd<i8, 32/64>` locals in
        // `Mask::valid`/`to_bitmask`, which this pipeline lowers with scalar
        // lane accesses only).
        a if a >= 16 && a.is_power_of_two() => TIRTy::I128,
        other => return Err(format!("memory slot alignment {other} unsupported [size={size}]")),
    };
    let lane_w = if align >= 16 { 16 } else { align };
    if size % lane_w != 0 {
        return Err(format!(
            "memory slot size {size} not a multiple of lane width {lane_w}"
        ));
    }
    let lanes = (size / lane_w) as usize;
    if lanes == 0 {
        return Err("memory slot is zero-sized".to_string());
    }
    if lanes == 1 {
        Ok(lane)
    } else {
        Ok(TIRTy::Tuple(vec![lane; lanes]))
    }
}

// ============================ RUNG 1: place addressing =======================

/// The trust-ir scalar LEAF type a PLACE addresses (the type of a typed
/// Load/Store at the place). Fails loud if the leaf is not a single memory
/// scalar.
fn place_leaf_tir_ty<'tcx>(cx: &Cx<'tcx, '_>, place: &Place<'tcx>) -> Result<TIRTy, String> {
    let leaf = cx.place_concrete_ty(place);
    // A single-access scalar leaf: an int/bool/thin-ptr, a single-pointer-width
    // wrapper (`Arc`/`Rc`/`NonNull`/`Unique` -> `Ptr`), OR — RUNG R3 — a niche-
    // optimized ENUM / integer newtype whose whole memory image is a SINGLE integer
    // scalar (`BackendRepr::Scalar(Int)`): `Option<NonZero<u64>>` niched to a bare
    // `u64`, `Option<&T>` (a `Ptr`), an `Ordering` `i8`, `NonZero<u64>` itself. Such
    // an enum place is Loaded/Stored as its scalar image, which agrees byte-for-byte
    // with the `discriminant` niche read and the `(x as Some).0` payload access at
    // offset 0 (both address the same slot). `cast_scalar_tir_ty` admits exactly the
    // scalar-repr types and is a strict superset of the historical
    // `scalar_or_ptr_wrapper_leaf` (identical on every previously-accepted leaf, so
    // no already-lowered function drifts): a non-niche `Option<usize>` is a
    // `ScalarPair`, NOT a `Scalar`, so it stays a by-ref aggregate and is never
    // misread as one scalar here.
    cast_scalar_tir_ty(cx, leaf)
        .ok_or_else(|| {
            format!(
                "place leaf is not a memory scalar: {} [leaf={leaf:?} place={place:?}]",
                ty_family(leaf)
            )
        })
}

/// A single-access scalar LEAF, like `memory_leaf_tir_ty`, but also admitting a
/// transparent single-pointer-width wrapper (`Arc<T>`/`Rc<T>`/`NonNull<T>`/`Unique<T>`
/// over a SIZED `T`) as a `Ptr`. RUNG 6 (Arc-WRITE) needs this: a CONSTRUCTED `Arc<T>`
/// VALUE — `Arc::new`'s thin-pointer result, then Stored into a variant field
/// (`MicroExpr::App(arc1, arc2)`) and later Loaded — flows as a single `Ptr`, but its
/// rustc type is a struct ADT (not `ty::Ref`/`ty::RawPtr`), so the tcx-free
/// `memory_leaf_tir_ty` rejects it. We consult the layout: a `BackendRepr::Scalar`
/// whose primitive is a pointer is a `Ptr` leaf (the same admission `cast_scalar_tir_ty`
/// already makes). A fat `Arc<str>` is a `ScalarPair`, not a `Scalar`, so it is NOT
/// admitted here — faithful (it is a 2-word value, not a single Ptr).
/// The ABI classification of a rust-call SPREAD slot (an args-tuple field of a
/// closure/shim call, on BOTH the caller side — `spread_closure_args` /
/// `virtual_rustcall_signature` — and the shim BODY side, the `spread_arg`
/// param synthesis). It must agree with `param_scalar_leaf_tir_ty`, the
/// classifier the CLOSURE BODY's own params and every non-spread call arg use:
/// the historical `scalar_or_ptr_wrapper_leaf`-only classification rejected an
/// INT-scalar ADT (a C-like enum such as gimli's `SectionId`, layout
/// `BackendRepr::Scalar(Int)`), so callers passed the field's ADDRESS while
/// the closure body read the param BY VALUE — the wp20 backtrace abort (the
/// discriminant became the low byte of a stack address). The union keeps every
/// previously-scalar case scalar and ADDS exactly the by-value admissions the
/// body already makes.
fn spread_field_scalar_leaf<'tcx>(cx: &Cx<'tcx, '_>, ty: Ty<'tcx>) -> Option<TIRTy> {
    param_scalar_leaf_tir_ty(cx, ty).or_else(|| scalar_or_ptr_wrapper_leaf(cx, ty))
}

fn scalar_or_ptr_wrapper_leaf<'tcx>(cx: &Cx<'tcx, '_>, ty: Ty<'tcx>) -> Option<TIRTy> {
    if let Some(t) = memory_leaf_tir_ty(cx.tcx, ty) {
        return Some(t);
    }
    let tal = cx
        .tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(ty))
        .ok()?;
    let BackendRepr::Scalar(scalar) = tal.backend_repr else {
        return None;
    };
    match scalar.primitive() {
        Primitive::Pointer(_) => Some(TIRTy::Ptr),
        _ => None,
    }
}

/// THREADS: the ADDRESS a by-ref call arg passes for an UNSIZED-leaf place. A
/// bare `(*fat_local)` place passes the fat CELL's address (the local's own
/// slot — a `Ptr` to the (data, metadata) pair, the same pointer-to-pair form a
/// `&dyn` receiver passes); a bare unsized LOCAL passes its carrier slot. Any
/// deeper unsized place shape fails loud. Returns `None` for sized places (the
/// ordinary `place_address` applies).
fn unsized_arg_carrier_addr<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    env: &HashMap<Local, trust_ir::ValueId>,
    place: &Place<'tcx>,
) -> Option<Result<trust_ir::ValueId, String>> {
    unsized_local_carrier(cx, cx.place_concrete_ty(place))?;
    let proj = place.projection.as_ref();
    if proj.len() == 1
        && matches!(proj.first(), Some(ProjectionElem::Deref))
        && is_fat_pointer(cx.tcx, cx.local_concrete_ty(place.local))
    {
        Some(place_address(cx, fb, env, &Place::from(place.local)))
    } else if proj.is_empty() {
        Some(place_address(cx, fb, env, place))
    } else {
        Some(Err(
            "unsized call-arg place shape not modelable (only (*fat) / bare unsized local)"
                .to_string(),
        ))
    }
}

/// Compute a PLACE's ADDRESS as a trust-ir `Ptr`. The base is the local's slot
/// pointer (for a memory-backed local) or the loaded pointer value (for a Deref
/// whose base is an SSA pointer); projections add byte offsets (Field/Downcast)
/// or element strides (Index). Fails loud on any projection element this minimal
/// port does not yet model.
/// The stack-slot address of an aggregate operand (a `Copy`/`Move` of a place).
/// Fails closed for a constant / by-value operand. Used by the simd-intrinsic
/// lowering, where every `uint8x8_t`/`uint64x1_t` argument is a memory-backed
/// aggregate passed by reference.
fn operand_place_address<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    env: &HashMap<Local, trust_ir::ValueId>,
    op: &Operand<'tcx>,
) -> Result<trust_ir::ValueId, String> {
    let (Operand::Copy(place) | Operand::Move(place)) = op else {
        return Err("simd intrinsic: expected a place operand for a vector argument".to_string());
    };
    place_address(cx, fb, env, place)
}

fn place_address<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    env: &HashMap<Local, trust_ir::ValueId>,
    place: &Place<'tcx>,
) -> Result<trust_ir::ValueId, String> {
    // Establish the base address + the rustc TYPE the base addresses (the type we
    // walk layouts of as the projection chain descends).
    let base_local = place.local;
    let proj = place.projection.as_ref();

    // A leading `Deref` of the base local: the base is a POINTER value, and the
    // resulting place addresses its pointee. The pointer is either the slot's
    // loaded value (memory-backed pointer cell) or an SSA pointer value.
    if let Some(ProjectionElem::Deref) = proj.first() {
        let base_ty = cx.local_concrete_ty(base_local);
        let pointee = match base_ty.kind() {
            ty::Ref(_, p, _) | ty::RawPtr(p, _) => *p,
            _ => return Err("Deref of non-pointer base local".to_string()),
        };
        let addr = load_pointer_local(cx, fb, env, base_local)?;
        let cur_ty = cx.mono(pointee);
        // When the pointee is a SLICE — or an UNSIZED-TAIL struct (`OsStr`,
        // whose metadata IS its tail slice's element count) — remember the fat
        // CELL address (the base local's slot) so a `from_end`
        // ConstantIndex/Subslice below can lazily read the length lane. A
        // `dyn` pointee's metadata is a vtable, not a count — excluded.
        // Loaded ONLY on demand — no IR drift for existing projection shapes.
        let fat_cell = if pointee_metadata_is_count(cx, cur_ty) {
            cx.slot_ptr(base_local)
        } else {
            None
        };
        // Continue with the remaining projections after the Deref.
        return walk_projection_address(cx, fb, env, addr, cur_ty, &proj[1..], fat_cell);
    }

    // RUNG 4 (ZST place): a base local classified `Zst` occupies NO storage and has
    // NO address. Any place rooted at it — the bare local, or a Field/Downcast into a
    // ZST subfield — is itself ZERO-SIZED, so it is never the target of a real
    // Load/Store (a ZST access moves 0 bytes). Its "address" is a DUMMY null `Ptr`
    // that is never dereferenced: e.g. `_3 = &mut _1` in a `ClosureOnceShim` where
    // `_1` is a CAPTURELESS (ZST) closure env, then passed to `call_mut(&mut self,..)`
    // whose ZST closure body reads no captures. Fail-closed: a ZST place can carry no
    // Deref (a ZST holds no pointer to follow — its fields are all ZST), so a Deref
    // projection here is unmodelable rather than silently null-dereferenced.
    if cx.is_zst_local(base_local) {
        if proj.iter().any(|e| matches!(e, ProjectionElem::Deref)) {
            return Err("ZST place with Deref projection (unmodelable)".to_string());
        }
        return Ok(fb.null_ptr());
    }

    // Otherwise the base is the local's slot (must be memory-backed for a place
    // with projections, or a bare memory local).
    let addr = cx
        .slot_ptr(base_local)
        .ok_or_else(|| "place base local is not memory-backed".to_string())?;
    let cur_ty = cx.local_concrete_ty(base_local);
    walk_projection_address(cx, fb, env, addr, cur_ty, proj, None)
}

/// Walk the projection chain from `base_addr` (which addresses a value of
/// `base_ty`), accumulating field byte offsets / array element strides, emitting
/// `GEP`s. Returns the final address.
///
/// `fat_cell` is the address of the fat-pointer CELL whose data lane produced
/// `base_addr` when the current pointee is a SLICE (set by the leading-Deref
/// caller / refreshed by a mid-chain Deref) — the lazily-read source of the
/// slice LENGTH for `from_end` ConstantIndex/Subslice elements. `None` when
/// the walk is over sized data (any `from_end` slice element then fails loud).
fn walk_projection_address<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    env: &HashMap<Local, trust_ir::ValueId>,
    base_addr: trust_ir::ValueId,
    base_ty: Ty<'tcx>,
    projection: &[ProjectionElem<Local, Ty<'tcx>>],
    fat_cell: Option<trust_ir::ValueId>,
) -> Result<trust_ir::ValueId, String> {
    let mut fat_cell = fat_cell;
    let lcx = LayoutCx::new(cx.tcx, ty::TypingEnv::fully_monomorphized());
    let mut cur_layout = cx
        .tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(base_ty))
        .map_err(|e| format!("place projection layout_of failed: {e:?}"))?;
    let mut addr = base_addr;
    let mut byte_offset: u64 = 0;

    for elem in projection {
        match elem {
            ProjectionElem::Field(field, _decl_ty) => {
                let off = cur_layout.fields.offset(field.index()).bytes();
                byte_offset += off;
                cur_layout = cur_layout.field(&lcx, field.index());
            }
            ProjectionElem::Downcast(_, variant_index) => {
                // A variant view contributes no offset; descend into the variant
                // so subsequent Field offsets are variant-relative.
                cur_layout = cur_layout.for_variant(&lcx, *variant_index);
            }
            ProjectionElem::Deref => {
                // A mid-chain Deref: load the pointer at the current address, then
                // continue addressing its pointee. Flush the accumulated byte
                // offset first.
                if byte_offset != 0 {
                    addr = gep_byte_offset(fb, addr, byte_offset);
                    byte_offset = 0;
                }
                let pointee = match cur_layout.ty.kind() {
                    ty::Ref(_, pt, _) | ty::RawPtr(pt, _) => cx.mono(*pt),
                    _ => return Err("mid-chain Deref of non-pointer".to_string()),
                };
                // Derefing a fat SLICE / unsized-tail-struct pointer: the cell
                // we are about to load from carries the length lane — remember
                // it for `from_end` elements below (read lazily; no drift
                // otherwise).
                fat_cell = if pointee_metadata_is_count(cx, pointee) {
                    Some(addr)
                } else {
                    None
                };
                let p = fb.load(TIRTy::Ptr, addr);
                addr = p;
                cur_layout = cx
                    .tcx
                    .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(pointee))
                    .map_err(|e| format!("deref pointee layout_of failed: {e:?}"))?;
            }
            ProjectionElem::Index(index_local) => {
                // Array/slice element index by a runtime local. Flush the byte
                // offset, then GEP to `addr + idx * stride`.
                //
                // RUNG 8: the element may be an AGGREGATE (e.g. the env slice
                // `&[(Arc<str>, Option<MicroExpr>)]`'s tuple element — the DELTA
                // scan indexes it, then Field-projects into the scalar leaves). We
                // do NOT require the element to be a scalar leaf: an element address
                // is `base + idx * element_STRIDE` regardless of the element's
                // internal shape, and the subsequent Field projections walk to the
                // scalar leaf. The stride is the element's `size.align_to(align)`
                // (its allocated extent, what the array/slice layout strides by) —
                // computed faithfully from `tcx.layout_of(element)`.
                if byte_offset != 0 {
                    addr = gep_byte_offset(fb, addr, byte_offset);
                    byte_offset = 0;
                }
                let elem_layout = element_layout(cx, &lcx, &cur_layout)?;
                // The index VALUE: an SSA scalar comes from env; a MEMORY-backed
                // index local (its address escapes elsewhere — e.g. `{begin}`
                // formatted by-ref in `slice_error_fail_rt` — while also
                // indexing here) is a typed Load from its slot.
                let idx_val = match cx.model.get(index_local) {
                    Some(LocalModel::Memory(_)) => {
                        let p = cx.slot_ptr(*index_local).ok_or_else(|| {
                            "index local slot not allocated (classification bug)".to_string()
                        })?;
                        let leaf = cast_scalar_tir_ty(cx, cx.local_concrete_ty(*index_local))
                            .ok_or_else(|| {
                                "memory-backed index local is not scalar".to_string()
                            })?;
                        fb.load(leaf, p)
                    }
                    _ => env.get(index_local).copied().ok_or_else(|| {
                        format!(
                            "index local read before assignment in block (needs phi) \
                             [local={index_local:?} proj={projection:?}]"
                        )
                    })?,
                };
                if let Some(elem_leaf) = memory_leaf_tir_ty(cx.tcx, elem_layout.ty) {
                    // Scalar element: a single typed GEP (idx * sizeof(leaf)). Keeps
                    // the existing scalar-array IR byte-identical (no drift).
                    addr = fb.gep(elem_leaf, addr, vec![idx_val]);
                } else {
                    // Aggregate element: GEP by the byte stride `idx * stride`.
                    // Multiply in the index local's own integer lane (usize -> U64),
                    // so the `mul` operand types match (the validator checks this).
                    let stride = elem_layout
                        .size
                        .align_to(elem_layout.align.abi)
                        .bytes();
                    let idx_ty = cx
                        .local_ty
                        .get(index_local)
                        .cloned()
                        .unwrap_or(TIRTy::U64);
                    let stride_c = fb.iconst(idx_ty.clone(), stride as i128);
                    let byte = fb.mul(idx_ty, idx_val, stride_c);
                    addr = fb.gep(TIRTy::I8, addr, vec![byte]);
                }
                cur_layout = elem_layout;
            }
            // A compile-time-known element index: `place[K]` (`from_end: false`)
            // or `place[len - K]` (`from_end: true`). `min_length` is MIR's
            // already-established bound guarantee (the bounds-check Assert
            // precedes this projection), so no check is emitted here — exactly
            // like the runtime `Index` arm above.
            ProjectionElem::ConstantIndex {
                offset,
                min_length: _,
                from_end,
            } => {
                if byte_offset != 0 {
                    addr = gep_byte_offset(fb, addr, byte_offset);
                    byte_offset = 0;
                }
                let elem_layout = element_layout(cx, &lcx, &cur_layout)?;
                let stride = elem_layout.size.align_to(elem_layout.align.abi).bytes();
                if !*from_end {
                    byte_offset += offset * stride;
                } else {
                    match cur_layout.ty.kind() {
                        // Array: the length is static, so the index is too.
                        ty::Array(_, n) => {
                            let n = n
                                .try_to_target_usize(cx.tcx)
                                .ok_or("from_end ConstantIndex: array length not constant")?;
                            if n < *offset {
                                return Err(
                                    "from_end ConstantIndex offset exceeds array length"
                                        .to_string(),
                                );
                            }
                            byte_offset += (n - offset) * stride;
                        }
                        // Slice: read the length from the fat cell (lazily),
                        // then GEP by `(len - K) * stride`.
                        ty::Slice(_) | ty::Str => {
                            let cell = fat_cell.ok_or_else(|| {
                                format!(
                                    "from_end ConstantIndex on a slice without a reachable \
                                     fat cell [base={base_ty:?} proj={projection:?}]"
                                )
                            })?;
                            let len_addr = gep_byte_offset(fb, cell, 8);
                            let len = fb.load(TIRTy::U64, len_addr);
                            let offc = fb.iconst(TIRTy::U64, *offset as i128);
                            let idx = fb.sub(TIRTy::U64, len, offc);
                            let stride_c = fb.iconst(TIRTy::U64, stride as i128);
                            let byte = fb.mul(TIRTy::U64, idx, stride_c);
                            addr = fb.gep(TIRTy::I8, addr, vec![byte]);
                        }
                        _ => {
                            return Err(
                                "from_end ConstantIndex on non-array/slice".to_string()
                            )
                        }
                    }
                }
                cur_layout = elem_layout;
            }
            // A subslice view: `place[from..to]` (`from_end: false`, arrays) or
            // `place[from .. len-to]` (`from_end: true`). The ADDRESS moves by
            // `from * stride`; the resulting place is the sub-array/subslice
            // (its own fat length, when one is later needed, is derived by the
            // fat-REBORROW lowering — this walk only addresses).
            ProjectionElem::Subslice { from, to, from_end } => {
                let elem_layout = element_layout(cx, &lcx, &cur_layout)?;
                let stride = elem_layout.size.align_to(elem_layout.align.abi).bytes();
                byte_offset += from * stride;
                match cur_layout.ty.kind() {
                    ty::Array(el, _) => {
                        // The sub-ARRAY's static element count re-types the
                        // layout for any further projections.
                        let n = cur_layout
                            .ty
                            .builtin_index()
                            .map(|_| ())
                            .and_then(|()| match cur_layout.ty.kind() {
                                ty::Array(_, n) => n.try_to_target_usize(cx.tcx),
                                _ => None,
                            })
                            .ok_or("Subslice: array length not constant")?;
                        let sub_n = if *from_end {
                            n.checked_sub(from + to)
                                .ok_or("Subslice bounds exceed array length")?
                        } else {
                            to.checked_sub(*from)
                                .ok_or("Subslice: to < from")?
                        };
                        let sub_ty = Ty::new_array(cx.tcx, *el, sub_n);
                        cur_layout = cx
                            .tcx
                            .layout_of(
                                ty::TypingEnv::fully_monomorphized().as_query_input(sub_ty),
                            )
                            .map_err(|e| format!("subarray layout_of failed: {e:?}"))?;
                        fat_cell = None;
                    }
                    // A subslice of a slice stays the same (unsized) type; the
                    // ORIGINAL fat cell's length no longer describes it, so it
                    // is dropped (a later from_end element fails loud rather
                    // than reading a stale length).
                    ty::Slice(_) | ty::Str => {
                        fat_cell = None;
                    }
                    _ => return Err("Subslice of non-array/slice".to_string()),
                }
            }
            other => {
                return Err(format!("place projection {other:?} not supported (RUNG 1)"));
            }
        }
    }

    if byte_offset != 0 {
        addr = gep_byte_offset(fb, addr, byte_offset);
    }
    Ok(addr)
}

/// The (element trust-ir int type, lane count) of a rustc SIMD vector type
/// (`Simd<u8, 16>` / `uint8x8_t` — layout `BackendRepr::SimdVector`). `None`
/// for float-element vectors or non-SIMD types (fail-closed at the callers).
fn simd_int_vector_lanes<'tcx>(cx: &Cx<'tcx, '_>, ty: Ty<'tcx>) -> Option<(TIRTy, u64)> {
    let tal = cx
        .tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(ty))
        .ok()?;
    let BackendRepr::SimdVector { element, count } = tal.backend_repr else {
        return None;
    };
    let elem = match element.primitive() {
        Primitive::Int(int, signed) => match (int, signed) {
            (Integer::I8, true) => TIRTy::I8,
            (Integer::I8, false) => TIRTy::U8,
            (Integer::I16, true) => TIRTy::I16,
            (Integer::I16, false) => TIRTy::U16,
            (Integer::I32, true) => TIRTy::I32,
            (Integer::I32, false) => TIRTy::U32,
            (Integer::I64, true) => TIRTy::I64,
            (Integer::I64, false) => TIRTy::U64,
            _ => return None,
        },
        _ => return None,
    };
    Some((elem, count))
}

/// Like `simd_int_vector_lanes`, but ALSO admits FLOAT-element SIMD vectors
/// (`float32x4_t` / `float64x2_t`), returning the trust-ir float element type.
/// Used by the `simd_gt` / `simd_le` / `simd_ne` comparison lowering, which must
/// handle `vcgtq_f32` (ordered float compare) as well as the integer forms.
/// Returns `(element_ty, lane_count)`; `None` for non-SIMD or f16/f128 lanes.
fn simd_vector_lanes_any<'tcx>(cx: &Cx<'tcx, '_>, ty: Ty<'tcx>) -> Option<(TIRTy, u64)> {
    let tal = cx
        .tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(ty))
        .ok()?;
    let BackendRepr::SimdVector { element, count } = tal.backend_repr else {
        return None;
    };
    let elem = match element.primitive() {
        Primitive::Int(int, signed) => match (int, signed) {
            (Integer::I8, true) => TIRTy::I8,
            (Integer::I8, false) => TIRTy::U8,
            (Integer::I16, true) => TIRTy::I16,
            (Integer::I16, false) => TIRTy::U16,
            (Integer::I32, true) => TIRTy::I32,
            (Integer::I32, false) => TIRTy::U32,
            (Integer::I64, true) => TIRTy::I64,
            (Integer::I64, false) => TIRTy::U64,
            _ => return None,
        },
        Primitive::Float(f) => match f {
            rustc_abi::Float::F32 => TIRTy::F32,
            rustc_abi::Float::F64 => TIRTy::F64,
            rustc_abi::Float::F16 | rustc_abi::Float::F128 => return None,
        },
        _ => return None,
    };
    Some((elem, count))
}

/// Whether a pointer to `pointee` is FAT with a COUNT metadata lane (a slice /
/// str, or an unsized-tail STRUCT whose tail is a slice — `OsStr`,
/// `os_str::bytes::Slice`): the lane at cell+8 is the element count a
/// `from_end` ConstantIndex/Subslice can subtract from. A `dyn` pointee's
/// metadata is a VTABLE pointer — excluded. Sized pointees are thin.
fn pointee_metadata_is_count<'tcx>(cx: &Cx<'tcx, '_>, pointee: Ty<'tcx>) -> bool {
    match pointee.kind() {
        ty::Slice(_) | ty::Str => true,
        ty::Adt(..) | ty::Tuple(..) => {
            if pointee.is_sized(cx.tcx, ty::TypingEnv::fully_monomorphized()) {
                return false;
            }
            // Unsized struct/tuple: metadata equals the TAIL's metadata; walk it.
            let tail = cx.tcx.struct_tail_for_codegen(
                pointee,
                ty::TypingEnv::fully_monomorphized(),
            );
            matches!(tail.kind(), ty::Slice(_) | ty::Str)
        }
        _ => false,
    }
}

/// The element `TyAndLayout` of an array/slice layout.
fn element_layout<'tcx>(
    _cx: &Cx<'tcx, '_>,
    lcx: &LayoutCx<'tcx>,
    arr_layout: &rustc_middle::ty::layout::TyAndLayout<'tcx>,
) -> Result<rustc_middle::ty::layout::TyAndLayout<'tcx>, String> {
    match arr_layout.ty.kind() {
        ty::Array(_, _) | ty::Slice(_) => Ok(arr_layout.field(lcx, 0)),
        _ => Err(format!("Index of non-array type: {}", ty_family(arr_layout.ty))),
    }
}

/// A byte-offset GEP: `gep(I8, base, [offset])` computes `base + offset` bytes
/// (TrustIr GEP scales each index by `size_of(pointee_ty)`, so an `I8` pointee
/// gives a raw byte offset). Returns the new `Ptr`.
///
/// RUNG 2a (`inbounds`): this is THE funnel for every static, layout-derived
/// byte offset this lowering emits, so the `inbounds` flag and the matching
/// `ProofAnnotation::InBounds` are decided in exactly one place — inside
/// `FunctionBuilder::gep_byte_offset`, which sets them IFF it can discharge the
/// claim from a recorded `PtrExtent`. The extents come from the entry-preamble
/// allocas (`note_alloc_extent`, whose size is the same rustc
/// `memory_layout_size_align` this file uses to compute the offsets) and
/// propagate along GEP chains. A base with no recorded extent — a block
/// parameter, a loaded pointer, a call result — yields `inbounds: false`. The
/// producer never asserts the flag; the builder checks it.
fn gep_byte_offset(
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    base: trust_ir::ValueId,
    offset: u64,
) -> trust_ir::ValueId {
    fb.gep_byte_offset(base, offset)
}

/// Load the POINTER VALUE held by a pointer-typed local. For a memory-backed
/// pointer cell this Loads `Ptr` from its slot; for an SSA pointer local it reads
/// the env binding (RUNG 1 produces SSA pointers only as `&place` results bound
/// to a scalar local — which we treat as memory-backed when address-taken; a
/// plain SSA pointer arises from `Rvalue::Ref` assigned to a never-address-taken
/// scalar local, kept in env).
fn load_pointer_local<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    env: &HashMap<Local, trust_ir::ValueId>,
    local: Local,
) -> Result<trust_ir::ValueId, String> {
    if let Some(slot) = cx.slot_ptr(local) {
        Ok(fb.load(TIRTy::Ptr, slot))
    } else if let Some(v) = env.get(&local).copied() {
        Ok(v)
    } else {
        Err("pointer local read before assignment in block (needs phi)".to_string())
    }
}

// ============================ operands / rvalues =============================

/// Lower one operand to a trust-ir ValueId + its trust-ir type. Handles a bare
/// scalar SSA local, a memory-backed place (Load), and a constant.
fn lower_operand<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    env: &HashMap<Local, trust_ir::ValueId>,
    op: &Operand<'tcx>,
) -> Result<(trust_ir::ValueId, TIRTy), String> {
    match op {
        Operand::Copy(place) | Operand::Move(place) => lower_place_value(cx, fb, env, place),
        Operand::Constant(c) => lower_const_operand(cx, fb, c),
        // ADDITIVE (RUNG 9 closure graph): a compile-time `RuntimeChecks` query
        // (`UbChecks` / `ContractChecks` / `OverflowChecks`). rustc resolves this to
        // a `bool` whose value is fixed by the session flags — the SAME value rustc's
        // own codegen const-folds it to (`RuntimeChecks::value(sess)`), per
        // rustc_middle::mir::statement (its type is `tcx.types.bool`). We emit that
        // `const bool` faithfully. This appears inside the `Iterator::all` /
        // overflow-checked index-step bodies the `.iter().all(|x| ..)` closure pulls
        // in. NOT a silent default: the value is read from the active session.
        Operand::RuntimeChecks(check) => {
            let v = fb.bool_const(check.value(cx.tcx.sess));
            Ok((v, TIRTy::Bool))
        }
    }
}

/// Emit a CALL ARGUMENT classified as `ArgAbi::Scalar(expected)`. The normal case
/// (`lower_operand`) covers an SSA scalar, a scalar constant (incl. a transparent
/// int-newtype constant), and a memory scalar/ptr leaf. The ADDITIVE case: a bare
/// memory-backed local whose type is a transparent INT newtype (`Group(u64)` /
/// `Tag(u8)`) — `lower_operand`'s `place_leaf_tir_ty` rejects it (it only admits
/// ptr wrappers), so we Load the inner scalar at the slot address at `expected`,
/// the same int the callee's by-value scalar param expects.
fn lower_scalar_call_arg<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    env: &HashMap<Local, trust_ir::ValueId>,
    op: &Operand<'tcx>,
    expected: &TIRTy,
) -> Result<trust_ir::ValueId, String> {
    if let Operand::Copy(place) | Operand::Move(place) = op {
        if place.projection.is_empty() {
            if let Some(LocalModel::Memory(_)) = cx.model.get(&place.local) {
                let cty = cx.local_concrete_ty(place.local);
                // A transparent int newtype the leaf-scalar path rejects but the
                // arg classifier admitted as a scalar: Load its inner scalar.
                if memory_leaf_tir_ty(cx.tcx, cty).is_none()
                    && param_scalar_leaf_tir_ty(cx, cty).as_ref() == Some(expected)
                {
                    let addr = place_address(cx, fb, env, place)?;
                    return Ok(fb.load(expected.clone(), addr));
                }
            }
        }
    }
    let (v, _t) = lower_operand(cx, fb, env, op)?;
    Ok(v)
}

/// Read a PLACE's VALUE (RUNG 0: an SSA scalar local from env; RUNG 1: a typed
/// Load from a memory place).
fn lower_place_value<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    env: &HashMap<Local, trust_ir::ValueId>,
    place: &Place<'tcx>,
) -> Result<(trust_ir::ValueId, TIRTy), String> {
    // Bare SSA scalar local.
    if place.projection.is_empty() {
        if let Some(LocalModel::Ssa(t)) = cx.model.get(&place.local) {
            let v = env.get(&place.local).copied().ok_or_else(|| {
                "local read before assignment in block (needs phi)".to_string()
            })?;
            return Ok((v, t.clone()));
        }
    }
    // Memory place: typed Load at the place address.
    let leaf_ty = place_leaf_tir_ty(cx, place)?;
    let addr = place_address(cx, fb, env, place)?;
    let v = fb.load(leaf_ty.clone(), addr);
    Ok((v, leaf_ty))
}

/// Lower a scalar integer/bool/float constant operand.
fn lower_const_operand<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    c: &ConstOperand<'tcx>,
) -> Result<(trust_ir::ValueId, TIRTy), String> {
    let ct = cx.instance.instantiate_mir_and_normalize_erasing_regions(
        cx.tcx,
        ty::TypingEnv::fully_monomorphized(),
        ty::EarlyBinder::bind(cx.tcx, c.const_),
    );
    let cty = cx.mono(c.const_.ty());
    // A bare scalar int/bool, OR (ADDITIVE) a transparent single-scalar-field newtype
    // (`#[repr(transparent)] struct Tag(u8)`) whose layout is a `BackendRepr::Scalar`.
    // `cast_scalar_tir_ty` admits the latter to its inner trust-ir int/ptr type; the
    // const-eval'd value is a `ConstValue::Scalar` whose ScalarInt is the inner scalar
    // bits, read at its own width by `const_value_to_i128`. (Needed for the SwissTable
    // group scan's `repeat(Tag(0x01))` / `Tag::DELETED` byte constants.)
    let tir = scalar_tir_ty(cty)
        .or_else(|| cast_scalar_tir_ty(cx, cty))
        .ok_or_else(|| format!("constant of non-scalar type {}", ty_family(cty)))?;
    let cv = match ct.eval(cx.tcx, ty::TypingEnv::fully_monomorphized(), c.span) {
        Ok(cv) => cv,
        Err(_) => return Err("constant could not be const-evaluated".to_string()),
    };
    // Preserve the full unsigned 128-bit magnitude before the general i128
    // carrier truncates it. This also covers transparent scalar newtypes whose
    // layout maps to the U128 trust-ir lane.
    // NOTE: written as nested `if`s rather than a let chain — this crate is
    // `edition = "2021"` (Cargo.toml) and let chains are Rust 2024+.
    if matches!(tir, TIRTy::U128) {
        if let Some(value) = const_value_to_u128(cv) {
            let v = fb.uconst(tir.clone(), value);
            return Ok((v, tir));
        }
    }
    // A bare integer / bool / float / scalar-newtype value: the fast path.
    if let Some(val) = const_value_to_i128(cv, cty) {
        let v = if matches!(tir, TIRTy::Bool) {
            fb.bool_const(val != 0)
        } else if matches!(tir, TIRTy::F32 | TIRTy::F64) {
            // `val` holds the raw IEEE bits (see `const_value_to_i128`'s Float
            // arm). Rebuild the exact float value. An `f32` widened to the
            // `Constant::Float(f64)` payload is lossless (f32 -> f64 is exact,
            // and the text format round-trips every f64 bit-exactly).
            let fval = if matches!(tir, TIRTy::F32) {
                f32::from_bits(val as u32) as f64
            } else {
                f64::from_bits(val as u64)
            };
            fb.fconst(tir.clone(), fval)
        } else if matches!(tir, TIRTy::Ptr) {
            // A pointer-lane scalar that DID flatten to an integer: the niche
            // encoding of a pointer option (`None::<NonNull<T>>` = 0) or an
            // aligned dangling sentinel. Emitting `Const { ty: Ptr, Int(val) }`
            // here type-puns int-as-pointer — the binary path tolerates it, but
            // the reference interpreter (rightly) rejects the constant as
            // ill-typed. Emit the faithful spelling instead: `NullPtr` for
            // zero, `IntToPtr(iconst)` for a nonzero sentinel (identical to
            // `lower_ptr_const_value`'s integer-address arm).
            if val == 0 {
                fb.null_ptr()
            } else {
                let iv = fb.iconst(TIRTy::U64, val);
                fb.cast(CastOp::IntToPtr, TIRTy::U64, TIRTy::Ptr, iv)
            }
        } else {
            fb.iconst(tir.clone(), val)
        };
        return Ok((v, tir));
    }
    // A POINTER-typed constant (the trust-ir leaf is `Ptr`): either an INTEGER
    // ADDRESS cast to a pointer (`null`, or a `NonNull::dangling()`-style aligned
    // sentinel) or a REFERENCE to an interned pointer-free CONST allocation
    // (`&'static usize` / `&'static Tag`). Both const-eval to a `ConstValue::Scalar`
    // that `const_value_to_i128` cannot flatten (its type is a pointer, or the
    // scalar carries provenance). See `lower_ptr_const_value`.
    if matches!(tir, TIRTy::Ptr) {
        let v = lower_ptr_const_value(cx, fb, cv, cty)?;
        return Ok((v, TIRTy::Ptr));
    }
    // A scalar-typed constant whose value `const_value_to_i128` cannot flatten and
    // which is not a pointer: fail loud, never a silent default.
    Err(format!(
        "constant value not a single scalar [cv={cv:?} ty={:?}]",
        cty.kind()
    ))
}

/// Lower a POINTER-typed constant VALUE (the trust-ir leaf is `Ptr`) to a `Ptr`.
///
/// Two shapes appear whole-program:
///   * **Integer address** — `ConstValue::Scalar(Scalar::Int)` where the const's
///     type is a raw pointer / reference: a `null` (`0x0`) or a
///     `NonNull::dangling()`-style aligned sentinel (`0x1`, or `align_of::<T>()`).
///     Lower to `NullPtr` (zero) or `IntToPtr(iconst)` (non-zero).
///   * **Reference to an interned const allocation** — `ConstValue::Scalar(
///     Scalar::Ptr)` where the pointer targets a CTFE `Memory` allocation
///     (`&'static usize`, `&'static Tag`, a promoted constant). Materialize the
///     pointee's exact bytes into an immortal heap image and yield its address.
///
/// FAIL-CLOSED: a const reference whose target carries POINTER PROVENANCE (a live
/// nested pointer — a vtable, a thread-local accessor, a `&&T`) is NOT
/// materializable as raw bytes; it stays a loud failure, never a silent
/// miscompile.
fn lower_ptr_const_value<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    cv: ConstValue,
    cty: Ty<'tcx>,
) -> Result<trust_ir::ValueId, String> {
    match cv {
        // An integer address cast to a pointer: `null` or a dangling sentinel.
        ConstValue::Scalar(Scalar::Int(si)) => {
            let addr = si.to_uint(si.size());
            if addr == 0 {
                Ok(fb.null_ptr())
            } else {
                let iv = fb.iconst(TIRTy::U64, addr as i128);
                Ok(fb.cast(CastOp::IntToPtr, TIRTy::U64, TIRTy::Ptr, iv))
            }
        }
        // A reference to an interned const allocation.
        ConstValue::Scalar(Scalar::Ptr(ptr, _)) => materialize_const_ref(cx, fb, ptr, cty),
        _ => Err(format!("pointer constant is not a scalar [cv={cv:?}]")),
    }
}

/// Materialize a `&'static`/`*const`/`*mut` CONSTANT REFERENCE (a pointer into an
/// interned CTFE allocation) into an immortal heap image of the pointee's bytes,
/// returning the image address as a `Ptr`. The pointee must be sized, non-ZST, and
/// POINTER-PROVENANCE-FREE in the referenced range (else fail loud — a live nested
/// pointer cannot be frozen to runtime bytes). An immortal heap image is the
/// faithful `&'static` model (the target outlives the frame). MODELING BOUNDARY:
/// each lowered use materializes its own image, so cross-use ADDRESS IDENTITY of a
/// promoted constant is not preserved — sound for value reads (Rust does not
/// guarantee promoted-constant address identity), the same boundary the str-literal
/// path documents.
fn materialize_const_ref<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    ptr: rustc_middle::mir::interpret::Pointer,
    cty: Ty<'tcx>,
) -> Result<trust_ir::ValueId, String> {
    let pointee = match cty.kind() {
        ty::Ref(_, p, _) | ty::RawPtr(p, _) => Some(*p),
        // ADDITIVE (THREADS): a NON-reference const whose whole layout is ONE
        // POINTER scalar — a pointer-carrying newtype/enum like `io::Error`
        // (its `repr` is a TAGGED `NonNull`; the const `NUL_ERR` is
        // `Scalar::Ptr(alloc_of_SimpleMessage, tag_offset)`). The const VALUE
        // is exactly that (possibly tag-offset) address; there is no typed
        // pointee to size-check — the target allocation is interned wholesale
        // below and the relative offset (which INCLUDES any tag addend) is
        // reapplied byte-exactly. Any non-pointer-scalar type stays a loud
        // failure.
        _ => {
            let is_ptr_scalar = cx
                .tcx
                .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(cty))
                .ok()
                .is_some_and(|l| match l.backend_repr {
                    BackendRepr::Scalar(s) => matches!(s.primitive(), Primitive::Pointer(_)),
                    _ => false,
                });
            if !is_ptr_scalar {
                return Err(format!(
                    "const ref is not a reference type: {}",
                    ty_family(cty)
                ));
            }
            None
        }
    };
    // Keep the historical sized-pointee guard for true references (a fat-pointee
    // `&str` const never reaches here — its leaf is 2 lanes, not `Ptr`).
    //
    // A `&ZST` const (THREADS: getenv's PROMOTED `&|k| ...` captureless-closure
    // ref, unsize-coerced to `&dyn Fn`) has NO bytes to intern; its value is a
    // DANGLING WELL-ALIGNED non-null pointer (rustc's own ZST-ref model) that
    // no consumer ever dereferences (the pointee has no bytes; the dyn call
    // passes it opaquely as the env pointer). Materialize `align` as the
    // address, exactly `NonNull::<T>::dangling()`.
    let size = match pointee {
        Some(p) => {
            let layout = cx
                .tcx
                .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(p))
                .map_err(|e| format!("const-ref pointee layout_of failed: {e:?}"))?;
            if !layout.is_sized() {
                return Err(format!(
                    "const-ref pointee is unsized: {}",
                    ty_family(p)
                ));
            }
            if layout.size.bytes() == 0 {
                let addr = layout.align.abi.bytes().max(1);
                let iv = fb.iconst(TIRTy::U64, addr as i128);
                return Ok(fb.cast(CastOp::IntToPtr, TIRTy::U64, TIRTy::Ptr, iv));
            }
            layout.size.bytes()
        }
        None => 0,
    };
    let (prov, offset) = ptr.prov_and_relative_offset();
    let alloc_id = prov.alloc_id();
    let alloc = match cx.tcx.global_alloc(alloc_id) {
        GlobalAlloc::Memory(a) => a,
        // A const-ref whose target is NOT a data allocation but a SYMBOL: a
        // `&STATIC`, a reference to a fn ITEM, or a vtable. The reference's VALUE is
        // the ADDRESS of that symbol — materialize a `SymbolAddr` (thin `Ptr`)
        // relocation to it, plus any relative byte offset (`&STATIC.field`). These
        // appear in Arc/Weak `Drop`: a reference to the `Global` allocator ZST
        // static, and a `Layout`/`Location` panic static. The linker resolves the
        // relocation the same way it resolves a `ReifyFnPointer` fn-pointer symbol.
        GlobalAlloc::Static(def_id) => {
            // LANE S: record the reference so the driver's whole-program
            // `statics` module DEFINES this symbol with its real CTFE bytes
            // (the `SymbolAddr` here stays a plain extern reference).
            record_referenced_static(def_id);
            let name = cx.tcx.symbol_name(Instance::mono(cx.tcx, def_id)).name.to_string();
            let base = fb.const_value(TIRTy::Ptr, Constant::symbol_addr(name));
            let off = offset.bytes();
            return Ok(if off == 0 { base } else { gep_byte_offset(fb, base, off) });
        }
        GlobalAlloc::Function { instance } => {
            let name = cx.tcx.symbol_name(instance).name.to_string();
            let base = fb.const_value(TIRTy::Ptr, Constant::symbol_addr(name));
            let off = offset.bytes();
            return Ok(if off == 0 { base } else { gep_byte_offset(fb, base, off) });
        }
        // A `TypeId` provenance pointer VALUE: rustc codegen drops the
        // provenance — the runtime value IS the offset bytes (a type-id hash
        // half) reinterpreted as a pointer.
        GlobalAlloc::TypeId { .. } => {
            let iv = fb.iconst(TIRTy::U64, offset.bytes() as i128);
            return Ok(fb.cast(CastOp::IntToPtr, TIRTy::U64, TIRTy::Ptr, iv));
        }
        // A const-ref to a symbolic VTable is not addressable here: vtable globals are
        // materialized ONLY in the pre-`fb` dyn-coercion pass (`materialize_dyn_vtables`,
        // keyed by `(self_ty, dyn_ty)`), which does not scan const-refs, so a fresh one
        // cannot be interned mid-lowering. No non-dyn program (Arc<i64> included) takes a
        // const-ref to a vtable; fail loud rather than silently miscompile.
        other @ GlobalAlloc::VTable(..) => {
            return Err(format!(
                "const ref target is not a resolvable allocation ({other:?})"
            ))
        }
    };
    let inner = alloc.inner();
    let range = alloc_range(offset, Size::from_bytes(size));
    if !inner.provenance().range_empty(range, &cx.tcx) {
        // The pointee carries live provenance (a promoted `LocalKey` holding a
        // thread-local accessor, a `&STATIC` chain) — its bytes cannot be frozen to
        // an immortal heap image. But the VALUE is a reference: the ADDRESS of the
        // referenced static. Materialize the static as a module global and yield its
        // address (`&promoted[0]` -> `GlobalAddr(gid) + offset`). Fail-closed if the
        // target is not a resolvable memory allocation.
        let gid = intern_alloc_global(cx, alloc_id)?;
        let base = fb.global_addr(gid);
        let off = offset.bytes();
        return Ok(if off == 0 {
            base
        } else {
            gep_byte_offset(fb, base, off)
        });
    }
    // Provenance-FREE pointee (frozen bytes, no live inner pointers): intern the whole
    // allocation as a READ-ONLY module global (rodata) and yield its address + offset —
    // the faithful `&'static` model (immutable static data, 'static lifetime) with NO
    // runtime allocation, exactly as the provenance-BEARING branch above already does.
    //
    // The old path `heap_alloc`'d an immortal image PER LOWERED USE and never freed it,
    // so a `&'static` const referenced on a HOT path LEAKED on every call — e.g. every
    // `bucket` / `fix_insert_index` / `capacity_to_buckets` reference to hashbrown's
    // static EMPTY control group allocated 8 bytes it never reclaimed (a HashMap
    // insert/get workload leaked hundreds of blocks). A rodata global is one stable
    // address for the program's life and zero allocations — leak-free, and object/link
    // data relocations resolve it (the same rodata lowering the str-literal path uses).
    let gid = intern_alloc_global(cx, alloc_id)?;
    let base = fb.global_addr(gid);
    let off = offset.bytes();
    Ok(if off == 0 {
        base
    } else {
        gep_byte_offset(fb, base, off)
    })
}

/// Extract a single scalar i128 from a const-eval'd ConstValue.
fn const_value_to_i128(cv: ConstValue, ty: Ty<'_>) -> Option<i128> {
    let scalar = match cv {
        ConstValue::Scalar(s) => s,
        _ => return None,
    };
    let si: ScalarInt = scalar.try_to_scalar_int().ok()?;
    match ty.kind() {
        ty::Int(_) => Some(si.to_int(si.size())),
        ty::Uint(_) | ty::Bool => Some(si.to_uint(si.size()) as i128),
        // ADDITIVE: a transparent single-scalar-field newtype over an unsigned int
        // (`#[repr(transparent)] struct Tag(u8)`). The const-eval'd `ConstValue::
        // Scalar` carries the inner scalar's bits at its own width; read them
        // unsigned (the inner field of these control-byte tags is a `u8`). Only an
        // ADT with a scalar layout reaches here (the caller guards with
        // `cast_scalar_tir_ty`), so this is the newtype-wrapped scalar value.
        ty::Adt(_, _) => Some(si.to_uint(si.size()) as i128),
        // A `char` literal: a 4-byte unsigned code point (layout primitive
        // Int(I32, unsigned) — `cast_scalar_tir_ty` already classifies every
        // char PLACE as `U32`; this admits the CONSTANT the same way).
        ty::Char => Some(si.to_uint(si.size()) as i128),
        // A FLOAT constant: the ScalarInt carries the raw IEEE bits at the float's
        // width. Return the bits unsigned; the caller (`lower_const_operand`)
        // rebuilds the exact `f32`/`f64` value from them (`from_bits`) — never an
        // integer reinterpretation.
        ty::Float(_) => Some(si.to_uint(si.size()) as i128),
        _ => None,
    }
}

/// Extract the complete unsigned bit-pattern of a scalar constant.
///
/// This is deliberately separate from `const_value_to_i128`: casting the
/// upper half of a U128 scalar through that carrier would turn `u128::MAX`
/// into `-1` and violate TrustIR's canonical integer spelling.
fn const_value_to_u128(cv: ConstValue) -> Option<u128> {
    let scalar = match cv {
        ConstValue::Scalar(s) => s,
        _ => return None,
    };
    let si: ScalarInt = scalar.try_to_scalar_int().ok()?;
    Some(si.to_uint(si.size()))
}

// ============ ADDITIVE (R1): CONSTANT AGGREGATE materialization ==============
//
// A CONSTANT AGGREGATE value passed BY VALUE (an enum / struct / tuple / array
// constant used as a call arg or held in a place leaf) — e.g.
// `Option::<Arguments>::None` on a nounwind-panic arg, or a monomorphized
// `Layout` / `TableLayout` allocator arg. The scalar-only const path
// (`lower_const_operand`) rejects these ("constant of non-scalar type ..."), so
// until now they failed loud. We materialize the constant's EXACT byte image into
// a fresh stack slot (an `Alloca` written lane-by-lane, byte-congruent with the
// `copy_aggregate_bytes` place-copy discipline) and pass the slot BY REF.
//
// FAIL-CLOSED: `const_agg_bytes` refuses any constant that carries POINTER
// PROVENANCE — a live pointer whose compile-time address is meaningless at
// runtime must never be frozen into raw integer bytes. Such a constant stays a
// loud failure, never a silent miscompile. (The two whole-program shapes this
// unblocks are pointer-free: `Layout`/`TableLayout` are pure integers; the enum
// `None` niche is a scalar/zero value with no live pointer.)

/// Read the raw byte IMAGE (`size_of` bytes of the memory representation) of a
/// CONSTANT AGGREGATE value, for materialization into a stack slot. Returns Err
/// (fail loud) when the constant is not a pointer-free in-memory / scalar-repr
/// aggregate — in particular when it carries POINTER PROVENANCE, since a
/// compile-time pointer address cannot be materialized as runtime bytes.
fn const_agg_bytes<'tcx>(cx: &Cx<'tcx, '_>, c: &ConstOperand<'tcx>) -> Result<Vec<u8>, String> {
    let cty = cx.mono(c.const_.ty());
    // Only a genuine BY-VALUE aggregate is handled here: a bare scalar / thin-ptr
    // is the scalar-const path's job, and a fat-pointer (str/slice) constant is
    // the str-literal path's job. Reject those so this helper's classification
    // predicate (`is_ok()`) does not shadow either.
    if scalar_tir_ty(cty).is_some()
        || memory_leaf_tir_ty(cx.tcx, cty).is_some()
        || is_fat_pointer(cx.tcx, cty)
        || is_str_or_byteslice_ref(cty)
    {
        return Err("const_agg_bytes: not a by-value aggregate constant".to_string());
    }
    let (size, _align) = memory_layout_size_align(cx, cty)?;
    let ct = cx.instance.instantiate_mir_and_normalize_erasing_regions(
        cx.tcx,
        ty::TypingEnv::fully_monomorphized(),
        ty::EarlyBinder::bind(cx.tcx, c.const_),
    );
    let cv = ct
        .eval(cx.tcx, ty::TypingEnv::fully_monomorphized(), c.span)
        .map_err(|_| "const aggregate could not be const-evaluated".to_string())?;
    match cv {
        // A scalar-repr aggregate (a niche-optimized enum whose whole value is one
        // scalar, e.g. `Option<&T>::None`): its memory image is that scalar's
        // bytes, little-endian, at the type's size.
        ConstValue::Scalar(Scalar::Int(si)) => {
            let bits = si.to_uint(si.size());
            let mut bytes = bits.to_le_bytes().to_vec();
            if size as usize > bytes.len() {
                return Err(format!(
                    "const aggregate size {size} exceeds scalar image {}",
                    bytes.len()
                ));
            }
            bytes.truncate(size as usize);
            Ok(bytes)
        }
        // A scalar-repr aggregate whose scalar is a POINTER (live provenance): its
        // runtime address is not a compile-time constant — fail loud.
        ConstValue::Scalar(Scalar::Ptr(..)) => {
            Err("const aggregate is a live pointer (provenance) — not materializable".to_string())
        }
        // An in-memory aggregate: read its exact bytes from the const allocation,
        // refusing any live pointer provenance in the range.
        ConstValue::Indirect { alloc_id, offset } => {
            let alloc = match cx.tcx.global_alloc(alloc_id) {
                GlobalAlloc::Memory(a) => a,
                _ => return Err("const aggregate alloc is not memory".to_string()),
            };
            let inner = alloc.inner();
            let range = alloc_range(offset, Size::from_bytes(size));
            if !inner.provenance().range_empty(range, &cx.tcx) {
                // A live nested pointer cannot be flattened to raw bytes here — the
                // relocation-aware `store_const_agg_at` handles this by-value aggregate
                // (storing a `GlobalAddr` at each pointer field). `const_agg_bytes`
                // stays the pointer-FREE byte-image path (and classifier).
                return Err(
                    "const aggregate carries pointer provenance — not materializable".to_string(),
                );
            }
            let start = offset.bytes() as usize;
            let end = start + size as usize;
            Ok(inner
                .inspect_with_uninit_and_ptr_outside_interpreter(start..end)
                .to_vec())
        }
        // A slice/str fat-pointer constant is the str-literal path's job; a ZST
        // const has no bytes and is classified `Zst` upstream (never reaches here).
        ConstValue::Slice { .. } => {
            Err("const aggregate is a slice fat pointer — handled by the str path".to_string())
        }
        ConstValue::ZeroSized => {
            Err("const aggregate is zero-sized — classified Zst upstream".to_string())
        }
    }
}

/// Materialize a CONSTANT AGGREGATE into a fresh stack slot and return its address
/// (a `Ptr`) for a by-ref (`AggByRef`) call arg. The slot is an `Alloca` of the
/// aggregate's `(size, align)`; the constant's byte image is written as
/// natural-aligned integer lanes (the exact width/discipline `copy_aggregate_bytes`
/// uses to copy a by-value aggregate place), so the slot is byte- and
/// alignment-accurate and any lane-typed reader agrees. Fails loud on a
/// non-materializable constant (see `const_agg_bytes`).
fn materialize_const_aggregate<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    c: &ConstOperand<'tcx>,
) -> Result<trust_ir::ValueId, String> {
    let cty = cx.mono(c.const_.ty());
    let (size, align) = memory_layout_size_align(cx, cty)?;
    let slot_ty = slot_lane_ty(size, align)?;
    let slot = fb.alloca_aligned(slot_ty, align);
    fb.note_alloc_extent(slot, size);
    // Resolves pointer provenance (a relocation -> `GlobalAddr`) as well as the
    // pointer-free byte image, so a provenance-bearing by-ref aggregate call arg
    // materializes correctly.
    store_const_agg_at(cx, fb, slot, cty, c)?;
    Ok(slot)
}

/// Store a raw aggregate byte IMAGE into memory at `addr`, as natural-aligned
/// integer lanes derived from `cty`'s `(size, align)` layout. This is the lane-
/// writing core shared by `materialize_const_aggregate` (a fresh `Alloca` slot,
/// by-ref call arg) and the RUNG R3 whole-aggregate CONSTANT assign (an existing
/// destination place). Byte-exact: each `align`-wide lane is assembled little-
/// endian and reinterpreted at the signed lane width, so the emitted `Const`
/// passes the validator's range check while storing the identical bits. Fails loud
/// if the byte image length disagrees with the layout size.
fn store_agg_bytes_at<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    addr: trust_ir::ValueId,
    cty: Ty<'tcx>,
    bytes: Vec<u8>,
) -> Result<(), String> {
    let (size, align) = memory_layout_size_align(cx, cty)?;
    if bytes.len() as u64 != size {
        return Err(format!(
            "const aggregate byte image {} != layout size {size}",
            bytes.len()
        ));
    }
    if size % align != 0 {
        return Err(format!(
            "const aggregate size {size} not a multiple of align {align}"
        ));
    }
    let lane_ty = lane_ty_for_align(align)?;
    let lanes = size / align;
    for i in 0..lanes {
        let off = i * align;
        // Assemble the lane's `align` bytes little-endian, then reinterpret at the
        // signed lane width so the `Const` passes the validator's range check while
        // storing the exact same bits (two's complement == the raw byte image).
        let mut v: u128 = 0;
        for b in 0..align {
            v |= (bytes[(off + b) as usize] as u128) << (b * 8);
        }
        let signed: i128 = match align {
            1 => v as u8 as i8 as i128,
            2 => v as u16 as i16 as i128,
            4 => v as u32 as i32 as i128,
            8 => v as u64 as i64 as i128,
            16 => v as i128,
            _ => return Err(format!("const aggregate lane width {align} unsupported")),
        };
        let cst = fb.iconst(lane_ty.clone(), signed);
        let a = if off == 0 { addr } else { gep_byte_offset(fb, addr, off) };
        fb.store(lane_ty.clone(), a, cst);
    }
    Ok(())
}

/// Materialize a BY-VALUE aggregate CONSTANT into memory at `addr`, INCLUDING any
/// pointer PROVENANCE (relocations) it carries. A drop-in for `const_agg_bytes` +
/// `store_agg_bytes_at` that additionally resolves each relocation: the raw byte
/// image is stored first (its pointer fields hold the target-relative offset), then
/// every relocation field is overwritten with `GlobalAddr(interned static) +
/// addend`. This lowers e.g. `hashbrown::raw::RawTableInner::NEW` — a `RawTableInner`
/// whose `ctrl` field points at the interned EMPTY-GROUP static (`Group::static_empty`).
/// Pointer-FREE constants take the same path with zero relocations (identical output
/// to `store_agg_bytes_at`). Fail-closed: a relocation whose target is not a
/// resolvable memory allocation stays a loud failure (via `intern_alloc_global`).
fn store_const_agg_at<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    addr: trust_ir::ValueId,
    cty: Ty<'tcx>,
    c: &ConstOperand<'tcx>,
) -> Result<(), String> {
    // The pointer-free fast path (a scalar-repr niche aggregate, or an Indirect with
    // no provenance in range) reuses the existing byte-image writer verbatim.
    if let Ok(bytes) = const_agg_bytes(cx, c) {
        return store_agg_bytes_at(cx, fb, addr, cty, bytes);
    }
    // Otherwise a by-value aggregate carrying provenance: read its raw image + the
    // relocation table from the CTFE allocation.
    let (size, _align) = memory_layout_size_align(cx, cty)?;
    let ct = cx.instance.instantiate_mir_and_normalize_erasing_regions(
        cx.tcx,
        ty::TypingEnv::fully_monomorphized(),
        ty::EarlyBinder::bind(cx.tcx, c.const_),
    );
    let cv = ct
        .eval(cx.tcx, ty::TypingEnv::fully_monomorphized(), c.span)
        .map_err(|_| "const aggregate could not be const-evaluated".to_string())?;
    // THREADS: a FAT-POINTER constant VALUE (`ConstValue::Slice`) — the
    // `&'static CStr` `c"main"` fallback in `Thread::cname`/`Thread::name`,
    // or a `&'static str` stored through an enum-payload field. Its 2-lane
    // image is (address of the interned allocation, metadata): store both.
    if let ConstValue::Slice { alloc_id, meta } = cv {
        if size != 16 {
            return Err(format!(
                "const Slice value into a non-fat ({size}-byte) destination"
            ));
        }
        let gid = intern_alloc_global(cx, alloc_id)?;
        let data = fb.global_addr(gid);
        fb.store(TIRTy::Ptr, addr, data);
        let meta_addr = gep_byte_offset(fb, addr, 8);
        let m = fb.iconst(TIRTy::U64, meta as i128);
        fb.store(TIRTy::U64, meta_addr, m);
        return Ok(());
    }
    let ConstValue::Indirect { alloc_id, offset } = cv else {
        return Err(format!(
            "const aggregate with provenance is not an in-memory value [cv={cv:?}]"
        ));
    };
    let alloc = match cx.tcx.global_alloc(alloc_id) {
        GlobalAlloc::Memory(a) => a,
        _ => return Err("const aggregate alloc is not memory".to_string()),
    };
    let inner = alloc.inner();
    let start = offset.bytes() as usize;
    let end = start + size as usize;
    // 1. Store the raw byte image (relocation slots hold the target-relative offset,
    //    little-endian — the addend we recover and re-apply as a GEP below).
    let raw = inner
        .inspect_with_uninit_and_ptr_outside_interpreter(start..end)
        .to_vec();
    store_agg_bytes_at(cx, fb, addr, cty, raw.clone())?;
    // 2. Overwrite each relocation field with the interned static's address.
    let ptr_size = cx.tcx.data_layout.pointer_size().bytes();
    for (reloc_off, prov) in inner.provenance().ptrs().iter() {
        let abs = reloc_off.bytes();
        // Only relocations WITHIN the projected [offset, offset+size) range apply.
        if abs < offset.bytes() || abs + ptr_size > offset.bytes() + size {
            continue;
        }
        let rel = abs - offset.bytes();
        // The addend (offset into the target allocation) is the raw pointer image.
        let mut addend: u64 = 0;
        for b in 0..ptr_size {
            addend |= (raw[(rel + b) as usize] as u64) << (b * 8);
        }
        // A `TypeId` provenance target: rustc codegen DROPS the provenance —
        // "the offset contains the bytes of the hash" — so the raw byte image
        // already stored above IS the runtime value. Nothing to overwrite.
        if matches!(
            cx.tcx.global_alloc(prov.alloc_id()),
            GlobalAlloc::TypeId { .. }
        ) {
            continue;
        }
        let gid = intern_alloc_global(cx, prov.alloc_id())?;
        let base = fb.global_addr(gid);
        let ptr = if addend == 0 {
            base
        } else {
            gep_byte_offset(fb, base, addend)
        };
        let field_addr = if rel == 0 { addr } else { gep_byte_offset(fb, addr, rel) };
        fb.store(TIRTy::Ptr, field_addr, ptr);
    }
    Ok(())
}

// ============================ RUNG 4: Rvalue::Cast ============================
//
// A self-contained port of trust-cg's `lower_cast` / `rust_cast_to_trust_ir_cast`,
// restricted to the scalar/pointer reinterprets this minimal model needs (the
// Box-deref recursion `sz`/whnf walk, debug align/null asserts, fn-ptr coercions).
// We NEVER emit `CastOp::Transmute` (the validator fails it closed); a transmute is
// mapped to the concrete op the validator admits — PtrToPtr / PtrToInt / IntToPtr /
// Bitcast — or to identity when the trust-ir src/dst types coincide.

/// The trust-ir SCALAR type a cast source/destination of rustc type `ty` carries,
/// via `layout_of(...).backend_repr`. Unlike `memory_leaf_tir_ty`, this also admits
/// a single-pointer-width transparent wrapper (`NonNull<T>`, `Unique<T>`) as `Ptr`
/// — the `BackendRepr::Scalar(Primitive::Pointer)` case the Box-deref `Transmute`
/// reads. Returns None for an aggregate / fat pointer / f16/f128 / non-scalar layout.
fn cast_scalar_tir_ty<'tcx>(cx: &Cx<'tcx, '_>, ty: Ty<'tcx>) -> Option<TIRTy> {
    // A plain scalar int/bool/thin-ptr first (no layout query needed).
    if let Some(t) = memory_leaf_tir_ty(cx.tcx, ty) {
        return Some(t);
    }
    // Otherwise consult the layout: a `BackendRepr::Scalar` leaf whose primitive is
    // a pointer, integer, or f32/f64 float maps to the matching trust-ir scalar
    // (covers NonNull / Unique / a single-scalar newtype). A pair / aggregate /
    // f16/f128 is not a cast scalar here.
    let tal = cx
        .tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(ty))
        .ok()?;
    let BackendRepr::Scalar(scalar) = tal.backend_repr else {
        return None;
    };
    match scalar.primitive() {
        Primitive::Pointer(_) => Some(TIRTy::Ptr),
        Primitive::Int(int, signed) => Some(match (int, signed) {
            (rustc_abi::Integer::I8, true) => TIRTy::I8,
            (rustc_abi::Integer::I8, false) => TIRTy::U8,
            (rustc_abi::Integer::I16, true) => TIRTy::I16,
            (rustc_abi::Integer::I16, false) => TIRTy::U16,
            (rustc_abi::Integer::I32, true) => TIRTy::I32,
            (rustc_abi::Integer::I32, false) => TIRTy::U32,
            (rustc_abi::Integer::I64, true) => TIRTy::I64,
            (rustc_abi::Integer::I64, false) => TIRTy::U64,
            (rustc_abi::Integer::I128, true) => TIRTy::I128,
            (rustc_abi::Integer::I128, false) => TIRTy::U128,
        }),
        // f32/f64 are first-class trust-ir scalars (see `scalar_tir_ty`); f16/f128
        // stay fail-closed until the backend lowers them.
        Primitive::Float(f) => match f {
            rustc_abi::Float::F32 => Some(TIRTy::F32),
            rustc_abi::Float::F64 => Some(TIRTy::F64),
            rustc_abi::Float::F16 | rustc_abi::Float::F128 => None,
        },
    }
}

/// Whether a trust-ir scalar type is a (thin) pointer in this minimal model.
fn is_ptr_tir(t: &TIRTy) -> bool {
    matches!(t, TIRTy::Ptr)
}

/// Read a cast OPERAND's value at its cast-scalar trust-ir type `src_tir`. A bare
/// SSA scalar comes from env; everything else (a memory leaf, a transparent-wrapper
/// pointer field, a projected place) is a typed Load at the place address; a
/// constant is materialized. Unlike `lower_operand`, this can Load a place whose
/// leaf is a pointer-layout wrapper (`NonNull<T>`) as a `Ptr`.
fn lower_cast_operand<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    env: &HashMap<Local, trust_ir::ValueId>,
    op: &Operand<'tcx>,
    src_tir: &TIRTy,
) -> Result<trust_ir::ValueId, String> {
    match op {
        Operand::Copy(place) | Operand::Move(place) => {
            if place.projection.is_empty() {
                if let Some(LocalModel::Ssa(_)) = cx.model.get(&place.local) {
                    return env.get(&place.local).copied().ok_or_else(|| {
                        "cast operand read before assignment in block (needs phi)".to_string()
                    });
                }
            }
            // A memory place: Load at the cast-scalar type (works for a pointer-
            // layout wrapper field the leaf-scalar path rejects).
            //
            // Load at the SOURCE PLACE's actual alignment, not the cast type's
            // natural alignment: a `Transmute<[u8; 8], u64>` (the body of
            // `u64::from_le_bytes`) reads a `u64` out of an align-1 byte array,
            // so a natural-align-8 `Load` asserts an alignment that does not
            // hold. aarch64 tolerates the unaligned access (masking the gap in
            // the binary), but the reference interpreter and any strict-
            // alignment consumer rightly reject `addr % 8 != 0`. The place's
            // layout alignment is the guarantee that actually holds (= 1 here),
            // and for a same-aligned scalar cast it equals the natural
            // alignment, so this is a no-op there.
            let addr = place_address(cx, fb, env, place)?;
            let place_ty = place.ty(&cx.body.local_decls, cx.tcx).ty;
            match memory_layout_size_align(cx, place_ty) {
                Ok((_size, place_align)) => Ok(fb.load_aligned(src_tir.clone(), addr, place_align)),
                // Layout not computable (rare) — fall back to the historical
                // natural-alignment load rather than fail the cast.
                Err(_) => Ok(fb.load(src_tir.clone(), addr)),
            }
        }
        Operand::Constant(_) => {
            let (v, _t) = lower_const_operand(cx, fb, match op {
                Operand::Constant(c) => c,
                _ => unreachable!(),
            })?;
            Ok(v)
        }
        Operand::RuntimeChecks(_) => Err("cast operand: RuntimeChecks".to_string()),
    }
}

/// RUNG 4: lower `dst = PtrMetadata(op)` where `op` is a FAT pointer modeled as a
/// 2-lane slot. The metadata (slice/str length `usize`, or dyn vtable `*const ()`)
/// is lane 1, at slot byte offset 8. We compute the operand place's base address
/// and load the metadata at +8 with the destination's scalar width. Bails loud for
/// a non-place operand or a non-fat pointer (whose metadata is the zero-sized unit).
fn lower_ptr_metadata<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    env: &HashMap<Local, trust_ir::ValueId>,
    op: &Operand<'tcx>,
    dst_ty: &TIRTy,
) -> Result<trust_ir::ValueId, String> {
    let (Operand::Copy(place) | Operand::Move(place)) = op else {
        return Err("PtrMetadata of a non-place operand".to_string());
    };
    let pty = cx.place_concrete_ty(place);
    if !is_fat_pointer(cx.tcx, pty) {
        return Err(format!(
            "PtrMetadata of non-fat pointer {} (thin-ptr metadata is unit)",
            ty_family(pty)
        ));
    }
    // The fat pointer's slot base address, then +8 to the metadata lane. The
    // destination scalar type (`usize` for a slice/str length, `Ptr` for a vtable)
    // sizes the load.
    let base = place_address(cx, fb, env, place)?;
    let meta_addr = gep_byte_offset(fb, base, 8);
    Ok(fb.load(dst_ty.clone(), meta_addr))
}

/// Lower `dst = op as DstTy (CastKind)` producing a value of `dst_ty`. Maps the MIR
/// cast kind to the concrete trust-ir cast the validator admits, or to identity
/// (the source value) when src/dst trust-ir types coincide.
fn lower_cast<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    env: &HashMap<Local, trust_ir::ValueId>,
    kind: &CastKind,
    op: &Operand<'tcx>,
    dst_ty: &TIRTy,
) -> Result<trust_ir::ValueId, String> {
    let src_rust = operand_concrete_ty(cx, op);
    // A `closure |..| .. as fn(..)` coercion (`PointerCoercion(ClosureFnPointer)`):
    // a NON-CAPTURING (ZST) closure becomes a fn pointer whose value is the ADDRESS
    // of the closure's FnOnce shim — exactly what rustc codegen emits
    // (`get_fn_addr(resolve_closure(.., FnOnce))`). The source closure carries no
    // runtime data (nothing to load); the result is a `Ptr`-typed `SymbolAddr`
    // relocation to that shim symbol. Handled BEFORE the scalar-leaf classification
    // below — a closure is not a scalar leaf, so the generic path would fail loud.
    // (`reserve_rehash` passes its `make_hasher` non-capturing closure to
    // `reserve_rehash_inner` this way, alongside the `&mut dyn` hasher.)
    if let CastKind::PointerCoercion(
        rustc_middle::ty::adjustment::PointerCoercion::ClosureFnPointer(_),
        _,
    ) = kind
    {
        let ty::Closure(def_id, args) = src_rust.kind() else {
            return Err(format!(
                "ClosureFnPointer coercion of non-closure source {}",
                ty_family(src_rust)
            ));
        };
        if *dst_ty != TIRTy::Ptr {
            return Err(format!(
                "ClosureFnPointer destination is not a thin fn pointer: {dst_ty:?}"
            ));
        }
        let instance = Instance::resolve_closure(cx.tcx, *def_id, args, ty::ClosureKind::FnOnce);
        let name = cx.tcx.symbol_name(instance).name.to_string();
        return Ok(fb.const_value(TIRTy::Ptr, Constant::symbol_addr(name)));
    }
    // A `fn_item as fn(..)` coercion (`PointerCoercion(ReifyFnPointer)`): a zero-sized
    // fn ITEM (`FnDef`) becomes a fn pointer whose value is the ADDRESS of that
    // function — exactly what rustc codegen emits (`get_fn_addr(instance)`). The source
    // `FnDef` carries no runtime data (it IS the function's identity), so the result is
    // a `Ptr`-typed `SymbolAddr` relocation to that function's symbol — which, after the
    // emit-each symbol-name fix, is the same v0-mangled name the callee module DEFINES.
    // Handled BEFORE the scalar-leaf classification below — a `FnDef` is not a scalar
    // leaf, so the generic path would fail loud (`source not a scalar leaf: fndef`).
    if let CastKind::PointerCoercion(
        rustc_middle::ty::adjustment::PointerCoercion::ReifyFnPointer(_),
        _,
    ) = kind
    {
        if *dst_ty != TIRTy::Ptr {
            return Err(format!(
                "ReifyFnPointer destination is not a thin fn pointer: {dst_ty:?}"
            ));
        }
        let instance = resolve_call_callee(cx, op).ok_or_else(|| {
            format!(
                "ReifyFnPointer source does not resolve to a fn item: {}",
                ty_family(src_rust)
            )
        })?;
        let name = cx.tcx.symbol_name(instance).name.to_string();
        return Ok(fb.const_value(TIRTy::Ptr, Constant::symbol_addr(name)));
    }
    let src_tir = match cast_scalar_tir_ty(cx, src_rust) {
        Some(t) => t,
        // A FAT-pointer cast SOURCE (`*const [T]`/`*const str`/`*mut [u8]`/`&dyn`):
        // its 2-lane slot has no single-scalar leaf, but the pointer casts MIR
        // actually emits on it (`*[T] as *U` / `*[T] as usize` — PtrToPtr /
        // PtrToInt / Transmute) operate on the DATA pointer (lane 0) and DROP the
        // metadata. Treat the source as a thin `Ptr`: `lower_cast_operand` at
        // `Ptr` Loads offset 0 of the slot = the data pointer, exactly the value
        // these casts preserve. (A fat DESTINATION never reaches here — a fat dst
        // routes to `lower_fat_pointer_assign` before `lower_cast`.)
        None if is_fat_pointer(cx.tcx, src_rust) => TIRTy::Ptr,
        // A `Transmute` whose SOURCE is an aggregate WRAPPER over exactly the
        // destination's bytes — the 1.99 `ptr::read_unaligned` carrier
        // (`transmute_neo::<Packed<T>, T>`, hot in the personality's DWARF
        // readers), a newtype over one scalar, etc. Transmute REQUIRES equal
        // sizes, so read the source PLACE directly at the destination scalar
        // type: `lower_cast_operand` Loads the operand's memory slot at that
        // type — byte-faithful reinterpret semantics, no lane classification
        // needed. (A source that is itself a scalar leaf never reaches this
        // arm; a non-place / size-mismatched source still fails loud.)
        None if matches!(kind, CastKind::Transmute) => {
            let layout = cx
                .tcx
                .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(src_rust))
                .map_err(|e| format!("Transmute source layout_of failed: {e:?}"))?;
            let dst_size = match dst_ty {
                TIRTy::Ptr => 8,
                t => int_lane_size(t),
            };
            if dst_size == 0 || layout.size.bytes() != dst_size {
                return Err(format!(
                    "Transmute aggregate source size {} != scalar destination {dst_ty:?}",
                    layout.size.bytes()
                ));
            }
            // A place OR an aggregate CONSTANT (a `TypeId` const transmuted to
            // `u128` in `<dyn Any>::is` / `payload_as_str` — materialized to a
            // slot and Loaded in the Transmute arm below).
            dst_ty.clone()
        }
        None => {
            return Err(format!(
                "Rvalue::Cast source not a scalar leaf: {}",
                ty_family(src_rust)
            ))
        }
    };

    match kind {
        // Integer<->integer width change: sext (signed src) / zext (unsigned src) /
        // trunc, or identity when widths already match. Signedness comes from the
        // SOURCE trust-ir type (the MIR semantics of `iN as iM`).
        CastKind::IntToInt => {
            let v = lower_cast_operand(cx, fb, env, op, &src_tir)?;
            // `bool as iN` — a bool is `{0,1}`, so keep the established
            // `select(b, 1, 0)` lowering directly producing the destination integer.
            // TrustIr also admits canonical `zext Bool -> integer`; retaining the
            // select form keeps producer output stable. A non-bool integer source
            // uses the normal resize.
            if matches!(src_tir, TIRTy::Bool) {
                if !dst_ty.is_integer() {
                    return Err(format!("bool as non-integer {dst_ty:?}"));
                }
                let one = fb.iconst(dst_ty.clone(), 1);
                let zero = fb.iconst(dst_ty.clone(), 0);
                Ok(fb.select(dst_ty.clone(), v, one, zero))
            } else {
                Ok(int_cast(fb, v, &src_tir, dst_ty))
            }
        }

        // Pointer<->pointer reinterprets (Box<T> -> *const T, &T <-> *const T,
        // fn-ptr coercions): identity on the address. Both carriers are `Ptr`, so
        // the source value IS the result (no cast node; a PtrToPtr lowers to a copy
        // anyway). If the trust-ir types differ but both are pointer-ish, emit a
        // PtrToPtr the validator admits.
        CastKind::PtrToPtr
        | CastKind::FnPtrToPtr
        | CastKind::PointerCoercion(rustc_middle::ty::adjustment::PointerCoercion::UnsafeFnPointer, _) => {
            let v = lower_cast_operand(cx, fb, env, op, &src_tir)?;
            if is_ptr_tir(&src_tir) && is_ptr_tir(dst_ty) {
                Ok(v) // identity
            } else if is_ptr_tir(&src_tir) || is_ptr_tir(dst_ty) {
                Ok(fb.cast(CastOp::PtrToPtr, src_tir, dst_ty.clone(), v))
            } else {
                Err(format!("PtrToPtr between non-pointers {src_tir:?} -> {dst_ty:?}"))
            }
        }

        // A `Transmute` between layout-compatible scalars — the canonical Box niche
        // read (`NonNull<T> as *const T`) and the debug align/null asserts'
        // ptr<->usize reinterprets. NEVER emit CastOp::Transmute (validator-rejected);
        // map to the concrete op.
        CastKind::Transmute => {
            // An AGGREGATE-CONSTANT source (`transmute::<TypeId, u128>(const ..)`
            // in `<dyn Any>::is` / `payload_as_str`): materialize its byte image
            // — TypeId-provenance slots become their raw hash bytes — into a
            // fresh slot, then Load at the destination scalar. Byte-faithful
            // reinterpret, same discipline as the aggregate-place read.
            if let Operand::Constant(c) = op {
                if cast_scalar_tir_ty(cx, src_rust).is_none() {
                    let slot = materialize_const_aggregate(cx, fb, c)?;
                    return Ok(fb.load(dst_ty.clone(), slot));
                }
            }
            let v = lower_cast_operand(cx, fb, env, op, &src_tir)?;
            transmute_cast(fb, v, &src_tir, dst_ty)
        }

        // `ptr as usize` / `usize as *ptr` provenance reinterprets.
        CastKind::PointerExposeProvenance if is_ptr_tir(&src_tir) && dst_ty.is_integer() => {
            let v = lower_cast_operand(cx, fb, env, op, &src_tir)?;
            ptr_int_cast(fb, v, &src_tir, dst_ty)
        }
        CastKind::PointerWithExposedProvenance if src_tir.is_integer() && is_ptr_tir(dst_ty) => {
            let v = lower_cast_operand(cx, fb, env, op, &src_tir)?;
            ptr_int_cast(fb, v, &src_tir, dst_ty)
        }

        // `float as int`: Rust `as` SATURATES (out-of-range clamps to the int's
        // min/max, NaN -> 0) — the dedicated `fptosi.sat`/`fptoui.sat` ops, which
        // trust-cg codegens natively (aarch64 fcvtzs/fcvtzu saturate by
        // definition). Signedness comes from the DESTINATION integer.
        CastKind::FloatToInt if is_float_tir(&src_tir) && dst_ty.is_integer() => {
            let v = lower_cast_operand(cx, fb, env, op, &src_tir)?;
            let cop = if is_signed(dst_ty) {
                CastOp::FPToSISat
            } else {
                CastOp::FPToUISat
            };
            Ok(fb.cast(cop, src_tir, dst_ty.clone(), v))
        }

        // `int as float`: exact for small ints, round-to-nearest-even beyond the
        // mantissa — `sitofp`/`uitofp` by SOURCE signedness (a `bool` source does
        // not exist in well-typed MIR: `bool as f64` is rejected by rustc).
        CastKind::IntToFloat if src_tir.is_integer() && is_float_tir(dst_ty) => {
            let v = lower_cast_operand(cx, fb, env, op, &src_tir)?;
            let cop = if is_signed(&src_tir) {
                CastOp::SIToFP
            } else {
                CastOp::UIToFP
            };
            Ok(fb.cast(cop, src_tir, dst_ty.clone(), v))
        }

        // `f32 as f64` / `f64 as f32`: IEEE widen (exact) / narrow (round-to-
        // nearest-even). Same-width is the identity (the value already carries
        // the destination type).
        CastKind::FloatToFloat if is_float_tir(&src_tir) && is_float_tir(dst_ty) => {
            let v = lower_cast_operand(cx, fb, env, op, &src_tir)?;
            match (&src_tir, dst_ty) {
                (TIRTy::F32, TIRTy::F64) => {
                    Ok(fb.cast(CastOp::FPExt, TIRTy::F32, TIRTy::F64, v))
                }
                (TIRTy::F64, TIRTy::F32) => {
                    Ok(fb.cast(CastOp::FPTrunc, TIRTy::F64, TIRTy::F32, v))
                }
                (s, d) if *s == *d => Ok(v),
                (s, d) => Err(format!("FloatToFloat cast {s:?} -> {d:?} unsupported")),
            }
        }

        other => Err(format!("Rvalue::Cast {:?}", cast_kind_short(other))),
    }
}

/// A short stable label for an unmodeled cast kind (so the bucket is honest).
fn cast_kind_short(k: &CastKind) -> &'static str {
    match k {
        CastKind::PointerExposeProvenance => "PointerExposeProvenance",
        CastKind::PointerWithExposedProvenance => "PointerWithExposedProvenance",
        CastKind::PointerCoercion(_, _) => "PointerCoercion",
        CastKind::IntToInt => "IntToInt",
        CastKind::FloatToInt => "FloatToInt",
        CastKind::FloatToFloat => "FloatToFloat",
        CastKind::IntToFloat => "IntToFloat",
        CastKind::PtrToPtr => "PtrToPtr",
        CastKind::FnPtrToPtr => "FnPtrToPtr",
        CastKind::Transmute => "Transmute",
        CastKind::Subtype => "Subtype",
    }
}

/// Integer width change cast (sext/zext/trunc), signedness from `src`. An equal-
/// width reinterpret that only changes SIGNEDNESS (e.g. `u64 -> i64`) is NOT a
/// no-op for the trust-ir type system — the value's tracked type must become `dst`,
/// or a downstream use / block-param edge sees a type mismatch. We emit a `Bitcast`
/// (equal bit width, validator-admitted) for that case so the result is `dst`-typed.
fn int_cast(
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    val: trust_ir::ValueId,
    src: &TIRTy,
    dst: &TIRTy,
) -> trust_ir::ValueId {
    if src == dst {
        return val;
    }
    let sw = int_bit_width(src);
    let dw = int_bit_width(dst);
    match (sw, dw) {
        (Some(s), Some(d)) if s < d => {
            if is_signed(src) {
                fb.sext(src.clone(), dst.clone(), val)
            } else {
                fb.zext(src.clone(), dst.clone(), val)
            }
        }
        (Some(s), Some(d)) if s > d => fb.trunc(src.clone(), dst.clone(), val),
        // Equal width but DIFFERENT trust-ir type (a signedness-only reinterpret):
        // a same-width Bitcast retypes the value to `dst` without changing its bits.
        _ => fb.cast(CastOp::Bitcast, src.clone(), dst.clone(), val),
    }
}

/// Per-lane numeric cast for the SIMD `simd_cast`/`simd_as` element map and the
/// `vcvtq_*` NEON conversions: int<->int width change (`int_cast`), int->float
/// (`sitofp`/`uitofp` by SOURCE signedness — `vcvtq_f32_s32`), float->int
/// (Rust-`as` SATURATING `fptosi.sat`/`fptoui.sat` by DEST signedness —
/// `vcvtq_s32_f32`), and float->float (`fpext`/`fptrunc`). Same-type is the
/// identity. Signedness/rounding follow the scalar `Rvalue::Cast` policy above.
fn simd_lane_cast(
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    v: trust_ir::ValueId,
    se: &TIRTy,
    de: &TIRTy,
) -> trust_ir::ValueId {
    if se == de {
        return v;
    }
    match (is_float_tir(se), is_float_tir(de)) {
        (false, false) => int_cast(fb, v, se, de),
        (false, true) => {
            let cop = if is_signed(se) {
                CastOp::SIToFP
            } else {
                CastOp::UIToFP
            };
            fb.cast(cop, se.clone(), de.clone(), v)
        }
        (true, false) => {
            let cop = if is_signed(de) {
                CastOp::FPToSISat
            } else {
                CastOp::FPToUISat
            };
            fb.cast(cop, se.clone(), de.clone(), v)
        }
        (true, true) => match (se, de) {
            (TIRTy::F32, TIRTy::F64) => fb.cast(CastOp::FPExt, se.clone(), de.clone(), v),
            (TIRTy::F64, TIRTy::F32) => fb.cast(CastOp::FPTrunc, se.clone(), de.clone(), v),
            _ => v,
        },
    }
}

/// A `ptr <-> int` reinterpret: PtrToInt / IntToPtr. The pointer is 64-bit, so the
/// integer side must be 64-bit-equivalent for the op the validator admits.
fn ptr_int_cast(
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    val: trust_ir::ValueId,
    src: &TIRTy,
    dst: &TIRTy,
) -> Result<trust_ir::ValueId, String> {
    if is_ptr_tir(src) && dst.is_integer() {
        // PtrToInt yields a pointer-width integer; if the destination is a narrower
        // int, follow with a trunc. (usize/isize are 64-bit, the common case = no
        // trunc.)
        let as_u64 = fb.cast(CastOp::PtrToInt, TIRTy::Ptr, TIRTy::U64, val);
        Ok(int_cast(fb, as_u64, &TIRTy::U64, dst))
    } else if src.is_integer() && is_ptr_tir(dst) {
        let as_u64 = int_cast(fb, val, src, &TIRTy::U64);
        Ok(fb.cast(CastOp::IntToPtr, TIRTy::U64, TIRTy::Ptr, as_u64))
    } else {
        Err(format!("ptr<->int cast between {src:?} and {dst:?}"))
    }
}

/// Lower a `Transmute` between two scalar trust-ir types to the concrete validator-
/// admitted op (NEVER `CastOp::Transmute`). Fails loud on a width-changing /
/// non-scalar / float transmute the minimal model cannot faithfully reinterpret.
fn transmute_cast(
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    val: trust_ir::ValueId,
    src: &TIRTy,
    dst: &TIRTy,
) -> Result<trust_ir::ValueId, String> {
    let sp = is_ptr_tir(src);
    let dp = is_ptr_tir(dst);
    match (sp, dp) {
        // ptr <-> ptr: identity.
        (true, true) => Ok(val),
        // ptr -> int / int -> ptr.
        (true, false) if dst.is_integer() => ptr_int_cast(fb, val, src, dst),
        (false, true) if src.is_integer() => ptr_int_cast(fb, val, src, dst),
        // int <-> int.
        (false, false) if src.is_integer() && dst.is_integer() => {
            match (int_bit_width(src), int_bit_width(dst)) {
                // Same width: a signedness-only reinterpret. `int_cast` retypes the
                // value to `dst` (identity if already `dst`-typed, else a same-width
                // Bitcast) so downstream uses see the right trust-ir type.
                (Some(s), Some(d)) if s == d => Ok(int_cast(fb, val, src, dst)),
                // Different width transmute is UB in valid Rust and never appears;
                // fail loud rather than silently truncate/extend.
                _ => Err(format!(
                    "Transmute changes integer width {src:?} -> {dst:?} (unmodelable)"
                )),
            }
        }
        // float <-> SAME-WIDTH int: an exact bit reinterpret (`f64::to_bits`,
        // `f64::from_bits`, and the f32 duals) — trust-ir `Bitcast` (validator:
        // equal-bit-width rule; trust-cg aarch64: FMOV between the GPR/FPR
        // files). Width equality is REQUIRED; anything else stays a loud
        // failure below.
        (false, false)
            if (is_float_tir(src) && dst.is_integer())
                || (src.is_integer() && is_float_tir(dst)) =>
        {
            let fw = |t: &TIRTy| match t {
                TIRTy::F32 => Some(32),
                TIRTy::F64 => Some(64),
                _ => None,
            };
            let sw = fw(src).or_else(|| int_bit_width(src));
            let dw = fw(dst).or_else(|| int_bit_width(dst));
            match (sw, dw) {
                (Some(s), Some(d)) if s == d => {
                    Ok(fb.cast(CastOp::Bitcast, src.clone(), dst.clone(), val))
                }
                _ => Err(format!(
                    "Transmute float<->int width mismatch {src:?} -> {dst:?}"
                )),
            }
        }
        _ => Err(format!(
            "Transmute {src:?} -> {dst:?} (only equal-width ptr/int reinterprets)"
        )),
    }
}

/// Lower an Rvalue producing a value of `dst_ty`.
fn lower_rvalue<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    env: &HashMap<Local, trust_ir::ValueId>,
    rv: &Rvalue<'tcx>,
    dst_ty: TIRTy,
) -> Result<trust_ir::ValueId, String> {
    match rv {
        // `WithRetag` controls pointer-provenance annotations. TrustIR currently
        // has no alias-tag operation; like ordinary rustc codegen without the
        // experimental retag instrumentation, value lowering is unchanged.
        Rvalue::Use(op, _) => {
            let (v, _) = lower_operand(cx, fb, env, op)?;
            Ok(v)
        }
        Rvalue::CopyForDeref(place) => {
            let (v, _) = lower_place_value(cx, fb, env, place)?;
            Ok(v)
        }
        Rvalue::Reborrow(_, _, place) => {
            let (v, src_ty) = lower_place_value(cx, fb, env, place)?;
            if src_ty != dst_ty {
                return Err(format!(
                    "scalar Reborrow changes TrustIR type {src_ty:?} -> {dst_ty:?}"
                ));
            }
            Ok(v)
        }
        // RUNG 1: address-of a place -> the place's ADDRESS (a Ptr).
        Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
            place_address(cx, fb, env, place)
        }
        Rvalue::UnaryOp(unop, op) => {
            // RUNG 4: `PtrMetadata(p)` reads the METADATA half of a pointer. For a
            // FAT pointer (`&[T]`/`&str`/`&dyn`) modeled as a 2-lane slot, the
            // metadata (slice/str length, or dyn vtable) lives at slot offset 8 —
            // load it there. For a THIN pointer the metadata is the unit `()` (zero
            // bytes); MIR rarely emits PtrMetadata on a thin pointer, so bail loud.
            // Note: PtrMetadata reads a PLACE, so we must NOT pre-lower the operand
            // as a value (the fat operand has no single-scalar value).
            if matches!(unop, MirUnOp::PtrMetadata) {
                return lower_ptr_metadata(cx, fb, env, op, &dst_ty);
            }
            let (v, t) = lower_operand(cx, fb, env, op)?;
            match unop {
                // Float negation is its own IEEE sign-flip op (`FNeg`), distinct
                // from integer two's-complement `Neg` (the validator enforces the
                // family split).
                MirUnOp::Neg if is_float_tir(&t) => Ok(fb.unop(UnOp::FNeg, t, v)),
                MirUnOp::Neg => Ok(fb.unop(UnOp::Neg, t, v)),
                MirUnOp::Not => {
                    // Integer `Not` is bitwise (`UnOp::Not`); bool `Not` is
                    // logical. The validator rejects `UnOp::Not` on `Bool`, and a
                    // bitwise not of a 1-bit value is the wrong semantics anyway,
                    // so lower bool `!x` as `icmp eq x, false` (matching trust-cg's
                    // `lower_unary_op` bool path).
                    if matches!(t, TIRTy::Bool) {
                        let f = fb.bool_const(false);
                        Ok(fb.icmp(ICmpOp::Eq, TIRTy::Bool, v, f))
                    } else {
                        Ok(fb.unop(UnOp::Not, t, v))
                    }
                }
                MirUnOp::PtrMetadata => unreachable!("handled above"),
            }
        }
        Rvalue::BinaryOp(binop, boxed) => {
            let (lhs_op, rhs_op) = &**boxed;
            let (lhs, lt) = lower_operand(cx, fb, env, lhs_op)?;
            let (mut rhs, rt) = lower_operand(cx, fb, env, rhs_op)?;
            // ADDITIVE (RUNG 9 closure graph): `BinOp::Offset` is pointer-element
            // stepping — `lhs.offset(rhs)` = `lhs + rhs * size_of::<T>()` over the
            // pointee `T`. This is the cursor advance inside the SPECIALIZED
            // `slice::Iter::try_fold` the `.iter().all(|x| ..)` closure pulls in
            // (raw `*const Constant` / `*mut Constant` bumped by 1 per element).
            //
            // TrustIR GEP has a narrower semantic domain than Rust's signed
            // pointer offset: its interpreter and Lean model reject every
            // negative index. Keep GEP for unsigned or statically non-negative
            // counts, and lower the general signed case through the sanctioned
            // integer-pointer lane. Both derive `T`'s byte stride from
            // `tcx.layout_of(T)`; neither erases element scaling.
            if matches!(binop, MirBinOp::Offset) {
                let lhs_ty = operand_concrete_ty(cx, lhs_op);
                let pointee = match lhs_ty.kind() {
                    ty::RawPtr(p, _) | ty::Ref(_, p, _) => *p,
                    _ => {
                        return Err(format!(
                            "BinOp::Offset lhs is not a raw/ref pointer: {}",
                            ty_family(lhs_ty)
                        ))
                    }
                };
                let (stride, _size, _align) = iter_elem_layout(cx, pointee)?;
                if stride == 0 {
                    // Offsetting a ZST pointer changes the address by exactly
                    // zero bytes for every signed count. Preserve the pointer
                    // identity directly; even a zero-index GEP could impose an
                    // allocation check that Rust does not impose here.
                    return Ok(lhs);
                }
                let signed_count = matches!(
                    rt,
                    TIRTy::I8 | TIRTy::I16 | TIRTy::I32 | TIRTy::I64 | TIRTy::I128
                );
                let statically_nonnegative = match rhs_op {
                    Operand::Constant(c) => {
                        const_operand_i128(cx, c).is_some_and(|value| value >= 0)
                    }
                    _ => false,
                };
                if signed_count && !statically_nonnegative {
                    // Rust's `offset` admits negative in-allocation steps, but a
                    // negative TrustIr GEP index is UB by the format contract
                    // (interpreter + Lean model both reject it). Lower the
                    // general signed case through the format's sanctioned
                    // C-raw-pointer path instead: PtrToInt -> signed byte
                    // arithmetic -> IntToPtr (precedent: the ptr_offset_from
                    // lowering above). This is exactly Rust's `offset` at the
                    // machine level; the GEP fast path below stays reserved for
                    // counts proven non-negative (unsigned or constant >= 0).
                    // Unblocks `slice::Iter::next_back` (`end.offset(-1)`) once
                    // the stable-wrapper inlining exposes its raw Offset.
                    let idx = if matches!(rt, TIRTy::I64) {
                        rhs
                    } else {
                        coerce_int_width(fb, rhs, &rt, &TIRTy::I64)?
                    };
                    let addr = fb.cast(CastOp::PtrToInt, TIRTy::Ptr, TIRTy::I64, lhs);
                    let stride_c = fb.iconst(TIRTy::I64, stride as i128);
                    let byte_off = fb.binop(BinOp::Mul, TIRTy::I64, idx, stride_c);
                    let addr2 = fb.binop(BinOp::Add, TIRTy::I64, addr, byte_off);
                    return Ok(fb.cast(CastOp::IntToPtr, TIRTy::I64, TIRTy::Ptr, addr2));
                }
                // Scale the element count by the byte stride, then GEP i8. The count
                // is an `isize`/`usize`; normalize it to a single I64 index type so
                // the stride multiply has matching operand types (the validator
                // rejects mixed-signedness binops). `coerce_int_width` is a no-op
                // when `rt` is already a 64-bit int, but it RETYPES a `u64`/`i64`
                // pointer-count to I64 so the `mul` below type-checks.
                let idx = if matches!(rt, TIRTy::I64) {
                    rhs
                } else if matches!(rt, TIRTy::U64) {
                    // Same bit width, only the signedness label differs: a free
                    // reinterpret to I64 (the index space the GEP expects).
                    fb.cast(CastOp::Bitcast, TIRTy::U64, TIRTy::I64, rhs)
                } else {
                    coerce_int_width(fb, rhs, &rt, &TIRTy::I64)?
                };
                let stride_c = fb.iconst(TIRTy::I64, stride as i128);
                let byte_off = fb.binop(BinOp::Mul, TIRTy::I64, idx, stride_c);
                let res = fb.gep(TIRTy::I8, lhs, vec![byte_off]);
                return Ok(res);
            }
            // The validator requires both binop operands to share a type. MIR
            // shifts permit a shift-amount of a DIFFERENT (often narrower) integer
            // type than the value; coerce the amount to the value's type with a
            // zero-extend / truncate (shift counts are non-negative, so zext is the
            // value-preserving widening). Other binops always have matching operand
            // types in well-typed MIR.
            if matches!(
                binop,
                MirBinOp::Shl
                    | MirBinOp::ShlUnchecked
                    | MirBinOp::Shr
                    | MirBinOp::ShrUnchecked
            ) && rt != lt
            {
                rhs = coerce_int_width(fb, rhs, &rt, &lt)?;
            }
            lower_binop(fb, *binop, lt, dst_ty, lhs, rhs)
        }
        Rvalue::Cast(kind, op, _dst_rust_ty) => lower_cast(cx, fb, env, kind, op, &dst_ty),
        Rvalue::Aggregate(_, _) => Err("Rvalue::Aggregate".to_string()),
        Rvalue::Discriminant(_) => Err("Rvalue::Discriminant".to_string()),
        Rvalue::Repeat(_, _) => Err("Rvalue::Repeat".to_string()),
        // A thread-local reference (`&/*tls*/ STATIC`) is the ADDRESS of a
        // thread-local static — model it as a TLS module global and yield its
        // `GlobalAddr` (the canonical thread-local-address lowering). Backs
        // `RandomState::new::KEYS`'s `LazyStorage::get_or_init(&tls, ..)`.
        Rvalue::ThreadLocalRef(def_id) => {
            let gid = intern_tls_global(cx, *def_id)?;
            Ok(fb.global_addr(gid))
        }
        Rvalue::WrapUnsafeBinder(_, _) => Err("Rvalue::WrapUnsafeBinder".to_string()),
    }
}

/// Bit width of a trust-ir scalar integer / bool type (for shift-amount coercion).
fn int_bit_width(t: &TIRTy) -> Option<u32> {
    Some(match t {
        TIRTy::Bool | TIRTy::I8 | TIRTy::U8 => 8,
        TIRTy::I16 | TIRTy::U16 => 16,
        TIRTy::I32 | TIRTy::U32 => 32,
        TIRTy::I64 | TIRTy::U64 => 64,
        TIRTy::I128 | TIRTy::U128 => 128,
        _ => return None,
    })
}

/// Coerce an integer value of `src` type to `dst` type via zero-extend (widen) or
/// truncate (narrow). Used to make a shift-amount match the shifted value's type
/// (the validator requires identical binop operand types). Shift counts are
/// non-negative, so a zero-extend is value-preserving.
fn coerce_int_width(
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    val: trust_ir::ValueId,
    src: &TIRTy,
    dst: &TIRTy,
) -> Result<trust_ir::ValueId, String> {
    let sw = int_bit_width(src)
        .ok_or_else(|| format!("shift-amount coerce: non-integer src {src:?}"))?;
    let dw = int_bit_width(dst)
        .ok_or_else(|| format!("shift-amount coerce: non-integer dst {dst:?}"))?;
    Ok(match sw.cmp(&dw) {
        std::cmp::Ordering::Less => fb.zext(src.clone(), dst.clone(), val),
        std::cmp::Ordering::Greater => fb.trunc(src.clone(), dst.clone(), val),
        // Same WIDTH but different SIGNEDNESS (e.g. `(x as i64) << (i % 8)` with
        // `i: usize` -> shift value i64, amount u64): the widths match so no
        // zext/trunc is needed, but the amount must still be RE-TYPED to the
        // value's type. A bare `val` here leaves a signedness-mismatched
        // operand pair — harmless on hardware (identical bits) but the v30
        // typed value model (and any typed consumer) rejects `Shl(i64, u64)`.
        // Bitcast is the exact signedness reinterpret.
        std::cmp::Ordering::Equal if src != dst => {
            fb.cast(CastOp::Bitcast, src.clone(), dst.clone(), val)
        }
        std::cmp::Ordering::Equal => val,
    })
}

/// Lower a scalar MIR BinaryOp.
fn lower_binop(
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    op: MirBinOp,
    opnd_ty: TIRTy,
    dst_ty: TIRTy,
    lhs: trust_ir::ValueId,
    rhs: trust_ir::ValueId,
) -> Result<trust_ir::ValueId, String> {
    // BOOL logical Bit{And,Or,Xor}: TrustIR admits direct scalar-Bool logic, but
    // this frontend keeps its established canonical form for stable output and
    // compatibility with older consumers: `a & b` = `select(a, b, false)`,
    // `a | b` = `select(a, true, b)`, `a ^ b` = `icmp ne a, b`. Each form has
    // exactly the direct Bool BinOp semantics. (Matches trust-cg's bool lowering.)
    if matches!(opnd_ty, TIRTy::Bool)
        && matches!(op, MirBinOp::BitAnd | MirBinOp::BitOr | MirBinOp::BitXor)
    {
        return Ok(match op {
            MirBinOp::BitAnd => {
                let f = fb.bool_const(false);
                fb.select(TIRTy::Bool, lhs, rhs, f)
            }
            MirBinOp::BitOr => {
                let t = fb.bool_const(true);
                fb.select(TIRTy::Bool, lhs, t, rhs)
            }
            MirBinOp::BitXor => fb.icmp(ICmpOp::Ne, TIRTy::Bool, lhs, rhs),
            _ => unreachable!(),
        });
    }

    // FLOAT operands: dispatch to the float arithmetic (`FAdd`..`FRem`) and float
    // compare (`FCmp`) families. Rust surface semantics: `==` is IEEE ordered-eq
    // (false on NaN), `!=` is unordered-ne (TRUE on NaN), and the orderings are
    // ordered compares (false when either side is NaN) — exactly rustc codegen's
    // `oeq/une/olt/ole/ogt/oge` mapping. Bit/shift/overflow ops on floats do not
    // exist in well-typed MIR; fail loud if ever seen.
    if is_float_tir(&opnd_ty) {
        return match op {
            MirBinOp::Add | MirBinOp::AddUnchecked => Ok(fb.binop(BinOp::FAdd, dst_ty, lhs, rhs)),
            MirBinOp::Sub | MirBinOp::SubUnchecked => Ok(fb.binop(BinOp::FSub, dst_ty, lhs, rhs)),
            MirBinOp::Mul | MirBinOp::MulUnchecked => Ok(fb.binop(BinOp::FMul, dst_ty, lhs, rhs)),
            MirBinOp::Div => Ok(fb.binop(BinOp::FDiv, dst_ty, lhs, rhs)),
            MirBinOp::Rem => Ok(fb.binop(BinOp::FRem, dst_ty, lhs, rhs)),
            MirBinOp::Eq => Ok(fb.fcmp(FCmpOp::OEq, opnd_ty, lhs, rhs)),
            MirBinOp::Ne => Ok(fb.fcmp(FCmpOp::UNe, opnd_ty, lhs, rhs)),
            MirBinOp::Lt => Ok(fb.fcmp(FCmpOp::OLt, opnd_ty, lhs, rhs)),
            MirBinOp::Le => Ok(fb.fcmp(FCmpOp::OLe, opnd_ty, lhs, rhs)),
            MirBinOp::Gt => Ok(fb.fcmp(FCmpOp::OGt, opnd_ty, lhs, rhs)),
            MirBinOp::Ge => Ok(fb.fcmp(FCmpOp::OGe, opnd_ty, lhs, rhs)),
            other => Err(format!("float BinOp {other:?} has no trust-ir lowering")),
        };
    }

    let signed = is_signed(&opnd_ty);
    // `Cmp` needs the operand AND destination types outside the `arith`/`cmp`
    // closures (which capture `dst_ty`/`opnd_ty` by move): clone up front.
    let cmp3_opnd_ty = opnd_ty.clone();
    let cmp3_dst_ty = dst_ty.clone();
    let arith =
        |fb: &mut trust_ir_build::FunctionBuilder<'_>, b: BinOp| fb.binop(b, dst_ty, lhs, rhs);
    let cmp = |fb: &mut trust_ir_build::FunctionBuilder<'_>, c: ICmpOp| fb.icmp(c, opnd_ty, lhs, rhs);
    match op {
        MirBinOp::Add | MirBinOp::AddUnchecked => Ok(arith(fb, BinOp::Add)),
        MirBinOp::Sub | MirBinOp::SubUnchecked => Ok(arith(fb, BinOp::Sub)),
        MirBinOp::Mul | MirBinOp::MulUnchecked => Ok(arith(fb, BinOp::Mul)),
        MirBinOp::Div => Ok(arith(fb, if signed { BinOp::SDiv } else { BinOp::UDiv })),
        MirBinOp::Rem => Ok(arith(fb, if signed { BinOp::SRem } else { BinOp::URem })),
        MirBinOp::BitAnd => Ok(arith(fb, BinOp::And)),
        MirBinOp::BitOr => Ok(arith(fb, BinOp::Or)),
        MirBinOp::BitXor => Ok(arith(fb, BinOp::Xor)),
        MirBinOp::Shl | MirBinOp::ShlUnchecked => Ok(arith(fb, BinOp::Shl)),
        MirBinOp::Shr | MirBinOp::ShrUnchecked => {
            Ok(arith(fb, if signed { BinOp::AShr } else { BinOp::LShr }))
        }
        MirBinOp::Eq => Ok(cmp(fb, ICmpOp::Eq)),
        MirBinOp::Ne => Ok(cmp(fb, ICmpOp::Ne)),
        MirBinOp::Lt => Ok(cmp(fb, if signed { ICmpOp::Slt } else { ICmpOp::Ult })),
        MirBinOp::Le => Ok(cmp(fb, if signed { ICmpOp::Sle } else { ICmpOp::Ule })),
        MirBinOp::Gt => Ok(cmp(fb, if signed { ICmpOp::Sgt } else { ICmpOp::Ugt })),
        MirBinOp::Ge => Ok(cmp(fb, if signed { ICmpOp::Sge } else { ICmpOp::Uge })),
        MirBinOp::AddWithOverflow | MirBinOp::SubWithOverflow | MirBinOp::MulWithOverflow => {
            Err("BinOp checked-overflow (needs tuple dest)".to_string())
        }
        MirBinOp::Offset => Err("BinOp::Offset (pointer)".to_string()),
        // THREE-WAY ordering (`Ord::cmp` — `usize`/`u32` on the Vec-growth and
        // `min_stack` max() paths). The result is `core::cmp::Ordering`, a
        // `#[repr(i8)]` enum with the GUARANTEED discriminants Less=-1, Equal=0,
        // Greater=1, whose whole layout is one `i8` scalar — so `dst_ty` here is
        // the enum's scalar image (I8). Lower as two comparisons + two selects:
        //   lt ? -1 : (gt ? 1 : 0)
        // exactly the documented semantics of `<int as Ord>::cmp`.
        MirBinOp::Cmp => {
            if int_bit_width(&cmp3_dst_ty).is_none() {
                return Err(format!(
                    "BinOp::Cmp destination is not an integer scalar: {cmp3_dst_ty:?}"
                ));
            }
            let lt = fb.icmp(
                if signed { ICmpOp::Slt } else { ICmpOp::Ult },
                cmp3_opnd_ty.clone(),
                lhs,
                rhs,
            );
            let gt = fb.icmp(
                if signed { ICmpOp::Sgt } else { ICmpOp::Ugt },
                cmp3_opnd_ty,
                lhs,
                rhs,
            );
            let neg_one = fb.iconst(cmp3_dst_ty.clone(), -1);
            let one = fb.iconst(cmp3_dst_ty.clone(), 1);
            let zero = fb.iconst(cmp3_dst_ty.clone(), 0);
            let gt_arm = fb.select(cmp3_dst_ty.clone(), gt, one, zero);
            Ok(fb.select(cmp3_dst_ty, lt, neg_one, gt_arm))
        }
    }
}

/// Lower a terminator. RUNG 0: Return / Goto / SwitchInt / Unreachable. RUNG 2:
/// edge args (cross-block phi), `Call`, `Assert`. Edges into a block supply the
/// block's live-in scalar params via `tc.edge_args`.
fn lower_terminator<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    env: &mut HashMap<Local, trust_ir::ValueId>,
    tc: &mut TermCtx<'_>,
    kind: &TerminatorKind<'tcx>,
    source_info: rustc_middle::mir::SourceInfo,
) -> Result<(), String> {
    match kind {
        TerminatorKind::Return => {
            match &tc.ret_abi {
                // Unit return, or sret (the aggregate result was already Stored
                // through the hidden sret pointer = `_0`'s slot): `ret []`. The
                // body wrote `_0` in place via the sret pointer, so there is no
                // value to return here.
                RetAbi::Unit | RetAbi::Sret => {
                    fb.ret(vec![]);
                }
                RetAbi::Scalar(_) => {
                    let ret_local = Local::from_u32(0);
                    // The return value: an SSA scalar bound in env, or a Load from
                    // the return slot if _0 is memory-backed (an address-taken
                    // scalar cell).
                    if let Some(LocalModel::Ssa(_)) = cx.model.get(&ret_local) {
                        let v = env.get(&ret_local).copied().ok_or_else(|| {
                            "return: _0 not bound in returning block (needs phi)".to_string()
                        })?;
                        fb.ret(vec![v]);
                    } else {
                        let (v, _) = lower_place_value(cx, fb, env, &Place::from(ret_local))?;
                        fb.ret(vec![v]);
                    }
                }
                // RUNG 10: by-value small-pair return. The body built `_0` in its
                // own entry slot through the ordinary layout-faithful aggregate
                // machinery; materialize it as ONE SSA 2-tuple with a single
                // whole-aggregate Load (offset-ordered lanes — byte-congruent
                // with the slot's field writes, see `pair_ret_model`) and return
                // it by value.
                RetAbi::Pair(pr) => {
                    let ret_local = Local::from_u32(0);
                    let slot = cx.slot_ptr(ret_local).ok_or_else(|| {
                        "pair return: _0 has no memory slot".to_string()
                    })?;
                    let v = fb.load(pr.tuple_ty(), slot);
                    fb.ret(vec![v]);
                }
            }
            Ok(())
        }
        TerminatorKind::Goto { target } => {
            let args = tc.edge_args(env, *target)?;
            fb.br(tc.target_block(*target), args);
            Ok(())
        }
        TerminatorKind::Unreachable => {
            fb.unreachable();
            Ok(())
        }
        TerminatorKind::SwitchInt { discr, targets } => {
            let (v, t) = lower_operand(cx, fb, env, discr)?;
            let default_bb: BasicBlock = targets.otherwise();
            // RUNG 2 (bool branch): a `SwitchInt` on a BOOL discriminant — the `&&`/
            // `||` short-circuit and match-on-bool shape — lowers to a two-way
            // `condbr`, NOT a `switch` with `Bool` cases. (trust-cg's switch admits
            // only INTEGER case values; a `Bool(false)` case is rejected at codegen.
            // The `sz` Box walk never hit this because its match was on an integer
            // niche.) The MIR is `switchInt(b) -> [0: false_arm, otherwise: true_arm]`
            // (and may list `1: true_arm` explicitly); we route `true -> then`,
            // `false -> else`, faithfully preserving each edge's phi args.
            if matches!(t, TIRTy::Bool) {
                let mut false_target: Option<BasicBlock> = None;
                let mut true_target: Option<BasicBlock> = None;
                for (val, target) in targets.iter() {
                    match val {
                        0 => false_target = Some(target),
                        1 => true_target = Some(target),
                        other => {
                            return Err(format!(
                                "bool SwitchInt has non-0/1 case value {other}"
                            ));
                        }
                    }
                }
                // Whichever explicit case is absent is the `otherwise` (default) arm.
                let true_bb = true_target.unwrap_or(default_bb);
                let false_bb = false_target.unwrap_or(default_bb);
                let then_args = tc.edge_args(env, true_bb)?;
                let else_args = tc.edge_args(env, false_bb)?;
                fb.condbr(
                    v,
                    tc.target_block(true_bb),
                    then_args,
                    tc.target_block(false_bb),
                    else_args,
                );
                return Ok(());
            }
            // 128-BIT selector (the `CheckEnums` u128 guard; `<u128 as
            // LowerHex>::fmt`-class jump tables): trust-cg's Switch realizes
            // only 8/16/32/64-bit selectors, so lower the switch as the
            // equivalent `ICmp(Eq)` + `CondBr` CHAIN — semantically identical
            // (case values are distinct, so first-match == only-match), and
            // every edge keeps its own phi args. Case constants ride the v24
            // canonical spelling (`uconst`/`Constant::u128` for U128 — full
            // range; bit-faithful `as i128` for I128, where Eq is bitwise).
            if matches!(t, TIRTy::I128 | TIRTy::U128) {
                let all: Vec<(u128, BasicBlock)> = targets.iter().collect();
                for (i, (val, target)) in all.iter().enumerate() {
                    let c = if matches!(t, TIRTy::U128) {
                        fb.uconst(t.clone(), *val)
                    } else {
                        fb.iconst(t.clone(), *val as i128)
                    };
                    let hit = fb.icmp(ICmpOp::Eq, t.clone(), v, c);
                    let case_args = tc.edge_args(env, *target)?;
                    if i + 1 == all.len() {
                        let def_args = tc.edge_args(env, default_bb)?;
                        fb.condbr(
                            hit,
                            tc.target_block(*target),
                            case_args,
                            tc.target_block(default_bb),
                            def_args,
                        );
                    } else {
                        let next = fb.create_block();
                        fb.condbr(hit, tc.target_block(*target), case_args, next, vec![]);
                        fb.switch_to_block(next);
                    }
                }
                if all.is_empty() {
                    let def_args = tc.edge_args(env, default_bb)?;
                    fb.br(tc.target_block(default_bb), def_args);
                }
                return Ok(());
            }
            let mut cases: Vec<SwitchCase> = Vec::new();
            for (val, target) in targets.iter() {
                cases.push(SwitchCase {
                    value: Constant::Int(val as i128),
                    target: tc.target_block(target),
                    args: tc.edge_args(env, target)?,
                });
            }
            let default_args = tc.edge_args(env, default_bb)?;
            fb.switch(v, cases, tc.target_block(default_bb), default_args);
            Ok(())
        }
        // RUNG 2: a direct call to an extern-declared callee. Lower each arg, emit
        // the call, bind the destination, then `br` to the success target threading
        // its live-in phi args. A diverging call (target == None) -> `unreachable`.
        TerminatorKind::Call {
            func,
            args,
            destination,
            target,
            unwind,
            fn_span,
            ..
        } => {
            // RUNG (atomics): an atomic-RMW / fence INTRINSIC — the Arc/Weak refcount
            // primitives. `core::intrinsics::atomic_xadd`/`atomic_xsub` (strong/weak++
            // / --) lower THROUGH trust-ir as `AtomicRMW { op: Add/Sub, ordering }`, and
            // `atomic_fence` as `Fence { ordering }` — NOT as opaque external call
            // leaves. trust-cg codegens both on aarch64 (LSE `LDADDAL`/`LDADDL`-family
            // RMW + `DMB ISH*` fence), so the reference-counting discipline is a
            // first-class VERIFIED instruction. The `AtomicOrdering` value rides on the
            // intrinsic's const generic (`atomic_ordering_from_args`). Handled BEFORE the
            // generic-call path so the intrinsic never becomes an extern stub.
            if let Some(callee) = resolve_call_callee(cx, func) {
                // RUNG (NEON pairwise-max): the aarch64 `vpmaxq_u8`/`vpmax_u8`
                // intrinsic bodies call the LLVM FOREIGN intrinsic
                // `llvm.aarch64.neon.umaxp.v{16,8}i8` (UNSIGNED pairwise
                // maximum) — a foreign item, NOT a rustc intrinsic, so it is
                // not caught by `tcx.intrinsic` below and would otherwise
                // become an undefined extern leaf. memchr's aarch64 NEON
                // `movemask_will_have_non_zero` uses `vpmaxq_u8(v, v)` as its
                // "any lane set?" reduce, so the 128-bit byte scan links to it.
                // Lower it INLINE through trust-ir the same way the `simd_*`
                // byte ops are (per-lane load / unsigned-max select / store),
                // so the 128-bit reduce never crosses an out-of-line vector
                // call ABI. Pairwise (N = lane count): out[i]=umax(a[2i],
                // a[2i+1]) for i<N/2; out[N/2+i]=umax(b[2i],b[2i+1]) for i<N/2.
                let callee_sym = cx.tcx.symbol_name(callee).name;
                if callee_sym == "llvm.aarch64.neon.umaxp.v16i8"
                    || callee_sym == "llvm.aarch64.neon.umaxp.v8i8"
                {
                    let ret_bb = target.ok_or_else(|| {
                        "neon umaxp: call must have a return target".to_string()
                    })?;
                    let [a, b] = &args[..] else {
                        return Err("neon umaxp: expected exactly two args".to_string());
                    };
                    let (se, sc) =
                        simd_int_vector_lanes(cx, operand_concrete_ty(cx, &a.node))
                            .ok_or_else(|| {
                                "neon umaxp: non-int-vector operand".to_string()
                            })?;
                    let w = int_lane_size(&se);
                    if w == 0 || sc == 0 || sc % 2 != 0 {
                        return Err(format!(
                            "neon umaxp: unsupported lane shape {se:?} x {sc}"
                        ));
                    }
                    // umaxp is UNSIGNED: compare the lanes as their unsigned
                    // int type so the max select is `Uge`.
                    let ulane = match se {
                        TIRTy::I8 | TIRTy::U8 => TIRTy::U8,
                        TIRTy::I16 | TIRTy::U16 => TIRTy::U16,
                        TIRTy::I32 | TIRTy::U32 => TIRTy::U32,
                        TIRTy::I64 | TIRTy::U64 => TIRTy::U64,
                        other => other,
                    };
                    let a_ptr = operand_place_address(cx, fb, env, &a.node)?;
                    let b_ptr = operand_place_address(cx, fb, env, &b.node)?;
                    let dst_ptr = place_address(cx, fb, env, destination)?;
                    let half = sc / 2;
                    for (src_ptr, out_base) in [(a_ptr, 0u64), (b_ptr, half)] {
                        for i in 0..half {
                            let off0 = (2 * i) * w;
                            let off1 = (2 * i + 1) * w;
                            let p0 = if off0 == 0 {
                                src_ptr
                            } else {
                                gep_byte_offset(fb, src_ptr, off0)
                            };
                            let p1 = gep_byte_offset(fb, src_ptr, off1);
                            let x = fb.load(ulane.clone(), p0);
                            let y = fb.load(ulane.clone(), p1);
                            let ge = fb.icmp(ICmpOp::Uge, ulane.clone(), x, y);
                            let m = fb.select(ulane.clone(), ge, x, y);
                            let odst = (out_base + i) * w;
                            let dd = if odst == 0 {
                                dst_ptr
                            } else {
                                gep_byte_offset(fb, dst_ptr, odst)
                            };
                            fb.store(ulane.clone(), dd, m);
                        }
                    }
                    let edge = tc.edge_args(env, ret_bb)?;
                    fb.br(tc.target_block(ret_bb), edge);
                    return Ok(());
                }
                // RUNG (NEON table lookup): `vqtbl1q_u8`/`vqtbl1q_s8` (and the
                // 64-bit `vtbl1_*` D-register forms) call the LLVM FOREIGN
                // intrinsic `llvm.aarch64.neon.tbl1.v{16,8}i8` (byte table
                // lookup / permuted gather) — a foreign item, NOT a rustc
                // intrinsic, so it is not caught by `tcx.intrinsic` below and
                // would otherwise become an undefined extern leaf (LINKFAIL).
                // Lower it INLINE through trust-ir the same per-lane way the
                // umaxp / simd_* byte ops are, so the 128-bit lookup never
                // crosses an out-of-line vector call ABI.
                //
                // tbl1 semantics: out[i] = (idx[i] < N) ? table[idx[i]] : 0,
                // where N is the TABLE lane count (16 for a Q-register table;
                // the aarch64 v8i8 form zero-pads its table to 16 bytes, so
                // N=16 still yields the correct out-of-range-reads-0 result).
                // The index is DYNAMIC, so the gather is a GEP with a RUNTIME
                // index (trust-cg lowers a single-index GEP to base + idx*1).
                // We MASK the index (idx & (N-1)) before the gather so the load
                // is always in-bounds (never reads past the N-byte table), then
                // SELECT on the ORIGINAL `idx[i] < N` to zero out-of-range
                // lanes — bit-exact with the aarch64 TBL "out-of-range → 0"
                // rule for a single-table lookup.
                if callee_sym == "llvm.aarch64.neon.tbl1.v16i8"
                    || callee_sym == "llvm.aarch64.neon.tbl1.v8i8"
                {
                    let ret_bb = target.ok_or_else(|| {
                        "neon tbl1: call must have a return target".to_string()
                    })?;
                    let [tbl, idx] = &args[..] else {
                        return Err("neon tbl1: expected exactly two args".to_string());
                    };
                    // Table lane count = the in-range bound N (tbl1 is a BYTE
                    // table, so each lane is one u8).
                    let (_te, n_lanes) =
                        simd_int_vector_lanes(cx, operand_concrete_ty(cx, &tbl.node))
                            .ok_or_else(|| "neon tbl1: non-int-vector table".to_string())?;
                    // Index / output lane count = the DESTINATION lane count.
                    let (_de, dc) =
                        simd_int_vector_lanes(cx, cx.place_concrete_ty(destination))
                            .ok_or_else(|| {
                                "neon tbl1: non-int-vector destination".to_string()
                            })?;
                    if n_lanes == 0 || (n_lanes & (n_lanes - 1)) != 0 {
                        return Err(format!(
                            "neon tbl1: table lane count {n_lanes} not a power of two"
                        ));
                    }
                    let tbl_ptr = operand_place_address(cx, fb, env, &tbl.node)?;
                    let idx_ptr = operand_place_address(cx, fb, env, &idx.node)?;
                    let dst_ptr = place_address(cx, fb, env, destination)?;
                    let n = n_lanes as i128; // in-range bound
                    let mask = (n_lanes - 1) as i128; // N-1: gather-safe mask
                    for i in 0..dc {
                        // idx[i] : u8, zero-extended to i64 for the compare /
                        // mask / GEP index (all pointer-width int ops).
                        let ip = if i == 0 {
                            idx_ptr
                        } else {
                            gep_byte_offset(fb, idx_ptr, i)
                        };
                        let ixb = fb.load(TIRTy::U8, ip);
                        let ix64 = int_cast(fb, ixb, &TIRTy::U8, &TIRTy::I64);
                        // in_range = idx[i] < N (ix64 is 0..=255, so unsigned).
                        let nb = fb.iconst(TIRTy::I64, n);
                        let in_range = fb.icmp(ICmpOp::Ult, TIRTy::I64, ix64, nb);
                        // masked = idx[i] & (N-1) — always a valid table index.
                        let mb = fb.iconst(TIRTy::I64, mask);
                        let masked = fb.binop(BinOp::And, TIRTy::I64, ix64, mb);
                        let gaddr = fb.gep(TIRTy::I8, tbl_ptr, vec![masked]);
                        let gval = fb.load(TIRTy::U8, gaddr);
                        // out[i] = in_range ? table[masked] : 0
                        let zero = fb.iconst(TIRTy::U8, 0);
                        let res = fb.select(TIRTy::U8, in_range, gval, zero);
                        let op = if i == 0 {
                            dst_ptr
                        } else {
                            gep_byte_offset(fb, dst_ptr, i)
                        };
                        fb.store(TIRTy::U8, op, res);
                    }
                    let edge = tc.edge_args(env, ret_bb)?;
                    fb.br(tc.target_block(ret_bb), edge);
                    return Ok(());
                }
                // RUNG (NEON saturating narrow / doubling-multiply-high): the
                // aarch64 `vqmovn_{u,s}16` / `vqmovun_s16` / `vqdmulhq_s16`
                // intrinsic bodies call the LLVM FOREIGN intrinsics
                // `llvm.aarch64.neon.{uqxtn,sqxtn,sqxtun}.v8i8` (saturating
                // narrow 16->8) and `llvm.aarch64.neon.sqdmulh.v8i16`
                // (saturating doubling multiply, high half). Like `umaxp`,
                // these are foreign items — NOT rustc `simd_*` intrinsics — so
                // they escape the `tcx.intrinsic` dispatch below and would
                // otherwise become undefined extern leaves at link. Lower each
                // INLINE per-lane through trust-ir scalar ops (widen to a signed
                // wide type, clamp to the destination lane's value range,
                // truncate). Pure integer arithmetic, so byte-exact.
                if matches!(
                    callee_sym,
                    "llvm.aarch64.neon.uqxtn.v8i8"
                        | "llvm.aarch64.neon.sqxtn.v8i8"
                        | "llvm.aarch64.neon.sqxtun.v8i8"
                        | "llvm.aarch64.neon.sqdmulh.v8i16"
                ) {
                    let ret_bb = target.ok_or_else(|| {
                        format!("neon {callee_sym}: call must have a return target")
                    })?;
                    let dst_ptr = place_address(cx, fb, env, destination)?;
                    if callee_sym == "llvm.aarch64.neon.sqdmulh.v8i16" {
                        // `sqdmulh`: r = sat_i16((2*a*b) >> 16). Forming `2*a*b`
                        // in i32 overflows at a=b=-32768 (== 2^31), so use the
                        // identity `(2*a*b) >> 16 == (a*b) >> 15` — `a*b` fits in
                        // i32 (|a|,|b| <= 32768 -> |a*b| <= 2^30). The shift is
                        // ARITHMETIC (rounds toward -inf, matching ARM `>>`).
                        let [a, b] = &args[..] else {
                            return Err(format!("neon {callee_sym}: expected two args"));
                        };
                        let (se, sc) = simd_int_vector_lanes(
                            cx,
                            operand_concrete_ty(cx, &a.node),
                        )
                        .ok_or_else(|| {
                            format!("neon {callee_sym}: non-int-vector operand")
                        })?;
                        let w = int_lane_size(&se);
                        if w != 2 {
                            return Err(format!(
                                "neon {callee_sym}: expected 16-bit lanes, got {w} bytes"
                            ));
                        }
                        let a_ptr = operand_place_address(cx, fb, env, &a.node)?;
                        let b_ptr = operand_place_address(cx, fb, env, &b.node)?;
                        let hic = fb.iconst(TIRTy::I32, 32767);
                        let loc = fb.iconst(TIRTy::I32, -32768);
                        let sh = fb.iconst(TIRTy::I32, 15);
                        for i in 0..sc {
                            let off = i * w;
                            let aa = if off == 0 { a_ptr } else { gep_byte_offset(fb, a_ptr, off) };
                            let bb = if off == 0 { b_ptr } else { gep_byte_offset(fb, b_ptr, off) };
                            let va = fb.load(se.clone(), aa);
                            let vb = fb.load(se.clone(), bb);
                            let aw = int_cast(fb, va, &se, &TIRTy::I32);
                            let bw = int_cast(fb, vb, &se, &TIRTy::I32);
                            let p = fb.binop(BinOp::Mul, TIRTy::I32, aw, bw);
                            let r = fb.binop(BinOp::AShr, TIRTy::I32, p, sh);
                            let over = fb.icmp(ICmpOp::Sgt, TIRTy::I32, r, hic);
                            let r1 = fb.select(TIRTy::I32, over, hic, r);
                            let under = fb.icmp(ICmpOp::Slt, TIRTy::I32, r1, loc);
                            let r2 = fb.select(TIRTy::I32, under, loc, r1);
                            let rr = int_cast(fb, r2, &TIRTy::I32, &se);
                            let dd = if off == 0 { dst_ptr } else { gep_byte_offset(fb, dst_ptr, off) };
                            fb.store(se.clone(), dd, rr);
                        }
                    } else {
                        // Saturating narrow: one Q source (u16/i16 x8) -> one D
                        // dest (u8/i8 x8). Compute in a SIGNED wide type (i32) so
                        // a signed source's negative values survive and the
                        // signed clamp works; a u16 source zero-extends. The
                        // dest lane's saturation range selects the clamp bounds.
                        let [a] = &args[..] else {
                            return Err(format!("neon {callee_sym}: expected one arg"));
                        };
                        let (se, sc) = simd_int_vector_lanes(
                            cx,
                            operand_concrete_ty(cx, &a.node),
                        )
                        .ok_or_else(|| {
                            format!("neon {callee_sym}: non-int-vector operand")
                        })?;
                        let (de, _dc) = simd_int_vector_lanes(
                            cx,
                            cx.place_concrete_ty(destination),
                        )
                        .ok_or_else(|| {
                            format!("neon {callee_sym}: non-int-vector destination")
                        })?;
                        let sw = int_lane_size(&se);
                        let dw = int_lane_size(&de);
                        // uqxtn: unsigned dest [0,255]; sqxtn: signed [-128,127];
                        // sqxtun: unsigned dest [0,255] from a signed source.
                        let (lo, hi) = match callee_sym {
                            "llvm.aarch64.neon.uqxtn.v8i8" => (0i128, 255i128),
                            "llvm.aarch64.neon.sqxtn.v8i8" => (-128i128, 127i128),
                            "llvm.aarch64.neon.sqxtun.v8i8" => (0i128, 255i128),
                            _ => unreachable!(),
                        };
                        let a_ptr = operand_place_address(cx, fb, env, &a.node)?;
                        let we = TIRTy::I32;
                        let hic = fb.iconst(we.clone(), hi);
                        let loc = fb.iconst(we.clone(), lo);
                        for i in 0..sc {
                            let soff = i * sw;
                            let sa = if soff == 0 { a_ptr } else { gep_byte_offset(fb, a_ptr, soff) };
                            let v = fb.load(se.clone(), sa);
                            let vw = int_cast(fb, v, &se, &we);
                            let over = fb.icmp(ICmpOp::Sgt, we.clone(), vw, hic);
                            let v1 = fb.select(we.clone(), over, hic, vw);
                            let under = fb.icmp(ICmpOp::Slt, we.clone(), v1, loc);
                            let v2 = fb.select(we.clone(), under, loc, v1);
                            let r = int_cast(fb, v2, &we, &de);
                            let doff = i * dw;
                            let dd = if doff == 0 { dst_ptr } else { gep_byte_offset(fb, dst_ptr, doff) };
                            fb.store(de.clone(), dd, r);
                        }
                    }
                    let edge = tc.edge_args(env, ret_bb)?;
                    fb.br(tc.target_block(ret_bb), edge);
                    return Ok(());
                }
                // RUNG (NEON shift-by-vector): `vshlq_u32` (and `.v*i*` siblings)
                // call the LLVM FOREIGN intrinsic `llvm.aarch64.neon.ushl.v4i32`
                // (per-lane logical shift by the CORRESPONDING lane of a SIGNED
                // shift-count vector). A foreign item, not a rustc `simd_*`, so it
                // would dangle as an extern leaf (LINKFAIL). NEON `ushl` semantics:
                // the count is a SIGNED value — positive shifts LEFT, negative
                // shifts RIGHT (logical), and a magnitude >= the element bit width
                // yields 0. Lowered per-lane INLINE through `Shl`/`LShr` + `Select`
                // (the corpus uses non-negative in-range counts; the negative /
                // out-of-range arms are modelled too so it is generally correct).
                if callee_sym.starts_with("llvm.aarch64.neon.ushl.") {
                    let ret_bb = target.ok_or_else(|| {
                        format!("neon {callee_sym}: call must have a return target")
                    })?;
                    let [a, b] = &args[..] else {
                        return Err(format!("neon {callee_sym}: expected exactly two args"));
                    };
                    let (se, sc) =
                        simd_int_vector_lanes(cx, operand_concrete_ty(cx, &a.node))
                            .ok_or_else(|| {
                                format!("neon {callee_sym}: non-int-vector data operand")
                            })?;
                    let (be, _bc) =
                        simd_int_vector_lanes(cx, operand_concrete_ty(cx, &b.node))
                            .ok_or_else(|| {
                                format!("neon {callee_sym}: non-int-vector shift operand")
                            })?;
                    let w = int_lane_size(&se);
                    let bits = (w * 8) as i128;
                    let a_ptr = operand_place_address(cx, fb, env, &a.node)?;
                    let b_ptr = operand_place_address(cx, fb, env, &b.node)?;
                    let dst_ptr = place_address(cx, fb, env, destination)?;
                    for i in 0..sc {
                        let off = i * w;
                        let aa = if off == 0 { a_ptr } else { gep_byte_offset(fb, a_ptr, off) };
                        let bb = if off == 0 { b_ptr } else { gep_byte_offset(fb, b_ptr, off) };
                        let av = fb.load(se.clone(), aa);
                        let cnt = fb.load(be.clone(), bb);
                        // Sign-extend the count to i32 for the direction/range logic.
                        let cnt_i = int_cast(fb, cnt, &be, &TIRTy::I32);
                        let zero32 = fb.iconst(TIRTy::I32, 0);
                        let is_left = fb.icmp(ICmpOp::Sge, TIRTy::I32, cnt_i, zero32);
                        let negc = fb.binop(BinOp::Sub, TIRTy::I32, zero32, cnt_i);
                        let mag = fb.select(TIRTy::I32, is_left, cnt_i, negc); // |cnt|
                        let bw = fb.iconst(TIRTy::I32, bits);
                        let in_range = fb.icmp(ICmpOp::Slt, TIRTy::I32, mag, bw);
                        // Clamp the shift magnitude below the bit width so the
                        // `Shl`/`LShr` never has an out-of-range (poison) amount;
                        // out-of-range lanes select 0 anyway.
                        let bwm1 = fb.iconst(TIRTy::I32, bits - 1);
                        let clamped = fb.select(TIRTy::I32, in_range, mag, bwm1);
                        let amt = int_cast(fb, clamped, &TIRTy::I32, &se);
                        let left = fb.binop(BinOp::Shl, se.clone(), av, amt);
                        let right = fb.binop(BinOp::LShr, se.clone(), av, amt);
                        let picked = fb.select(se.clone(), is_left, left, right);
                        let zse = fb.iconst(se.clone(), 0);
                        let res = fb.select(se.clone(), in_range, picked, zse);
                        let dd = if off == 0 { dst_ptr } else { gep_byte_offset(fb, dst_ptr, off) };
                        fb.store(se.clone(), dd, res);
                    }
                    let edge = tc.edge_args(env, ret_bb)?;
                    fb.br(tc.target_block(ret_bb), edge);
                    return Ok(());
                }
                // RUNG (NEON float min/max): `vminq_f32`/`vmaxq_f32` call the LLVM
                // FOREIGN intrinsics `llvm.aarch64.neon.fmin.v4f32` /
                // `llvm.aarch64.neon.fmax.v4f32` — per-lane IEEE min/max
                // (`fmin`/`fmax.4s`). Lowered per-lane INLINE through trust-ir's
                // `BinOp::FMin`/`FMax`, which trust-cg codegens directly.
                if callee_sym.starts_with("llvm.aarch64.neon.fmin.")
                    || callee_sym.starts_with("llvm.aarch64.neon.fmax.")
                {
                    let ret_bb = target.ok_or_else(|| {
                        format!("neon {callee_sym}: call must have a return target")
                    })?;
                    let [a, b] = &args[..] else {
                        return Err(format!("neon {callee_sym}: expected exactly two args"));
                    };
                    let (se, sc) =
                        simd_vector_lanes_any(cx, operand_concrete_ty(cx, &a.node))
                            .ok_or_else(|| {
                                format!("neon {callee_sym}: non-SIMD-vector operand")
                            })?;
                    if !is_float_tir(&se) {
                        return Err(format!(
                            "neon {callee_sym}: non-float lane type {se:?}"
                        ));
                    }
                    let op = if callee_sym.starts_with("llvm.aarch64.neon.fmin.") {
                        BinOp::FMin
                    } else {
                        BinOp::FMax
                    };
                    let w = simd_lane_bytes(&se);
                    let a_ptr = operand_place_address(cx, fb, env, &a.node)?;
                    let b_ptr = operand_place_address(cx, fb, env, &b.node)?;
                    let dst_ptr = place_address(cx, fb, env, destination)?;
                    for i in 0..sc {
                        let off = i * w;
                        let aa = if off == 0 { a_ptr } else { gep_byte_offset(fb, a_ptr, off) };
                        let bb = if off == 0 { b_ptr } else { gep_byte_offset(fb, b_ptr, off) };
                        let va = fb.load(se.clone(), aa);
                        let vb = fb.load(se.clone(), bb);
                        let r = fb.binop(op, se.clone(), va, vb);
                        let dd = if off == 0 { dst_ptr } else { gep_byte_offset(fb, dst_ptr, off) };
                        fb.store(se.clone(), dd, r);
                    }
                    let edge = tc.edge_args(env, ret_bb)?;
                    fb.br(tc.target_block(ret_bb), edge);
                    return Ok(());
                }
                // RUNG (NEON float->int saturating convert): `vcvtq_s32_f32` calls
                // the LLVM FOREIGN intrinsic `llvm.fptosi.sat.v4i32.v4f32` (and the
                // unsigned `fptoui.sat` sibling) — the per-lane Rust-`as` SATURATING
                // float->int convert (truncate toward zero, out-of-range clamps to
                // the int's min/max, NaN -> 0). Lowered per-lane INLINE through
                // `simd_lane_cast` (`FPToSISat`/`FPToUISat`), which trust-cg
                // codegens as aarch64 `fcvtzs`/`fcvtzu` (saturating by definition).
                if callee_sym.starts_with("llvm.fptosi.sat.")
                    || callee_sym.starts_with("llvm.fptoui.sat.")
                {
                    let ret_bb = target.ok_or_else(|| {
                        format!("neon {callee_sym}: call must have a return target")
                    })?;
                    let [a] = &args[..] else {
                        return Err(format!("neon {callee_sym}: expected exactly one arg"));
                    };
                    let (se, sc) =
                        simd_vector_lanes_any(cx, operand_concrete_ty(cx, &a.node))
                            .ok_or_else(|| {
                                format!("neon {callee_sym}: non-SIMD-vector source")
                            })?;
                    let (de, dc) =
                        simd_vector_lanes_any(cx, cx.place_concrete_ty(destination))
                            .ok_or_else(|| {
                                format!("neon {callee_sym}: non-SIMD-vector destination")
                            })?;
                    if sc != dc {
                        return Err(format!(
                            "neon {callee_sym}: lane count mismatch {sc} != {dc}"
                        ));
                    }
                    let sw = simd_lane_bytes(&se);
                    let dw = simd_lane_bytes(&de);
                    let src_ptr = operand_place_address(cx, fb, env, &a.node)?;
                    let dst_ptr = place_address(cx, fb, env, destination)?;
                    for i in 0..sc {
                        let sa = if i == 0 { src_ptr } else { gep_byte_offset(fb, src_ptr, i * sw) };
                        let v = fb.load(se.clone(), sa);
                        let c = simd_lane_cast(fb, v, &se, &de);
                        let da = if i == 0 { dst_ptr } else { gep_byte_offset(fb, dst_ptr, i * dw) };
                        fb.store(de.clone(), da, c);
                    }
                    let edge = tc.edge_args(env, ret_bb)?;
                    fb.br(tc.target_block(ret_bb), edge);
                    return Ok(());
                }
                // RUNG (NEON deinterleave load): `vld2q_u8` calls the LLVM FOREIGN
                // intrinsic `llvm.aarch64.neon.ld2.v16i8.p0` — read `2*N` elements
                // from one pointer and split them into two N-lane vectors (even
                // elements -> `.0`, odd -> `.1`), the `uint8x16x2_t` result. The
                // destination is the 32-byte tuple struct laid out `[vec0][vec1]`
                // contiguously (`#[repr(C)]`), so it is written per-lane directly —
                // avoiding the by-value 32-byte aggregate path entirely.
                if callee_sym.starts_with("llvm.aarch64.neon.ld2.") {
                    let ret_bb = target.ok_or_else(|| {
                        format!("neon {callee_sym}: call must have a return target")
                    })?;
                    let [p] = &args[..] else {
                        return Err(format!("neon {callee_sym}: expected exactly one arg"));
                    };
                    let (n_lanes, elem_bytes) = parse_vni_shape(callee_sym).ok_or_else(|| {
                        format!("neon {callee_sym}: cannot parse lane shape")
                    })?;
                    let lane_ty = match elem_bytes {
                        1 => TIRTy::U8,
                        2 => TIRTy::U16,
                        4 => TIRTy::U32,
                        8 => TIRTy::U64,
                        _ => {
                            return Err(format!(
                                "neon {callee_sym}: unsupported element width {elem_bytes}"
                            ))
                        }
                    };
                    let (src_v, src_tir) = lower_operand(cx, fb, env, &p.node)?;
                    if !matches!(src_tir, TIRTy::Ptr) {
                        return Err(format!(
                            "neon {callee_sym}: source is not a thin pointer ({src_tir:?})"
                        ));
                    }
                    let dst_ptr = place_address(cx, fb, env, destination)?;
                    let vec_bytes = n_lanes * elem_bytes;
                    for i in 0..n_lanes {
                        // `.0[i] = src[2i]`, `.1[i] = src[2i+1]` (deinterleave).
                        let s0off = (2 * i) * elem_bytes;
                        let s1off = (2 * i + 1) * elem_bytes;
                        let s0 = if s0off == 0 { src_v } else { gep_byte_offset(fb, src_v, s0off) };
                        let s1 = gep_byte_offset(fb, src_v, s1off);
                        let b0 = fb.load(lane_ty.clone(), s0);
                        let b1 = fb.load(lane_ty.clone(), s1);
                        let d0off = i * elem_bytes;
                        let d1off = vec_bytes + i * elem_bytes;
                        let d0 = if d0off == 0 { dst_ptr } else { gep_byte_offset(fb, dst_ptr, d0off) };
                        let d1 = gep_byte_offset(fb, dst_ptr, d1off);
                        fb.store(lane_ty.clone(), d0, b0);
                        fb.store(lane_ty.clone(), d1, b1);
                    }
                    let edge = tc.edge_args(env, ret_bb)?;
                    fb.br(tc.target_block(ret_bb), edge);
                    return Ok(());
                }
                if let Some(idef) = cx.tcx.intrinsic(callee.def_id()) {
                    let iname = idef.name.as_str();
                    // UNWIND lane: `core::intrinsics::catch_unwind` — the inline
                    // `__rust_try` expansion (rustc `codegen_gnu_try`, direct-call
                    // form). Invoke `do_call(data)`; a normal return yields
                    // `false`; the CATCH-ALL landing pad (`catch 0`) calls
                    // `do_catch(data, exn)` then yields `true`. The pre-pass
                    // resolved + declared both DIRECT callees (`tc.catch_expand`).
                    if iname == "catch_unwind" && tc.eh {
                        let (try_fid, catch_fid) = tc.catch_expand.ok_or_else(|| {
                            "catch_unwind: expansion callees not pre-declared (pre-pass bug)"
                                .to_string()
                        })?;
                        let ret_bb = target.ok_or_else(|| {
                            "catch_unwind: call must have a return target".to_string()
                        })?;
                        let [_try_op, data_op, _catch_op] = &args[..] else {
                            return Err(format!(
                                "catch_unwind: expected 3 args, got {}",
                                args.len()
                            ));
                        };
                        let (data_v, dt) = lower_operand(cx, fb, env, &data_op.node)?;
                        if !matches!(dt, TIRTy::Ptr) {
                            return Err(format!(
                                "catch_unwind: data operand is not a thin pointer ({dt:?})"
                            ));
                        }
                        let norm_blk = fb.create_block();
                        let pad_blk = fb.create_block();
                        fb.invoke_void(try_fid, vec![data_v], norm_blk, vec![], pad_blk);
                        // Normal return: the intrinsic yields `false` (no unwind).
                        fb.switch_to_block(norm_blk);
                        let f = fb.bool_const(false);
                        bind_call_destination(cx, fb, env, destination, f)?;
                        let edge_n = tc.edge_args(env, ret_bb)?;
                        fb.br(tc.target_block(ret_bb), edge_n);
                        // Catch-all pad: `do_catch(data, exn)`, then yield `true`.
                        fb.switch_to_block(pad_blk);
                        let (exn, _sel) = fb.landingpad(false, vec![0]);
                        fb.call_void(catch_fid, vec![data_v, exn]);
                        let t = fb.bool_const(true);
                        bind_call_destination(cx, fb, env, destination, t)?;
                        let edge_c = tc.edge_args(env, ret_bb)?;
                        fb.br(tc.target_block(ret_bb), edge_c);
                        return Ok(());
                    }
                    // UNWIND lane, `#[track_caller]`: the `caller_location`
                    // intrinsic — INLINE `get_caller_location` (rustc parity:
                    // the location is computed against the call's `fn_span`).
                    // A track_caller body forwards its hidden param; a plain
                    // body materializes its own span's Location const.
                    if iname == "caller_location" && tc.caller_location_inline {
                        let ret_bb = target.ok_or_else(|| {
                            "caller_location: call must have a return target".to_string()
                        })?;
                        let si = rustc_middle::mir::SourceInfo {
                            span: *fn_span,
                            ..source_info
                        };
                        let loc = get_caller_location(cx, fb, si)?;
                        bind_call_destination(cx, fb, env, destination, loc)?;
                        let edge = tc.edge_args(env, ret_bb)?;
                        fb.br(tc.target_block(ret_bb), edge);
                        return Ok(());
                    }
                    // THREADS: the FULL first-class atomic set. Every atomic
                    // intrinsic the std thread/lock/Arc machinery monomorphizes
                    // lowers THROUGH trust-ir's native atomics (AtomicLoad /
                    // AtomicStore / AtomicRMW / CmpXchg / Fence) — never as an
                    // opaque extern leaf. A POINTER-typed `T` (`AtomicPtr` CAS
                    // in the rwlock queue) computes in the U64 lane, bridged
                    // with PtrToInt/IntToPtr at the edges.
                    let rmw_op = match iname {
                        "atomic_xadd" => Some(AtomicRMWOp::Add),
                        "atomic_xsub" => Some(AtomicRMWOp::Sub),
                        "atomic_xchg" => Some(AtomicRMWOp::Xchg),
                        "atomic_and" => Some(AtomicRMWOp::And),
                        "atomic_or" => Some(AtomicRMWOp::Or),
                        "atomic_xor" => Some(AtomicRMWOp::Xor),
                        "atomic_max" => Some(AtomicRMWOp::Max),
                        "atomic_min" => Some(AtomicRMWOp::Min),
                        "atomic_umax" => Some(AtomicRMWOp::UMax),
                        "atomic_umin" => Some(AtomicRMWOp::UMin),
                        _ => None,
                    };
                    let is_atomic = rmw_op.is_some()
                        || matches!(
                            iname,
                            "atomic_fence"
                                | "atomic_singlethreadfence"
                                | "atomic_load"
                                | "atomic_store"
                                | "atomic_cxchg"
                                | "atomic_cxchgweak"
                                | "atomic_nand"
                        );
                    if is_atomic {
                        let orderings = atomic_orderings_from_args(callee.args)?;
                        let ordering = orderings[0];
                        let ret_bb = target.ok_or_else(|| {
                            "atomic intrinsic: call must have a return target".to_string()
                        })?;
                        // The intrinsic's `T` (the atomic cell type) and its
                        // integer compute lane. Fence has no `T`.
                        let t_arg = callee.args.iter().find_map(|a| a.as_type());
                        let lane_info = match t_arg {
                            Some(t) if iname != "atomic_fence"
                                && iname != "atomic_singlethreadfence" =>
                            {
                                Some(atomic_int_lane(cx, t)?)
                            }
                            _ => None,
                        };
                        // Coerce a lowered operand into the integer lane.
                        let to_lane = |fb: &mut trust_ir_build::FunctionBuilder<'_>,
                                       v: trust_ir::ValueId,
                                       vty: &TIRTy,
                                       lane: &TIRTy|
                         -> trust_ir::ValueId {
                            if matches!(vty, TIRTy::Ptr) {
                                fb.cast(CastOp::PtrToInt, TIRTy::Ptr, lane.clone(), v)
                            } else {
                                v
                            }
                        };
                        // Bridge a lane-typed result back to the DESTINATION's
                        // pointer model when `T` (or the dest local) is a pointer.
                        let from_lane = |fb: &mut trust_ir_build::FunctionBuilder<'_>,
                                         v: trust_ir::ValueId,
                                         lane: &TIRTy,
                                         is_ptr: bool|
                         -> trust_ir::ValueId {
                            if is_ptr {
                                fb.cast(CastOp::IntToPtr, lane.clone(), TIRTy::Ptr, v)
                            } else {
                                v
                            }
                        };
                        match iname {
                            "atomic_fence" | "atomic_singlethreadfence" => {
                                fb.fence(ordering);
                            }
                            "atomic_load" => {
                                let [src] = &args[..] else {
                                    return Err(
                                        "atomic_load: expected exactly one arg".to_string()
                                    );
                                };
                                let (ptr, pty) = lower_operand(cx, fb, env, &src.node)?;
                                if !matches!(pty, TIRTy::Ptr) {
                                    return Err(format!(
                                        "atomic_load: src is not a pointer ({pty:?})"
                                    ));
                                }
                                let (lane, is_ptr) =
                                    lane_info.ok_or_else(|| "atomic_load: no T".to_string())?;
                                let v = fb.atomic_load(lane.clone(), ptr, ordering);
                                let v = from_lane(fb, v, &lane, is_ptr);
                                bind_call_destination(cx, fb, env, destination, v)?;
                            }
                            "atomic_store" => {
                                let [dst, val] = &args[..] else {
                                    return Err(
                                        "atomic_store: expected exactly two args".to_string()
                                    );
                                };
                                let (ptr, pty) = lower_operand(cx, fb, env, &dst.node)?;
                                if !matches!(pty, TIRTy::Ptr) {
                                    return Err(format!(
                                        "atomic_store: dst is not a pointer ({pty:?})"
                                    ));
                                }
                                let (v, vty) = lower_operand(cx, fb, env, &val.node)?;
                                let (lane, _is_ptr) =
                                    lane_info.ok_or_else(|| "atomic_store: no T".to_string())?;
                                let v = to_lane(fb, v, &vty, &lane);
                                fb.atomic_store(lane, ptr, v, ordering);
                            }
                            "atomic_cxchg" | "atomic_cxchgweak" => {
                                // `atomic_cxchg{,weak}::<T, SUCC, FAIL>(dst: *mut T,
                                // expected: T, desired: T) -> (T, bool)`. TrustIr
                                // `CmpXchg` IS this operation (a weak CAS may spuriously
                                // fail; the strong instruction is a REFINEMENT of the
                                // weak contract — every caller loops).
                                let [dst, expected, desired] = &args[..] else {
                                    return Err(
                                        "atomic_cxchg: expected exactly three args".to_string()
                                    );
                                };
                                let failure =
                                    orderings.get(1).copied().unwrap_or(ordering);
                                let (ptr, pty) = lower_operand(cx, fb, env, &dst.node)?;
                                if !matches!(pty, TIRTy::Ptr) {
                                    return Err(format!(
                                        "atomic_cxchg: dst is not a pointer ({pty:?})"
                                    ));
                                }
                                let (exp, ety) = lower_operand(cx, fb, env, &expected.node)?;
                                let (des, dty) = lower_operand(cx, fb, env, &desired.node)?;
                                let (lane, is_ptr) =
                                    lane_info.ok_or_else(|| "atomic_cxchg: no T".to_string())?;
                                let exp = to_lane(fb, exp, &ety, &lane);
                                let des = to_lane(fb, des, &dty, &lane);
                                let (old, ok) = fb.cmpxchg(
                                    lane.clone(),
                                    ptr,
                                    exp,
                                    des,
                                    ordering,
                                    failure,
                                );
                                // Bind the `(T, bool)` tuple destination: store the
                                // old value at field 0 and the success flag at field
                                // 1's layout offset.
                                let dest_cty = cx.place_concrete_ty(destination);
                                let dl = cx
                                    .tcx
                                    .layout_of(
                                        ty::TypingEnv::fully_monomorphized()
                                            .as_query_input(dest_cty),
                                    )
                                    .map_err(|e| {
                                        format!("atomic_cxchg dest layout_of failed: {e:?}")
                                    })?;
                                let flag_off = dl.fields.offset(1).bytes();
                                let dst_addr = place_address(cx, fb, env, destination)?;
                                let old_v = from_lane(fb, old, &lane, is_ptr);
                                if is_ptr {
                                    fb.store(TIRTy::Ptr, dst_addr, old_v);
                                } else {
                                    fb.store(lane.clone(), dst_addr, old_v);
                                }
                                let flag_addr = gep_byte_offset(fb, dst_addr, flag_off);
                                fb.store(TIRTy::Bool, flag_addr, ok);
                            }
                            "atomic_nand" => {
                                // `atomic_nand::<T, U, ORD>(dst: *mut T, src: U) -> T`
                                // — atomically `*dst = !(*dst & src)`, returning the
                                // OLD value. TrustIr has no Nand `AtomicRMWOp` (and a
                                // format change is out of scope), so lower the
                                // intrinsic's EXACT contract as the standard CmpXchg
                                // retry loop over existing verified ops:
                                //   old0 = AtomicLoad(Relaxed) ptr
                                //   loop(old): new = Not(And(old, val))
                                //     (cur, ok) = CmpXchg(ptr, old, new, ORD, fail)
                                //     ok ? done : loop(cur)
                                // The bound result is the SUCCESSFUL iteration's
                                // CmpXchg-read `cur` (== the pre-update cell value ==
                                // the `expected` it matched). The seed load's ordering
                                // is immaterial to the result (a stale seed just
                                // retries); Relaxed matches LLVM's AtomicExpand
                                // expansion of an unsupported RMW.
                                let [dst, src] = &args[..] else {
                                    return Err(
                                        "atomic_nand: expected exactly two args"
                                            .to_string(),
                                    );
                                };
                                let (ptr, pty) = lower_operand(cx, fb, env, &dst.node)?;
                                if !matches!(pty, TIRTy::Ptr) {
                                    return Err(format!(
                                        "atomic_nand: dst is not a pointer ({pty:?})"
                                    ));
                                }
                                let (val, vty) = lower_operand(cx, fb, env, &src.node)?;
                                let (lane, is_ptr) = lane_info
                                    .ok_or_else(|| "atomic_nand: no T".to_string())?;
                                if is_ptr {
                                    // No `AtomicPtr::fetch_nand` exists in Rust; a
                                    // pointer-typed `T` here is shape drift.
                                    return Err(
                                        "atomic_nand: pointer-typed T is not a Rust \
                                         shape"
                                            .to_string(),
                                    );
                                }
                                let val = to_lane(fb, val, &vty, &lane);
                                // CmpXchg FAILURE ordering: the strongest
                                // non-release ordering not above the success one
                                // (LLVM getStrongestFailureOrdering).
                                let failure = match ordering {
                                    TIROrdering::Release => TIROrdering::Relaxed,
                                    TIROrdering::AcqRel => TIROrdering::Acquire,
                                    o => o,
                                };
                                let old0 =
                                    fb.atomic_load(lane.clone(), ptr, TIROrdering::Relaxed);
                                let retry = fb.create_block();
                                let done = fb.create_block();
                                let old = fb.add_block_param(retry, lane.clone());
                                fb.br(retry, vec![old0]);
                                fb.switch_to_block(retry);
                                let anded = fb.binop(BinOp::And, lane.clone(), old, val);
                                let newv = fb.unop(UnOp::Not, lane.clone(), anded);
                                let (cur, ok) = fb.cmpxchg(
                                    lane.clone(),
                                    ptr,
                                    old,
                                    newv,
                                    ordering,
                                    failure,
                                );
                                fb.condbr(ok, done, vec![], retry, vec![cur]);
                                // `cur` dominates `done` (its sole predecessor is
                                // the loop block), so it binds directly.
                                fb.switch_to_block(done);
                                bind_call_destination(cx, fb, env, destination, cur)?;
                            }
                            _ => {
                                // An atomic RMW: `atomic_<op>::<T, U, ORD>(dst: *mut T,
                                // src: U) -> T` — atomically `*dst = op(*dst, src)`,
                                // returning the OLD value. Every ordering — including a
                                // stand-alone `Release` (the classic Arc
                                // `fetch_sub(1, Release)`) — lowers BYTE-FAITHFULLY:
                                // trust-cg's aarch64 RMW isel emits the release-only
                                // LSE opcode family.
                                let op = rmw_op.expect("is_atomic admits only known ops");
                                let [dst, src] = &args[..] else {
                                    return Err(
                                        "atomic RMW intrinsic: expected exactly two args"
                                            .to_string(),
                                    );
                                };
                                let (ptr, pty) = lower_operand(cx, fb, env, &dst.node)?;
                                if !matches!(pty, TIRTy::Ptr) {
                                    return Err(format!(
                                        "atomic RMW intrinsic: dst is not a pointer ({pty:?})"
                                    ));
                                }
                                let (val, vty) = lower_operand(cx, fb, env, &src.node)?;
                                let (lane, is_ptr) =
                                    lane_info.ok_or_else(|| "atomic RMW: no T".to_string())?;
                                let val = to_lane(fb, val, &vty, &lane);
                                let old = fb.atomic_rmw(op, lane.clone(), ptr, val, ordering);
                                // Bridge back to the destination's pointer model
                                // (`AtomicPtr::fetch_byte_sub` in the rwlock queue).
                                let dest_cty = cx.place_concrete_ty(destination);
                                let dest_is_ptr = is_ptr
                                    || matches!(dest_cty.kind(), ty::RawPtr(..) | ty::Ref(..));
                                let old = if dest_is_ptr {
                                    from_lane(fb, old, &lane, true)
                                } else {
                                    old
                                };
                                bind_call_destination(cx, fb, env, destination, old)?;
                            }
                        }
                        let edge = tc.edge_args(env, ret_bb)?;
                        fb.br(tc.target_block(ret_bb), edge);
                        return Ok(());
                    }
                    // THREADS: `ptr_offset_from{,_unsigned}::<T>(a, b)` — the
                    // element-count distance between two pointers into one
                    // allocation: `(a as usize - b as usize) / size_of::<T>()`
                    // (exact division per the intrinsic's precondition). Pure
                    // pointer arithmetic — lower it natively instead of
                    // leaving an extern leaf per monomorphization
                    // (`IntoIter<JoinHandle>::size_hint`, `Vec<Box<dyn FnOnce>>`
                    // drops on the spawn-hook path, ...).
                    if matches!(iname, "ptr_offset_from" | "ptr_offset_from_unsigned") {
                        let [a, b] = &args[..] else {
                            return Err(
                                "ptr_offset_from: expected exactly two args".to_string()
                            );
                        };
                        let t_arg = callee
                            .args
                            .iter()
                            .find_map(|arg| arg.as_type())
                            .ok_or_else(|| "ptr_offset_from: no T".to_string())?;
                        let (size, _align) = memory_layout_size_align(cx, t_arg)?;
                        let ret_bb = target.ok_or_else(|| {
                            "ptr_offset_from: call must have a return target".to_string()
                        })?;
                        let signed = iname == "ptr_offset_from";
                        let lane = if signed { TIRTy::I64 } else { TIRTy::U64 };
                        let (av, aty) = lower_operand(cx, fb, env, &a.node)?;
                        let (bv, bty) = lower_operand(cx, fb, env, &b.node)?;
                        let ai = if matches!(aty, TIRTy::Ptr) {
                            fb.cast(CastOp::PtrToInt, TIRTy::Ptr, lane.clone(), av)
                        } else {
                            av
                        };
                        let bi = if matches!(bty, TIRTy::Ptr) {
                            fb.cast(CastOp::PtrToInt, TIRTy::Ptr, lane.clone(), bv)
                        } else {
                            bv
                        };
                        let diff = fb.binop(BinOp::Sub, lane.clone(), ai, bi);
                        let v = if size > 1 {
                            let s = fb.iconst(lane.clone(), size as i128);
                            fb.binop(
                                if signed { BinOp::SDiv } else { BinOp::UDiv },
                                lane.clone(),
                                diff,
                                s,
                            )
                        } else {
                            diff
                        };
                        bind_call_destination(cx, fb, env, destination, v)?;
                        let edge = tc.edge_args(env, ret_bb)?;
                        fb.br(tc.target_block(ret_bb), edge);
                        return Ok(());
                    }
                    // `arith_offset::<T>(ptr, count)` — Rust's WRAPPING pointer
                    // offset (`ptr.wrapping_offset`): `ptr + count * size_of::<T>()`
                    // with two's-complement wraparound, negative counts valid.
                    // A trust-ir GEP cannot express this (negative index = format
                    // UB), but the C-raw-pointer path can: PtrToInt -> modular
                    // I64 multiply/add (trust-ir Add IS modular) -> IntToPtr.
                    // Exposed by the stable-wrapper inlining: the new smallsort's
                    // `bidirectional_merge`/`merge_down` step pointers DOWN.
                    // ZST strides change the address by zero bytes: return the
                    // pointer unchanged.
                    if iname == "arith_offset" {
                        if let ([p, c], Some(ret_bb)) = (&args[..], target) {
                            let elem = callee.args.type_at(0);
                            let (stride, _size, _align) = iter_elem_layout(cx, elem)?;
                            let (pv, pty) = lower_operand(cx, fb, env, &p.node)?;
                            let (cv, cty) = lower_operand(cx, fb, env, &c.node)?;
                            if matches!(pty, TIRTy::Ptr) {
                                let v = if stride == 0 {
                                    pv
                                } else {
                                    let idx = if matches!(cty, TIRTy::I64) {
                                        cv
                                    } else {
                                        coerce_int_width(fb, cv, &cty, &TIRTy::I64)?
                                    };
                                    let addr =
                                        fb.cast(CastOp::PtrToInt, TIRTy::Ptr, TIRTy::I64, pv);
                                    let stride_c = fb.iconst(TIRTy::I64, stride as i128);
                                    let byte_off =
                                        fb.binop(BinOp::Mul, TIRTy::I64, idx, stride_c);
                                    let addr2 =
                                        fb.binop(BinOp::Add, TIRTy::I64, addr, byte_off);
                                    fb.cast(CastOp::IntToPtr, TIRTy::I64, TIRTy::Ptr, addr2)
                                };
                                bind_call_destination(cx, fb, env, destination, v)?;
                                let edge = tc.edge_args(env, *ret_bb)?;
                                fb.br(tc.target_block(*ret_bb), edge);
                                return Ok(());
                            }
                        }
                    }
                    // `saturating_add/sub::<T>(a, b)` for UNSIGNED lanes: clamp
                    // instead of wrap. Historically these leaked as extern
                    // leaves satisfied by 32-bit harness shims — silently
                    // TRUNCATING u64 monos (fc_bits: saturating_sub<u64>
                    // returned 0 forever). Lower natively: add = AddOverflow +
                    // Select(MAX); sub = Ult + Select(0, a-b). Signed monos
                    // (different clamp poles) fall through to the extern
                    // emission (fail-closed).
                    if matches!(iname, "saturating_add" | "saturating_sub") {
                        if let ([a, b], Some(ret_bb)) = (&args[..], target) {
                            let (av, at) = lower_operand(cx, fb, env, &a.node)?;
                            let (bv, bt) = lower_operand(cx, fb, env, &b.node)?;
                            let max: Option<i128> = match at {
                                TIRTy::U8 => Some(0xff),
                                TIRTy::U16 => Some(0xffff),
                                TIRTy::U32 => Some(0xffff_ffff),
                                TIRTy::U64 => Some(u64::MAX as i128),
                                _ => None,
                            };
                            if at == bt {
                                if let Some(max) = max {
                                    let lane = at.clone();
                                    let v = if iname == "saturating_add" {
                                        let (s, o) = fb.overflow(
                                            OverflowOp::AddOverflow,
                                            lane.clone(),
                                            av,
                                            bv,
                                        );
                                        let mx = fb.iconst(lane.clone(), max);
                                        fb.select(lane.clone(), o, mx, s)
                                    } else {
                                        let lt = fb.icmp(ICmpOp::Ult, lane.clone(), av, bv);
                                        let diff = fb.binop(BinOp::Sub, lane.clone(), av, bv);
                                        let zero = fb.iconst(lane.clone(), 0);
                                        fb.select(lane.clone(), lt, zero, diff)
                                    };
                                    bind_call_destination(cx, fb, env, destination, v)?;
                                    let edge = tc.edge_args(env, *ret_bb)?;
                                    fb.br(tc.target_block(*ret_bb), edge);
                                    return Ok(());
                                }
                            }
                        }
                    }
                    // `bswap::<T>(x)` / `bitreverse::<T>(x)` (swap_bytes /
                    // reverse_bits): no native trust-ir UnOp exists, so expand
                    // the classic masked-swap ladder inline — pairwise bit
                    // swap (bitreverse only), then nibble/byte/half/word swaps.
                    // Pure And/Or/Shl/LShr over the operand's own lane, so it
                    // works for signed and unsigned monos alike; trust-cg's
                    // bitreverse idiom recognizer can fuse the ladder back to
                    // RBIT/REV. u8 bswap is the identity. Fail closed: non-int
                    // lanes fall through to the extern emission.
                    if matches!(iname, "bswap" | "bitreverse") {
                        if let ([x], Some(ret_bb)) = (&args[..], target) {
                            let (xv, xt) = lower_operand(cx, fb, env, &x.node)?;
                            let width: u32 = match xt {
                                TIRTy::U8 | TIRTy::I8 => 8,
                                TIRTy::U16 | TIRTy::I16 => 16,
                                TIRTy::U32 | TIRTy::I32 => 32,
                                TIRTy::U64 | TIRTy::I64 => 64,
                                _ => 0,
                            };
                            if width != 0 {
                                let lane = xt.clone();
                                let mask_to_width = |m: u128| -> i128 {
                                    (m & (u128::MAX >> (128 - width))) as i128
                                };
                                let mut steps: Vec<(i128, i128)> = Vec::new();
                                if iname == "bitreverse" {
                                    steps.push((mask_to_width(0x5555_5555_5555_5555_5555_5555_5555_5555), 1));
                                    steps.push((mask_to_width(0x3333_3333_3333_3333_3333_3333_3333_3333), 2));
                                    steps.push((mask_to_width(0x0f0f_0f0f_0f0f_0f0f_0f0f_0f0f_0f0f_0f0f), 4));
                                }
                                let mut half = 8;
                                while half < width {
                                    // e.g. 64-bit: (0x00FF.., 8), (0x0000FFFF.., 16), (0xFFFFFFFF, 32)
                                    let unit = u128::MAX / ((1u128 << half.min(127)) + 1);
                                    steps.push((mask_to_width(unit), half as i128));
                                    half *= 2;
                                }
                                let mut v = xv;
                                for (m, s) in steps {
                                    let mc = fb.iconst(lane.clone(), m);
                                    let sc = fb.iconst(lane.clone(), s);
                                    let lo = fb.binop(BinOp::And, lane.clone(), v, mc);
                                    let lo = fb.binop(BinOp::Shl, lane.clone(), lo, sc);
                                    let hi = fb.binop(BinOp::LShr, lane.clone(), v, sc);
                                    let hi = fb.binop(BinOp::And, lane.clone(), hi, mc);
                                    v = fb.binop(BinOp::Or, lane.clone(), lo, hi);
                                }
                                bind_call_destination(cx, fb, env, destination, v)?;
                                let edge = tc.edge_args(env, *ret_bb)?;
                                fb.br(tc.target_block(*ret_bb), edge);
                                return Ok(());
                            }
                        }
                    }
                    // `disjoint_bitor::<T>(a, b)`: bitwise OR whose operands the
                    // caller PROMISES share no set bits — the disjointness is a
                    // UB claim enabling backend add/or fusion; plain `Or` is a
                    // sound refinement. Used by the float formatter's big-int
                    // core. Fail closed: non-matching lanes fall through to the
                    // extern emission.
                    if iname == "disjoint_bitor" {
                        if let ([a, b], Some(ret_bb)) = (&args[..], target) {
                            let (av, at) = lower_operand(cx, fb, env, &a.node)?;
                            let (bv, bt) = lower_operand(cx, fb, env, &b.node)?;
                            let lane_ok = at == bt
                                && matches!(
                                    at,
                                    TIRTy::Bool
                                        | TIRTy::U8
                                        | TIRTy::U16
                                        | TIRTy::U32
                                        | TIRTy::U64
                                        | TIRTy::I8
                                        | TIRTy::I16
                                        | TIRTy::I32
                                        | TIRTy::I64
                                );
                            if lane_ok {
                                let v = fb.binop(BinOp::Or, at.clone(), av, bv);
                                bind_call_destination(cx, fb, env, destination, v)?;
                                let edge = tc.edge_args(env, *ret_bb)?;
                                fb.br(tc.target_block(*ret_bb), edge);
                                return Ok(());
                            }
                        }
                    }
                    // `carrying_mul_add::<T, U>(a, b, c, d) -> (U, T)`: the
                    // full-width multiply-accumulate `wide = a*b + c + d`
                    // returning `(wide as U, wide >> BITS)` = (lo, hi) — the
                    // fallback body in core/src/intrinsics/fallback.rs is the
                    // spec. Used by the float formatter's big-int core (u32)
                    // and udiv128 (u64). Lower by widening: u32 via U64
                    // arithmetic, u64/usize via U128 (the i128 lanes are fully
                    // supported end-to-end since the trust-cg pair fixes). The
                    // (lo, hi) tuple result is lane-stored through the
                    // destination place; an SSA-modeled scalar destination
                    // cannot hold a pair and falls through to the extern
                    // emission (fail-closed).
                    if iname == "carrying_mul_add" {
                        let dest_is_ssa = destination.projection.is_empty()
                            && matches!(
                                cx.model.get(&destination.local),
                                Some(LocalModel::Ssa(_))
                            );
                        if let ([a, b, c, d], Some(ret_bb)) = (&args[..], target) {
                            let (av, at) = lower_operand(cx, fb, env, &a.node)?;
                            let (bv, bt) = lower_operand(cx, fb, env, &b.node)?;
                            let (cv, ct) = lower_operand(cx, fb, env, &c.node)?;
                            let (dv, dt) = lower_operand(cx, fb, env, &d.node)?;
                            let homogeneous = at == bt && bt == ct && ct == dt;
                            let plan = match at {
                                TIRTy::U32 => Some((TIRTy::U64, TIRTy::U32, 4u64, 32)),
                                TIRTy::U64 => Some((TIRTy::U128, TIRTy::U64, 8u64, 64)),
                                _ => None,
                            };
                            if homogeneous && !dest_is_ssa {
                                if let Some((wide, lane, lane_size, bits)) = plan {
                                    let wa = fb.cast(CastOp::ZExt, lane.clone(), wide.clone(), av);
                                    let wb = fb.cast(CastOp::ZExt, lane.clone(), wide.clone(), bv);
                                    let wc = fb.cast(CastOp::ZExt, lane.clone(), wide.clone(), cv);
                                    let wd = fb.cast(CastOp::ZExt, lane.clone(), wide.clone(), dv);
                                    let mul = fb.binop(BinOp::Mul, wide.clone(), wa, wb);
                                    let s1 = fb.binop(BinOp::Add, wide.clone(), mul, wc);
                                    let w = fb.binop(BinOp::Add, wide.clone(), s1, wd);
                                    let lo = fb.cast(CastOp::Trunc, wide.clone(), lane.clone(), w);
                                    let sh = fb.iconst(wide.clone(), bits as i128);
                                    let hiw = fb.binop(BinOp::LShr, wide.clone(), w, sh);
                                    let hi = fb.cast(CastOp::Trunc, wide.clone(), lane.clone(), hiw);
                                    let addr = place_address(cx, fb, env, destination)?;
                                    fb.store(lane.clone(), addr, lo);
                                    // RUNG 2a: a STATIC, layout-derived lane
                                    // offset — route it through the one
                                    // byte-offset funnel so it is subject to
                                    // the same `inbounds` discharge as every
                                    // other constant field offset.
                                    let addr_hi = gep_byte_offset(fb, addr, lane_size);
                                    fb.store(lane, addr_hi, hi);
                                    let edge = tc.edge_args(env, *ret_bb)?;
                                    fb.br(tc.target_block(*ret_bb), edge);
                                    return Ok(());
                                }
                            }
                        }
                    }
                    // `select_unpredictable::<T>(b, t, f)`: semantically a plain
                    // conditional select — the "unpredictable" part is only a
                    // branch-prediction HINT. Lower scalar-lane `T` natively to a
                    // `Select` instead of leaving an extern leaf per
                    // monomorphization (core's unicode case-table binary search
                    // instantiates `T = MaybeUninit<usize>` / `*mut usize`, which
                    // previously aborted in the self-contained battery). Fail
                    // closed: any shape the checks below reject falls through to
                    // the historical extern-call emission unchanged.
                    if iname == "select_unpredictable" {
                        if let ([c, t, f], Some(ret_bb)) = (&args[..], target) {
                            let (cv, cty) = lower_operand(cx, fb, env, &c.node)?;
                            let (tv, tty) = lower_operand(cx, fb, env, &t.node)?;
                            let (fv, fty) = lower_operand(cx, fb, env, &f.node)?;
                            if matches!(cty, TIRTy::Bool) && tty == fty {
                                let v = fb.select(tty.clone(), cv, tv, fv);
                                bind_call_destination(cx, fb, env, destination, v)?;
                                let edge = tc.edge_args(env, *ret_bb)?;
                                fb.br(tc.target_block(*ret_bb), edge);
                                return Ok(());
                            }
                        }
                    }
                    // `cold_path()`: a pure branch-placement HINT (rustc
                    // codegens it to nothing) — a no-op here. EH lane only:
                    // the abort lane keeps its historical extern-call emission
                    // BYTE-IDENTICALLY (wp5/wp9 regression pin).
                    if tc.eh && idef.name.as_str() == "cold_path" {
                        let ret_bb = target.ok_or_else(|| {
                            "cold_path: call must have a return target".to_string()
                        })?;
                        let edge = tc.edge_args(env, ret_bb)?;
                        fb.br(tc.target_block(ret_bb), edge);
                        return Ok(());
                    }
                    // `typed_swap_nonoverlapping::<T>(a, b)`: swap `size_of::<T>()`
                    // bytes between two non-overlapping pointers — a 3-way lane
                    // copy through a fresh temp slot (the exact bytewise
                    // semantics; `T`'s layout is static).
                    if tc.eh && idef.name.as_str() == "typed_swap_nonoverlapping" {
                        let [a, b] = &args[..] else {
                            return Err(
                                "typed_swap_nonoverlapping: expected two args".to_string()
                            );
                        };
                        let ty_arg = callee
                            .args
                            .iter()
                            .find_map(|ga| ga.as_type())
                            .ok_or_else(|| {
                                "typed_swap_nonoverlapping: no type arg".to_string()
                            })?;
                        let (size, align) = memory_layout_size_align(cx, ty_arg)?;
                        let (av, at) = lower_operand(cx, fb, env, &a.node)?;
                        let (bv, bt) = lower_operand(cx, fb, env, &b.node)?;
                        if !matches!(at, TIRTy::Ptr) || !matches!(bt, TIRTy::Ptr) {
                            return Err(
                                "typed_swap_nonoverlapping: non-pointer args".to_string()
                            );
                        }
                        let tmp = fb.alloca_aligned(slot_lane_ty(size, align)?, align);
                        fb.note_alloc_extent(tmp, size);
                        copy_aggregate_bytes(fb, av, tmp, size, align)?;
                        copy_aggregate_bytes(fb, bv, av, size, align)?;
                        copy_aggregate_bytes(fb, tmp, bv, size, align)?;
                        let ret_bb = target.ok_or_else(|| {
                            "typed_swap_nonoverlapping: call must have a return target"
                                .to_string()
                        })?;
                        let edge = tc.edge_args(env, ret_bb)?;
                        fb.br(tc.target_block(ret_bb), edge);
                        return Ok(());
                    }
                    // `is_val_statically_known::<T>(v)`: a pure OPTIMIZATION
                    // HINT — rustc's own codegen lowers the runtime call to
                    // `const false` (the documented conservative answer, both
                    // outcomes semantically equal). Fold identically.
                    if tc.eh && idef.name.as_str() == "is_val_statically_known" {
                        let c = fb.bool_const(false);
                        bind_call_destination(cx, fb, env, destination, c)?;
                        let ret_bb = target.ok_or_else(|| {
                            "is_val_statically_known: call must have a return target"
                                .to_string()
                        })?;
                        let edge = tc.edge_args(env, ret_bb)?;
                        fb.br(tc.target_block(ret_bb), edge);
                        return Ok(());
                    }
                    // `size_of_val::<T>` / `align_of_val::<T>` on a SIZED `T` are
                    // COMPILE-TIME CONSTANTS (the value does not depend on the pointer
                    // argument — only an unsized `T`'s size/align is metadata-derived).
                    // Fold to `const usize` from `T`'s layout — the exact constant rustc
                    // itself folds for a sized type — so the drop path's dealloc `Layout`
                    // is self-contained (no `size_of_val` extern leaf). Arc/Weak `drop`
                    // build `Layout::from_size_align(size_of_val, align_of_val)` for the
                    // `ArcInner<T>` dealloc this way. Only fold when the layout is
                    // computable (sized); an unsized `T` falls through to the call path.
                    if matches!(idef.name.as_str(), "size_of_val" | "align_of_val") {
                        let want_size = idef.name.as_str() == "size_of_val";
                        if let Some(ty_arg) = callee.args.iter().find_map(|a| a.as_type()) {
                            if let Ok((size, align)) = memory_layout_size_align(cx, ty_arg) {
                                let val = if want_size { size } else { align };
                                let c = fb.iconst(TIRTy::U64, val as i128);
                                bind_call_destination(cx, fb, env, destination, c)?;
                                let ret_bb = target.ok_or_else(|| {
                                    "size/align_of_val: call must have a return target"
                                        .to_string()
                                })?;
                                let edge = tc.edge_args(env, ret_bb)?;
                                fb.br(tc.target_block(ret_bb), edge);
                                return Ok(());
                            }
                            // THREADS: an UNSIZED `T` — the value's size/align is
                            // METADATA-derived. The single arg is a FAT pointer
                            // place whose 16-byte cell holds (data, metadata):
                            //   * `dyn Trait`: metadata = vtable; size = vt[1],
                            //     align = vt[2] (rustc's vtable header layout).
                            //   * `[T]` / `str`: metadata = element count;
                            //     size = count * stride, align = elem align.
                            // Lower these as PLAIN LOADS — never an extern leaf
                            // whose hand-written C signature can drift from the
                            // pointer-to-pair ABI (the `Box<dyn FnOnce>` drop's
                            // `Layout::for_value` fed a garbage align into
                            // `Alignment::new_unchecked` exactly that way).
                            let mdesc = match ty_arg.kind() {
                                ty::Dynamic(..) => Some(None),
                                ty::Str => Some(Some((1u64, 1u64))),
                                ty::Slice(elem) => {
                                    // `size_of::<T>()` is already the array
                                    // stride (padded to align).
                                    let (es, ea) =
                                        memory_layout_size_align(cx, cx.mono(*elem))?;
                                    Some(Some((es, ea)))
                                }
                                _ => None,
                            };
                            if let Some(meta_kind) = mdesc {
                                let [arg] = &args[..] else {
                                    return Err(
                                        "size/align_of_val: expected exactly one arg"
                                            .to_string(),
                                    );
                                };
                                let (Operand::Copy(place) | Operand::Move(place)) = &arg.node
                                else {
                                    return Err(
                                        "size/align_of_val: arg is not a place".to_string()
                                    );
                                };
                                // The fat CELL address (the pointer operand is a
                                // fat local/place; its slot holds the pair).
                                let cell = place_address(cx, fb, env, place)?;
                                let meta_addr = gep_byte_offset(fb, cell, 8);
                                let v = match meta_kind {
                                    // dyn: read the vtable's size/align slot.
                                    None => {
                                        let vt = fb.load(TIRTy::Ptr, meta_addr);
                                        let slot = if want_size { 8 } else { 16 };
                                        let a = gep_byte_offset(fb, vt, slot);
                                        fb.load(TIRTy::U64, a)
                                    }
                                    // slice/str: size = count * stride; align const.
                                    Some((stride, ea)) => {
                                        if want_size {
                                            let count = fb.load(TIRTy::U64, meta_addr);
                                            let s =
                                                fb.iconst(TIRTy::U64, stride as i128);
                                            fb.binop(BinOp::Mul, TIRTy::U64, count, s)
                                        } else {
                                            fb.iconst(TIRTy::U64, ea as i128)
                                        }
                                    }
                                };
                                bind_call_destination(cx, fb, env, destination, v)?;
                                let ret_bb = target.ok_or_else(|| {
                                    "size/align_of_val: call must have a return target"
                                        .to_string()
                                })?;
                                let edge = tc.edge_args(env, ret_bb)?;
                                fb.br(tc.target_block(ret_bb), edge);
                                return Ok(());
                            }
                        }
                    }
                    // RUNG (simd/NEON): hashbrown's NEON control-byte group scan.
                    // rustc inlines the `core::intrinsics::simd::simd_*` calls to
                    // per-lane `uint8x8_t` ops; the six that back the group scan
                    // lower THROUGH trust-ir vector ops (V64 / D-register), NOT as
                    // opaque extern leaves. trust-cg codegens genuine aarch64 NEON
                    // (`ldr d`/`cmeq.8b`/`cmge.8b`/`cmgt.8b`/`orr.8b`).
                    // `uint8x8_t`/`int8x8_t` = `<8 x i8>`; the compare mask =
                    // `<8 x bool>` (stored at its V64 8-byte width); `uint64x1_t`
                    // lane 0 = the u64 group bitmask. Handled BEFORE the generic
                    // call path so the intrinsic never becomes an extern stub.
                    // FAIL-CLOSED on any `simd_*` we do not map.
                    let simd_name = idef.name.as_str();
                    if simd_name.starts_with("simd_") {
                        let ret_bb = target.ok_or_else(|| {
                            "simd intrinsic: call must have a return target".to_string()
                        })?;
                        match simd_name {
                            // `simd_eq`/`simd_ge`/`simd_lt` byte compares and
                            // `simd_or` byte bitwise-or. The lane COUNT is read
                            // from the operand's SIMD layout, NOT hardcoded:
                            // NEON uses both `uint8x8_t` (V64, 8 lanes —
                            // hashbrown group match) and `uint8x16_t` (V128, 16
                            // lanes — memchr's byte scan / `simd_contains`).
                            // Hardcoding 8 lanes silently dropped the HIGH 8
                            // bytes of a 128-bit vector, leaving them
                            // uninitialised — the memchr NUL-scan
                            // truncate-name-to-8-bytes miscompile. Element stays
                            // byte-wide (`i8`): these are byte-lane ops and byte
                            // equality is signedness-agnostic (`cmeq.{8b,16b}`).
                            // `simd_or` — lanewise bitwise OR. A bitwise op is
                            // width-AGNOSTIC: the destination byte IMAGE is
                            // identical regardless of how the bytes are grouped
                            // into lanes, so OR the WHOLE vector as `<8|16 x i8>`
                            // (a single NEON `orr.{8b,16b}` covering every byte).
                            // The old code read only the lane COUNT and assumed
                            // `i8` lanes: for `uint32x4_t` (4 lanes, 16 bytes) it
                            // emitted a 4-iteration i8 loop that wrote just 4 of 16
                            // bytes, leaving the top 12 UNINITIALISED (garbage /
                            // non-deterministic). `uint16x8_t` (8 lanes, 16 bytes)
                            // matched the `sc==8` byte path and wrote 8 of 16.
                            "simd_or" => {
                                let [a, b] = &args[..] else {
                                    return Err(format!("{simd_name}: expected exactly two args"));
                                };
                                let (se, sc) = simd_int_vector_lanes(
                                    cx,
                                    operand_concrete_ty(cx, &a.node),
                                )
                                .ok_or_else(|| {
                                    format!("{simd_name}: non-int-vector source")
                                })?;
                                let total = int_lane_size(&se) * sc; // TOTAL bytes
                                let a_ptr = operand_place_address(cx, fb, env, &a.node)?;
                                let b_ptr = operand_place_address(cx, fb, env, &b.node)?;
                                let dst_ptr = place_address(cx, fb, env, destination)?;
                                if total == 8 || total == 16 {
                                    // One NEON `orr.{8b,16b}` over the full D/Q
                                    // register — byte lanes, bit-exact for ANY
                                    // element width. `total==8` keeps hashbrown's
                                    // `uint8x8_t` group-scan `orr.8b` byte-for-byte.
                                    let vi8 =
                                        TIRTy::Vector(Box::new(TIRTy::I8), total as u32);
                                    let va = fb.load(vi8.clone(), a_ptr);
                                    let vb = fb.load(vi8.clone(), b_ptr);
                                    let r = fb.binop(BinOp::Or, vi8.clone(), va, vb);
                                    fb.store(vi8, dst_ptr, r);
                                } else {
                                    // Wider `core::simd` portable vectors: byte-
                                    // image-exact in pointer-width u64 chunks plus
                                    // an i8 tail (bitwise, so chunking is exact).
                                    let mut off = 0u64;
                                    while off + 8 <= total {
                                        let aa = if off == 0 { a_ptr } else { gep_byte_offset(fb, a_ptr, off) };
                                        let bb = if off == 0 { b_ptr } else { gep_byte_offset(fb, b_ptr, off) };
                                        let va = fb.load(TIRTy::U64, aa);
                                        let vb = fb.load(TIRTy::U64, bb);
                                        let r = fb.binop(BinOp::Or, TIRTy::U64, va, vb);
                                        let dd = if off == 0 { dst_ptr } else { gep_byte_offset(fb, dst_ptr, off) };
                                        fb.store(TIRTy::U64, dd, r);
                                        off += 8;
                                    }
                                    while off < total {
                                        let aa = gep_byte_offset(fb, a_ptr, off);
                                        let bb = gep_byte_offset(fb, b_ptr, off);
                                        let va = fb.load(TIRTy::I8, aa);
                                        let vb = fb.load(TIRTy::I8, bb);
                                        let r = fb.binop(BinOp::Or, TIRTy::I8, va, vb);
                                        let dd = gep_byte_offset(fb, dst_ptr, off);
                                        fb.store(TIRTy::I8, dd, r);
                                        off += 1;
                                    }
                                }
                            }
                            // `simd_eq`/`simd_ge`/`simd_lt` — lanewise integer
                            // compare → a per-lane all-ones/all-zeros mask
                            // (`cmeq`/`cmge`/`cmgt`/`cmhi`/`cmhs`). BOTH the lane
                            // WIDTH and COUNT come from the operand's SIMD layout,
                            // and the compare SIGNEDNESS from the element type
                            // (`cmge` for `i32`, `cmhs` for `u32`). The old code
                            // hardcoded `i8` lanes and a SIGNED byte icmp for EVERY
                            // width: `uint32x4_t` compared/wrote only 4 of 16 bytes
                            // and used signed `sge`/`slt` on unsigned inputs.
                            "simd_eq" | "simd_ge" | "simd_lt" => {
                                let [a, b] = &args[..] else {
                                    return Err(format!("{simd_name}: expected exactly two args"));
                                };
                                let (se, sc) = simd_int_vector_lanes(
                                    cx,
                                    operand_concrete_ty(cx, &a.node),
                                )
                                .ok_or_else(|| {
                                    format!("{simd_name}: non-int-vector source")
                                })?;
                                // The SIGNED lane spelling trust-cg's NEON vector
                                // ICmp requires (`<N x i{8,16,32,64}>`); the compare
                                // signedness rides on the ICmpOp, not this type.
                                let slane = match int_lane_size(&se) {
                                    1 => TIRTy::I8,
                                    2 => TIRTy::I16,
                                    4 => TIRTy::I32,
                                    8 => TIRTy::I64,
                                    _ => {
                                        return Err(format!(
                                            "{simd_name}: unsupported element width"
                                        ))
                                    }
                                };
                                let signed = is_signed(&se);
                                let op = match simd_name {
                                    "simd_eq" => ICmpOp::Eq,            // cmeq
                                    "simd_ge" if signed => ICmpOp::Sge, // cmge
                                    "simd_ge" => ICmpOp::Uge,           // cmhs
                                    "simd_lt" if signed => ICmpOp::Slt, // cmgt swapped
                                    "simd_lt" => ICmpOp::Ult,           // cmhi swapped
                                    _ => unreachable!(),
                                };
                                let a_ptr = operand_place_address(cx, fb, env, &a.node)?;
                                let b_ptr = operand_place_address(cx, fb, env, &b.node)?;
                                let dst_ptr = place_address(cx, fb, env, destination)?;
                                // trust-cg lowers exactly these lane shapes to a
                                // single NEON vector compare whose V64/V128 mask
                                // store writes the FULL register width: <8 x i8>,
                                // <16 x i8>, <8 x i16>, <4 x i32>, <2 x i64>.
                                let neon_shape = matches!(
                                    (&slane, sc),
                                    (TIRTy::I8, 8)
                                        | (TIRTy::I8, 16)
                                        | (TIRTy::I16, 8)
                                        | (TIRTy::I32, 4)
                                        | (TIRTy::I64, 2)
                                );
                                if neon_shape {
                                    let vty =
                                        TIRTy::Vector(Box::new(slane.clone()), sc as u32);
                                    let vbool =
                                        TIRTy::Vector(Box::new(TIRTy::Bool), sc as u32);
                                    let va = fb.load(vty.clone(), a_ptr);
                                    let vb = fb.load(vty.clone(), b_ptr);
                                    let mask = fb.icmp(op, vty, va, vb);
                                    fb.store(vbool, dst_ptr, mask);
                                } else {
                                    // Any other shape (e.g. `core::simd` portable
                                    // wide vectors): a per-lane scalar compare that
                                    // materialises a WIDTH-CORRECT all-ones/all-
                                    // zeros lane mask (`-1` = 0xFF..FF at `slane`
                                    // width, matching a hardware compare mask).
                                    let w = int_lane_size(&se);
                                    let ones = fb.iconst(slane.clone(), -1);
                                    let zero = fb.iconst(slane.clone(), 0);
                                    for i in 0..sc {
                                        let off = i * w;
                                        let aa = if off == 0 { a_ptr } else { gep_byte_offset(fb, a_ptr, off) };
                                        let bb = if off == 0 { b_ptr } else { gep_byte_offset(fb, b_ptr, off) };
                                        let va = fb.load(slane.clone(), aa);
                                        let vb = fb.load(slane.clone(), bb);
                                        let bit = fb.icmp(op, slane.clone(), va, vb);
                                        let mask = fb.select(slane.clone(), bit, ones, zero);
                                        let dd = if off == 0 { dst_ptr } else { gep_byte_offset(fb, dst_ptr, off) };
                                        fb.store(slane.clone(), dd, mask);
                                    }
                                }
                            }
                            // `simd_splat(x: T) -> {u,i}TxN`: broadcast the scalar
                            // to ALL lanes. BOTH the lane WIDTH and the lane
                            // COUNT are read from the DESTINATION vector's SIMD
                            // layout, not hardcoded to `<8 x i8>`:
                            //   * `vdupq_n_u8`  -> `<16 x i8>` (`dup.16b`),
                            //   * `vdup_n_u8`   -> `<8 x i8>`  (`dup.8b`),
                            //   * `vdupq_n_u16` -> `<8 x i16>` (`dup.8h`) — the
                            //     shift-amount vector inside `vshrn_n_u16`'s
                            //     `simd_shr(a, vdupq_n_u16(N))`.
                            // Hardcoding `<8 x i8>` splatted a 16-bit lane value
                            // into 8 BYTE lanes: it both dropped the high half of
                            // a 128-bit needle AND corrupted every `uint16x8_t`
                            // shift-amount lane (e.g. `4` became the byte pair
                            // `0x0404`), silently breaking the memchr movemask.
                            // `pack_lanes` admits <16 x i8>/<8 x i16>/<4 x i32>/
                            // <2 x i64>/<8 x i8>; map the (unsigned) element to
                            // its signed lane type and cast the scalar to it.
                            "simd_splat" => {
                                let [x] = &args[..] else {
                                    return Err("simd_splat: expected exactly one arg".to_string());
                                };
                                let (se, sc) = simd_int_vector_lanes(
                                    cx,
                                    cx.place_concrete_ty(destination),
                                )
                                .unwrap_or((TIRTy::I8, 8));
                                // The signed lane type `vector.pack_lanes` admits.
                                let slane = match se {
                                    TIRTy::I8 | TIRTy::U8 => TIRTy::I8,
                                    TIRTy::I16 | TIRTy::U16 => TIRTy::I16,
                                    TIRTy::I32 | TIRTy::U32 => TIRTy::I32,
                                    TIRTy::I64 | TIRTy::U64 => TIRTy::I64,
                                    _ => TIRTy::I8,
                                };
                                let vty = TIRTy::Vector(Box::new(slane.clone()), sc as u32);
                                let (xv, xty) = lower_operand(cx, fb, env, &x.node)?;
                                // The pack_lanes lane operand must be the vector's
                                // element type: cast the scalar (width-adjust +
                                // signedness reinterpret) to `slane`.
                                let lane = int_cast(fb, xv, &xty, &slane);
                                let dst_ptr = place_address(cx, fb, env, destination)?;
                                match trust_ir::dialect::vector::pack_lanes_repeated(
                                    vty.clone(),
                                    lane,
                                ) {
                                    Ok(splat_op) => {
                                        let vec = fb
                                            .dialect_op(splat_op)
                                            .into_iter()
                                            .next()
                                            .ok_or_else(|| {
                                                "simd_splat: pack_lanes produced no result"
                                                    .to_string()
                                            })?;
                                        fb.store(vty.clone(), dst_ptr, vec);
                                    }
                                    // A width `vector.pack_lanes` does not admit
                                    // (a NEON register holds at most 128 bits, so
                                    // only <16 x i8>/<8 x i16>/<4 x i32>/<2 x i64>/
                                    // <8 x i8>). `core::simd` portable vectors go
                                    // wider — `Sealed::valid::<i8, {32,64}>`
                                    // const-eval builds a `Simd<i8, {32,64}>`
                                    // whose splat has no single-instruction form.
                                    // Materialise it faithfully as a per-lane
                                    // store loop (correct for any N; the old
                                    // hardcoded `<8 x i8>` silently emitted a
                                    // wrong-width 8-lane splat here). No hardware
                                    // SIMD instruction, but byte-image exact.
                                    Err(_) => {
                                        let w = int_lane_size(&slane);
                                        for i in 0..sc {
                                            let off = i * w;
                                            let dd = if off == 0 {
                                                dst_ptr
                                            } else {
                                                gep_byte_offset(fb, dst_ptr, off)
                                            };
                                            fb.store(slane.clone(), dd, lane);
                                        }
                                    }
                                }
                            }
                            // `simd_extract(v, idx) -> elem`: read lane `idx` of the
                            // vector buffer. For hashbrown this is `uint64x1_t`
                            // lane 0 = the u64 group bitmask (a plain scalar load of
                            // the reinterpreted mask; faithful, through trust-ir).
                            "simd_extract" => {
                                let [vec, idx] = &args[..] else {
                                    return Err(
                                        "simd_extract: expected exactly two args".to_string()
                                    );
                                };
                                let vec_ptr = operand_place_address(cx, fb, env, &vec.node)?;
                                let lane = match &idx.node {
                                    Operand::Constant(c) => {
                                        const_operand_u64(cx, c).ok_or_else(|| {
                                            "simd_extract: lane index is not a resolved constant"
                                                .to_string()
                                        })?
                                    }
                                    _ => {
                                        return Err(
                                            "simd_extract: lane index must be a constant".to_string(),
                                        )
                                    }
                                };
                                let result_ty =
                                    scalar_tir_ty(cx.place_concrete_ty(destination))
                                        .ok_or_else(|| {
                                            "simd_extract: non-scalar result element".to_string()
                                        })?;
                                let elem_bytes = int_lane_size(&result_ty);
                                if elem_bytes == 0 {
                                    return Err(
                                        "simd_extract: unsupported result element width".to_string(),
                                    );
                                }
                                let off = lane * elem_bytes;
                                let addr = if off == 0 {
                                    vec_ptr
                                } else {
                                    gep_byte_offset(fb, vec_ptr, off)
                                };
                                let elem = fb.load(result_ty, addr);
                                bind_call_destination(cx, fb, env, destination, elem)?;
                            }
                            // `simd_insert(vec, idx, val) -> vec'`: the source
                            // vector with lane `idx` (a const) replaced by the
                            // scalar `val` — `vld1q_lane_u32::<LANE>(ptr, v)` lowers
                            // to `simd_insert(v, LANE, *ptr)`. Copy every source lane
                            // into the destination place, then overwrite the one
                            // selected lane. Lane WIDTH + COUNT come from the source
                            // vector's SIMD layout (float lanes admitted too).
                            "simd_insert" => {
                                let [vec, idx, val] = &args[..] else {
                                    return Err(format!(
                                        "{simd_name}: expected exactly three args"
                                    ));
                                };
                                let (se, sc) =
                                    simd_vector_lanes_any(cx, operand_concrete_ty(cx, &vec.node))
                                        .ok_or_else(|| {
                                            format!("{simd_name}: non-SIMD-vector source")
                                        })?;
                                let lane = match &idx.node {
                                    Operand::Constant(c) => {
                                        const_operand_u64(cx, c).ok_or_else(|| {
                                            format!(
                                                "{simd_name}: lane index is not a resolved constant"
                                            )
                                        })?
                                    }
                                    _ => {
                                        return Err(format!(
                                            "{simd_name}: lane index must be a constant"
                                        ))
                                    }
                                };
                                if lane >= sc {
                                    return Err(format!(
                                        "{simd_name}: lane {lane} out of range (lanes={sc})"
                                    ));
                                }
                                let vec_ptr = operand_place_address(cx, fb, env, &vec.node)?;
                                let dst_ptr = place_address(cx, fb, env, destination)?;
                                let w = simd_lane_bytes(&se);
                                // Copy all source lanes into the destination.
                                for i in 0..sc {
                                    let off = i * w;
                                    let sa = if off == 0 { vec_ptr } else { gep_byte_offset(fb, vec_ptr, off) };
                                    let da = if off == 0 { dst_ptr } else { gep_byte_offset(fb, dst_ptr, off) };
                                    let v = fb.load(se.clone(), sa);
                                    fb.store(se.clone(), da, v);
                                }
                                // Overwrite the selected lane with `val`.
                                let (val_v, val_ty) = lower_operand(cx, fb, env, &val.node)?;
                                let vcast = simd_lane_cast(fb, val_v, &val_ty, &se);
                                let loff = lane * w;
                                let la = if loff == 0 { dst_ptr } else { gep_byte_offset(fb, dst_ptr, loff) };
                                fb.store(se.clone(), la, vcast);
                            }
                            // `simd_shr(a, b)`: per-lane shift right (logical
                            // for unsigned lanes, arithmetic for signed) —
                            // `vshrn_n_u16`'s widened-lane shift.
                            "simd_shr" | "simd_shl" => {
                                let [a, b] = &args[..] else {
                                    return Err(format!(
                                        "{simd_name}: expected exactly two args"
                                    ));
                                };
                                let (se, sc) =
                                    simd_int_vector_lanes(cx, operand_concrete_ty(cx, &a.node))
                                        .ok_or_else(|| {
                                            format!("{simd_name}: non-int-vector source")
                                        })?;
                                let a_ptr = operand_place_address(cx, fb, env, &a.node)?;
                                let b_ptr = operand_place_address(cx, fb, env, &b.node)?;
                                let dst_ptr = place_address(cx, fb, env, destination)?;
                                let w = int_lane_size(&se);
                                let op = if simd_name == "simd_shl" {
                                    BinOp::Shl
                                } else if is_signed(&se) {
                                    BinOp::AShr
                                } else {
                                    BinOp::LShr
                                };
                                for i in 0..sc {
                                    let off = i * w;
                                    let aa = if off == 0 { a_ptr } else { gep_byte_offset(fb, a_ptr, off) };
                                    let bb = if off == 0 { b_ptr } else { gep_byte_offset(fb, b_ptr, off) };
                                    let va = fb.load(se.clone(), aa);
                                    let vb = fb.load(se.clone(), bb);
                                    let r = fb.binop(op, se.clone(), va, vb);
                                    let dd = if off == 0 { dst_ptr } else { gep_byte_offset(fb, dst_ptr, off) };
                                    fb.store(se.clone(), dd, r);
                                }
                            }
                            // `simd_and` / `simd_xor`: lanewise bitwise op —
                            // byte-image-exact in pointer-width chunks.
                            "simd_and" | "simd_xor" => {
                                let [a, b] = &args[..] else {
                                    return Err(format!(
                                        "{simd_name}: expected exactly two args"
                                    ));
                                };
                                let (se, sc) =
                                    simd_int_vector_lanes(cx, operand_concrete_ty(cx, &a.node))
                                        .ok_or_else(|| {
                                            format!("{simd_name}: non-int-vector source")
                                        })?;
                                let total = int_lane_size(&se) * sc;
                                if total == 0 || total % 8 != 0 {
                                    return Err(format!(
                                        "{simd_name}: vector byte size {total} not a \
                                         multiple of 8"
                                    ));
                                }
                                let a_ptr = operand_place_address(cx, fb, env, &a.node)?;
                                let b_ptr = operand_place_address(cx, fb, env, &b.node)?;
                                let dst_ptr = place_address(cx, fb, env, destination)?;
                                let op = if simd_name == "simd_and" { BinOp::And } else { BinOp::Xor };
                                for i in 0..(total / 8) {
                                    let off = i * 8;
                                    let aa = if off == 0 { a_ptr } else { gep_byte_offset(fb, a_ptr, off) };
                                    let bb = if off == 0 { b_ptr } else { gep_byte_offset(fb, b_ptr, off) };
                                    let va = fb.load(TIRTy::U64, aa);
                                    let vb = fb.load(TIRTy::U64, bb);
                                    let r = fb.binop(op, TIRTy::U64, va, vb);
                                    let dd = if off == 0 { dst_ptr } else { gep_byte_offset(fb, dst_ptr, off) };
                                    fb.store(TIRTy::U64, dd, r);
                                }
                            }
                            // `simd_bitmask(mask) -> uN`: pack each lane's TOP
                            // bit into an integer, bit i = lane i — per-lane
                            // load + shift/mask/or fold (LE lane order).
                            "simd_bitmask" => {
                                let [a] = &args[..] else {
                                    return Err(
                                        "simd_bitmask: expected exactly one arg".to_string()
                                    );
                                };
                                let (se, sc) =
                                    simd_int_vector_lanes(cx, operand_concrete_ty(cx, &a.node))
                                        .ok_or_else(|| {
                                            "simd_bitmask: non-int-vector source".to_string()
                                        })?;
                                if sc > 64 {
                                    return Err(format!(
                                        "simd_bitmask: {sc} lanes exceed the u64 fold"
                                    ));
                                }
                                let dst_tir =
                                    scalar_tir_ty(cx.place_concrete_ty(destination)).ok_or_else(
                                        || "simd_bitmask: non-scalar destination".to_string(),
                                    )?;
                                let src_ptr = operand_place_address(cx, fb, env, &a.node)?;
                                let w = int_lane_size(&se);
                                let top = (w * 8 - 1) as i128;
                                let mut acc = fb.iconst(TIRTy::U64, 0);
                                for i in 0..sc {
                                    let off = i * w;
                                    let sa = if off == 0 {
                                        src_ptr
                                    } else {
                                        gep_byte_offset(fb, src_ptr, off)
                                    };
                                    let v = fb.load(se.clone(), sa);
                                    let vu = int_cast(fb, v, &se, &TIRTy::U64);
                                    let sh = fb.iconst(TIRTy::U64, top);
                                    let bit0 = fb.binop(BinOp::LShr, TIRTy::U64, vu, sh);
                                    let one = fb.iconst(TIRTy::U64, 1);
                                    let bit = fb.binop(BinOp::And, TIRTy::U64, bit0, one);
                                    let pos = fb.iconst(TIRTy::U64, i as i128);
                                    let placed = fb.binop(BinOp::Shl, TIRTy::U64, bit, pos);
                                    acc = fb.binop(BinOp::Or, TIRTy::U64, acc, placed);
                                }
                                let out = int_cast(fb, acc, &TIRTy::U64, &dst_tir);
                                bind_call_destination(cx, fb, env, destination, out)?;
                            }
                            // `simd_shuffle(a, b, IDX)`: build each output lane
                            // from the concatenated (a, b) source at the CONST
                            // index vector's positions — per-lane loads/stores.
                            "simd_shuffle" => {
                                let [a, b, idx] = &args[..] else {
                                    return Err(
                                        "simd_shuffle: expected exactly three args".to_string()
                                    );
                                };
                                let (se, sc) =
                                    simd_int_vector_lanes(cx, operand_concrete_ty(cx, &a.node))
                                        .ok_or_else(|| {
                                            "simd_shuffle: non-int-vector source".to_string()
                                        })?;
                                let (de, dc) = simd_int_vector_lanes(
                                    cx,
                                    cx.place_concrete_ty(destination),
                                )
                                .ok_or_else(|| {
                                    "simd_shuffle: non-int-vector destination".to_string()
                                })?;
                                if de != se {
                                    return Err(
                                        "simd_shuffle: element type mismatch".to_string()
                                    );
                                }
                                let Operand::Constant(ic) = &idx.node else {
                                    return Err(
                                        "simd_shuffle: index vector must be constant".to_string()
                                    );
                                };
                                let raw = const_agg_bytes(cx, ic)
                                    .map_err(|e| format!("simd_shuffle: index bytes: {e}"))?;
                                if raw.len() as u64 != dc * 4 {
                                    return Err(format!(
                                        "simd_shuffle: index vector {} bytes != {dc} u32 lanes",
                                        raw.len()
                                    ));
                                }
                                let a_ptr = operand_place_address(cx, fb, env, &a.node)?;
                                let b_ptr = operand_place_address(cx, fb, env, &b.node)?;
                                let dst_ptr = place_address(cx, fb, env, destination)?;
                                let w = int_lane_size(&se);
                                for i in 0..dc as usize {
                                    let mut le = [0u8; 4];
                                    le.copy_from_slice(&raw[i * 4..i * 4 + 4]);
                                    let lane = u64::from(u32::from_le_bytes(le));
                                    let (src, li) = if lane < sc {
                                        (a_ptr, lane)
                                    } else if lane < 2 * sc {
                                        (b_ptr, lane - sc)
                                    } else {
                                        return Err(format!(
                                            "simd_shuffle: lane index {lane} out of range"
                                        ));
                                    };
                                    let sa = if li == 0 { src } else { gep_byte_offset(fb, src, li * w) };
                                    let v = fb.load(se.clone(), sa);
                                    let off = (i as u64) * w;
                                    let dd = if off == 0 { dst_ptr } else { gep_byte_offset(fb, dst_ptr, off) };
                                    fb.store(se.clone(), dd, v);
                                }
                            }
                            // `simd_cast` / `simd_as` between INT vectors of the
                            // SAME lane count (`vshrn_n_u16`'s u16x8 -> u8x8
                            // narrowing): per-lane load + int resize + store —
                            // the exact per-lane int-conversion semantics,
                            // emitted as scalar lane accesses.
                            "simd_cast" | "simd_as" => {
                                let [a] = &args[..] else {
                                    return Err(format!(
                                        "{simd_name}: expected exactly one arg"
                                    ));
                                };
                                // `simd_vector_lanes_any` on BOTH ends so a FLOAT
                                // source or destination is admitted: `vcvtq_f32_s32`
                                // (int->float `sitofp`, `<4 x i32>` -> `<4 x f32>`)
                                // and the float->float / float->int forms. The
                                // per-lane conversion op is chosen by
                                // `simd_lane_cast` (sitofp/uitofp/fptosi.sat/
                                // fpext/fptrunc/int-width-change).
                                let (se, sc) =
                                    simd_vector_lanes_any(cx, operand_concrete_ty(cx, &a.node))
                                        .ok_or_else(|| {
                                            format!("{simd_name}: non-SIMD-vector source")
                                        })?;
                                let (de, dc) = simd_vector_lanes_any(
                                    cx,
                                    cx.place_concrete_ty(destination),
                                )
                                .ok_or_else(|| {
                                    format!("{simd_name}: non-SIMD-vector destination")
                                })?;
                                if sc != dc {
                                    return Err(format!(
                                        "{simd_name}: lane count mismatch {sc} != {dc}"
                                    ));
                                }
                                let src_ptr = operand_place_address(cx, fb, env, &a.node)?;
                                let dst_ptr = place_address(cx, fb, env, destination)?;
                                let sw = simd_lane_bytes(&se);
                                let dw = simd_lane_bytes(&de);
                                for i in 0..sc {
                                    let sa = if i == 0 {
                                        src_ptr
                                    } else {
                                        gep_byte_offset(fb, src_ptr, i * sw)
                                    };
                                    let v = fb.load(se.clone(), sa);
                                    let c = simd_lane_cast(fb, v, &se, &de);
                                    let da = if i == 0 {
                                        dst_ptr
                                    } else {
                                        gep_byte_offset(fb, dst_ptr, i * dw)
                                    };
                                    fb.store(de.clone(), da, c);
                                }
                            }
                            // `simd_reduce_all(mask) -> bool`: every lane of an
                            // all-0/all-1 int MASK vector is all-ones. AND-fold
                            // the vector's bytes in pointer-width chunks, then
                            // compare the fold against all-ones — bit-exact for
                            // the mask precondition the intrinsic requires.
                            "simd_reduce_all" => {
                                let [a] = &args[..] else {
                                    return Err(
                                        "simd_reduce_all: expected exactly one arg".to_string()
                                    );
                                };
                                let (se, sc) =
                                    simd_int_vector_lanes(cx, operand_concrete_ty(cx, &a.node))
                                        .ok_or_else(|| {
                                            "simd_reduce_all: non-int-vector source".to_string()
                                        })?;
                                let total = int_lane_size(&se) * sc;
                                if total == 0 || total % 8 != 0 {
                                    return Err(format!(
                                        "simd_reduce_all: vector byte size {total} not a \
                                         multiple of 8"
                                    ));
                                }
                                let src_ptr = operand_place_address(cx, fb, env, &a.node)?;
                                let mut acc: Option<trust_ir::ValueId> = None;
                                for i in 0..(total / 8) {
                                    let a8 = if i == 0 {
                                        src_ptr
                                    } else {
                                        gep_byte_offset(fb, src_ptr, i * 8)
                                    };
                                    let w = fb.load(TIRTy::U64, a8);
                                    acc = Some(match acc {
                                        None => w,
                                        Some(prev) => fb.binop(BinOp::And, TIRTy::U64, prev, w),
                                    });
                                }
                                let folded = acc.expect("total >= 8 checked above");
                                let ones = fb.uconst(TIRTy::U64, u64::MAX as u128);
                                let all = fb.icmp(ICmpOp::Eq, TIRTy::U64, folded, ones);
                                bind_call_destination(cx, fb, env, destination, all)?;
                            }
                            // `simd_gt` / `simd_le` / `simd_ne`: per-lane
                            // comparison producing an all-ones (lane true) /
                            // all-zeros (lane false) MASK at the element's byte
                            // width — the NEON `cmhi`/`cmge`/`cmtst`/`fcmgt`
                            // lane semantics. BOTH the element type (signedness
                            // AND float-ness) and the lane COUNT are read from
                            // the operand's SIMD layout; the compare is emitted
                            // per-lane at the CORRECT element stride, unlike the
                            // byte-hardcoded `simd_eq`/`ge`/`lt` fallback whose
                            // 1-byte stride silently truncated wide-lane
                            // vectors (the `vcgtq_u32` family is `<4 x i32>`, a
                            // 16-byte Q register). The result element is an
                            // INTEGER of the same width even for FLOAT inputs
                            // (`vcgtq_f32` -> `uint32x4_t`), so the all-ones lane
                            // is written through a width-matched `select`.
                            // Backs: `vcgtq_u32` (unsigned gt), `vcgtq_s32`
                            // (signed gt), `vcgtq_f32` (ordered float gt),
                            // `vcleq_u32` (unsigned le), and `vtstq_u32`
                            // (`simd_and` then `simd_ne` vs the zero vector).
                            "simd_gt" | "simd_le" | "simd_ne" => {
                                let [a, b] = &args[..] else {
                                    return Err(format!(
                                        "{simd_name}: expected exactly two args"
                                    ));
                                };
                                let (se, sc) = simd_vector_lanes_any(
                                    cx,
                                    operand_concrete_ty(cx, &a.node),
                                )
                                .ok_or_else(|| {
                                    format!("{simd_name}: non-SIMD-vector source")
                                })?;
                                // Element byte width + the same-width signed int
                                // MASK lane type (all-ones `-1` = 0xFF..FF when
                                // true, 0 when false; the compare's output is an
                                // integer mask regardless of input float-ness).
                                let (w, mask_ty) = match &se {
                                    TIRTy::I8 | TIRTy::U8 | TIRTy::Bool => {
                                        (1u64, TIRTy::I8)
                                    }
                                    TIRTy::I16 | TIRTy::U16 => (2, TIRTy::I16),
                                    TIRTy::I32 | TIRTy::U32 | TIRTy::F32 => {
                                        (4, TIRTy::I32)
                                    }
                                    TIRTy::I64 | TIRTy::U64 | TIRTy::F64 => {
                                        (8, TIRTy::I64)
                                    }
                                    _ => {
                                        return Err(format!(
                                            "{simd_name}: unsupported element \
                                             type {se:?}"
                                        ))
                                    }
                                };
                                let a_ptr =
                                    operand_place_address(cx, fb, env, &a.node)?;
                                let b_ptr =
                                    operand_place_address(cx, fb, env, &b.node)?;
                                let dst_ptr =
                                    place_address(cx, fb, env, destination)?;
                                let ones = fb.iconst(mask_ty.clone(), -1);
                                let zero = fb.iconst(mask_ty.clone(), 0);
                                let float = is_float_tir(&se);
                                let signed = is_signed(&se);
                                for i in 0..sc {
                                    let off = i * w;
                                    let aa = if off == 0 {
                                        a_ptr
                                    } else {
                                        gep_byte_offset(fb, a_ptr, off)
                                    };
                                    let bb = if off == 0 {
                                        b_ptr
                                    } else {
                                        gep_byte_offset(fb, b_ptr, off)
                                    };
                                    let va = fb.load(se.clone(), aa);
                                    let vb = fb.load(se.clone(), bb);
                                    let bit = if float {
                                        let op = match simd_name {
                                            "simd_gt" => FCmpOp::OGt,
                                            "simd_le" => FCmpOp::OLe,
                                            "simd_ne" => FCmpOp::UNe,
                                            _ => unreachable!(),
                                        };
                                        fb.fcmp(op, se.clone(), va, vb)
                                    } else {
                                        let op = match simd_name {
                                            "simd_gt" => {
                                                if signed {
                                                    ICmpOp::Sgt
                                                } else {
                                                    ICmpOp::Ugt
                                                }
                                            }
                                            "simd_le" => {
                                                if signed {
                                                    ICmpOp::Sle
                                                } else {
                                                    ICmpOp::Ule
                                                }
                                            }
                                            "simd_ne" => ICmpOp::Ne,
                                            _ => unreachable!(),
                                        };
                                        fb.icmp(op, se.clone(), va, vb)
                                    };
                                    let mask = fb.select(
                                        mask_ty.clone(),
                                        bit,
                                        ones,
                                        zero,
                                    );
                                    let dd = if off == 0 {
                                        dst_ptr
                                    } else {
                                        gep_byte_offset(fb, dst_ptr, off)
                                    };
                                    fb.store(mask_ty.clone(), dd, mask);
                                }
                            }
                            // `simd_add` / `simd_sub` / `simd_mul`: lanewise
                            // INTEGER arithmetic at the operand's real lane width
                            // — `vaddq_{u8,s16,u32}` / `vsubq_{u32,s16}` /
                            // `vmulq_{u32,s16}`, and the widening `vaddl_u8`
                            // (whose `simd_cast` has already widened both
                            // `uint8x8_t` operands to `uint16x8_t` before this
                            // add). Unlike the bitwise `simd_and`/`simd_xor`
                            // u64-chunk fold, add/sub/mul carry ACROSS bits, so
                            // each lane must be computed at ITS OWN width; this
                            // mirrors the proven per-lane `simd_shr`/`simd_shl`
                            // shape. Wrapping (2's-complement) semantics match
                            // NEON `add`/`sub`/`mul.{Ns}`. Float element vectors
                            // (`vaddq_f32` etc.) are NOT int vectors, so they
                            // fail-closed here — the float class handles them.
                            "simd_add" | "simd_sub" | "simd_mul" => {
                                let [a, b] = &args[..] else {
                                    return Err(format!(
                                        "{simd_name}: expected exactly two args"
                                    ));
                                };
                                // `simd_vector_lanes_any` (not the int-only shape)
                                // so FLOAT-lane vectors (`vaddq_f32`/`vmulq_f32`,
                                // `<4 x f32>`) lower through the SAME per-lane
                                // shape as the integer forms, but with the IEEE
                                // `FAdd`/`FSub`/`FMul` ops (NEON `fadd`/`fmul.4s`).
                                let (se, sc) =
                                    simd_vector_lanes_any(cx, operand_concrete_ty(cx, &a.node))
                                        .ok_or_else(|| {
                                            format!("{simd_name}: non-SIMD-vector source")
                                        })?;
                                let a_ptr = operand_place_address(cx, fb, env, &a.node)?;
                                let b_ptr = operand_place_address(cx, fb, env, &b.node)?;
                                let dst_ptr = place_address(cx, fb, env, destination)?;
                                let w = simd_lane_bytes(&se);
                                let op = if is_float_tir(&se) {
                                    match simd_name {
                                        "simd_add" => BinOp::FAdd,
                                        "simd_sub" => BinOp::FSub,
                                        _ => BinOp::FMul,
                                    }
                                } else {
                                    match simd_name {
                                        "simd_add" => BinOp::Add,
                                        "simd_sub" => BinOp::Sub,
                                        _ => BinOp::Mul,
                                    }
                                };
                                for i in 0..sc {
                                    let off = i * w;
                                    let aa = if off == 0 { a_ptr } else { gep_byte_offset(fb, a_ptr, off) };
                                    let bb = if off == 0 { b_ptr } else { gep_byte_offset(fb, b_ptr, off) };
                                    let va = fb.load(se.clone(), aa);
                                    let vb = fb.load(se.clone(), bb);
                                    let r = fb.binop(op, se.clone(), va, vb);
                                    let dd = if off == 0 { dst_ptr } else { gep_byte_offset(fb, dst_ptr, off) };
                                    fb.store(se.clone(), dd, r);
                                }
                            }
                            // `simd_fma(x, y, z) -> x*y + z`: per-lane multiply-add
                            // (`vfmaq_f32(a,b,c)` = `simd_fma(b,c,a)` = `b*c + a`).
                            // trust-ir has NO fused-multiply-add op (BinOp lacks
                            // FMA), and the module-builder extern path that would
                            // emit a per-lane C `fmaf` call is not reachable from
                            // terminator lowering, so this lowers as a separate
                            // `FMul` then `FAdd`. That is byte-exact whenever the
                            // intermediate product `x*y` is exactly representable in
                            // the lane type (the corpus's small exact operands), but
                            // it DOUBLE-rounds and so may differ by 1 ULP from a
                            // true hardware `fmla` for products that are not exact.
                            "simd_fma" => {
                                let [x, y, z] = &args[..] else {
                                    return Err(format!(
                                        "{simd_name}: expected exactly three args"
                                    ));
                                };
                                let (se, sc) =
                                    simd_vector_lanes_any(cx, operand_concrete_ty(cx, &x.node))
                                        .ok_or_else(|| {
                                            format!("{simd_name}: non-SIMD-vector source")
                                        })?;
                                if !is_float_tir(&se) {
                                    return Err(format!(
                                        "{simd_name}: non-float lane type {se:?}"
                                    ));
                                }
                                let x_ptr = operand_place_address(cx, fb, env, &x.node)?;
                                let y_ptr = operand_place_address(cx, fb, env, &y.node)?;
                                let z_ptr = operand_place_address(cx, fb, env, &z.node)?;
                                let dst_ptr = place_address(cx, fb, env, destination)?;
                                let w = simd_lane_bytes(&se);
                                for i in 0..sc {
                                    let off = i * w;
                                    let xa = if off == 0 { x_ptr } else { gep_byte_offset(fb, x_ptr, off) };
                                    let ya = if off == 0 { y_ptr } else { gep_byte_offset(fb, y_ptr, off) };
                                    let za = if off == 0 { z_ptr } else { gep_byte_offset(fb, z_ptr, off) };
                                    let xv = fb.load(se.clone(), xa);
                                    let yv = fb.load(se.clone(), ya);
                                    let zv = fb.load(se.clone(), za);
                                    let prod = fb.binop(BinOp::FMul, se.clone(), xv, yv);
                                    let r = fb.binop(BinOp::FAdd, se.clone(), prod, zv);
                                    let dd = if off == 0 { dst_ptr } else { gep_byte_offset(fb, dst_ptr, off) };
                                    fb.store(se.clone(), dd, r);
                                }
                            }
                            // `simd_neg(a)`: lanewise integer negation —
                            // `vnegq_s32`, and the first step of `vabsq_s32`
                            // (`simd_neg` then `simd_ge` + `simd_select`). Per-lane
                            // `UnOp::Neg` at the real lane width. Only signed
                            // element vectors reach here (NEON has no `vnegq_u*`).
                            "simd_neg" => {
                                let [a] = &args[..] else {
                                    return Err(
                                        "simd_neg: expected exactly one arg".to_string()
                                    );
                                };
                                let (se, sc) =
                                    simd_int_vector_lanes(cx, operand_concrete_ty(cx, &a.node))
                                        .ok_or_else(|| {
                                            "simd_neg: non-int-vector source".to_string()
                                        })?;
                                let a_ptr = operand_place_address(cx, fb, env, &a.node)?;
                                let dst_ptr = place_address(cx, fb, env, destination)?;
                                let w = int_lane_size(&se);
                                for i in 0..sc {
                                    let off = i * w;
                                    let aa = if off == 0 { a_ptr } else { gep_byte_offset(fb, a_ptr, off) };
                                    let va = fb.load(se.clone(), aa);
                                    let r = fb.unop(UnOp::Neg, se.clone(), va);
                                    let dd = if off == 0 { dst_ptr } else { gep_byte_offset(fb, dst_ptr, off) };
                                    fb.store(se.clone(), dd, r);
                                }
                            }
                            // `simd_select(mask, a, b)`: per-lane blend — lane `i`
                            // takes `a`'s lane where `mask`'s lane is set (all
                            // ones), else `b`'s lane. Used by `vabsq_s32`'s
                            // `simd_select(simd_ge(a, neg), a, neg)`. rustc's
                            // contract is that each mask lane is all-zeros or
                            // all-ones, so `lane != 0` is the exact predicate.
                            // The mask element width is read independently of the
                            // data element width (they coincide for the NEON
                            // integer masks, but this stays correct if they ever
                            // differ).
                            "simd_select" => {
                                let [mask, a, b] = &args[..] else {
                                    return Err(
                                        "simd_select: expected exactly three args".to_string()
                                    );
                                };
                                let (se, sc) =
                                    simd_int_vector_lanes(cx, operand_concrete_ty(cx, &a.node))
                                        .ok_or_else(|| {
                                            "simd_select: non-int-vector source".to_string()
                                        })?;
                                let (me, _mc) =
                                    simd_int_vector_lanes(cx, operand_concrete_ty(cx, &mask.node))
                                        .ok_or_else(|| {
                                            "simd_select: non-int-vector mask".to_string()
                                        })?;
                                let m_ptr = operand_place_address(cx, fb, env, &mask.node)?;
                                let a_ptr = operand_place_address(cx, fb, env, &a.node)?;
                                let b_ptr = operand_place_address(cx, fb, env, &b.node)?;
                                let dst_ptr = place_address(cx, fb, env, destination)?;
                                let w = int_lane_size(&se);
                                let mw = int_lane_size(&me);
                                let zero_m = fb.iconst(me.clone(), 0);
                                for i in 0..sc {
                                    let moff = i * mw;
                                    let ma = if moff == 0 { m_ptr } else { gep_byte_offset(fb, m_ptr, moff) };
                                    let mv = fb.load(me.clone(), ma);
                                    let cond = fb.icmp(ICmpOp::Ne, me.clone(), mv, zero_m);
                                    let off = i * w;
                                    let aa = if off == 0 { a_ptr } else { gep_byte_offset(fb, a_ptr, off) };
                                    let bb = if off == 0 { b_ptr } else { gep_byte_offset(fb, b_ptr, off) };
                                    let va = fb.load(se.clone(), aa);
                                    let vb = fb.load(se.clone(), bb);
                                    let r = fb.select(se.clone(), cond, va, vb);
                                    let dd = if off == 0 { dst_ptr } else { gep_byte_offset(fb, dst_ptr, off) };
                                    fb.store(se.clone(), dd, r);
                                }
                            }
                            // `simd_reduce_add_ordered(x, y)` / `simd_reduce_max(x)`
                            // / `simd_reduce_min(x)`: horizontal fold of an int
                            // vector to one scalar — the NEON `vaddvq_*` /
                            // `vmaxvq_*` / `vminvq_*` (and the D-register `vaddv_*` /
                            // `vmaxv_*`) reduces. Each lane is loaded from the
                            // operand's place at its byte offset and folded with the
                            // ELEMENT-typed scalar op: wrapping `Add` for the sum, a
                            // signed/unsigned compare + `Select` for max/min.
                            // Signedness comes from the vector's element layout, so
                            // `vmaxvq_s16` folds with `Sgt` while `vmaxvq_u8` folds
                            // with `Ugt`. Mirrors the `simd_reduce_all` scalar-fold
                            // pattern (no out-of-line vector leaf). The `_ordered`
                            // sum seeds the fold with its accumulator operand `y`
                            // (which is `0` for the bare `vaddvq_*`), left-to-right;
                            // max/min seed with lane 0.
                            "simd_reduce_add_ordered"
                            | "simd_reduce_max"
                            | "simd_reduce_min" => {
                                let a = args.first().ok_or_else(|| {
                                    format!("{simd_name}: expected at least one arg")
                                })?;
                                let (elem, sc) = simd_int_vector_lanes(
                                    cx,
                                    operand_concrete_ty(cx, &a.node),
                                )
                                .ok_or_else(|| {
                                    format!("{simd_name}: non-int-vector source")
                                })?;
                                let w = int_lane_size(&elem);
                                if w == 0 || sc == 0 {
                                    return Err(format!(
                                        "{simd_name}: unsupported lane shape \
                                         {elem:?} x {sc}"
                                    ));
                                }
                                let src_ptr =
                                    operand_place_address(cx, fb, env, &a.node)?;
                                let signed = is_signed(&elem);
                                // Seed with lane 0.
                                let mut acc = fb.load(elem.clone(), src_ptr);
                                // `_ordered` sum prepends the accumulator operand:
                                // `acc_arg + lane0 + lane1 + ...` (left-to-right).
                                if simd_name == "simd_reduce_add_ordered" {
                                    if let Some(accum) = args.get(1) {
                                        let (av, aty) = lower_operand(
                                            cx,
                                            fb,
                                            env,
                                            &accum.node,
                                        )?;
                                        let seed = int_cast(fb, av, &aty, &elem);
                                        acc = fb.binop(
                                            BinOp::Add,
                                            elem.clone(),
                                            seed,
                                            acc,
                                        );
                                    }
                                }
                                for i in 1..sc {
                                    let p = gep_byte_offset(fb, src_ptr, i * w);
                                    let lane = fb.load(elem.clone(), p);
                                    acc = match simd_name {
                                        "simd_reduce_add_ordered" => fb.binop(
                                            BinOp::Add,
                                            elem.clone(),
                                            acc,
                                            lane,
                                        ),
                                        "simd_reduce_max" => {
                                            let op = if signed {
                                                ICmpOp::Sgt
                                            } else {
                                                ICmpOp::Ugt
                                            };
                                            let c = fb
                                                .icmp(op, elem.clone(), lane, acc);
                                            fb.select(elem.clone(), c, lane, acc)
                                        }
                                        // simd_reduce_min
                                        _ => {
                                            let op = if signed {
                                                ICmpOp::Slt
                                            } else {
                                                ICmpOp::Ult
                                            };
                                            let c = fb
                                                .icmp(op, elem.clone(), lane, acc);
                                            fb.select(elem.clone(), c, lane, acc)
                                        }
                                    };
                                }
                                // The reduce result IS the element type; cast to the
                                // destination scalar type only if it differs.
                                let dst_ty = scalar_tir_ty(
                                    cx.place_concrete_ty(destination),
                                )
                                .unwrap_or_else(|| elem.clone());
                                let r = int_cast(fb, acc, &elem, &dst_ty);
                                bind_call_destination(cx, fb, env, destination, r)?;
                            }
                            // `simd_saturating_add` / `simd_saturating_sub`:
                            // per-lane saturating integer add/sub — the aarch64
                            // `vqadd*` / `vqsub*` family (`uqadd`/`sqadd`/
                            // `uqsub`/`sqsub`). Each lane is computed in a SIGNED
                            // wide type (2x the lane width) so that unsigned
                            // underflow surfaces as a negative value; the result
                            // is clamped to the LANE type's value range and
                            // truncated back. Using a signed-wide detour makes
                            // both the signed clamp AND the unsigned-sub floor
                            // (`a<b -> 0`) fall out of one min/max clamp. Pure
                            // integer arithmetic, so byte-exact.
                            "simd_saturating_add" | "simd_saturating_sub" => {
                                let [a, b] = &args[..] else {
                                    return Err(format!(
                                        "{simd_name}: expected exactly two args"
                                    ));
                                };
                                let (se, sc) = simd_int_vector_lanes(
                                    cx,
                                    operand_concrete_ty(cx, &a.node),
                                )
                                .ok_or_else(|| {
                                    format!("{simd_name}: non-int-vector source")
                                })?;
                                let w = int_lane_size(&se);
                                // Signed wide type = 2x the lane width. A 64-bit
                                // lane would need a 128-bit detour the backend
                                // does not lower here — fail-closed.
                                let we = match w {
                                    1 => TIRTy::I16,
                                    2 => TIRTy::I32,
                                    4 => TIRTy::I64,
                                    _ => {
                                        return Err(format!(
                                            "{simd_name}: unsupported lane width \
                                             {w} bytes"
                                        ))
                                    }
                                };
                                // The LANE type's saturation bounds, as wide-type
                                // constants.
                                let bits = w * 8;
                                let (lo, hi) = if is_signed(&se) {
                                    (
                                        -(1i128 << (bits - 1)),
                                        (1i128 << (bits - 1)) - 1,
                                    )
                                } else {
                                    (0i128, (1i128 << bits) - 1)
                                };
                                let op = if simd_name == "simd_saturating_add" {
                                    BinOp::Add
                                } else {
                                    BinOp::Sub
                                };
                                let a_ptr =
                                    operand_place_address(cx, fb, env, &a.node)?;
                                let b_ptr =
                                    operand_place_address(cx, fb, env, &b.node)?;
                                let dst_ptr =
                                    place_address(cx, fb, env, destination)?;
                                let hic = fb.iconst(we.clone(), hi);
                                let loc = fb.iconst(we.clone(), lo);
                                for i in 0..sc {
                                    let off = i * w;
                                    let aa = if off == 0 { a_ptr } else { gep_byte_offset(fb, a_ptr, off) };
                                    let bb = if off == 0 { b_ptr } else { gep_byte_offset(fb, b_ptr, off) };
                                    let va = fb.load(se.clone(), aa);
                                    let vb = fb.load(se.clone(), bb);
                                    let aw = int_cast(fb, va, &se, &we);
                                    let bw = int_cast(fb, vb, &se, &we);
                                    let s = fb.binop(op, we.clone(), aw, bw);
                                    let over = fb.icmp(ICmpOp::Sgt, we.clone(), s, hic);
                                    let s1 = fb.select(we.clone(), over, hic, s);
                                    let under = fb.icmp(ICmpOp::Slt, we.clone(), s1, loc);
                                    let s2 = fb.select(we.clone(), under, loc, s1);
                                    let r = int_cast(fb, s2, &we, &se);
                                    let dd = if off == 0 { dst_ptr } else { gep_byte_offset(fb, dst_ptr, off) };
                                    fb.store(se.clone(), dd, r);
                                }
                            }
                            other => {
                                return Err(format!(
                                    "unmapped simd intrinsic `{other}` (fail-closed; add a \
                                     trust-ir vector lowering before enabling it)"
                                ));
                            }
                        }
                        let edge = tc.edge_args(env, ret_bb)?;
                        fb.br(tc.target_block(ret_bb), edge);
                        return Ok(());
                    }
                    // RUNG (bit-count): `cttz`/`cttz_nonzero` — count trailing
                    // zeros. memchr's aarch64 NEON `first_offset` computes the
                    // matched byte index as `mask.trailing_zeros() >> 2`
                    // (`cttz` over the movemask u64), so the 128-bit byte scan
                    // links to it. trust-ir has no dedicated cttz op, but the
                    // identity `cttz(x) == popcount((x - 1) & !x)` expresses it
                    // exactly over the verified `Sub`/`Not`/`And`/`CtPop` ops
                    // (x==0 -> all-ones mask -> popcount == bit width, the
                    // `trailing_zeros(0) == width` contract; `cttz_nonzero`
                    // never sees x==0 so the same formula is a safe superset).
                    // The intrinsic returns `u32`; the popcount is computed at
                    // the operand width then cast down. Handled BEFORE the
                    // generic call path so it never becomes an extern leaf.
                    if matches!(idef.name.as_str(), "cttz" | "cttz_nonzero") {
                        let ret_bb = target.ok_or_else(|| {
                            "cttz intrinsic: call must have a return target".to_string()
                        })?;
                        let [x] = &args[..] else {
                            return Err(format!(
                                "cttz intrinsic {}: expected exactly one arg",
                                idef.name
                            ));
                        };
                        let (xv, xty) = lower_operand(cx, fb, env, &x.node)?;
                        if int_lane_size(&xty) == 0 {
                            return Err(format!(
                                "cttz intrinsic {}: operand is not an integer ({xty:?})",
                                idef.name
                            ));
                        }
                        let one = fb.iconst(xty.clone(), 1);
                        let xm1 = fb.binop(BinOp::Sub, xty.clone(), xv, one);
                        let nx = fb.unop(UnOp::Not, xty.clone(), xv);
                        let masked = fb.binop(BinOp::And, xty.clone(), xm1, nx);
                        let pc = fb.unop(UnOp::CtPop, xty.clone(), masked);
                        let dst_ty = scalar_tir_ty(cx.place_concrete_ty(destination))
                            .unwrap_or(TIRTy::U32);
                        let r = int_cast(fb, pc, &xty, &dst_ty);
                        bind_call_destination(cx, fb, env, destination, r)?;
                        let edge = tc.edge_args(env, ret_bb)?;
                        fb.br(tc.target_block(ret_bb), edge);
                        return Ok(());
                    }
                    // RUNG (floats): the BODILESS float-math intrinsics — width-
                    // suffixed sqrt/floor/ceil/trunc and the generic `fabs` — have
                    // no fallback MIR body ("must be overridden by the codegen
                    // backend"), so they lower HERE as first-class trust-ir float
                    // unary ops (trust-cg codegens each natively: aarch64
                    // fsqrt / frintm / frintp / frintz / fabs). The
                    // `minimum_number_nsz_*` / `maximum_number_nsz_*` pair (which
                    // DO carry a fallback MIR body) now lowers to the native
                    // FMin/FMax binary ops below — the same FMINNM/FMAXNM
                    // instruction native rustc selects — instead of the
                    // compare+branch reference body. The transcendental /
                    // rounding intrinsics (`powf64`, `expf32`, `roundf64`, ...)
                    // are NOT handled here: the pre-pass declared them as REAL
                    // extern calls to the C libm symbols (`pow`, `expf`,
                    // `round`, ... — see `libm_intrinsic_extern_symbol`), so they
                    // flow through the ordinary direct-call path.
                    let float_unop = match idef.name.as_str() {
                        "sqrtf32" | "sqrtf64" => Some(UnOp::FSqrt),
                        "floorf32" | "floorf64" => Some(UnOp::FFloor),
                        "ceilf32" | "ceilf64" => Some(UnOp::FCeil),
                        "truncf32" | "truncf64" => Some(UnOp::FTrunc),
                        "fabs" => Some(UnOp::FAbs),
                        _ => None,
                    };
                    if let Some(fop) = float_unop {
                        let ret_bb = target.ok_or_else(|| {
                            "float intrinsic: call must have a return target".to_string()
                        })?;
                        let [x] = &args[..] else {
                            return Err(format!(
                                "float intrinsic {}: expected exactly one arg",
                                idef.name
                            ));
                        };
                        let (xv, xty) = lower_operand(cx, fb, env, &x.node)?;
                        // Only f32/f64 have a verified backend lowering; a generic
                        // `fabs::<f16/f128>` (or any non-float arg) fails loud.
                        if !matches!(xty, TIRTy::F32 | TIRTy::F64) {
                            return Err(format!(
                                "float intrinsic {} arg is not an f32/f64 ({xty:?})",
                                idef.name
                            ));
                        }
                        let r = fb.unop(fop, xty, xv);
                        bind_call_destination(cx, fb, env, destination, r)?;
                        let edge = tc.edge_args(env, ret_bb)?;
                        fb.br(tc.target_block(ret_bb), edge);
                        return Ok(());
                    }
                    // FLOATS: `f64::min`/`f64::max` (and the f32 duals) — the
                    // `minimum_number_nsz_*`/`maximum_number_nsz_*` intrinsics —
                    // lower to the NATIVE trust-ir FMin/FMax binary ops (aarch64
                    // FMINNM/FMAXNM: IEEE-754 minNum/maxNum, a quiet-NaN operand
                    // LOSES), the same instruction native rustc's
                    // `llvm.minnum`/`llvm.maxnum` select — replacing the
                    // fallback-MIR-body call path with one verified instruction.
                    // The nsz contract is preserved exactly: on equal-magnitude
                    // signed zeros the instruction's choice is one of the two the
                    // intrinsic explicitly allows.
                    let float_binop = match idef.name.as_str() {
                        "minimum_number_nsz_f32" | "minimum_number_nsz_f64" => {
                            Some(BinOp::FMin)
                        }
                        "maximum_number_nsz_f32" | "maximum_number_nsz_f64" => {
                            Some(BinOp::FMax)
                        }
                        _ => None,
                    };
                    if let Some(fop) = float_binop {
                        let ret_bb = target.ok_or_else(|| {
                            "float min/max intrinsic: call must have a return target"
                                .to_string()
                        })?;
                        let [x, y] = &args[..] else {
                            return Err(format!(
                                "float intrinsic {}: expected exactly two args",
                                idef.name
                            ));
                        };
                        let (xv, xty) = lower_operand(cx, fb, env, &x.node)?;
                        let (yv, yty) = lower_operand(cx, fb, env, &y.node)?;
                        if !matches!(xty, TIRTy::F32 | TIRTy::F64) || yty != xty {
                            return Err(format!(
                                "float intrinsic {} args are not matching f32/f64 \
                                 ({xty:?}, {yty:?})",
                                idef.name
                            ));
                        }
                        let r = fb.binop(fop, xty, xv, yv);
                        bind_call_destination(cx, fb, env, destination, r)?;
                        let edge = tc.edge_args(env, ret_bb)?;
                        fb.br(tc.target_block(ret_bb), edge);
                        return Ok(());
                    }
                    // FLOATS: `powif64`/`powif32` — float ** i32 — expands INLINE
                    // to the classic square-and-multiply loop, the SAME algorithm
                    // as compiler-rt's `__powidf2` (what `llvm.powi` becomes as a
                    // libcall):
                    //   r = 1; loop { if b & 1 { r *= a };
                    //                 b /= 2 (signed, toward zero);
                    //                 if b == 0 { break }; a *= a }
                    //   return b_initial < 0 ? 1/r : r
                    // An honest multiplication/loop expansion over existing
                    // verified ops — no extern, no new instruction, bit-identical
                    // to the libcall for every input.
                    if matches!(idef.name.as_str(), "powif32" | "powif64") {
                        let fty = if idef.name.as_str() == "powif64" {
                            TIRTy::F64
                        } else {
                            TIRTy::F32
                        };
                        let ret_bb = target.ok_or_else(|| {
                            "powi intrinsic: call must have a return target".to_string()
                        })?;
                        let [a0, b0] = &args[..] else {
                            return Err(
                                "powi intrinsic: expected exactly two args".to_string()
                            );
                        };
                        let (av, aty) = lower_operand(cx, fb, env, &a0.node)?;
                        let (bv, bty) = lower_operand(cx, fb, env, &b0.node)?;
                        if aty != fty || !matches!(bty, TIRTy::I32) {
                            return Err(format!(
                                "powi intrinsic arg types ({aty:?}, {bty:?}) are not \
                                 ({fty:?}, I32)"
                            ));
                        }
                        let zero = fb.iconst(TIRTy::I32, 0);
                        let recip = fb.icmp(ICmpOp::Slt, TIRTy::I32, bv, zero);
                        let one_f = fb.fconst(fty.clone(), 1.0);
                        let head = fb.create_block();
                        let exit = fb.create_block();
                        let r = fb.add_block_param(head, fty.clone());
                        let a = fb.add_block_param(head, fty.clone());
                        let b = fb.add_block_param(head, TIRTy::I32);
                        fb.br(head, vec![one_f, av, bv]);
                        // head(r, a, b): one do-while iteration per halving of b.
                        fb.switch_to_block(head);
                        let one_i = fb.iconst(TIRTy::I32, 1);
                        let bit = fb.binop(BinOp::And, TIRTy::I32, b, one_i);
                        let zero_h = fb.iconst(TIRTy::I32, 0);
                        let odd = fb.icmp(ICmpOp::Ne, TIRTy::I32, bit, zero_h);
                        let ra = fb.binop(BinOp::FMul, fty.clone(), r, a);
                        let r2 = fb.select(fty.clone(), odd, ra, r);
                        let two = fb.iconst(TIRTy::I32, 2);
                        let b2 = fb.binop(BinOp::SDiv, TIRTy::I32, b, two);
                        let zero_t = fb.iconst(TIRTy::I32, 0);
                        let last = fb.icmp(ICmpOp::Eq, TIRTy::I32, b2, zero_t);
                        let a2 = fb.binop(BinOp::FMul, fty.clone(), a, a);
                        fb.condbr(last, exit, vec![], head, vec![r2, a2, b2]);
                        // exit: `r2` dominates (its def block is the sole
                        // predecessor); `recip` dominates from the pre-loop block.
                        fb.switch_to_block(exit);
                        let one_f2 = fb.fconst(fty.clone(), 1.0);
                        let inv = fb.binop(BinOp::FDiv, fty.clone(), one_f2, r2);
                        let res = fb.select(fty, recip, inv, r2);
                        bind_call_destination(cx, fb, env, destination, res)?;
                        let edge = tc.edge_args(env, ret_bb)?;
                        fb.br(tc.target_block(ret_bb), edge);
                        return Ok(());
                    }
                }
            }
            // Both panic lanes: a size-scaled raw-memory intrinsic mono
            // (`copy` / `write_bytes`) lowered INLINE with the
            // element stride baked in (pre-pass `MemIntrinsicInline`):
            // byte-exact libc memmove / libc memset for non-ZST elements, an
            // exact no-op for ZST elements — never the byte-scaled harness leaf.
            if let Some(mi) = tc.mem_intrinsic {
                return lower_mem_intrinsic_inline(
                    cx,
                    fb,
                    env,
                    tc,
                    mi,
                    args,
                    *target,
                );
            }
            // A cross-crate raw-pointer `offset` / `wrapping_offset` wrapper,
            // inlined through the preselected faithful pointer-arithmetic lane.
            if let Some(inline) = tc.raw_ptr_offset {
                return lower_raw_ptr_offset_inline(
                    cx,
                    fb,
                    env,
                    tc,
                    inline,
                    args,
                    destination,
                    *target,
                );
            }
            // RUNG 5: an `<Arc<T> as Deref>::deref` inlined to pointer arithmetic.
            // The single arg is `&Arc<T>` — the ADDRESS holding the thin Arc
            // pointer. Load that thin pointer, add the ArcInner data offset, and
            // bind the resulting `&T` to the destination. No `call`, no extern.
            if let Some(off) = tc.arc_deref_offset {
                let [arg] = &args[..] else {
                    return Err("Arc::deref inline: expected exactly one arg".to_string());
                };
                let (arg_ptr, arg_ty) = lower_operand(cx, fb, env, &arg.node)?;
                if !matches!(arg_ty, TIRTy::Ptr) {
                    return Err(format!("Arc::deref inline: arg is not a pointer ({arg_ty:?})"));
                }
                // `arg_ptr` = `&Arc<T>` = address of the 8-byte thin Arc pointer.
                let arc_thin = fb.load(TIRTy::Ptr, arg_ptr);
                // `&(*self.ptr).data` = thin pointer + ArcInner data offset.
                let data_ref = gep_byte_offset(fb, arc_thin, off);
                bind_call_destination(cx, fb, env, destination, data_ref)?;
                let ret_bb = target
                    .ok_or_else(|| "Arc::deref inline: deref call must have a return target".to_string())?;
                let edge = tc.edge_args(env, ret_bb)?;
                fb.br(tc.target_block(ret_bb), edge);
                return Ok(());
            }
            // RUNG 6: an `Arc::<T>::new(x)` inlined to a heap allocation of
            // `ArcInner<T>` + counter/data Stores. Allocate `total_size` bytes
            // (align `block_align`), Store `strong=1`/`weak=1` at offsets
            // `0`/`pointer_size`, Store `x` at `data_offset`, and bind the block base
            // (the thin `Arc<T>` value) to the destination. No `call`, no extern.
            //
            // HONEST: this faithfully CONSTRUCTS the block (and the RUNG-5 read finds
            // `x` at `data_offset`), but Arc DROP (the strong-count decrement + the
            // conditional dealloc) is NOT modeled — a dropped Arc LEAKS its block. For
            // a verification round-trip that owns its inputs and compares constructed
            // RESULTS this is sound; faithful refcounting/dealloc is separate.
            if let Some(layout) = tc.arc_new_layout.clone() {
                let [arg] = &args[..] else {
                    return Err("Arc::new inline: expected exactly one arg".to_string());
                };
                let ptr_size = cx.tcx.data_layout.pointer_size().bytes();
                // The block: `total_size` bytes from the Rust heap (`__rust_alloc`),
                // aligned to `block_align`. An i8 element with a constant count gives
                // exactly `total_size` bytes (the adapter folds count*1).
                let count = fb.iconst(TIRTy::I64, layout.total_size as i128);
                let base = fb.heap_alloc(
                    TIRTy::I8,
                    Some(count),
                    Some(layout.block_align),
                    trust_ir::inst::AllocOrigin::RustHeap,
                );
                // `strong = 1` at offset 0, `weak = 1` at offset `pointer_size`. Both
                // are `AtomicUsize` — a `pointer_size` integer; the RUNG-5 read never
                // touches them, but a faithful block initializes them as Rust does.
                let counter_ty = if ptr_size == 8 { TIRTy::U64 } else { TIRTy::U32 };
                let one = fb.iconst(counter_ty.clone(), 1);
                fb.store(counter_ty.clone(), base, one);
                let weak_addr = gep_byte_offset(fb, base, ptr_size);
                let one2 = fb.iconst(counter_ty.clone(), 1);
                fb.store(counter_ty, weak_addr, one2);
                // `data = x` at `data_offset`. A single scalar pointee is a typed
                // Store of the lowered arg value; an aggregate pointee is a lane copy
                // from the arg's source slot; a ZST pointee Stores nothing.
                let data_addr = if layout.data_offset == 0 {
                    base
                } else {
                    gep_byte_offset(fb, base, layout.data_offset)
                };
                if layout.data_size != 0 {
                    if let Some(scalar) = layout.data_scalar.clone() {
                        let (v, _t) = lower_operand(cx, fb, env, &arg.node)?;
                        fb.store(scalar, data_addr, v);
                    } else {
                        // Aggregate pointee: copy `size_of::<T>` bytes lane-by-lane
                        // from the arg's source slot into `base + data_offset`.
                        let (Operand::Copy(place) | Operand::Move(place)) = &arg.node else {
                            return Err(
                                "Arc::new inline: aggregate arg is not a place".to_string()
                            );
                        };
                        let src_addr = place_address(cx, fb, env, place)?;
                        copy_aggregate_bytes(
                            fb,
                            src_addr,
                            data_addr,
                            layout.data_size,
                            layout.data_align,
                        )?;
                    }
                }
                bind_call_destination(cx, fb, env, destination, base)?;
                let ret_bb = target.ok_or_else(|| {
                    "Arc::new inline: constructor call must have a return target".to_string()
                })?;
                let edge = tc.edge_args(env, ret_bb)?;
                fb.br(tc.target_block(ret_bb), edge);
                return Ok(());
            }
            // RUNG 7: the `(uN, uN, &str) -> uN` saturating-add diagnostic helper,
            // inlined to `a.saturating_add(b)` = `overflow(Add) + select-to-max`,
            // DROPPING the dead `&str` message arg entirely. This faithfully
            // reproduces `checked_add_u32`'s observable effect without ever
            // materializing the `&str` const (which the in-process JIT cannot
            // relocate). No `call`, no extern.
            if let Some(lane) = tc.sat_add_lane.clone() {
                let [a0, a1, _msg] = &args[..] else {
                    return Err("saturating-add inline: expected exactly 3 args".to_string());
                };
                let (lhs, _lt) = lower_operand(cx, fb, env, &a0.node)?;
                let (rhs, _rt) = lower_operand(cx, fb, env, &a1.node)?;
                // `(sum, overflow) = a + b`; saturate to the unsigned MAX of this
                // lane on overflow: `select(overflow, MAX, sum)`.
                let (sum, ovf) = fb.overflow(OverflowOp::AddOverflow, lane.clone(), lhs, rhs);
                let max = uint_max_const(fb, &lane)?;
                let saturated = fb.select(lane, ovf, max, sum);
                bind_call_destination(cx, fb, env, destination, saturated)?;
                let ret_bb = target.ok_or_else(|| {
                    "saturating-add inline: call must have a return target".to_string()
                })?;
                let edge = tc.edge_args(env, ret_bb)?;
                fb.br(tc.target_block(ret_bb), edge);
                return Ok(());
            }
            // RUNG 8b: `IntoIterator::into_iter(<vec or &vec or slice>)` inlined to a
            // `(cur,end)` cursor init. The single arg is a pointer to the SOURCE Vec
            // (a `&Vec` for borrowed, or the moved-Vec slot for owned); read its
            // `{ptr@0, len@<2*ptr_size>}`, compute `end = ptr + len*stride`, and Store
            // the two cursor words into the destination iterator slot (`cur@0,end@8`).
            // No `call`, no extern. (The Vec's buffer is leaked — owned `into_iter`
            // just copies the buffer pointer; the leak model owns this.)
            if let Some(model) = tc.into_iter_model.clone() {
                let [arg] = &args[..] else {
                    return Err("into_iter inline: expected exactly one arg".to_string());
                };
                // The source Vec address. For OWNED iteration the arg is the Vec BY
                // VALUE (an aggregate place) — take its slot ADDRESS. For BORROWED the
                // arg is a `&Vec`/`&[T]` reference VALUE — lower it to the held pointer.
                let vec_ptr = match model.kind {
                    IterKind::VecIntoIter => {
                        let (Operand::Copy(place) | Operand::Move(place)) = &arg.node else {
                            return Err(
                                "into_iter inline: owned Vec arg is not a place".to_string()
                            );
                        };
                        place_address(cx, fb, env, place)?
                    }
                    IterKind::SliceIter => {
                        let (p, _t) = lower_operand(cx, fb, env, &arg.node)?;
                        p
                    }
                    // `StrBytes` never appears as an `into_iter` model: the str
                    // BYTES iterator is BUILT by the `str::bytes` cursor-init
                    // inline and hopped by the blanket-identity `into_iter`
                    // (`StrInlineOp`), never by this Vec-source path.
                    IterKind::StrBytes => {
                        return Err(
                            "into_iter inline: StrBytes is not a Vec-source model".to_string()
                        );
                    }
                };
                let iter_ptr = place_address(cx, fb, env, destination)?;
                // Read the source Vec's `ptr` (buffer base) + `len` at their faithful
                // `tcx.layout_of`-derived offsets (the RawVec field order is an
                // internal detail we do NOT assume).
                let ptr_addr = if model.vec_ptr_off == 0 {
                    vec_ptr
                } else {
                    gep_byte_offset(fb, vec_ptr, model.vec_ptr_off)
                };
                let base = fb.load(TIRTy::Ptr, ptr_addr);
                let len_addr = gep_byte_offset(fb, vec_ptr, model.vec_len_off);
                let len = fb.load(TIRTy::I64, len_addr);
                // `end = base + len * stride` (i8-element GEP by a byte count).
                let stride = fb.iconst(TIRTy::I64, model.stride as i128);
                let byte_len = fb.binop(BinOp::Mul, TIRTy::I64, len, stride);
                let end = fb.gep(TIRTy::I8, base, vec![byte_len]);
                // Store the cursor at the MODEL's offsets — the REAL `ptr`/`end`
                // fields for an owned `vec::IntoIter` (THREADS: real bodies
                // like `size_hint` / the drop glue read this same state), the
                // classic `(0, 8)` pair for slice iterators.
                let cur_addr = if model.cur_off == 0 {
                    iter_ptr
                } else {
                    gep_byte_offset(fb, iter_ptr, model.cur_off)
                };
                fb.store(TIRTy::Ptr, cur_addr, base);
                let end_addr = gep_byte_offset(fb, iter_ptr, model.end_off);
                fb.store(TIRTy::Ptr, end_addr, end);
                // THREADS (owned IntoIter): initialize the REAL `buf` + `cap`
                // fields too — the drop glue frees `buf` with `cap` elements.
                if let Some(buf_off) = model.init_buf_off {
                    let buf_addr = if buf_off == 0 {
                        iter_ptr
                    } else {
                        gep_byte_offset(fb, iter_ptr, buf_off)
                    };
                    fb.store(TIRTy::Ptr, buf_addr, base);
                }
                if let Some(cap_off) = model.init_cap_off {
                    let src_cap_addr = if model.vec_cap_off == 0 {
                        vec_ptr
                    } else {
                        gep_byte_offset(fb, vec_ptr, model.vec_cap_off)
                    };
                    let cap = fb.load(TIRTy::I64, src_cap_addr);
                    let dst_cap_addr = if cap_off == 0 {
                        iter_ptr
                    } else {
                        gep_byte_offset(fb, iter_ptr, cap_off)
                    };
                    fb.store(TIRTy::I64, dst_cap_addr, cap);
                }
                let ret_bb = target
                    .ok_or_else(|| "into_iter inline: call must have a return target".to_string())?;
                let edge = tc.edge_args(env, ret_bb)?;
                fb.br(tc.target_block(ret_bb), edge);
                return Ok(());
            }
            // RUNG 8b: `Iterator::next(&mut iter)` inlined to a cursor index-bump +
            // `Some`/`None` write into the destination `Option<..>` slot. The single
            // arg is `&mut iter`; load its `(cur,end)` words. If `cur < end`: take the
            // element pointer `p = cur`, bump `cur += stride`, write it back, and write
            // `Some(p)` — for a `slice::Iter` that is the `&T` pointer itself; for a
            // `vec::IntoIter` it is the by-value `T` (a `size_of::<T>` aggregate move
            // into the Some payload). Else write `None`. The Option niche encoding is
            // taken from `mir_enum_layout` so the surrounding discriminant-read agrees.
            if let Some(model) = tc.iter_next_model.clone() {
                let [arg] = &args[..] else {
                    return Err("next inline: expected exactly one arg".to_string());
                };
                let (iter_ptr, _t) = lower_operand(cx, fb, env, &arg.node)?;
                let ret_bb = target
                    .ok_or_else(|| "next inline: call must have a return target".to_string())?;
                lower_iter_next(cx, fb, env, tc, &model, iter_ptr, destination, ret_bb)?;
                return Ok(());
            }
            // RUNG 8b: `Box::<U>::new_uninit()` inlined to a `heap_alloc` of the
            // pointee buffer (`total_size` bytes, `align`), binding the buffer pointer
            // to the destination box local. No `call`, no extern.
            if let Some(layout) = tc.box_new_uninit.clone() {
                if !args.is_empty() {
                    return Err("Box::new_uninit inline: expected zero args".to_string());
                }
                let count = fb.iconst(TIRTy::I64, layout.total_size as i128);
                let buf = fb.heap_alloc(
                    TIRTy::I8,
                    Some(count),
                    Some(layout.align),
                    trust_ir::inst::AllocOrigin::RustHeap,
                );
                bind_call_destination(cx, fb, env, destination, buf)?;
                let ret_bb = target.ok_or_else(|| {
                    "Box::new_uninit inline: call must have a return target".to_string()
                })?;
                let edge = tc.edge_args(env, ret_bb)?;
                fb.br(tc.target_block(ret_bb), edge);
                return Ok(());
            }
            // RUNG 8b: `box_assume_init_into_vec_unsafe::<T,N>(box)` inlined to a
            // 3-word `Vec{ptr=<box buffer>, cap=N, len=N}` header materialization into
            // the destination Vec slot. The box's buffer pointer is the single arg.
            // No `call`, no extern.
            if let Some(layout) = tc.box_into_vec.clone() {
                let [arg] = &args[..] else {
                    return Err("box->Vec inline: expected exactly one arg".to_string());
                };
                let (box_ptr, _t) = lower_operand(cx, fb, env, &arg.node)?;
                let vec_ptr = place_address(cx, fb, env, destination)?;
                // The destination's `Vec<T>` field offsets (faithful `tcx.layout_of`,
                // NOT a hardcoded `{ptr,cap,len}` order — the RawVec field order is an
                // internal detail).
                let vec_ty = cx.place_concrete_ty(destination);
                let vfo = vec_field_offsets(cx, vec_ty)?;
                // `ptr = box buffer` at `ptr_off`.
                let ptr_addr = if vfo.ptr_off == 0 {
                    vec_ptr
                } else {
                    gep_byte_offset(fb, vec_ptr, vfo.ptr_off)
                };
                fb.store(TIRTy::Ptr, ptr_addr, box_ptr);
                // `cap = N` at `cap_off`, `len = N` at `len_off`.
                let n = fb.iconst(TIRTy::I64, layout.count as i128);
                let cap_addr = if vfo.cap_off == 0 {
                    vec_ptr
                } else {
                    gep_byte_offset(fb, vec_ptr, vfo.cap_off)
                };
                fb.store(TIRTy::I64, cap_addr, n);
                let n2 = fb.iconst(TIRTy::I64, layout.count as i128);
                let len_addr = if vfo.len_off == 0 {
                    vec_ptr
                } else {
                    gep_byte_offset(fb, vec_ptr, vfo.len_off)
                };
                fb.store(TIRTy::I64, len_addr, n2);
                let ret_bb = target
                    .ok_or_else(|| "box->Vec inline: call must have a return target".to_string())?;
                let edge = tc.edge_args(env, ret_bb)?;
                fb.br(tc.target_block(ret_bb), edge);
                return Ok(());
            }
            // ADDITIVE (R4 stage 2): an in-module str/byte call shape — fat-pair
            // lane reads / cursor writes instead of a `call`. No extern. See the
            // `StrInlineOp` section header for the design + faithfulness notes.
            if let Some(op) = tc.str_inline.clone() {
                let ret_bb = target
                    .ok_or_else(|| "str inline: call must have a return target".to_string())?;
                let [arg] = &args[..] else {
                    return Err("str inline: expected exactly one arg".to_string());
                };
                match op {
                    // `str::as_bytes`: identity on the fat pair — copy both
                    // pointer-width lanes into the fat `&[u8]` destination slot
                    // (the `lower_fat_lane_copy` lane discipline).
                    StrInlineOp::AsBytes => {
                        let pair = str_call_arg_pair_addr(cx, fb, env, &arg.node)?;
                        let dst = place_address(cx, fb, env, destination)?;
                        for off in [0u64, 8] {
                            let sa = if off == 0 { pair } else { gep_byte_offset(fb, pair, off) };
                            let da = if off == 0 { dst } else { gep_byte_offset(fb, dst, off) };
                            let v = fb.load(TIRTy::I64, sa);
                            fb.store(TIRTy::I64, da, v);
                        }
                    }
                    // `str::len`: the metadata lane (+8) of the arg pair.
                    StrInlineOp::Len => {
                        let pair = str_call_arg_pair_addr(cx, fb, env, &arg.node)?;
                        let len_addr = gep_byte_offset(fb, pair, 8);
                        let len = fb.load(TIRTy::U64, len_addr);
                        bind_call_destination(cx, fb, env, destination, len)?;
                    }
                    // `str::bytes` / `<[u8]>::iter`: cursor init `cur = data ptr`,
                    // `end = ptr + len` (stride 1 byte) at +0/+8 of the iterator
                    // slot — the exact shape `lower_iter_next` consumes.
                    StrInlineOp::ByteCursorInit => {
                        let pair = str_call_arg_pair_addr(cx, fb, env, &arg.node)?;
                        let base = fb.load(TIRTy::Ptr, pair);
                        let len_addr = gep_byte_offset(fb, pair, 8);
                        let len = fb.load(TIRTy::I64, len_addr);
                        let end = fb.gep(TIRTy::I8, base, vec![len]);
                        let dst = place_address(cx, fb, env, destination)?;
                        fb.store(TIRTy::Ptr, dst, base);
                        let end_addr = gep_byte_offset(
                            fb,
                            dst,
                            cx.tcx.data_layout.pointer_size().bytes(),
                        );
                        fb.store(TIRTy::Ptr, end_addr, end);
                    }
                    // Blanket `into_iter` identity: a `size_of::<I>` aggregate
                    // copy from the arg's iterator slot to the destination's.
                    StrInlineOp::IterIdentity { size, align } => {
                        let (Operand::Copy(place) | Operand::Move(place)) = &arg.node else {
                            return Err(
                                "into_iter identity: arg is not a place".to_string()
                            );
                        };
                        let src = place_address(cx, fb, env, place)?;
                        let dst = place_address(cx, fb, env, destination)?;
                        copy_aggregate_bytes(fb, src, dst, size, align)?;
                    }
                }
                let edge = tc.edge_args(env, ret_bb)?;
                fb.br(tc.target_block(ret_bb), edge);
                return Ok(());
            }
            // Direct extern call, R6 fn-pointer INDIRECT call, or DYN/VIRTUAL dispatch.
            // For the indirect form, lower the `func` operand to its fn-pointer VALUE
            // (MIR evaluates the callee before the args, so this Load precedes the arg
            // lowering). The virtual form is built AFTER `arg_vals` below (it needs the
            // lowered receiver to read the vtable), so it is `None` here.
            let mut ctgt: Option<CallTarget> = if let Some(sig) = tc.indirect_sig {
                let (fnptr, _t) = lower_operand(cx, fb, env, func)?;
                Some(CallTarget::Indirect(fnptr, sig))
            } else if tc.virtual_dispatch.is_some() {
                None
            } else {
                let callee = tc
                    .callee_id
                    .ok_or_else(|| "Call: callee not declared (pre-pass bug)".to_string())?;
                Some(CallTarget::Direct(callee))
            };

            // RUNG 3: the call's ABI return form (must agree with the pre-pass
            // `call_extern_signature`, including the RUNG 10 in-module-edge
            // decision).
            let call_ret =
                call_return_abi(cx, destination, tc.pair_ret_ok, callee_is_extern_c(cx, func))?;
            let has_sret = call_ret.has_sret();

            // Build the trust-ir arg list in signature order: [sret ptr]? ++ per
            // MIR arg (scalar value, or a by-ref aggregate Ptr = the source slot
            // address). A ZST arg occupies no slot.
            let mut arg_vals: Vec<trust_ir::ValueId> =
                Vec::with_capacity(args.len() + has_sret as usize);
            if has_sret {
                // The hidden result pointer = the destination slot's address. The
                // call writes the aggregate result in place through it.
                let dest_addr = place_address(cx, fb, env, destination)?;
                arg_vals.push(dest_addr);
            }
            // RUNG 9: a closure-body callee uses the `"rust-call"` ABI — SPREAD the
            // trailing args tuple. Pass the receiver `self` (the capture struct, by
            // ref), then each tuple field: a scalar field by value (loaded from the
            // tuple slot at its field offset), a by-value aggregate field by ref (a
            // pointer into the tuple slot). This matches the closure body's untupled
            // signature exactly.
            if is_closure_rust_call(cx, func)
                || matches!(tc.virtual_dispatch, Some((_, _, true)))
            {
                // THREADS: a CONSTANT args tuple (`f(None)` in
                // `try_with_current` -> `const (None,)`) is materialized into
                // ONE stack slot the first spread field touches; later fields
                // re-address the same slot.
                let mut const_tuple_addr: Option<trust_ir::ValueId> = None;
                for slot in spread_closure_args(cx, args)? {
                    match slot {
                        SpreadSlot::Whole(op, ArgAbi::Scalar(t)) => {
                            let v = lower_scalar_call_arg(cx, fb, env, &op, &t)?;
                            arg_vals.push(v);
                        }
                        SpreadSlot::Whole(op, ArgAbi::AggByRef) => {
                            let (Operand::Copy(place) | Operand::Move(place)) = &op else {
                                return Err("closure self arg is not a place".to_string());
                            };
                            // An UNSIZED receiver (`move (*_8)` in Box's
                            // call_once) passes its fat CARRIER cell address.
                            let addr = match unsized_arg_carrier_addr(cx, fb, env, place) {
                                Some(r) => r?,
                                None => place_address(cx, fb, env, place)?,
                            };
                            arg_vals.push(addr);
                        }
                        SpreadSlot::Whole(_, ArgAbi::Zst) => {}
                        // A closure receiver is classified with `pair_value_ok=false`,
                        // so it is never a by-value pair — unreachable.
                        SpreadSlot::Whole(_, ArgAbi::PairByValue(_)) => {
                            return Err(
                                "closure receiver unexpectedly a by-value pair (RUNG 11)"
                                    .to_string(),
                            )
                        }
                        SpreadSlot::TupleField { tuple, off, abi } => {
                            let base = match &tuple {
                                Operand::Copy(place) | Operand::Move(place) => {
                                    place_address(cx, fb, env, place)?
                                }
                                // A constant args tuple: materialize its byte
                                // image (provenance included) once, then spread
                                // fields out of that slot.
                                Operand::Constant(c) => match const_tuple_addr {
                                    Some(a) => a,
                                    None => {
                                        let a = materialize_const_aggregate(cx, fb, c)?;
                                        const_tuple_addr = Some(a);
                                        a
                                    }
                                },
                                _ => {
                                    return Err(
                                        "closure args tuple is not a place".to_string()
                                    )
                                }
                            };
                            let addr =
                                if off == 0 { base } else { gep_byte_offset(fb, base, off) };
                            match abi {
                                ArgAbi::Scalar(t) => {
                                    // Load the spread scalar field by value.
                                    let v = fb.load(t, addr);
                                    arg_vals.push(v);
                                }
                                ArgAbi::AggByRef => {
                                    // Pass a pointer into the tuple slot at the field.
                                    arg_vals.push(addr);
                                }
                                ArgAbi::Zst => {}
                                // Closure spread fields never classify as by-value
                                // pairs (see `spread_closure_args`) — unreachable.
                                ArgAbi::PairByValue(_) => {
                                    return Err(
                                        "closure spread field unexpectedly a by-value pair \
                                         (RUNG 11)"
                                            .to_string(),
                                    )
                                }
                            }
                        }
                    }
                }
            } else {
            for a in args.iter() {
                match classify_call_arg(cx, &a.node, tc.pair_ret_ok)? {
                    ArgAbi::Scalar(t) => {
                        let v = lower_scalar_call_arg(cx, fb, env, &a.node, &t)?;
                        arg_vals.push(v);
                    }
                    ArgAbi::AggByRef => match &a.node {
                        // A str/byte-slice LITERAL arg (R3 stage 1) passes the ADDRESS
                        // of its materialized (ptr,len) pair slot; ANY OTHER aggregate
                        // constant (R1: an enum/struct/tuple value — `None`, `Layout`,
                        // ...) is materialized into a fresh stack slot at the call
                        // site and passed by that slot's address. The two are
                        // distinguished exactly as `classify_call_arg` admitted them.
                        Operand::Constant(c) => {
                            let addr = if str_const_bytes(cx, c).is_some() {
                                str_const_mat(cx, c)?.pair_ptr
                            } else {
                                materialize_const_aggregate(cx, fb, c)?
                            };
                            arg_vals.push(addr);
                        }
                        // Pass a pointer to the source aggregate's slot (by-ref ABI).
                        // An UNSIZED arg place passes its fat CARRIER cell address.
                        Operand::Copy(place) | Operand::Move(place) => {
                            let addr = match unsized_arg_carrier_addr(cx, fb, env, place) {
                                Some(r) => r?,
                                None => place_address(cx, fb, env, place)?,
                            };
                            arg_vals.push(addr);
                        }
                        _ => {
                            return Err("by-value aggregate call arg is not a place".to_string())
                        }
                    },
                    ArgAbi::Zst => {}
                    // RUNG 11: pass the small pair BY VALUE as ONE SSA 2-tuple — a
                    // single whole-aggregate Load of the source slot (byte-congruent
                    // with the callee's whole-aggregate spill Store: `pair_ret_model`
                    // pins tuple-offset == field-offset). HONEST BOUNDARY: the
                    // source's inter-lane padding must be INITIALIZED (the whole-agg
                    // Load reads the full byte image, padding included). In the
                    // supported whole-program path a small-pair value originates from
                    // a by-value return (RUNG 10 spill) or a by-value pair param
                    // (RUNG 11 spill), both of which zero padding — the exact dual of
                    // RUNG 10's `_0` entry zero-fill.
                    ArgAbi::PairByValue(pr) => match &a.node {
                        Operand::Copy(place) | Operand::Move(place) => {
                            let addr = place_address(cx, fb, env, place)?;
                            let v = fb.load(pr.tuple_ty(), addr);
                            arg_vals.push(v);
                        }
                        _ => {
                            return Err("by-value pair call arg is not a place".to_string())
                        }
                    },
                }
            }
            }
            // `#[track_caller]` ABI (rustc `codegen_call_terminator` parity): a
            // callee that `requires_caller_location` receives ONE extra
            // trailing argument — `get_caller_location` at the call's
            // `fn_span`: this caller's own hidden param when the walk roots in
            // a track_caller body (location forwarding), else the CTFE'd
            // Location of the call site. Matches the `Ptr` the pre-pass
            // appended to the callee's synthesized signature
            // (`call_signature_params_returns`) and the hidden param every
            // lowered track_caller BODY binds — same predicate on all three.
            if callee_needs_caller_location(cx, func) {
                let si = rustc_middle::mir::SourceInfo {
                    span: *fn_span,
                    ..source_info
                };
                arg_vals.push(get_caller_location(cx, fb, si)?);
            }

            // DYN/VIRTUAL dispatch: the receiver is the first non-sret arg, lowered as
            // a pointer to the {data, vtable} fat pair. Load the concrete method
            // fn-pointer from `vtable[slot]`, then REPLACE the receiver arg with the
            // data pointer (the concrete method's `self` is the thin env pointer). The
            // `CallIndirect` signature was registered from the call's own arg/dest ABI.
            if let Some((sig, vslot, _is_rc)) = tc.virtual_dispatch {
                let base = has_sret as usize;
                let recv = *arg_vals.get(base).ok_or_else(|| {
                    "virtual dispatch: missing &dyn receiver arg".to_string()
                })?;
                let data = fb.load(TIRTy::Ptr, recv);
                let vtable_addr = gep_byte_offset(fb, recv, 8);
                let vtable = fb.load(TIRTy::Ptr, vtable_addr);
                let slot_addr = gep_byte_offset(fb, vtable, (vslot as u64) * 8);
                let fnptr = fb.load(TIRTy::Ptr, slot_addr);
                arg_vals[base] = data;
                ctgt = Some(CallTarget::Indirect(fnptr, sig));
            }
            let ctgt =
                ctgt.ok_or_else(|| "Call: dispatch target not built (pre-pass bug)".to_string())?;

            // UNWIND lane: a call carrying a faithful unwind edge lowers as
            // `Invoke`. The unwind destination is a synthesized landing pad:
            // a per-edge cleanup pad that stores the exception object and
            // branches (with the target's live-in args) into the MIR cleanup
            // block, or the shared terminate pad (double-panic trap). A DIRECT
            // callee is invoked as-is; an INDIRECT/virtual callee is invoked
            // through the pre-pass's per-signature direct THUNK —
            // `Invoke(thunk, fnptr, args..)` — because trust-ir `Invoke` is
            // direct-only by format. The unwind propagates through the
            // pad-less thunk frame and lands in THIS frame's pad, so the
            // caller's cleanup runs faithfully.
            if tc.eh {
                match &ctgt {
                    CallTarget::Direct(fid) => {
                        if let Some(pad) = eh_unwind_dest(fb, env, tc, unwind)? {
                            return lower_invoke_call(
                                cx,
                                fb,
                                env,
                                tc,
                                *fid,
                                arg_vals,
                                &call_ret,
                                destination,
                                *target,
                                pad,
                            );
                        }
                    }
                    CallTarget::Indirect(fnptr, _sig) => {
                        if let Some(tfid) = tc.indirect_thunk {
                            if let Some(pad) = eh_unwind_dest(fb, env, tc, unwind)? {
                                let mut targs = Vec::with_capacity(arg_vals.len() + 1);
                                targs.push(*fnptr);
                                targs.extend(arg_vals.iter().copied());
                                return lower_invoke_call(
                                    cx,
                                    fb,
                                    env,
                                    tc,
                                    tfid,
                                    targs,
                                    &call_ret,
                                    destination,
                                    *target,
                                    pad,
                                );
                            }
                        }
                    }
                }
            }

            // Emit the call. We must collect the destination binding BEFORE moving
            // to the next block.
            if let Some(ret_bb) = target {
                match &call_ret {
                    // sret: the result is already written into the destination slot
                    // by the callee; the call returns void.
                    CallRet::Sret => emit_call_void(fb, &ctgt, arg_vals),
                    CallRet::Direct(returns) if returns.is_empty() => {
                        emit_call_void(fb, &ctgt, arg_vals)
                    }
                    CallRet::Direct(_) => {
                        let result = emit_call_value(fb, &ctgt, arg_vals);
                        bind_call_destination(cx, fb, env, destination, result)?;
                    }
                    // RUNG 10: the call returns ONE by-value 2-tuple; spill it
                    // into the destination slot with a single whole-aggregate
                    // Store (byte-congruent with the lane offsets the
                    // destination's field readers use — see `pair_ret_model`).
                    CallRet::Pair(pr) => {
                        let result = emit_call_value(fb, &ctgt, arg_vals);
                        let dst = place_address(cx, fb, env, destination)?;
                        fb.store(pr.tuple_ty(), dst, result);
                    }
                }
                let edge = tc.edge_args(env, *ret_bb)?;
                fb.br(tc.target_block(*ret_bb), edge);
            } else {
                // A diverging call (e.g. a `-> !` panic). The result, if any, is
                // never observed; emit the call then `unreachable`.
                match &call_ret {
                    CallRet::Sret => emit_call_void(fb, &ctgt, arg_vals),
                    CallRet::Direct(returns) if returns.is_empty() => {
                        emit_call_void(fb, &ctgt, arg_vals)
                    }
                    CallRet::Direct(_) | CallRet::Pair(_) => {
                        let _ = emit_call_value(fb, &ctgt, arg_vals);
                    }
                }
                fb.unreachable();
            }
            Ok(())
        }
        // RUNG 2: an overflow / bounds / division / pointer-validity assert.
        // Evaluate `cond`; branch to `target` when it equals `expected`, else the
        // failure (panic) path:
        //   * panic=abort — a shared TRAP block (`unreachable`), byte-identical
        //     to the historical lowering: the message variant only selects which
        //     panic, which the trap subsumes on the never-taken failure path.
        //   * UNWIND lane (a supported message kind) — rustc parity: the failure
        //     arm CALLS the `core::panicking` entry point the pre-pass declared
        //     (message operands + the CTFE'd `&'static Location`), as an
        //     `Invoke` when the assert carries a cleanup/terminate unwind edge —
        //     so an overflow/bounds/div-zero panic UNWINDS, runs cleanup, and is
        //     catchable, exactly like native codegen.
        TerminatorKind::Assert {
            cond,
            expected,
            target,
            msg,
            unwind,
        } => {
            let (cond_v, ct) = lower_operand(cx, fb, env, cond)?;
            if !matches!(ct, TIRTy::Bool) {
                return Err(format!("Assert cond is not bool ({ct:?})"));
            }
            // `assert_cond` is `cond == expected`.
            let assert_cond = if *expected {
                cond_v
            } else {
                let f = fb.bool_const(false);
                fb.icmp(ICmpOp::Eq, TIRTy::Bool, cond_v, f)
            };
            if tc.eh {
                if let Some(ap) = tc.assert_panic {
                    let fail = fb.create_block();
                    let then_args = tc.edge_args(env, *target)?;
                    fb.condbr(
                        assert_cond,
                        tc.target_block(*target),
                        then_args,
                        fail,
                        vec![],
                    );
                    record_assert_site(fb, tc)?;
                    fb.switch_to_block(fail);
                    // Pad synthesis switches back to `tc.cur_blk` when done —
                    // the invoke lives in the failure arm now.
                    tc.cur_blk = fail;
                    let mut pargs: Vec<trust_ir::ValueId> = Vec::new();
                    match (ap.args, &**msg) {
                        (AssertPanicArgs::BoundsCheck, AssertKind::BoundsCheck { len, index }) => {
                            // `fn panic_bounds_check(index, len, &Location)`.
                            let (iv, _) = lower_operand(cx, fb, env, index)?;
                            let (lv, _) = lower_operand(cx, fb, env, len)?;
                            pargs.push(iv);
                            pargs.push(lv);
                        }
                        (
                            AssertPanicArgs::Misaligned,
                            AssertKind::MisalignedPointerDereference { required, found },
                        ) => {
                            let (rv, _) = lower_operand(cx, fb, env, required)?;
                            let (fv, _) = lower_operand(cx, fb, env, found)?;
                            pargs.push(rv);
                            pargs.push(fv);
                        }
                        (
                            AssertPanicArgs::InvalidEnum,
                            AssertKind::InvalidEnumConstruction(source),
                        ) => {
                            // `fn panic_invalid_enum_construction(source: u128,
                            // &Location)`. The operand is the already-widened
                            // `u128` discriminant image (`CheckEnums` masks it
                            // in MIR); anything else is ABI drift — fail loud.
                            let (sv, st) = lower_operand(cx, fb, env, source)?;
                            if !matches!(st, TIRTy::U128) {
                                return Err(format!(
                                    "InvalidEnumConstruction source is not u128 ({st:?})"
                                ));
                            }
                            pargs.push(sv);
                        }
                        (AssertPanicArgs::LocationOnly, _) => {}
                        _ => {
                            return Err(
                                "Assert panic-arg shape mismatch (pre-pass bug)".to_string()
                            )
                        }
                    }
                    pargs.push(get_caller_location(cx, fb, source_info)?);
                    if let Some(pad) = eh_unwind_dest(fb, env, tc, unwind)? {
                        // The entry point is `-> !`: the normal edge is never
                        // taken; give the Invoke a dead normal block.
                        let dead = fb.create_block();
                        fb.invoke_void(ap.fid, pargs, dead, vec![], pad);
                        fb.switch_to_block(dead);
                        fb.unreachable();
                    } else {
                        // `Continue`/`Unreachable` unwind action: a plain call —
                        // the unwind (if any) walks through this frame via its
                        // always-emitted tables, entering no pad here.
                        fb.call_void(ap.fid, pargs);
                        fb.unreachable();
                    }
                    return Ok(());
                }
            }
            let trap = tc.trap(fb);
            let then_args = tc.edge_args(env, *target)?;
            fb.condbr(
                assert_cond,
                tc.target_block(*target),
                then_args,
                trap,
                vec![],
            );
            record_assert_site(fb, tc)?;
            Ok(())
        }
        // RUNG 4: `drop(place) -> [return: target, unwind: ..]`. We run the place's
        // destruction semantics on the happy path, then `br` to `target`:
        //   * a place that does NOT need drop (a Copy/scalar/no-drop type) drops to
        //     nothing — just thread the successor.
        //   * a place that needs drop -> a CALL to its `drop_in_place::<T>` glue
        //     (declared extern in the pre-pass), passing the place ADDRESS, then
        //     `br target`. This is faithful: drop_in_place runs the real destructor.
        // The unwind/cleanup edge is NOT modeled faithfully: cleanup is the failure
        // path (a panic mid-drop), which we route to a trap. The normal path — what
        // matters for executing whnf/def_eq — lowers and validates.
        TerminatorKind::Drop {
            place, target, unwind, ..
        } => {
            // VIRTUAL (dyn) drop: `Drop((*_fat))` on a `dyn Trait` pointee —
            // the `drop_glue::<dyn Trait>` shim shape. Load the fat cell's
            // (data, vtable) lanes and call `vtable[0]` (the concrete type's
            // `drop_in_place`) with the data pointer. A direct glue call here
            // would name the shim ITSELF (infinite recursion).
            if let Some(sig) = tc.dyn_drop_sig {
                let [ProjectionElem::Deref] = place.projection.as_slice() else {
                    return Err(format!(
                        "dyn Drop place shape not modelable (want (*fat_local)): {place:?}"
                    ));
                };
                // The fat (data, vtable) CELL: the base local's own slot.
                let cell = place_address(cx, fb, env, &Place::from(place.local))?;
                let data = fb.load(TIRTy::Ptr, cell);
                let vt_addr = gep_byte_offset(fb, cell, 8);
                let vt = fb.load(TIRTy::Ptr, vt_addr);
                // Vtable slot 0 = drop_in_place::<concrete> (rustc layout:
                // [drop, size, align, methods...]). The frontend's SYNTHESIZED
                // vtables put a NULL in slot 0 for a no-drop concrete type —
                // guard the dispatch so a no-drop pointee just skips (the
                // faithful semantics: nothing to drop).
                let fnp = fb.load(TIRTy::Ptr, vt);
                let fnp_i = fb.cast(CastOp::PtrToInt, TIRTy::Ptr, TIRTy::U64, fnp);
                let zero = fb.iconst(TIRTy::U64, 0);
                let is_null = fb.icmp(ICmpOp::Eq, TIRTy::U64, fnp_i, zero);
                let call_blk = fb.create_block();
                let cont_blk = fb.create_block();
                fb.condbr(is_null, cont_blk, vec![], call_blk, vec![]);
                fb.switch_to_block(call_blk);
                // UNWIND lane: a dyn drop with a cleanup/terminate edge rides
                // the per-signature thunk (`Invoke(thunk, vtable_fnptr, data)`)
                // so a panicking destructor enters THIS frame's cleanup pad.
                let mut invoked = false;
                if tc.eh {
                    if let Some(tfid) = tc.indirect_thunk {
                        tc.cur_blk = call_blk;
                        if let Some(pad) = eh_unwind_dest(fb, env, tc, unwind)? {
                            fb.invoke_void(tfid, vec![fnp, data], cont_blk, vec![], pad);
                            invoked = true;
                        }
                    }
                }
                if !invoked {
                    fb.call_indirect_void(fnp, sig, vec![data]);
                    fb.br(cont_blk, vec![]);
                }
                fb.switch_to_block(cont_blk);
                let args = tc.edge_args(env, *target)?;
                fb.br(tc.target_block(*target), args);
                return Ok(());
            }
            if let Some(drop_glue) = tc.drop_callee_id {
                // The place address (the slot, or a loaded deref pointer). Drop glue
                // takes `*mut T`.
                let addr = place_address(cx, fb, env, place)?;
                // UNWIND lane: drop glue with a cleanup/terminate unwind action
                // is a faithful Invoke (a destructor that panics unwinds into
                // the enclosing cleanup region, or traps on double panic).
                if tc.eh {
                    if let Some(pad) = eh_unwind_dest(fb, env, tc, unwind)? {
                        let cont = fb.create_block();
                        fb.invoke_void(drop_glue, vec![addr], cont, vec![], pad);
                        fb.switch_to_block(cont);
                        let args = tc.edge_args(env, *target)?;
                        fb.br(tc.target_block(*target), args);
                        return Ok(());
                    }
                }
                fb.call_void(drop_glue, vec![addr]);
            }
            // (A no-drop place declared no glue: just branch.)
            let args = tc.edge_args(env, *target)?;
            fb.br(tc.target_block(*target), args);
            Ok(())
        }
        // UNWIND lane: `resume` re-raises the in-flight exception after this
        // frame's cleanup ran — the faithful `Resume` over the exception object
        // every landing pad stored into the per-function slot.
        TerminatorKind::UnwindResume if tc.eh => {
            let exn_slot = tc.exn_slot.ok_or_else(|| {
                "UnwindResume reached without an exception slot (EH pre-scan bug)".to_string()
            })?;
            let exn = fb.load(TIRTy::Ptr, exn_slot);
            fb.resume(exn);
            Ok(())
        }
        // UNWIND lane: an `UnwindTerminate(reason)` TERMINATOR (a cleanup block
        // that must not continue unwinding — e.g. an `extern "C"` shim's outer
        // cleanup) calls the reason's `core::panicking` terminate entry point
        // (rustc's `codegen_terminate_terminator`): the nounwind entry prints
        // the reason message and aborts. `fn() -> !`, so call + unreachable.
        TerminatorKind::UnwindTerminate(reason) if tc.eh => {
            let fid = tc.terminate_fids[terminate_reason_idx(*reason)].ok_or_else(|| {
                "UnwindTerminate reached without its declared core::panicking \
                 entry point (terminate pre-pass bug)"
                    .to_string()
            })?;
            fb.call_void(fid, Vec::new());
            fb.unreachable();
            Ok(())
        }
        // RUNG 4: `resume` / `terminate` are the tail of a cleanup landing pad — the
        // EXCEPTIONAL unwinding path. Under panic=abort the happy path is what we
        // lower; cleanup is modeled as a TRAP (`unreachable`), NOT as faithful
        // unwinding. This is the honest, sound-for-the-normal-run choice: on a valid
        // (non-panicking) run these edges are never taken, and a trap is exactly the
        // abort `UnwindTerminate` denotes. (We do NOT silently continue past them.)
        // Under panic=abort `UnwindTerminate` keeps the trap (double panic == abort;
        // the UNWIND lane's message-parity call is the arm above).
        TerminatorKind::UnwindResume | TerminatorKind::UnwindTerminate(_) => {
            fb.unreachable();
            Ok(())
        }
        TerminatorKind::TailCall { .. } => Err("Terminator::TailCall".to_string()),
        TerminatorKind::Yield { .. } => Err("Terminator::Yield".to_string()),
        TerminatorKind::CoroutineDrop => Err("Terminator::CoroutineDrop".to_string()),
        TerminatorKind::FalseEdge { .. } => Err("Terminator::FalseEdge".to_string()),
        TerminatorKind::FalseUnwind { .. } => Err("Terminator::FalseUnwind".to_string()),
        TerminatorKind::InlineAsm { .. } => Err("Terminator::InlineAsm".to_string()),
    }
}

/// How a lowered `Call` terminator dispatches: a DIRECT call to a declared extern
/// `FuncId`, or a FN-POINTER INDIRECT call (`CallIndirect`) through a lowered
/// fn-pointer VALUE with a registered `FuncTy` (R6).
enum CallTarget {
    Direct(trust_ir::FuncId),
    Indirect(trust_ir::ValueId, trust_ir::FuncTyId),
}

/// Emit a value-returning call for either dispatch form.
fn emit_call_value(
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    tgt: &CallTarget,
    args: Vec<trust_ir::ValueId>,
) -> trust_ir::ValueId {
    match tgt {
        CallTarget::Direct(fid) => fb.call(*fid, args),
        CallTarget::Indirect(fnptr, sig) => fb.call_indirect(*fnptr, *sig, args),
    }
}

/// Emit a void call for either dispatch form.
fn emit_call_void(
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    tgt: &CallTarget,
    args: Vec<trust_ir::ValueId>,
) {
    match tgt {
        CallTarget::Direct(fid) => fb.call_void(*fid, args),
        CallTarget::Indirect(fnptr, sig) => fb.call_indirect_void(*fnptr, *sig, args),
    }
}

/// UNWIND lane: synthesize the unwind DESTINATION for a direct call/drop with
/// unwind action `unwind`, or `None` when the edge stays elided (`Continue` —
/// unwinding walks through this frame via its always-emitted unwind tables —
/// and `Unreachable` — the callee cannot unwind).
///
///   * `Cleanup(bb)` -> a fresh PER-EDGE cleanup pad:
///         padN: (%exn, %sel) = landingpad cleanup
///               store %exn -> exn_slot
///               br <bb's trust-ir block>(bb's live-in args, evaluated HERE)
///     Per-edge (not shared per target) because the `br` args are this call
///     site's env values — the state MIR cleanup entry sees. The pad has no
///     block params (the unwind edge passes nothing), and its args dominate it
///     through its single predecessor, the invoke block.
///   * `Terminate(reason)` -> the SHARED per-reason terminate pad (landingpad
///     cleanup + `panic_cannot_unwind`/`panic_in_cleanup` call + unreachable,
///     filled after the block loop): the double-panic abort with rustc's
///     diagnostic message.
///
/// Leaves the builder positioned back on the invoke block (`tc.cur_blk`).
fn eh_unwind_dest(
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    env: &HashMap<Local, trust_ir::ValueId>,
    tc: &mut TermCtx<'_>,
    unwind: &rustc_middle::mir::UnwindAction,
) -> Result<Option<trust_ir::BlockId>, String> {
    if !tc.eh {
        return Ok(None);
    }
    match unwind {
        rustc_middle::mir::UnwindAction::Cleanup(bb) => {
            let exn_slot = tc.exn_slot.ok_or_else(|| {
                "EH: cleanup unwind edge without an exception slot (pre-scan bug)".to_string()
            })?;
            let args = tc.edge_args(env, *bb)?;
            let tgt = tc.target_block(*bb);
            let pad = fb.create_block();
            fb.switch_to_block(pad);
            let (exn, _sel) = fb.landingpad(true, vec![]);
            fb.store(TIRTy::Ptr, exn_slot, exn);
            fb.br(tgt, args);
            fb.switch_to_block(tc.cur_blk);
            Ok(Some(pad))
        }
        rustc_middle::mir::UnwindAction::Terminate(reason) => {
            let idx = terminate_reason_idx(*reason);
            if let Some(tp) = tc.terminate_pads[idx] {
                return Ok(Some(tp));
            }
            let tp = fb.create_block();
            tc.terminate_pads[idx] = Some(tp);
            Ok(Some(tp))
        }
        _ => Ok(None),
    }
}

/// UNWIND lane: emit a DIRECT call as `Invoke` with `pad` as its unwind edge.
/// The normal edge lands in a fresh BIND block where the callee's result binds
/// the MIR destination (the result is defined only on the normal edge, and the
/// bind block's single predecessor is the invoke — the domination the format
/// requires), then branches to the MIR return target with its live-in args. A
/// diverging call (no return target) gets an `unreachable` normal block.
#[allow(clippy::too_many_arguments)]
fn lower_invoke_call<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    env: &mut HashMap<Local, trust_ir::ValueId>,
    tc: &mut TermCtx<'_>,
    fid: trust_ir::FuncId,
    args: Vec<trust_ir::ValueId>,
    call_ret: &CallRet,
    destination: &Place<'tcx>,
    target: Option<BasicBlock>,
    pad: trust_ir::BlockId,
) -> Result<(), String> {
    let Some(ret_bb) = target else {
        // Diverging invoke (a `-> !` panic-family call with a live cleanup
        // edge): the normal edge is never taken.
        let dead = fb.create_block();
        match call_ret {
            CallRet::Sret => fb.invoke_void(fid, args, dead, vec![], pad),
            CallRet::Direct(returns) if returns.is_empty() => {
                fb.invoke_void(fid, args, dead, vec![], pad)
            }
            CallRet::Direct(_) | CallRet::Pair(_) => {
                let _ = fb.invoke(fid, args, dead, vec![], pad);
            }
        }
        fb.switch_to_block(dead);
        fb.unreachable();
        return Ok(());
    };
    let bind_blk = fb.create_block();
    let result = match call_ret {
        CallRet::Sret => {
            fb.invoke_void(fid, args, bind_blk, vec![], pad);
            None
        }
        CallRet::Direct(returns) if returns.is_empty() => {
            fb.invoke_void(fid, args, bind_blk, vec![], pad);
            None
        }
        CallRet::Direct(_) | CallRet::Pair(_) => {
            Some(fb.invoke(fid, args, bind_blk, vec![], pad))
        }
    };
    fb.switch_to_block(bind_blk);
    match (call_ret, result) {
        (CallRet::Direct(_), Some(r)) => bind_call_destination(cx, fb, env, destination, r)?,
        (CallRet::Pair(pr), Some(r)) => {
            let dst = place_address(cx, fb, env, destination)?;
            fb.store(pr.tuple_ty(), dst, r);
        }
        _ => {}
    }
    let edge = tc.edge_args(env, ret_bb)?;
    fb.br(tc.target_block(ret_bb), edge);
    Ok(())
}

/// Resolve a FN-POINTER operand (an arg of the `catch_unwind` intrinsic) to its
/// CONSTANT fn-item instance: either a direct `FnDef`-typed constant, or a
/// `Copy`/`Move` of a bare local whose unique assignment is a
/// `ReifyFnPointer` cast of an `FnDef` constant (the shape rustc's MIR gives
/// `intrinsics::catch_unwind(do_call, data, do_catch)`). Fail-closed on
/// anything else — the expansion must not guess a callee.
fn resolve_fnptr_operand<'tcx>(
    cx: &Cx<'tcx, '_>,
    body: &Body<'tcx>,
    op: &Operand<'tcx>,
) -> Result<Instance<'tcx>, String> {
    let resolve_fndef = |t: Ty<'tcx>| -> Option<Instance<'tcx>> {
        let ty::FnDef(def_id, args) = *t.kind() else {
            return None;
        };
        Instance::try_resolve(cx.tcx, ty::TypingEnv::fully_monomorphized(), def_id, args)
            .ok()
            .flatten()
    };
    // A constant already typed `FnDef` (pre-coercion form).
    if let Operand::Constant(c) = op {
        if let Some(inst) = resolve_fndef(cx.mono(c.const_.ty())) {
            return Ok(inst);
        }
    }
    // A bare local: find its unique `ReifyFnPointer(const FnDef)` assignment.
    if let Operand::Copy(p) | Operand::Move(p) = op {
        if p.projection.is_empty() {
            for data in body.basic_blocks.iter() {
                for stmt in &data.statements {
                    let StatementKind::Assign(bx) = &stmt.kind else { continue };
                    let (pl, rv) = &**bx;
                    if pl.local != p.local || !pl.projection.is_empty() {
                        continue;
                    }
                    if let Rvalue::Cast(
                        CastKind::PointerCoercion(
                            rustc_middle::ty::adjustment::PointerCoercion::ReifyFnPointer(_),
                            _,
                        ),
                        src,
                        _,
                    ) = rv
                    {
                        if let Operand::Constant(c) = src {
                            if let Some(inst) = resolve_fndef(cx.mono(c.const_.ty())) {
                                return Ok(inst);
                            }
                        }
                    }
                }
            }
        }
    }
    Err("catch_unwind: fn-pointer operand is not a resolvable constant fn item".to_string())
}

/// Both panic lanes: emit an inlined size-scaled raw-memory intrinsic call site
/// (see `MemIntrinsicInline`). The count operand is scaled by the mono's
/// element STRIDE (from `iter_elem_layout`) before use — the semantic the
/// intrinsics define (`count` counts ELEMENTS, not bytes):
///   * `copy(src, dst, count)` -> `memmove(dst, src, count * stride)` (NOTE
///     the intrinsic's src-first order vs libc's dst-first);
///   * `write_bytes(dst, val, count)` -> `memset(dst, zext(val), count *
///     stride)`.
///   * either operation over a ZST -> no call (zero bytes for every count).
/// The copying forms return unit — nothing is bound. Ends with the branch to
/// the call's return target (these intrinsics never unwind).
#[allow(clippy::too_many_arguments)]
fn lower_mem_intrinsic_inline<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    env: &mut HashMap<Local, trust_ir::ValueId>,
    tc: &mut TermCtx<'_>,
    mi: MemIntrinsicInline,
    args: &[rustc_span::Spanned<Operand<'tcx>>],
    target: Option<BasicBlock>,
) -> Result<(), String> {
    // Scale an element count (I64/U64 isize/usize operand) to a U64 byte total.
    let scale_to_bytes = |fb: &mut trust_ir_build::FunctionBuilder<'_>,
                          count: trust_ir::ValueId,
                          ct: &TIRTy,
                          stride: u64|
     -> Result<trust_ir::ValueId, String> {
        let count_u = match ct {
            TIRTy::U64 => count,
            TIRTy::I64 => fb.cast(CastOp::Bitcast, TIRTy::I64, TIRTy::U64, count),
            other => {
                return Err(format!(
                    "mem intrinsic inline: count operand is not a 64-bit int ({other:?})"
                ))
            }
        };
        let stride_c = fb.iconst(TIRTy::U64, stride as i128);
        Ok(fb.binop(BinOp::Mul, TIRTy::U64, count_u, stride_c))
    };
    match mi {
        MemIntrinsicInline::ZstCopy => {
            let [_src_op, _dst_op, _n_op] = &args[..] else {
                return Err("copy ZST intrinsic inline: expected 3 args".to_string());
            };
            // Zero-sized elements cover zero bytes regardless of `count`.
        }
        MemIntrinsicInline::ZstWriteBytes => {
            let [_dst_op, _val_op, _n_op] = &args[..] else {
                return Err("write_bytes ZST intrinsic inline: expected 3 args".to_string());
            };
            // Zero-sized elements cover zero bytes regardless of `count`.
        }
        MemIntrinsicInline::Copy { stride, memmove, order } => {
            let [first_op, second_op, n_op] = &args[..] else {
                return Err("copy intrinsic inline: expected 3 args".to_string());
            };
            let (src_op, dst_op) = match order {
                CopyOperandOrder::SourceDestination => (first_op, second_op),
                CopyOperandOrder::DestinationSource => (second_op, first_op),
            };
            let (src, _st) = lower_operand(cx, fb, env, &src_op.node)?;
            let (dst, _dt) = lower_operand(cx, fb, env, &dst_op.node)?;
            let (n, nt) = lower_operand(cx, fb, env, &n_op.node)?;
            let total = scale_to_bytes(fb, n, &nt, stride)?;
            fb.call_void(memmove, vec![dst, src, total]);
            // Returns unit: nothing to bind.
        }
        MemIntrinsicInline::WriteBytes { stride, memset } => {
            let [dst_op, val_op, n_op] = &args[..] else {
                return Err("write_bytes inline: expected 3 args".to_string());
            };
            let (dst, _dt) = lower_operand(cx, fb, env, &dst_op.node)?;
            let (val, vt) = lower_operand(cx, fb, env, &val_op.node)?;
            let val_i32 = match vt {
                TIRTy::U8 | TIRTy::I8 => fb.cast(CastOp::ZExt, vt, TIRTy::I32, val),
                TIRTy::I32 => val,
                other => {
                    return Err(format!(
                        "write_bytes inline: value operand is not a byte ({other:?})"
                    ))
                }
            };
            let (n, nt) = lower_operand(cx, fb, env, &n_op.node)?;
            let total = scale_to_bytes(fb, n, &nt, stride)?;
            fb.call_void(memset, vec![dst, val_i32, total]);
            // Returns unit: nothing to bind.
        }
    }
    let ret_bb = target
        .ok_or_else(|| "mem intrinsic inline: call must have a return target".to_string())?;
    let edge = tc.edge_args(env, ret_bb)?;
    fb.br(tc.target_block(ret_bb), edge);
    Ok(())
}

fn bind_call_destination<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    env: &mut HashMap<Local, trust_ir::ValueId>,
    destination: &Place<'tcx>,
    result: trust_ir::ValueId,
) -> Result<(), String> {
    if destination.projection.is_empty() {
        if let Some(LocalModel::Ssa(_)) = cx.model.get(&destination.local) {
            env.insert(destination.local, result);
            return Ok(());
        }
    }
    let leaf_ty = place_leaf_tir_ty(cx, destination)?;
    let addr = place_address(cx, fb, env, destination)?;
    fb.store(leaf_ty, addr, result);
    Ok(())
}

/// Inline a canonical raw-pointer `offset` / `wrapping_offset` wrapper after
/// the pre-pass selected the allocation-relative GEP lane or the general
/// integer-pointer lane. The direct MIR `BinOp::Offset` path uses the same
/// element-to-byte scaling and signed-domain split.
#[allow(clippy::too_many_arguments)]
fn lower_raw_ptr_offset_inline<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    env: &mut HashMap<Local, trust_ir::ValueId>,
    tc: &mut TermCtx<'_>,
    inline: RawPtrOffsetInline,
    args: &[rustc_span::Spanned<Operand<'tcx>>],
    destination: &Place<'tcx>,
    target: Option<BasicBlock>,
) -> Result<(), String> {
    let [ptr_op, count_op] = &args[..] else {
        return Err(format!(
            "raw pointer offset wrapper inline: expected 2 args, got {}",
            args.len()
        ));
    };
    let (ptr, ptr_ty) = lower_operand(cx, fb, env, &ptr_op.node)?;
    if !matches!(ptr_ty, TIRTy::Ptr) {
        return Err(format!(
            "raw pointer offset wrapper inline: arg 0 is not a pointer ({ptr_ty:?})"
        ));
    }
    let stride = match inline {
        RawPtrOffsetInline::Gep { stride } | RawPtrOffsetInline::Integer { stride } => stride,
    };
    let result = if stride == 0 {
        // Every ZST element offset is zero bytes; do not evaluate an otherwise
        // unrepresentable negative index into TrustIR GEP.
        ptr
    } else {
        let (count, count_ty) = lower_operand(cx, fb, env, &count_op.node)?;
        let count_i64 = to_i64_value(fb, count, &count_ty)?;
        let stride_value = fb.iconst(TIRTy::I64, stride as i128);
        let byte_offset = fb.binop(BinOp::Mul, TIRTy::I64, count_i64, stride_value);
        match inline {
            RawPtrOffsetInline::Gep { .. } => fb.gep(TIRTy::I8, ptr, vec![byte_offset]),
            RawPtrOffsetInline::Integer { .. } => {
                let addr = fb.cast(CastOp::PtrToInt, TIRTy::Ptr, TIRTy::I64, ptr);
                let advanced = fb.binop(BinOp::Add, TIRTy::I64, addr, byte_offset);
                fb.cast(CastOp::IntToPtr, TIRTy::I64, TIRTy::Ptr, advanced)
            }
        }
    };
    bind_call_destination(cx, fb, env, destination, result)?;
    let ret_bb = target
        .ok_or_else(|| "raw pointer offset wrapper: call must have a return target".to_string())?;
    let edge = tc.edge_args(env, ret_bb)?;
    fb.br(tc.target_block(ret_bb), edge);
    Ok(())
}

/// RUNG 8b: emit `Iterator::next(&mut iter)` as a cursor index-bump producing a
/// `Some`/`None` into the destination `Option<..>` slot, then branch to the call's
/// return block. `iter_ptr` points at the iterator's `(cur,end)` cursor; `model`
/// gives the element stride / by-value width. The Option's niche encoding +
/// Some-payload offset come from `mir_enum_layout`, so the surrounding
/// `discriminant`/`switchInt` agrees with what we write.
///
/// Shape (a 2-way diamond, mirroring rustc's `for` desugar `match next() { Some=>..,
/// None=>.. }`):
///   cur = load iter@0; end = load iter@ptr_size
///   if ptrtoint(cur) < ptrtoint(end):
///       [some] p = cur; store iter@0 = gep(cur, stride);
///              <write Some(p / *p) into dest>; br target
///   else:
///       [none] <write None into dest>; br target
#[allow(clippy::too_many_arguments)]
fn lower_iter_next<'tcx>(
    cx: &Cx<'tcx, '_>,
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    env: &mut HashMap<Local, trust_ir::ValueId>,
    tc: &mut TermCtx<'_>,
    model: &IterModel,
    iter_ptr: trust_ir::ValueId,
    destination: &Place<'tcx>,
    ret_bb: BasicBlock,
) -> Result<(), String> {
    let ptr_size = cx.tcx.data_layout.pointer_size().bytes();
    // The destination Option type + its faithful enum layout (niche encoding,
    // Some-payload field offset, variant indices).
    let opt_ty = cx.place_concrete_ty(destination);
    let opt_layout = mir_enum_layout(cx, opt_ty)?;
    // `Option<T>` source order: variant 0 = None, variant 1 = Some.
    let none_variant = VariantIdx::from_usize(0);
    let some_variant = VariantIdx::from_usize(1);
    let some_payload_off = opt_layout
        .variants
        .get(some_variant.as_usize())
        .and_then(|v| v.1.first().copied())
        .ok_or_else(|| "next inline: Option Some variant has no payload field offset".to_string())?;

    // The destination Option slot's base address (a memory place).
    let dst_addr = place_address(cx, fb, env, destination)?;

    // Load the cursor `(cur, end)` at the MODEL's offsets (the REAL
    // `vec::IntoIter` field offsets for owned iteration — THREADS) and compare
    // `cur < end` (unsigned pointer order).
    let _ = ptr_size;
    let cur_addr = if model.cur_off == 0 {
        iter_ptr
    } else {
        gep_byte_offset(fb, iter_ptr, model.cur_off)
    };
    let cur = fb.load(TIRTy::Ptr, cur_addr);
    let end_addr = gep_byte_offset(fb, iter_ptr, model.end_off);
    let end = fb.load(TIRTy::Ptr, end_addr);
    let cur_i = fb.cast(CastOp::PtrToInt, TIRTy::Ptr, TIRTy::U64, cur);
    let end_i = fb.cast(CastOp::PtrToInt, TIRTy::Ptr, TIRTy::U64, end);
    let lt = fb.icmp(ICmpOp::Ult, TIRTy::U64, cur_i, end_i);

    let some_blk = fb.create_block();
    let none_blk = fb.create_block();
    fb.condbr(lt, some_blk, vec![], none_blk, vec![]);

    // --- Some branch: take `p = cur`, bump `cur += stride`, write `Some(..)`. ---
    fb.switch_to_block(some_blk);
    let stride = fb.iconst(TIRTy::I64, model.stride as i128);
    let next_cur = fb.gep(TIRTy::I8, cur, vec![stride]);
    fb.store(TIRTy::Ptr, cur_addr, next_cur);
    let some_addr = if some_payload_off == 0 {
        dst_addr
    } else {
        gep_byte_offset(fb, dst_addr, some_payload_off)
    };
    match model.kind {
        IterKind::SliceIter => {
            // `Some(&T)`: the payload IS the element pointer `p = cur`.
            fb.store(TIRTy::Ptr, some_addr, cur);
        }
        IterKind::VecIntoIter => {
            // `Some(T)` by value: copy `elem_size` bytes from `*cur` into the payload
            // (a `size_of::<T>` aggregate move, lane width = `elem_align`). A ZST
            // element copies nothing.
            if model.elem_size != 0 {
                copy_aggregate_bytes(fb, cur, some_addr, model.elem_size, model.elem_align)?;
            }
        }
        // ADDITIVE (R4 stage 2): `str::Bytes` — `Some(u8)` BY VALUE: the single
        // byte at `cur` (`Copied<slice::Iter<u8>>::next` = `*cur`).
        IterKind::StrBytes => {
            let b = fb.load(TIRTy::U8, cur);
            fb.store(TIRTy::U8, some_addr, b);
        }
    }
    // Set the Some discriminant (a niche-untagged Some writes nothing; the valid
    // payload bytes carry the not-niche state). Done AFTER the payload write so a
    // Direct-tag layout's tag is not clobbered by the payload.
    set_discriminant_at(fb, dst_addr, &opt_layout, some_variant)?;
    let some_edge = tc.edge_args(env, ret_bb)?;
    fb.br(tc.target_block(ret_bb), some_edge);

    // --- None branch: write the `None` discriminant/niche only. ---
    fb.switch_to_block(none_blk);
    set_discriminant_at(fb, dst_addr, &opt_layout, none_variant)?;
    let none_edge = tc.edge_args(env, ret_bb)?;
    fb.br(tc.target_block(ret_bb), none_edge);
    Ok(())
}
