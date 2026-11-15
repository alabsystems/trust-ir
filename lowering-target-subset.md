# Lowering-target conformance subset

**Version:** v5 (2026-10-20)
**Machine-readable mirror:** `trust_ir_conformance::subset`
(`crates/trust-ir-conformance/src/subset.rs`) — the gate test
(`crates/trust-ir-conformance/tests/lowering_subset.rs`) fails if this doc
and the constants drift.
**Exclusion source:** the B3 **depth ledger** ("Depth ledger", on the
internal B3 lean-ir-parity roadmap) and the fast-4 vector-crosslane
lowering/proof table (internal roadmap).

This document pins the exact `Inst` / `Ty` / `ProofAnnotation` (plus
`CastOp` and dialect-op) surface a **conforming frontend is allowed to emit**
and a conforming backend is required to consume on the "perfectly proven"
path. It is the contract surface the `integration-frontend-emission` roadmap
item calls for: versioned, machine-readable, and gate-tested.

## Why these exclusions (and not the historical list)

The historically-cited exclusion list (`Transmute` / `PtrData` /
`PtrMetadata` / `F16` / … as "Lean-lagging") is **stale**: every Rust↔Lean
schema-parity allowlist is **empty** (`Inst`/`Ty` 2026-07-02; `CastOp`
2026-07-10; `FatPtrKind`, `Constant` and the field-level `Inst` axis
2026-09-19) (`crates/trust-ir/tests/lean_schema_parity.rs`) — every Rust
`Inst` / `CastOp` / `Ty` / `FatPtrKind` / `Constant` variant has a Lean
constructor, and every `Inst` field a Lean binder. Name and field parity is
not subset membership: that remains the classifier below. The
honest exclusions are now the **depth-ledger partials**: constructs whose
Lean semantics execute and agree with the reference interpreter but do not
yet model the construct's full generality. The v2 subset excludes exactly
those partial regions (plus dialect ops without proven lowerings and the
by-construction-unpinned `Custom` annotation). v3 is a soundness erratum on
top of v2: it moves no name, but narrows two structural conditions
(`Transmute` to integer/pointer scalars on both sides; the whole module to
the executable model's 64-bit little-endian byte model) and brings the core
classifier's `Dealloc` verdict up to the v2 drop — see "History". v4 is an
EXPANSION on top of v3: the v25 B1 scalars `Isize` / `Usize` / `Char` enter
the type list, and one structural condition is added (a `Char` may originate
only from a range-validated `Const` or a `zext u8 -> char`). Every v3 module
is a valid v4 module.

## What "in the subset" means

A construct is in the subset when its Lean operational semantics cover the
construct **as emitted** (not merely name-parity), so the safety and
transform proofs can reason about every instruction on the path. Claim-style
proof annotations remain claims — the subset pins which annotation
*vocabulary* is part of the contract, not that a claim is discharged (back
claims with `ProofRef` per fast-1; see the trust boundary note in
`TRUST.md`).

## Types — `Ty` (35 of 42 allowed)

Allowed:

`I8` `I16` `I32` `I64` `I128` `U8` `U16` `U32` `U64` `U128` `F32` `F64`
`Bool` `Ptr` `Vector` `Unit` `Never` `Array` `Tuple` `Struct` `Enum` `Func`
`Sequence` `Set` `Record` `Closure` `Ref` `RefMut` `PtrConst` `PtrMut` `Rc`
`FatPtr` `Isize` `Usize` `Char`

Excluded:

| Ty | Why (depth ledger) |
|----|--------------------|
| `F16` | Both engines now execute binary16 arithmetic, unary operations, casts, byte images and bitcasts; see the execution qualification (`reports/2026-11-06-binary16-execution.md` in the development tree). Observable NaN payloads remain unsupported in Lean at every width, and `FMin`/`FMax` retain shared semantic debt. Binary16 remains excluded by this versioned contract: executable semantics does not establish consumer/native lowering or authorize subset admission. |
| `Error` | Producer-internal fail-closed placeholder; never wire-legal. |
| `Refine` | `Refine(TyId, PredId)` is representation-preserving, but the *predicate* is proof surface the Lean model does not interpret, so admitting it would put an unmodelled obligation on the proven path. Wire-legal and round-trips; the checker fails closed on it. |
| `Dialect` | Exact namespace/name/version semantic type with no machine representation. Ordinary exact-typed calls, CFG parameters, copies, and dialect operations may carry it in semantic IR; explicit checked legalization must remove it before Core admission. Wrapping it in another type or leaving it in an unused table does not legalize it. |
| `Handle` | v43 nominal opaque runtime handle (`Ty::Handle(HandleTy { name, runtime })`): one pointer word whose only origins are the validator-pinned bodyless C entry points of a trusted runtime (`trust_bignum::Nat` in v1) and whose only uses are exact-typed transport. Runtime-opaque by construction — it has no interpreter origin and no Lean operational rule — so a module carrying one is outside the proven subset; the machine allowlist and `bridge.rs` both fail closed on it. Wrapping it in another type or leaving it in an unused table does not admit it. |
| `Storage` | v64 geometry-only possibly-uninitialized storage: exact size/alignment for addressable layouts; no by-value Core lowering, initialized value, active field, provenance, access or ABI admission. |
| `Tensor` | **v5 addendum (the tensor region, PKG-U13a, wire v67, 2026-11-13).** `tensor<E, r>` fixes only an integer element type and a rank; each extent is a run-time value the tensor carries. It has no memory layout (`TyShape::Tensor` answers `UnsupportedTyShape`, as `Sequence` does), so no backend can place it, and the W5b Lean model has no tensor value (SemR executes it instead). `bridge.rs` and the mirror exclude it by name; wrapping it in another type or leaving it in an unused table does not admit it. |

`FatPtr` is two little-endian target words: data address followed by length
or vtable pointer. v5 selects four-byte words for canonical wasm32 and retains
eight-byte words for the legacy64 model. Length metadata is `U32` on wasm32,
`U64` on64; vtable metadata remains `Ptr`. Both classifiers check that exact
lane. The model does not claim vtable contents. All non-model targets fail the
whole-module condition5, including empty or scalar-only bodies.

Note on `Vector`: in the subset without a shape condition. The Lean
executable proofs are discharged at `<4 x i32>` / `<2 x i64>` (+ bool
masks); `<16 x i8>` / `<8 x i16>` are covered Rust-side by interpreter
cross-checks (fast-4 "honest boundary"). Widening the Lean executable subset
lifts the proofs without changing this contract.

## Instructions — `Inst` (53 of 74 allowed)

Allowed:

`BinOp` `UnOp` `Overflow` `ICmp` `FCmp` `Cast` `Load` `Store` `Alloca`
`HeapAlloc` `GEP` `PtrData` `PtrMetadata` `PtrFromParts`
`AtomicLoad` `AtomicStore` `AtomicRMW` `CmpXchg` `Fence` `Borrow`
`BorrowMut` `EndBorrow` `Retain` `Release` `IsUnique` `Br` `CondBr` `Switch`
`Return` `Unreachable` `Call` `CallIndirect` `Invoke` `ExtractField`
`InsertField` `ExtractElement` `InsertElement` `SeqMap` `SeqMapAddK` `SeqMapNot`
`Const` `NullPtr` `GlobalAddr` `Undef` `Assume` `Assert` `Copy` `Select`
`OpenFrame` `BindSlot` `LoadSlot` `CloseFrame` `DialectOp`

Sub-op enums (`BinOp`'s 26 ops incl. `FMin`/`FMax`, the boolean-carrier
`BAnd`/`BOr`/`BXor` and the WS3.20 `RotL`/`RotR`/`FCopySign`, `UnOp`'s 13
incl. the WS3.20 `CtLz`/`CtTz`/`BSwap`/`BitReverse`, `OverflowOp`'s 3,
`ICmpOp`'s 10, `FCmpOp`'s 12, `AtomicRMWOp`'s 10, all 5 `Ordering`s, all 4
`AllocOrigin`s incl. `CleanHeap`) are included in full; `CastOp` is the
exception (next section). Counted against `crates/trust-ir/src/inst.rs`.
The WS3.20 sub-ops carry Lean semantics (`Semantics/Arith.lean`) and
interpreter-agreement fixtures like every other listed op; their binary tags
(BinOp 23..=25, UnOp 9..=12) landed with the v51 INST wire batch
(`docs/wire-allocation.md`), which is a codec fact, not a subset one.

`Assert` is admitted whatever its panic kind (plan item P, wire v52,
`docs/SPEC_RATIFICATIONS.md` §19): the kind changes which panic a failed check
is, never whether it fails, so it is a lowering-FIDELITY fact, not a subset
one. A backend that traps on every failed check stays inside the subset; one
that lowers failed checks faithfully (Rust's panic entry point and message)
additionally admits modules under
`CodegenAdmission::with_require_assert_panic_kinds`, which refuses an
`Unspecified` assert by name (`refuse/assert_panic_kind_unspecified`).

`Assert` stays admitted whatever its panic SITE too (amendment P, wire v54,
`docs/SPEC_RATIFICATIONS.md` §19.1): a site changes which panic a failed
check is and where it is reported, never whether it fails. `AssertInvoke`,
the sited check with an unwind edge, is excluded by name (table below) until
a consumer lowers it.

Excluded:

| Inst | Why (depth ledger) |
|------|--------------------|
| `CallCannotUnwind`, `CallIndirectCannotUnwind` | A normative, per-call no-crossing host-unwind boundary (binary v53, distinct constructors in all codecs), not a no-panic proof or ordinary-call annotation. Normal call typing and operands remain unchanged. Rust reference, Lean execution and Clean Core reflection explicitly refuse because they do not model or enforce host unwinding. These variants stay outside the proven subset until that semantic depth and a faithful consumer are qualified; a normal-return-only projection does not admit them. |
| `Dealloc` | **The format cannot state a free.** The instruction names ONE field, `ptr`, against `HeapAlloc`'s four: no `AllocOrigin`, no layout. A correct release needs both — Rust's `GlobalAlloc::dealloc` requires the SAME `Layout` the allocation was made with, Clean/Swift release goes through the reference-counted runtime rather than a raw free, and only C `free` takes a bare pointer — so a backend that guessed `free(ptr)` would be wrong for three of the four origins. trust-cg failed closed on it then, which contradicted this doc's earlier claim that a conforming backend was REQUIRED to consume it. Resolved 2026-09-01 in the backend's favour (G18-1): see "Deallocation" below for the measurement and for why widening the instruction was rejected. Re-decided 2026-09-27 the other way round: a backend that recovers origin and layout from dataflow is not a conforming lowering either (trust-cg lowered such a subset from 2026-09-18; its conformance change, trust-cg main c1b7c2c54, retired that lowering and refuses every `Dealloc` as `[TCG-DEALLOC]`). Still wire-legal and still executable in the reference interpreter except on a `SwiftHeap`/`CleanHeap` cell, where both engines call it UB (Lean for a scalar-typed cell; an aggregate `HeapAlloc` is `unsupported.layout` there; a reference-counted cell is released by `Release`; `docs/SPEC_RATIFICATIONS.md`, "A reference-counted cell is released by `Release`, never by `Dealloc`"); `validate_module_for_codegen` refuses it as `UnlowerableForCodegen`. |
| `Resume` | **Modelled under `PanicStrategy::Unwind`; awaiting admission (amendment D Part 2, 2026-10-02).** Under the `Abort` default it is a structured `unsupported.host_unwind` / `UnsupportedInstruction`, as before; under `Unwind` both engines re-raise the exception at its operand's address (any other value is UB; `docs/SPEC_RATIFICATIONS.md` §21 rule 6). No consumer lowers a panic=unwind build yet, so it stays excluded by name until a subset bump admits it with the lowering. |
| `LandingPad` | **Modelled under `PanicStrategy::Unwind`; awaiting admission (amendment D Part 2, 2026-10-02).** Under `Unwind` both engines enter a pad only by a taken unwind edge and bind `(exception, selector)` — 1 for a catch-all, 0 for a cleanup; a typed catch clause is refused (`docs/SPEC_RATIFICATIONS.md` §21 rule 5); v5 adds structural condition 10 (every `catch_type_indices ⊆ {0}`) when trust-cg lowers it. Under the `Abort` default — the normal-path contract — a pad is dead code: the validator refuses every placement that could enter one other than by an unwind edge (`MisplacedLandingPad`), and BOTH engines fail closed on a directly-entered pad instead of binding a fabricated `(null, 0)` — the reference interpreter with `UnsupportedInstruction`, the Lean executable model with `unsupported.host_unwind`, both "landingpad entered without an unwind edge" (Lean side since WS2.24, which also retired the packed-aggregate two-result convention: `Overflow` / `CmpXchg` now bind two destinations positionally in both engines). |
| `CoroSuspend` | "Coroutine resume dispatch": the suspend side is modelled, and since WS2.25 (2026-09-20) the semantics are PROVED rather than open — `semCoroSuspend_step_equiv` is the `stepInst`-sequence equivalence at the real fresh operand ids (the definitional shape lock `semCoroSuspend_is_macro_expansion` was never that), `stepNWithContext_coroSuspend_eq_expansion` lifts it to the evaluator, and `CoroGen.coro_two_state_roundtrip` is the whole-module resume/`Switch` state-machine theorem with its `next + 1` mutant refuted (`lean/trust_ir-semantics/TrustIr/Proofs/CoroutineProps.lean`, gated by `AxiomAudit.lean`). The row STAYS excluded, fail-closed, until a subset version bump admits the instruction with the WS2.1 validator arm (yielded value vs `FuncTy.returns`, pointer-typed `frame`) as its well-formedness precondition and the interpreter/Lean agreement fixtures are extended to the resume dispatch. |
| `MakeAggregate` | **v3 addendum (WS3.5, 2026-09-19).** The register-level aggregate seed (`%r = make_aggregate <ty> [variant N] (%a, %b)`, the ONLY register origination of an aggregate with a typed-reference lane — F-049) landed as the coordinated Rust + Lean + validator triple but WITHOUT its wire tag; the v51 `INST` wire batch (`wire-allocations.toml`) has since given it Inst tag 60, so all four formats carry it. trust-cg has no lowering yet (refused there until WS7), and the Lean semantics are an honest partial — struct / tuple / array construction is `buildAggregate` with `extract_make_aggregate` proved, while enum and record construction fail closed as `unsupported.enum_def_table` (the Lean machine state carries no definition tables, so `discriminants[variant]` and record field names are unmodelled). Admission is a later version bump once the lowering and the Lean depth land. |
| `ArraySplat` | **v4 addendum (v50, 2026-09-27).** The constant-size uniform array (`%r = array_splat [e x n] %v`, `n` copies of one register value; its constant twin `Constant::Splat`, `splat[ c; n ]`, is excluded wherever a constant is emitted — an `Inst::Const` value or a global initializer, at any depth). It landed complete as a FORMAT construct: wire tags (Inst 59, Constant 16, binary v50), Lean semantics (`semArraySplat` / `Value.ofConstant (.splat ..)`, both `List.replicate`, with the `extract_array_splat` law proved), a lazy reference-interpreter value (O(1) in `n`), and a constant-time validator rule with the §3 canonicality check. What it lacks is a CONSUMER: trust-cg has no lowering, and admitting a new opcode is an additive expansion under the bump policy below (allowlist + this doc + `SUBSET_VERSION` in lockstep, with the lowering). `bridge.rs` (`constant_splat_excluded` for the constant) and the mirror exclude both by name until then. **Coupling:** the validated one-spelling rule (`docs/SPEC_RATIFICATIONS.md` §3.1) makes `Splat` the ONLY valid spelling of a uniform constant list such as `[0u8; 16]`, so while this exclusion stands such an array has no validated in-subset constant spelling; the §3.1 validation, the producer switch to the splat constructors, the trust-cg lowering and this admission must reach consumers in ONE pin move (§3.1 "Landing order"). |
| `AssertInvoke` | **v4 addendum (amendment P, wire v54, 2026-10-01).** The sited check whose failure must enter an in-frame landing pad (MIR `UnwindAction::Cleanup` / `Terminate`): `assert_invoke %c[, KIND], panic @func.E at LOC to bbN(..) unwind bbM`. It landed complete as a FORMAT construct — Inst tag 67, the validator's `Invoke` unwind rules, both engines (the panic=abort projection: a passing check takes its normal edge, a failing one is the sited panic; the Lean theorem `assertInvoke_is_sited_assert_then_br`) — but no consumer lowers its unwind edge (trust-cg compiles panic=abort only), and admitting an opcode no consumer lowers is not admission. `bridge.rs` and the mirror exclude it by name until a subset bump admits it with the lowering. A plain sited `Assert` is inside. |
| `MemCopy`, `MemSet` | **Not yet admitted (WS3.20, F-057).** Both have Lean semantics (`semMemCopy` / `semMemSet`, Semantics/Memory.lean, with the byte-level contract `memcopy_preserves_bytes`), execute in the reference interpreter, and are validated (`bulk_memory_ops`); admitting a new opcode is an additive EXPANSION under the bump policy below (allowlist + this doc + `SUBSET_VERSION` in lockstep, and a consumer that lowers them — trust-cg has none yet); their binary tags (Inst 61 / 62) landed with the v51 INST wire batch. `bridge.rs` and the mirror exclude them by name until that bump, so a module using them fails closed rather than being called in-subset by omission. |
| `Drop` | **Rewritten 2026-10-01 (amendment D, wire v55, `docs/SPEC_RATIFICATIONS.md` §20).** A drop RESOLVES through the module drop-glue table and executes in both models as a call of its `drop_glue` row's glue (the reference interpreter; the Lean model's `EvalContext.resolveDrop`, proved an identity of the evaluator by `stepNWithContext_resolveDrops`); an UNRESOLVED drop is refused by both (`UnsupportedInstruction`; `unsupported.destructor`) and by the default codegen gate. Awaiting a backend lowering: `bridge.rs` and the mirror exclude it by name until the v5 EXPANSION admits it (structural condition 9: every drop resolves). |
| `DropInvoke` | **v4 addendum (amendment D, wire v55, 2026-10-01).** The unwinding twin of `Drop` (`drop_invoke <ty>, %p to bbN(..) unwind bbM`, Inst tag 68): executes in both models as an `Invoke` of its glue under the panic=abort projection (the unwind edge is never taken), with `Invoke`'s validator rules. Awaiting a backend lowering of the drop and its EH call-site entry: excluded by name with `Drop` until the v5 expansion. |
| `TensorContract` | **v5 addendum (the tensor region, PKG-U13a, wire v67, 2026-11-13).** The integer tensor contraction in XLA `DotGeneral`'s shape (`tensor_contract tensor<i32, 2> %a, %b batch [] contract [1:0]` is a matrix multiply; Inst tag 71): wrapping integer arithmetic summed in a pinned order, with paired axes of different extents and a result count past `usize` undefined behaviour. The reference interpreter and SemR execute it, and the validator checks its ranks and axes (`InvalidTensorContract`), but no backend lowers it and its operands have no layout, so the default codegen gate refuses it (`UnlowerableForCodegen`) and `bridge.rs` and the mirror exclude it by name until a subset bump admits it with a lowering. |
| `TensorMap`, `TensorReduce`, `TensorView` | **v5 addendum (the tensor region's map, reduce and view, PKG-U13c, wire v68, 2026-11-14).** The element-wise map of a scalar body over same-shaped tensors and scalars (`tensor_map tensor<i32, 2> (%a, %b) { add i32 $0, $1 }`, Inst tag 72), the left fold of a tensor over strictly ascending axes by one of nine integer operators (`tensor_reduce add tensor<i32, 1> %x axes [1] order row_major`, tag 73), and the read of a tensor through an affine-and-Euclidean coordinate function with an optional fill (`tensor_view`, tag 74: transpose, slice, pad, broadcast, reshape). Operand extents that differ, a node's own scalar verdict, a result count past `usize` and each of the view's five run-time preconditions are undefined behaviour. The reference interpreter and SemR execute all three, and the validator checks their static rules (`InvalidTensorMap`, `InvalidTensorReduce`, `InvalidTensorView`), but no backend lowers them and a tensor has no layout, so the default codegen gate refuses each (`UnlowerableForCodegen`) and `bridge.rs` and the mirror exclude them by name until a subset bump admits them with a lowering. |
| `TensorGather`, `TensorScatter` | **v5 addendum (the tensor region's gather and scatter, PKG-U13d, wire v69, 2026-11-14).** The read of a tensor at coordinates that are themselves data (`tensor_gather tensor<i32, 1> %x coords [%c0, %c1]`, Inst tag 75: one integer coordinate tensor per data axis, each of the result's rank) and the write of a source tensor over a copy of an initial tensor at such coordinates (`tensor_scatter tensor<i32, 2> %init, %src coords [%c0, %c1]`, tag 76), the row-major-last write to a repeated coordinate winning. Coordinate tensors whose extents differ (from each other, or from the scatter's source) and a coordinate outside its axis (the bounds precondition, a `BoundsCheck` obligation sited on the instruction) are undefined behaviour. The reference interpreter and SemR execute both, and the validator checks their static rules (`InvalidTensorGather`, `InvalidTensorScatter`), but no backend lowers them and a tensor has no layout, so the default codegen gate refuses each (`UnlowerableForCodegen`) and `bridge.rs` and the mirror exclude them by name until a subset bump admits them with a lowering. |
| `InvokeIndirect` | **v4 addendum (amendment D Part 2, wire v56, 2026-10-02).** The unwinding twin of `CallIndirect` (`invoke_indirect %f(functy.K)(%a, ..) [cc=X] to bbN(..) unwind bbM`, Inst tag 69): `CallIndirect`'s callee, signature, argument, convention and closure rules, then `Invoke`'s successors (its results are defined on the normal edge only). Both models execute it; its unwind edge is taken only under `PanicStrategy::Unwind` (`docs/SPEC_RATIFICATIONS.md` §21). Awaiting a backend lowering of the indirect call and its EH call-site entry: `bridge.rs` and the mirror exclude it by name until the v5 expansion. |

**`Invoke` is allowed on the normal-path contract:** under the ratified
`panic=abort` policy (the UB/numerics policy and the panic/UB decision
record, internal) the unwind edge is never taken;
the Lean executable model and the reference interpreter agree on the normal
edge (result binding included). A conforming frontend may emit `Invoke`
whose unwind edge exists for ABI reasons but must not rely on unwind-edge
*semantics* (landing-pad dispatch, `Resume` transfer) — those are exactly
the excluded region. A verdict computed under `PanicStrategy::Abort` about a
function with an unwind surface (`ModuleValidationReport::unwind_surface`)
covers the panic=abort projection only; a consumer compiling the module with
panic=unwind must not rely on it (the UB/numerics policy §4, "Unwinding";
`docs/SPEC_RATIFICATIONS.md` §21 rule 7). One computed under
`PanicStrategy::Unwind` covers both builds.

### Structural conditions (enforced by the checker, not name-level)

1. **`Transmute` is integer/pointer scalar-to-scalar only, on BOTH sides.**
   Depth ledger "Transmute generality": `semCast` models scalar
   reinterpretation; aggregate transmutes are structured unsupported. Scalar
   means `I8`–`I128`/`U8`–`U128`/`Ptr` — source AND destination. **v3
   removed `F32`/`F64`/`Bool`** (soundness erratum, WS2.9): the Lean value
   model has no byte buffer, so it refused a float/bool *source* but
   MISTRANSLATED a float/bool *destination* — `transmute u32 -> f32` bound an
   integer value at a float type, `transmute u8 -> bool` a bool whose payload
   could exceed 1 — while the reference interpreter refused every
   `Transmute`. Since v3 both engines execute exactly the same set
   (int↔int at one width, int↔ptr, ptr↔ptr) and refuse the rest by name
   (`UnsupportedCast` / `unsupported.cast`). The sanctioned int↔float
   reinterpret is `Bitcast`, which both engines model through the IEEE bit
   pattern. Enforced by `is_transmute_scalar` (mirror), `transmute_scalar_ty`
   (core classifier) and `transmuteScalarTy` (`Semantics/Cast.lean`).
2. **The pointer trio uses canonical metadata.** Thin pointers require
   `metadata_ty == Unit`; `FatPtr(Slice|Str)` requires `U64`; and
   `FatPtr(TraitObject)` requires `Ptr`. `PtrData` rejects types outside the
   exact executable pointer-trio set. (The v2 fat-pointer-only target
   restriction is subsumed by condition 5.)
3. **`DialectOp` payloads are allowlisted individually** (next section).
4. **`CallIndirect`'s callee is a `Ty::Func` value on the proven path.**
   G18-2 ratifies application as BY VALUE, and G18-2(b) declares the closure
   environment's byte image (`Module.closure_layouts`, v58), so the codegen
   refusal is lifted exactly for a closure type whose frame is declared and
   coherent — which moves nothing here: a declared frame gives the Lean model
   no closure-application rule. Enforced by both checkers since v58
   (`trust_ir::bridge::CLOSURE_APPLICATION_VIOLATION`, the mirror's
   `check_function`), on the callee's TYPE from the function's value typing,
   however the closure value reaches the call; before v58 the codegen refusal
   was the construct's only gate, so neither checker enforced this condition
   until the `closure_layout` golden carried an application to the Lean
   differential, which refused it as a type error.
   G18-2 made `Ty::Closure` eliminable — a `CallIndirect` may now take a
   closure callee, and the reference interpreter applies it by spreading the
   captured environment as leading arguments (see "Closure application"
   below). That mode is deliberately OUTSIDE this subset: the Lean model's
   `CallIndirect` case resolves a function-pointer value and has no
   closure-application rule, so the construct is not covered *as emitted*. It
   is also the one construct here whose backend failure mode is a
   MISCOMPILE rather than a refusal, which is why the refusal is a validator
   check (`UnlowerableForCodegen`) rather than only a line in this table.
   Closure INTRODUCTION (`Const` + `InsertField`) and capture PROJECTION
   (`ExtractField`) stay in the subset, unchanged.
5. **The module selects a supported executable byte model** (v5).
   Target-free modules retain the original64-bit little-endian model. An
   explicit target must be little-endian and either pin `pointer_size == 8`
   (the unchanged legacy64 rule) or pin `pointer_size == 4` with architecture
   exactly `wasm32` (the first triple component). No other32-bit scalar ABI is
   inferred from its pointer width. Big-endian,16-bit, malformed and unknown
   32-bit postures remain outside the subset. The raw size is read directly,
   never through `Module::pointer_bits`' overflow fallback.

   Lean's closed `ByteModel` is selected from the actual module before
   contextual evaluation. Pointer widths, integer constants and casts,
   alignment/size selectors, thin/fat images, metadata, memory/atomic access,
   allocation, globals and contextual steps carry that selection. Successful
   32-bit accesses retain provenance, liveness, alignment and allocation
   bounds, with an additional address-space bound. Allocation exhaustion is
   a named capacity refusal. The target-image/step and coroutine theorems are
   checked by the standing full Lean census and kernel replay; native
   Rust/Lean comparisons test the agreement boundary, rather than proving
   the Rust implementation. Existing depth-ledger partials are unchanged.

   The condition is whole-module, reported once at `SubsetSite::ModuleTarget`
   even without functions. This is no scalar-only exception, producer waiver,
   or permission to restamp a host-target module for another consumer.
6. **A `Char` originates only from a range-validated `Const` or from
   `Cast ZExt` of a `U8`** (v4, WS2.17). `Ty::Char` is a 32-bit carrier whose
   inhabitants are the Unicode scalar values — `0..=0x10FFFF` minus the
   surrogate block `0xD800..=0xDFFF` — so admitting the TYPE is sound only
   while every way of MAKING one re-establishes that invariant. The two
   admitted origins do: `validate_module` range-checks a `Char` literal on
   the typed constant walk's per-node funnel — every LEAF, so a surrogate
   nested in a tuple / struct / record / array / enum constant is refused
   too — and every `u8` is a Unicode scalar value,
   so `zext u8 -> char` holds by construction. Refused: a `Transmute` or
   `Bitcast` into `Char` (a reinterpretation of an arbitrary 32-bit pattern —
   `char::from_u32_unchecked` lowers this way, and such a body correctly
   leaves the subset), any other cast into `Char` (`Trunc` drops high bits
   from a `u32`), and `Load` / `AtomicLoad` / `LoadSlot` at a type that
   carries a `Char` BY VALUE (a memory read of bytes the model cannot
   constrain). "Carries by value" is resolved THROUGH THE MODULE MEMBER
   TABLES, not off the inline type surface: `load { char }`, `load [char; 2]`
   and `load E` (a variant with a `char` payload) are refused exactly like
   `load char`, because one `ExtractField` / `ExtractElement` later the
   program holds that `Char`. The walk follows the member tables to the end,
   at any depth, and also answers "carries a `Char`" when a member id resolves
   to nothing or the type reaches a by-value cycle (an infinitely large type,
   which `validate_module` refuses on its own), so a dangling or cyclic table
   fails closed. A pointer-to-`char` type is NOT a
   `Char` by value, so `load &char` — and `load &{ char }` — is untouched.
   The condition is per-instruction, so the origins it does NOT restrict are
   the ones that merely TRANSPORT a `Char` some other rule already accounts
   for: a block parameter (the branch that passes it is in the same function),
   a `Copy` / `Select` (its operands), an `ExtractField` / `ExtractElement`
   (the aggregate was itself built or loaded under this condition), and a
   `Call` result (an in-module callee's body is subset-checked on its own; a
   body-less declaration's return value is a trusted-declaration row, as for
   any other type). `Undef` at a `Char` binds POISON, which is inert and
   undefined to inspect (`docs/ub-numerics-policy.md` §4), not an
   invalid-looking scalar. The condition is enforced
   by `char_origin_violation_in` in both spellings. Its DYNAMIC half is
   the reference interpreter, which reports an invalid `Char` as undefined
   behaviour at every SSA bind site (`check_char_validity`), on every module
   it executes — in subset or not — mirroring the Lean `validChar` predicate
   (`TrustIr/Basic.lean`).
7. **`CmpXchg` is STRONG only** (crystal lane, D3). A weak compare-exchange
   (`cmpxchg weak`, `weak: true`) may fail spuriously, so its outcome is not a
   function of the state; the reference interpreter and the Lean executable
   model both refuse it as a structured error (`unsupported.weak_cmpxchg`,
   pinned by `weak_cmpxchg_is_structured_unsupported_stable`), exactly as they
   refuse an unresolved `Drop`. A frontend may emit it for the derived-MIR channel; it is off
   the proven path. The variant stays allowlisted (a strong `CmpXchg` is in),
   and the weak form is excluded by `check_inst` (machine mirror) and
   `ConformanceSubset::inst_excluded` (core classifier) alike.
8. **No `uninit` lane** (crystal lane, E3b). A `Const` whose constant carries
   `Constant::Uninit` (an unwritten struct/tuple lane, binary v49) is outside
   the subset. Both executable models give it a meaning (the lane holds no
   value; a write replaces it; a read is undefined behaviour), but the backend
   does not lower it: the Trust callee sidecar emits it for execution in the
   reference interpreter and in Clean's EvalIR, never for codegen. Excluded by
   `check_inst` (machine mirror) and `ConformanceSubset::inst_excluded` (core
   classifier) alike.

## Casts — `CastOp` (14 of 17 allowed)

Allowed:

`Trunc` `ZExt` `SExt` `FPTrunc` `FPExt` `FPToUI` `FPToSI` `UIToFP` `SIToFP`
`PtrToInt` `IntToPtr` `PtrToPtr` `Bitcast` `Transmute` (integer/pointer
scalar-to-scalar only, both sides — condition 1 above; int↔float is
`Bitcast`)

Excluded:

| CastOp | Why |
|--------|-----|
| `ReifyFnPointer` | Depth ledger "ReifyFnPointer addressability" (unchecked): in the Lean model the fn-item value is preserved but the reified pointer is not `CallIndirect`-resolvable — no fn-pointer table entry is minted — so the construct is not covered *as emitted*. The **backend is no longer the constraint**: trust-cg lowers `Func(_)`/`Ptr` reification in both directions, gated on materialized code-pointer provenance (`trust-cg-lower::adapter`). Emit `Constant::FnDef` (builder `fn_addr`) instead. |
| `FPToSISat` | No proven lowering yet: ay `encode_cast` fails **closed** on it — a faithful BV/FP encoding is an `ite`-chain over `fp.isNaN`/`fp.geq`/`fp.lt`, and until that is written and cross-checked ay refuses rather than risk an unsound approximation (`trust-ir-ay::encode_cast`) — so the subset excludes it until one exists. The Lean side is *not* the open item: exact `semCast` cases landed 2026-07-10 and the depth-ledger box is checked. |
| `FPToUISat` | Same as `FPToSISat` — ay fails closed on the saturating BV/FP encoding (Lean has exact `semCast` cases); outside the subset until a proven lowering exists. |

## Dialect ops (6 allowed, by qualified name)

Allowed — exactly the portable `vector.*` ops with a proven trust-ir
lowering (Lean `runsAgreeFrom_*` refinement) or a deliberate
single-instruction identity (fast-4 table):

`vector.pack_lanes` `vector.extract_lane` `vector.insert_lane`
`vector.mask_to_bits` `vector.reduce` `vector.shuffle`

Excluded:

| Dialect op | Why |
|------------|-----|
| `vector.fma` | Carried without a trust-ir lowering by **ratified** fast-4 policy (single-rounding contract; a scalar fallback would be a semantics change, so there is nothing in-repo to refine). Its correctness rests on the backend's target lowering, which is outside this repo's proof surface. |
| every other dialect (`clean.*`, `gpu.*`, `avx512.*`, `ane.*`, `verif.*`, …) | No proven lowerings; dialect ops round-trip opaquely by design. `clean.*` (Clean's managed-runtime ops) was audited for admission on 2026-07-04 and **refused** — zero depth-ledger backing; see "Producer notes". A namespace outside the in-tree decoded set (`vector` / `gpu` / `avx512` / `ane` / `trust_rust`) has no registered lowering at all, so `validate_module_for_codegen` refuses it as `UnlowerableForCodegen` (WS2.20); `validate_module` still accepts it for opaque round-trip. |

## Proof annotations — `ProofAnnotation` (36 of 40 allowed)

Allowed:

`InBounds` `NotNull` `ValidBorrow` `UniqueBorrow` `SharedBorrow`
`ValidDealloc` `NoOverflow` `NoWrap` `DivNonZero` `ShiftInRange` `Wrapping`
`Pure` `Terminates` `Deterministic` `Associative` `Commutative`
`DataRaceFree` `AtomicOrdering` `BoundedOutput` `Monotonic` `NoAlias`
`Aligned` `NoPanic` `NoUndef` `Tainted` `TrustedSink` `ReadonlyTable`
`AppendOnlyBuffer` `AtomicSetInsert` `ParallelMap` `BoundedLoop`
`DivergenceClass` `ProofRef` `ValueRange` `KnownBits` `BranchWeights`

Excluded:

| Annotation | Why |
|------------|-----|
| `Custom` | A producer-defined `ProofTag` whose meaning is not pinned by any spec — it cannot be part of a *pinned* contract. Consumers needing protocol tags (e.g. the ay CHC batch fixtures) ride outside the proven-path subset by definition. |
| `FreshSymbolicHavoc` | The deliberately inert `Inst::Undef` marker. It is NOT feature-gated and IS wire-encodable (binary tag `0x25`), but it was never ratified into the subset, so the checker fails closed on it. |
| `RegionHavocStore` | The `Inst::Store` region-havoc marker (wire-encodable, binary tag `0x26`, not feature-gated). Excluded on the subset's own admission criterion — Lean coverage *as emitted*: the executable model has no region-havoc rule, `semStore` and the reference interpreter write exactly ONE typed location, so nothing in the proven-path semantics covers "treat every location this pointer may reach as freshly unconstrained". It is also the one annotation here that is not an ignorable claim: its consumer contract *requires* a translation havocking at least the store's whole reachable region, or refusal — so admitting it would oblige a conforming backend to a behaviour the model does not state, and a consumer that read the decorated `Store` as an ordinary single-location write would under-approximate the write set (the stale-read false-proof shape). Production emission is real but rides the VERIFICATION lane, not the proven-codegen path: trust's `trust-ir-bridge` emits it for `copy_nonoverlapping` with a symbolic element count, paired with the equally-excluded `FreshSymbolicHavoc` on the fresh value — admitting one without the other would split that pair. |

The count above is against the whole enum (40 variants); the default build
sees 39, because the feature-gated `Goal` (`clean-expr`) is outside v1 scope
by construction (off the default zero-dep surface). The checker fails closed
on any annotation it does not recognize. `Constant` variants are not
separately allowlisted: they follow the (checked) type they inhabit.

## The gate

`crates/trust-ir-conformance/tests/lowering_subset.rs` walks **every module
fixture** in the conformance corpus through
`trust_ir_conformance::subset::module_subset_violations` and asserts,
two-sided (mirroring the B3 schema-parity gate):

* a fixture **not** on the exemption list must produce zero violations;
* a fixture **on** the exemption list must actually violate — a stale
  exemption fails the gate.

It also asserts this doc and the machine constants agree (every allowlisted
name and documented exclusion appears here verbatim), that the gate's
fixture table stays in lockstep with `conformance.rs::corpus()`, and that
the worked example below holds.

### Exempt fixtures (wire-format coverage is broader than the proven subset)

The `call_unwind_boundary` fixture covers the four distinct ordinary/boundary
direct/indirect constructors through all codecs. Its boundary calls are outside
the proven subset; transport and structural typing are not host-unwind proof.

The corpus's job is byte-golden **wire-format** coverage of the *entire* IR
surface — deliberately broader than the proven subset. These fixtures
intentionally exercise out-of-subset constructs; the gate documents which is
which rather than forbidding them:

| Fixture | Out-of-subset construct it exists to cover |
|---------|--------------------------------------------|
| `ty_primitives` | `F16` (full primitive-type wire surface) |
| `inst_vector_crosslane` | `vector.fma` |
| `inst_memory` | `Dealloc` (full memory-instruction wire surface; excluded because the format cannot state the allocator origin or layout a free needs — see the `Inst` exclusion table) |
| `inst_dialect` | opaque `verif.bfs_step` payload (every `AttrValue` variant) |
| `ty_dialect_v39` | `Dialect` — v39 nominal dialect type wire coverage (header 39); exact-typed transport only, no legalization, so excluded as emitted |
| `ty_handle` | `Handle` — v43 nominal opaque runtime handle wire coverage (header 43): the pinned `trust_bignum::Nat` declarations plus a transport body; runtime-opaque, so excluded as emitted |
| `proof_annotations` | `Custom` (every annotation variant) |
| `chc_batch` | `Custom` (ay CHC protocol tags) |
| `array_splat` | `ArraySplat` / `Constant::Splat` — v50 uniform-array wire coverage (the only golden with header 50), at u64-scale lengths; excluded until a subset bump admits them with a trust-cg lowering — see the `Inst` exclusion table |
| `inst_wire_batch` | `MakeAggregate`, `MemCopy`, `MemSet` — v51 INST wire batch coverage (the only golden with header 51), beside the in-subset `RotL` / `RotR` / `FCopySign` / `CtLz` / `CtTz` / `BSwap` / `BitReverse` sub-ops the same batch tagged; the three instructions stay excluded until their admission bumps — see the `Inst` exclusion table |
| `assert_invoke` | `AssertInvoke` (with the `LandingPad` / `Resume` of its cleanup pad) — amendment P wire coverage of the sited check with an unwind edge (Inst tag 67, header 54); excluded until a subset bump admits it with a lowering — see the `Inst` exclusion table |
| `drop_glue` | `Drop`, `DropInvoke` (with the `LandingPad` / `Resume` of its cleanup pad) — amendment D wire coverage of the drop-glue table and the unwinding drop (Inst tag 68, header 55); both execute in both models, but no backend lowers a drop yet, so excluded until the v5 expansion — see the `Inst` exclusion table |
| `unwind_twins` | `InvokeIndirect` (with the `LandingPad` of its catch-all pad) — amendment D Part 2 wire coverage of the unwinding indirect call (Inst tag 69, header 56); executed by the reference interpreter under both panic strategies, but no backend lowers it, so excluded until the v5 expansion — see the `Inst` exclusion table |
| `closure_layout` | closure APPLICATION (`CallIndirect` over a `Ty::Closure` callee) — v58 declared-closure-frame wire coverage, applying the closure whose frame the row declares; outside the subset by structural condition 4 (no Lean closure-application rule) |

| `storage_only` | v64 complete parent storage geometry and scalar byte access; storage remains outside the proven Core lowering subset and grants no initialized aggregate/value or callable authority. |
| `make_closure` | `MakeClosure` and closure application — v63 runtime-capture wire coverage; both remain outside the proven lowering subset and grant no native/provider proof admission |
| `tensor_contract` | `Tensor`, `TensorContract` — the tensor region's wire coverage (an integer matrix multiply over two `tensor<i32, 2>` parameters; the only golden whose header is `TENSOR_FORMAT_VERSION`); both engines execute it, but a tensor has no memory layout and no backend lowers a contraction, so excluded by name — see the `Ty` and `Inst` exclusion tables |
| `tensor_map_reduce_view` | `Tensor`, `TensorMap`, `TensorReduce`, `TensorView` — the tensor region's map, reduce and view chained in one function (every map node kind, a row sum, a left pad with a fill; the only golden whose header is `TENSOR_MAP_REDUCE_VIEW_FORMAT_VERSION`); both engines execute it, but a tensor has no memory layout and no backend lowers the three, so excluded by name — see the `Ty` and `Inst` exclusion tables |
| `tensor_weight_blob` | `Tensor` and the `Constant::TensorBlob` its `Const` nodes carry — content-addressed weight blobs (one row named at `i32` and `u8`, an empty row, a blob fed to a contraction; the only golden whose header is `TENSOR_BLOB_FORMAT_VERSION`); both engines read them, but a tensor has no memory layout and no backend lowers a blob constant, so excluded through its tensor type — see the `Ty` exclusion table |
| `tensor_gather_scatter` | `Tensor`, `TensorGather`, `TensorScatter` — the tensor region's gather and scatter chained in one function (a gather of a `tensor<i32, 2>` at `i64` and `u8` coordinate tensors, then a scatter of the result at `usize` coordinates; the only golden whose header is `TENSOR_GATHER_SCATTER_FORMAT_VERSION`); both engines execute it, but a tensor has no memory layout and no backend lowers the two, so excluded by name — see the `Ty` and `Inst` exclusion tables |

## Worked example

`frontend_emission_subset` (fixture:
`crates/trust-ir-conformance/tests/generate.rs::build_frontend_emission_subset`)
is the roadmap's worked example: a tiny two-function "frontend" emission —
`checked_add` (overflow-checked add that traps on overflow, per
`panic=abort`) and `sum3` (two calls through it) — emitted entirely through
the subset with source spans on **every** instruction
(`ModuleBuilder::intern_file` + `FunctionBuilder::set_span`) and the
function-level ABI set through the builder
(`set_calling_conv(Rust)` / `set_attrs`). The gate validates it
(`validate_module`), checks it subset-clean and span-covered, and executes
it end-to-end through the reference interpreter (`sum3(39) == 42`). As a
corpus fixture it is also byte-golden across binary / text / JSON /
MessagePack.

## Ratified format decisions

Each entry below settles a question that had been re-opened repeatedly as an
"owner decision". They are DECISIONS, not deferrals: every one names what was
measured, what was rejected, and where the ruling is enforced in code.

### Deallocation — `Inst::Dealloc` leaves the subset (G18-1, 2026-09-01)

**Ruling: `Dealloc` is EXCLUDED from the lowering-target subset. The
instruction is not widened.**

The contradiction being settled: this document listed `Dealloc` as
backend-required while trust-cg fails closed on it. Both could not be right.

Measured before deciding:

* **No producer emits `Dealloc`.** Clean lowers `dec x` to `Release` (the
  reference-counted runtime path, `clean-compiler::emit_trust_ir`); the Rust
  frontend constructs it nowhere; across trust / clean / trust-ir the only
  constructions are this repo's own tests and the `trust-ir` CLI's demo
  builders. The Rust producers spell a free as a call; Clean spells a cell's
  release as `Release`.
* **The refusal is a FORMAT gap, not a backend gap.** `Dealloc { ptr }` states
  neither the `AllocOrigin` that owns the region nor the layout being released.
  Rust's `GlobalAlloc::dealloc` requires the exact `Layout` used to allocate;
  Clean's and Swift's release goes through the RC runtime; only C `free` takes
  a bare pointer. Three of the four origins are mis-served by any single guess.
* **Widening would not have restored the subset claim.** The alternative was to
  mirror `HeapAlloc`'s `{ ty, count, align, origin }` on a new wire version.
  Rejected on two independent grounds: it would mint wire surface nothing
  writes, and the subset's admission criterion is Lean coverage *as emitted* —
  Lean's `semDealloc` is a pointer-only dead-marking rule (`Semantics/Memory`)
  with no allocator identity and no layout check, so a four-field `Dealloc`
  would be *less* covered than the one-field form and would land in the
  exclusion table regardless. Widening would have cost a wire version and still
  required this same doc edit.

Consequences, all in effect:

* `Dealloc` stays **wire-legal**, keeps its binary tag, and keeps its
  reference-interpreter semantics (narrowed 2026-09-27: on a `SwiftHeap` /
  `CleanHeap` cell it is undefined behaviour — in both engines for a
  scalar-typed cell, in the interpreter alone for an aggregate one — see "A
  reference-counted cell is released by `Release`, never by `Dealloc`" in the
  internal spec ratifications). No blob is invalidated, no golden is
  regenerated, `MIN_READ_VERSION` is untouched, and no new wire version was
  minted for this.
* `trust_ir_conformance::subset` no longer allowlists it, so the corpus gate
  reports it (fixture `inst_memory` is exempted, with the reason recorded in
  the exemption table above).
* `validate_module_for_codegen` refuses a body containing it, as
  `ValidationError::UnlowerableForCodegen`, naming the missing information.
  `validate_module` is unchanged — this is a codegen-intent refusal, not a
  well-formedness error.

To free memory, spell the release the way its runtime pins it, never as
`Dealloc`: `Release` for a reference-counted (`CleanHeap` / `SwiftHeap`) cell,
the pinned `drop` entry for a handle, and for `RustHeap` / `CMalloc` a call the
producer pairs with its own allocation (Rust drop glue's `__rust_dealloc`).
That is what every shipping producer already does. A call-spelled free of a
`HeapAlloc` result is a pairing the format does not guarantee (it states no
allocator layout for `HeapAlloc`); see the 2026-09-27 re-decision below.

**The one open edge, and where it is closed (WS3.22, F-060, 2026-09-20).**
The consequence of spelling a free as a call is that the reference interpreter
and the Lean model cannot SEE it: a bodyless callee is an opaque extern call,
so a use after release through a runtime is invisible unless the callee is
KNOWN to be a release. That knowledge now lives in ONE place,
`trust_ir_build::pinned_release_entry_points()` (keyed lookup
`pinned_release_entry_for_symbol`), DERIVED from the two pin tables rather
than listed a third time: the unique consuming-only entry of each
`TRUSTED_HANDLE_RUNTIMES` row (`HandleRuntimePin::release_entry`, the `drop`
role — `trust_bignum_nat_drop`) and the `release` role of each
`TRUSTED_RC_RUNTIMES` row (`RcRuntimePin::release_entry` — `clean_dec`). A host
model of a pinned runtime (`trust_ir::interpret::HostCalls`) MUST model a call
to a symbol in that table as the same dead-marking step `semDealloc` performs
on the released subject, keyed by the symbol and by nothing else, so that a
double release or a use after release through a pinned runtime is an
interpreter fault instead of an opaque call. The reference model
`trust_ir_build::PinnedHandleHost` (WS2.13) does exactly that: a handle
release is `HostState::release_handle` (every later use, a second release
included, is `UndefinedBehavior` "used after release"), and a `CleanHeap`
release is the interpreter's own `Release`, which marks the cell dead at count
zero (a second `clean_dec` is "freed allocation", a load through the cell is
"use after dealloc" — the very fault a load after `Inst::Dealloc` raises); a
release the table stopped naming is not served (`UnsupportedCall`, fail
closed), never a no-op. `crates/trust-ir-build/tests/release_entry_points.rs`
holds the executable witness with its no-op-release mutant, and gate 8's
`ws3_22_pinned_release_differential` checks a seeded release/use corpus
against an independent liveness oracle. What stays opaque is stated, not
hidden: `RustHeap` has no pinned runtime, so `__rust_dealloc` (and C `free`)
is a convention no table names — the interpreter refuses such a call by name
with or without a host (`UnsupportedCall`) and nothing sees the release.
`Dealloc` is NOT widened and the ruling above is kept (DECIDE, WS3.22: no
producer emits `Dealloc`); reopen a `Dealloc { origin, layout }` only if a
producer needs a free that no pinned runtime entry point can spell.

**Re-decided 2026-09-27: a backend does not recover what `Dealloc` does not
state.** From 2026-09-18 trust-cg lowered a provenance-resolved subset — a
`Dealloc` whose pointer reaches same-function `HeapAlloc` sites through `Copy`,
a thin `PtrToPtr`, `Select` arms and block parameters, released through
`__rust_dealloc` with the allocation's layout or through `free` — and so
ACCEPTED the must-refuse row `refuse/dealloc_instruction`, a recorded
disagreement. The disagreement is settled on both sides: `Dealloc` is refused
for codegen whatever its provenance, a conforming backend refuses it rather
than recovering the origin or the layout, and trust-cg's conformance change
(trust-cg main c1b7c2c54, 2026-09-27) retired that lowering and refuses the row
on every compiler lane (the ratification's `(external)` entry names the tests). Nothing new met the reopen condition
above — no producer constructs `Dealloc` (the lowering was added to close a
backend completeness-audit row, not for a producer) — and
admitting the subset would have needed three things the format does not have:
a pinned RustHeap/CMalloc allocator ABI, and a normative statement of the
layout a lowered `HeapAlloc` passes its allocator (trust-cg's is its own
natural-C size, which deliberately over-allocates some aggregates). And where
the engines give `Dealloc` a meaning, a backend still cannot lower it: on a
reference-counted cell it is undefined behaviour (in both engines for a
scalar-typed cell, in the interpreter alone for an aggregate one), and on any
other cell the free it performs needs an allocator and a layout that the
instruction does not name. (The one-meaning rule for a reference-counted cell
is `docs/SPEC_RATIFICATIONS.md`, "A reference-counted cell is released by
`Release`, never by `Dealloc`": the interpreter, Lean and the validator's
Clean-TV heap fragment now all release a `CleanHeap` cell by `Release`, and
the fragment refuses a `Dealloc` of one as a wrong emission.) `HeapAlloc` is a
different matter: this repo's own `frontend/`
emits `HeapAlloc(RustHeap)` for inline `Box::new_uninit` / `Arc::new` blocks,
and Rust drop glue frees them by calling `__rust_dealloc` — correct only under
trust-cg's allocation convention, because the format states no allocator
layout for `HeapAlloc`. Stating one, or refusing `HeapAlloc(RustHeap)` for
codegen, is an open follow-up that is due now and is not decided here. The ratification,
with its enforcement, is `docs/SPEC_RATIFICATIONS.md`, "Deallocation is refused
for codegen, whatever its provenance".

### Closure application — `Ty::Closure` becomes eliminable (G18-2, 2026-09-01)

**Ruling: `Inst::CallIndirect` accepts a `Ty::Closure` callee. The `Ty::Func`
rule is unchanged. The new mode is outside this subset (structural condition 4
above) and is refused for codegen.**

The defect: `Ty::Closure` was INTRODUCTION-ONLY. A closure could be built
(`Const` + per-capture `InsertField`) and destructured (`ExtractField` reads a
CAPTURE — the `func` lane is deliberately not a field), but never applied,
because `CallIndirect` demanded `Ty::Func`. A first-class function type whose
values can be introduced and projected but never eliminated is not a function
type.

The rule, which is strictly additive:

* the edge's declared `sig` must be `closure_types[c].func` — the closure's
  **apparent** signature, what a caller sees — compared by id, the same
  strictness the `Ty::Func` edge applies to its own callee;
* `args` is checked against that signature **verbatim**, by exactly the
  pre-existing arity and argument-type rules;
* the captured environment is supplied by the ABI as **leading arguments,
  spread in capture order**, so the target function's physical signature must be
  `captures ++ apparent params -> apparent returns`.

Why spread rather than one env pointer: `ClosureTy` states the environment as N
explicit typed values — "captures are explicit values, not an implicit env
pointer" (`Ty::Closure`'s own doc, the ty#4145 lesson) — and the value model has
no env object to address. Passing one env argument would require synthesizing a
tuple type the module never declared. A producer that wants the pointer-env ABI
keeps spelling it as an explicit environment aggregate plus a `Ty::Func`
pointer; that path is untouched.

Enforcement: `CallIndirectClosureSigMismatch` (total — a type-level rule) and
`CallIndirectClosureTargetMismatch` (where the defining closure constant is
visible in the same function, through `Copy`; a closure arriving from a
parameter or another module is trusted as declared exactly as a
dynamically-flowing function pointer is, and the reference interpreter's check
is total). No wire change: `CallIndirect`'s fields are untouched and only the
callee's *type* differs.

#### Application is BY VALUE, and capture mode is the slot's type (2026-09-19)

**Ruling: first-class closure application is `FnOnce`-shaped. The captures are
ARGUMENTS, so a body's write to a capture is not observed by the caller's
closure value and is not observed by a later application. A BY-REFERENCE
capture is a capture SLOT WHOSE TYPE IS A POINTER; capture MODE therefore needs
no new `ClosureTy` field. A Rust `Fn`/`FnMut` closure whose state must persist
across calls is spelled the way the codegen refusal already prescribes — an
environment aggregate in memory plus a `Ty::Func` that takes the environment
pointer — and that spelling validates, lowers and persists today.**

This settles the question the spread-ABI rule above left implicit, and it
settles it the only way this format can. A `Ty::Closure` value is an SSA
REGISTER value with no address; a `Borrow` result is a thin `Ptr`, so no
pointer TO a closure register can be obtained; and `CallIndirect` cannot hand
a body a pointer to the caller's closure register whose writes the next call
would observe. A callee TYPED `RefMut(Closure)` (the draft design's spelling)
can be declared — as a parameter — but it is not a closure application and
never becomes one: the closure-application arm fires only on a callee typed
`Ty::Closure` itself, and the reference interpreter refuses every callee that
is neither `Ty::Func` nor `Ty::Closure` at run time (`callee has non-function
type`). (The structural validator admits such a callee because it has NO
callee-type rule for a `CallIndirect` outside the nominal-type path — a
`U64`-typed callee is admitted the same way; that is a recorded gap, pinned by
`a_non_callable_callee_type_is_a_recorded_gap`, not a rule about pointers.)
Nor can a closure be LAUNDERED into a callee the closure arm cannot see:
`Bitcast` / `Transmute` / `PtrToPtr` of a closure value to `Ptr` or to an
integer is refused structurally (`CastLayoutUnsupported`, "closure has no
concrete memory layout evidence") — the same absent layout, and a rule the
closure-layout table must keep when it gives the closure a size. Making
by-reference APPLICATION coherent would need a new
call-through-pointer form (a new `Inst` or a new `CallIndirect` callee class,
plus a Lean `Call.lean` rule) — a coordinated triple, proposed only as a
decision gate, not assumed here.

Consequences, each pinned executably by
`crates/trust-ir-build/tests/closure_application_by_value.rs` — three spellings
of ONE source program (a counter bumped twice, reported as `first * 10 +
second`), so the returned number reads the capture discipline off directly:

| Spelling | Capture slot | Result | Lowerable |
|---|---|---|---|
| env aggregate + `Ty::Func` taking `Ptr` | — | `12` (state persists) | yes |
| `Ty::Closure`, capture typed `U64` | by value | `11` (second call sees the seed) | no — `UnlowerableForCodegen` |
| `Ty::Closure`, capture typed `Ptr` | by reference | `12` (the pointee is shared) | no — `UnlowerableForCodegen` |

The middle row is the producer hazard, and the ruling assigns it: a producer
that reaches for a first-class closure to spell `FnMut`-with-state gets
by-value semantics and a different answer. That is the **producer's** error,
and a producer conformance row must refuse it.

The codegen refusal is **unchanged** by this ratification. It is lifted only
for a closure type that carries a declared layout row (the table below),
because rustc reorders `repr(Rust)` upvars and a backend that laid the
environment out in declaration order would MISCOMPILE rather than fail. For a
closure type with NO row, `ty_layout_shape` on the `Ty::Closure` is
`UnsupportedTyShape` and every application is refused — however the closure
VALUE reaches the site: the refusal reads the callee's type off the function's
value-type map, which covers a function parameter, a `Call` result, `Select`,
`Copy`, a loop-carried block parameter, an `ExtractField` out of an aggregate
and a `Load`, not only a `Const` in the applying function (each pinned by the
test). A closure that a producer round-trips through MEMORY
(`Alloca`/`Store`/`Load` at the closure type, or a global's initializer read
through `GlobalAddr`/`Load`) is structurally valid and fails CLOSED in the
reference interpreter (`has no byte layout`); that is the same absent layout.
The interpreter's byte funnel does not yet read the declared frame, so a
declared closure still fails closed there (an open WS3.13 half, not a rule).

#### G18-2(b), 2026-09-19 — the environment frame is DECLARED (wire v58)

**`Module.closure_layouts` (wire v58, WS3.9 Batch IDENT)** carries the
environment frame's byte image: `ClosureLayoutDescriptor { closure, size,
align, capture_offsets }`, offsets in CAPTURE order, with exactly the v42
tuple-table rules (one row per closure type, a resolvable closure type,
power-of-two alignment dividing the size, one offset per capture, natural
capture alignment, containment, non-overlap; a self-capturing closure fails
closed by name), checked on decode, in `validate_module`
(`TupleLayoutInconsistent`, its reason prefixed `Module.closure_layouts: `)
and by `trust-ir-diff`. It closes the
`repr(Rust)` upvar-reordering half: trust-cg lays a closure out as a
declaration-order C struct today, which is the wrong image for a reordered
Rust closure.

**Subset status.** `Ty::Closure` remains OUTSIDE this subset. The codegen
refusal is now conditional rather than unconditional:
`validate_module_for_codegen` refuses a `CallIndirect` over a closure type
with NO layout row, or with an INCOHERENT one (`UnlowerableForCodegen`; the
pre-v58 refusal text VERBATIM — the gate-9 `closure_application_by_value`
test pins its two clauses — followed by one sentence naming the missing
row), and admits one whose frame is declared and
coherent. Admitting it is a statement about the FORMAT — the environment has
a byte image a backend can lay out — and not a claim that any backend
implements the application ABI; the trust-cg half is roadmap WS7, and trust-cg
itself still refuses a captured closure constant and a multi-capture closure
frame by its own rules until it reads this table.

**The laundering rule is kept.** A declared frame gives the closure a SIZE,
which is exactly when a pure same-size cast rule would start to admit
`Bitcast closure -> Ptr` / `Transmute closure -> U64`. The layout evidence
therefore refuses every layout-sensitive cast that names a closure BY VALUE on
either side — directly, or inside an aggregate no pointer breaks — before any
width is compared (`LayoutError::ClosureCast`, surfaced as
`CastLayoutUnsupported`), declared frame or not. A pointer or reference TO a
closure is an address and is not affected. Pinned by
`closure_layout::a_declared_frame_does_not_admit_casting_the_closure_to_a_callable`.

### Unions — the byte-overlap model is RATIFIED (G18-3, 2026-09-01)

**Ruling: TrustIr does NOT get `Ty::Union(UnionId)` or a `UnionDef`. A C/Rust
`union` is spelled as BYTE-OVERLAPPING STORAGE — one allocation sized to the
largest field and aligned to the strictest field alignment, written and read
through TYPED `Store` / `Load` at a shared base address. This closes the
question; it is not to be re-opened without new evidence.**

*Reaffirmed 2026-10-02 (decision gate DG-06):* the v2 architecture's
re-proposal of `UnionDef` / `Ty::Union` presented no new evidence of the kind
this ruling requires, so the byte-overlap model stands and no union carrier
is scheduled.

What a `UnionDef` was proposed to add, and where each fact already lives:

| Proposed `UnionDef` content | Where it is stated today |
|---|---|
| total size | the carrier's `Alloca { ty }` (`Array(U8, N)`, or the widest field's type) |
| alignment | the carrier's `Alloca { align }` |
| per-field type | the `ty` on the `Load` / `Store` at the access |
| the deliberate aliasing | two typed accesses at one address — nothing else needs to say it |
| per-field `NoUndef` / `Aligned` | `InstrNode.proofs` on the ACCESS |

The decisive argument is the one about the annotations, and it runs the
opposite way to the framing that kept re-opening this. **A union has no notion
of an active field at the type level — and neither does rustc**, which is
exactly why reading a union field is `unsafe`. So a per-field `NoUndef` on a
`UnionDef` could only ever be the *unconditional* form, i.e. a claim that is
FALSE whenever that field is not the live one. The per-access annotation the
format already supports is strictly more precise, because an access happens at
a program point where the claim can be true. `crates/trust-ir/tests/union_byte_overlap_model.rs`
is the executable half of this ruling: it builds `union { a: u32, b: f32 }` and
`union { small: u8, big: u64 }` on the existing surface, punns through them in
the reference interpreter, and pins that a read of never-written union bytes is
REFUSED as an uninitialized read even with a `NoUndef` annotation attached —
the exact claim a `UnionDef` would have carried unconditionally.

Two further grounds:

* **A nominal union re-opens a manufactured-agreement hazard.** A `UnionId` is
  module-local, so cross-module identity would have to be reconstructed from a
  rendered name plus structure. That is the direction-(2) failure the vtable
  naming comparator's refusal exists to close (`ty::stable_vtable_global_name`
  — "a closed grammar can still be lossy, and a lossy one merges two distinct
  coercions onto one global while every guard reports success"); it has already
  shipped a real defect once. `Array(U8, N)` has STRUCTURAL identity: it denotes
  the same type in every module, with no comparator in the loop.
* **The measured population is ~7-9 bodies**, all of which lower correctly
  today. Against that: a 39th `Ty` variant, a new module table, a Lean
  constructor plus semantics and parity-allowlist entry, validator, `shape`,
  interpreter byte funnels, diff identity, and four serialization formats.
  **Correction (2026-09-26, WS3.18 / F-050):** the Rust producer has since
  measured 26-69 bodies blocked by its union lane alone (612 jointly with
  closure-to-fn-pointer coercion), so the population figure understated the
  surface. That is the "new evidence" the ruling asks for, and it was
  re-examined rather than waved off. The blocked bodies do not need a union
  TYPE. They need three things the carrier model did not yet state: how a
  partially initialised union moves by value, how it crosses a call edge, and
  what refusal a producer meets when it spells a union as a struct. The
  producer guidance below supplies all three on the existing surface. The
  ruling is kept. Re-opening it now goes through the F-125 decision gate
  (roadmap WS8.20), which has to cite this section.

Correction to the record: the surviving characterization of this model as
"byte-array + `Transmute`" is stale. The Rust lowering that implements this
model uses neither a transmute nor a cast — a union field place resolves to the
carrier's base address (every union field is at offset 0) and the access is an
ordinary typed `Load` / `Store`. That matters here, because structural
condition 1 restricts `Transmute` to scalars, and the actual model never
invokes it: the byte-overlap union is inside the subset as it stands. That
lowering is this repo's own `frontend/src/mir_lower.rs` (the workspace-excluded
`rustc_private` driver), not the shipping tRust producer. tRust does not emit
the carrier yet: it refuses union places (the 26-69 bodies above), and
adopting the guidance below is its half of the work (WS5.17).

#### Producer guidance: carrier, access, moves and call edges (WS3.18, 2026-09-26)

Adopted with the ruling kept (roadmap WS3.18, closing the plan-of-record half
of F-050). Every rule below uses constructs the format already has. The
executable pins are `crates/trust-ir-conformance/tests/union_carrier.rs` and
`crates/trust-ir/tests/union_byte_overlap_model.rs`.

1. **A union value lives in memory, never in an SSA aggregate.** Its storage is a
   carrier of type `Array(U8, N)`: an `Alloca`, or a module `Global`. `N` is
   the union's size (rustc `layout.size`). The alignment is stated on the
   carrier (`Alloca { align }` / `Global.align`) as rustc `layout.align`,
   which is the strictest field's alignment. The statement is load-bearing:
   `[u8; N]` alone is 1-aligned, so a carrier that omits `align` can sit at
   an address where a wider field access faults as misaligned. A union nested
   in a struct is an `[u8; N]` field at its declared offset. The struct
   layout rule admits such a field; the WS2.3 mutation control pins that.
2. **Field access is a typed access at the carrier base.** Every union field
   is at offset 0, so a field place is the carrier's address, and a nested
   place projects from there with `GEP`. Reading field `f: T` is `Load T`
   from that address; writing it is `Store T`. Per-field `Aligned` /
   `NoUndef` go on the ACCESS, where they can be true. A field access never
   needs `Transmute` or `Bitcast`.
3. **A by-value union move is a byte copy between carriers:**
   `MemCopy { dst, src, bytes: N, overlap: false }` (WS3.20). It copies each
   byte's value, its init state and, by address, pointer provenance, so a
   partially initialised union (`MaybeUninit<T>`) moves without a fault and
   its uninitialised bytes STAY uninitialised at the destination.
   **Never** spell the move as a whole `Load` of the `Array(U8, N)` carrier
   into an SSA value. An array's elements cover every byte, so the typed load
   faults on the first uninitialised byte. The WS2.14 padding rule does not
   apply, because no byte of a carrier is padding. And an SSA `[u8; N]` value
   has no way to hold an uninitialised byte. The same holds for an aggregate
   that CONTAINS a carrier field: a whole-struct `Load` requires every byte
   of the `[u8; N]` field, so a struct holding a possibly-uninitialised union
   also moves by `MemCopy`.
4. **A union crosses a call edge by address.** The caller copies the union
   (`MemCopy`) into a carrier it owns for the call. It passes that carrier's
   address in a pointer slot marked `byval` with `pass: indirect` (WS3.11).
   A union result comes back through a caller-allocated carrier passed as the
   single `sret` pointer (`pass: indirect`), and the signature then returns
   nothing. The explicit copy is what makes the call by-value in the
   reference interpreter, which does not model the hidden `byval` copy: a
   callee write to its copy never reaches the caller's union.
   The value spellings do not carry an uninitialised byte. `indirect` on an
   `[u8; N]`-typed slot needs an SSA `[u8; N]`, which rule 3 rules out. A
   register lane is refused as well: the reference interpreter refuses a
   poison value across any call or return boundary. Where the target
   classifies a union into registers (`direct` / `cast`, e.g. a `repr(C)`
   union of at most 16 bytes on x86-64 SysV), a FULLY initialised union
   crosses as its scalar lane(s), loaded from the carrier at the lane type. A
   union that may be partially initialised has no faithful register spelling
   today. That covers every union the producer cannot show to be fully
   written, `MaybeUninit<T>` included. The producer must refuse that call site
   by name; zero-filling the uninitialised bytes to make it pass would invent
   a value (a named residual beside F-054).
5. **Padding stays padding.** When an ordinary struct, tuple or enum is
   built field-wise (padding never written), a whole-aggregate `Load` reads
   only the bytes a live field covers (WS2.14). A whole-aggregate `Store`
   writes the uncovered bytes as uninitialised, never as zeros. A later
   scalar read of a padding byte therefore yields poison, which faults as
   soon as it is inspected or returned, and never a fabricated `0`. Field
   bytes stay strict: a whole-aggregate load of an unwritten FIELD byte is
   undefined behaviour.
6. **The struct spelling is refused by name.** A union spelled as a
   `StructDef` whose fields share offset 0 is
   `StructLayoutInconsistent { reason: "fields overlap" }` (WS2.3, with or
   without a pinned target). The rendered diagnostic names this carrier and
   this section, and the reference interpreter's own refusal of such a
   layout does the same.

**Subset status of the move.** `MemCopy` is not yet admitted to this subset
(see the Excluded table); its binary tag (Inst 61) landed with the v51 INST
wire batch. A body that moves a union by value (rule 3), or makes the by-value
copy for a call (rule 4), therefore validates, executes in the reference
interpreter and has Lean semantics (`semMemCopy`), but it is off the proven
path until the `MemCopy` admission bump. Rules 1, 2 and 5 stay inside the
subset as they stand.

**Wire identity of the move.** Since the v51 INST wire batch the canonical
binary writer encodes a `MemCopy` (Inst tag 61, read-gated on v51), so a
module that moves a union by value (rule 3 or rule 4) HAS a wire identity
like any other: a binary encoding at the batch version and a
`stable_digest`, and the digest-keyed entry points (the linked import walk,
bundle binding, the CLI's `convert --format bin`) hash it rather than refuse
it. Before v51 the writer could not encode the move, so such a module had no
wire identity and `trust_ir_build::wire_identity_blocker` refused it by name
(`ModuleHasNoWireIdentity`); `union_carrier.rs` pins the flip
(`a_union_move_has_a_wire_identity_since_the_inst_wire_batch`, which also
runs the binary-decoded move). Neither workaround the old gap invited was
ever admissible: a whole-carrier `Load` is the spelling rule 3 forbids, and
zero-filling the uninitialised bytes invents a value (rule 4).

## Producer notes

Adoption record: which producers enforce this subset on their own emission
(self-gating), and the ratified rationale for producer surfaces that stay
outside it. tRust's frontend emission is pinned by the worked example above;
this section records the second first-class producer.

### Clean (`clean-compiler` — `emit_trust_ir`)

Clean's TrustIr backend **self-gates on this subset**: the handoff
configuration (`RuntimeLowering::ExternCalls`, which lowers Clean's managed
runtime to bodyless `external` runtime-call declarations) validates and
subset-checks the module it built at emit time and fails closed on any
violation (cross-repo adoption in
Clean's `crates/clean-compiler/src/emit_trust_ir.rs`). A producer can run
the versioned checker dep-light: depend on `trust-ir-conformance` with
`default-features = false` — the library target carries
`subset::module_subset_violations` with no feature requirements — or use
the in-process core bridge gate `Module::check_conformance_subset`, which
enforces the same per-construct verdicts on the function-emission surface
(the conformance checker additionally walks the interned type tables,
signatures, and globals; `tests/bridge_subset_agreement.rs` pins the two
verdict-identical).

Ratified with the 2026-07-04 promotion audit:

* **`clean.*` dialect ops: exempt-with-rationale, NOT admitted.** Clean's
  Dialect runtime-lowering mode wraps the 16 managed-runtime ops
  (`clean.rc.inc` / `clean.rc.dec` / `clean.rc.is_shared` + the
  `clean.obj.*` family) and `clean.str.const` in opaque `DialectOp`
  payloads. No `clean.*` op has a B3 depth-ledger entry — zero Lean
  semantics, no proven lowering — so admitting them would violate bump
  condition (1) below ("not faked"). They stay excluded: Dialect mode is a
  debug/round-trip surface, not a handoff mode, and is *expected* to fail
  this subset.
* **Strings: the `GlobalAddr` idiom, not `clean.str.const`.** The
  subset-clean lowering (what ExternCalls mode already emits) is a
  per-literal internal `Global` (`Ty::Array` of `U8` with a NUL-terminated
  `Constant::Aggregate` initializer) + `Inst::GlobalAddr` + a call to the
  runtime string constructor (`clean_mk_string`).
* **Non-scalar field access must not fall back to dialect ops.** At audit
  time, object-typed `sproj`/`sset` fell through to `clean.obj.sproj` /
  `clean.obj.sset` even in ExternCalls mode — that mode's one
  out-of-subset leak. The subset-clean idiom is the extern runtime-call
  form already used for scalar fields (or failing closed with a structured
  "unsupported" error); a silent dialect fallback breaks the mode's
  dialect-free promise.
* **Function addresses: `Constant::FnDef` (builder `fn_addr`), no cast.**
  Clean emits `Inst::Const { ty: Ty::Func(_), value: Constant::FnDef(_) }`
  against a shared closure-entry `FuncTy`, so the closure idiom needs
  neither `ReifyFnPointer` nor a `Bitcast` — exactly the sanctioned
  alternative the `ReifyFnPointer` exclusion names.

## Versioning and bump policy

The subset is versioned as a single integer
(`trust_ir_conformance::subset::SUBSET_VERSION`, currently **3**; this doc's
`**Version:**` header must match — the gate cross-checks the marker).

* **Expanding the subset (additive)** — e.g. admitting `vector.fma`, full
  fat pointers, or `F16` — requires, in one change: (1) the corresponding
  depth-ledger entry resolved by real, `lake build`-verified Lean semantics
  (or a fast-4-style refinement proof for a dialect op) — not faked; (2) the
  allowlist constant(s) and this doc updated in lockstep; (3) the version
  bumped (v1 → v2) and a dated entry added to the history below; (4) fixture
  exemptions re-derived (the two-sided gate forces stale exemptions out).
  Consumers may treat expansions as backward-compatible: every v(N) module
  is a valid v(N+1) module.
* **Shrinking the subset (breaking)** — removing a construct previously
  allowed — is a contract break for every frontend. It requires a
  coordinated announcement to the producers (tRust / Clean) and the
  backend, a version bump, and a migration note here. Expected only if a
  soundness hole is found in a construct's semantics.
* **Never** change the meaning of an existing version: v1 is frozen by this
  document as of its date; later versions get their own sections/history
  entries.

### History

* **v5 addendum (2026-11-14, no version bump)** — content-addressed weight
  blobs (PKG-U13e, wire v70) add `Constant::TensorBlob` and the module blob
  table. Nothing moved in the subset: a blob constant stands only at a
  `Ty::Tensor`, which both classifiers already exclude, and the codegen gate
  refuses its `Const` by name (`refuse/tensor_blob_codegen`). An unreferenced
  table row is content, not a construct a backend lowers. The counts do not
  change. The new golden `tensor_weight_blob` is an exempt fixture. The
  version stays 5.
* **v5 addendum (2026-11-14, no version bump)** — the tensor region's
  gather and scatter (PKG-U13d, wire v69) add `Inst::TensorGather` and
  `Inst::TensorScatter`. Nothing moved in the subset: both are added to the
  exclusion tables by name (`ConformanceSubset::inst_excluded`, the mirror's
  `inst_name`), as `TensorContract` was. The section's count becomes "53 of
  74". The new golden `tensor_gather_scatter` is an exempt fixture. The
  version stays 5.
* **v5 addendum (2026-11-14, no version bump)** — the tensor region's map,
  reduce and view (PKG-U13c, wire v68) add `Inst::TensorMap`,
  `Inst::TensorReduce` and `Inst::TensorView`. Nothing moved in the subset:
  all three are added to the exclusion tables by name
  (`ConformanceSubset::inst_excluded`, the mirror's `inst_name`), as
  `TensorContract` was. The section's count becomes "53 of 72". The new
  golden `tensor_map_reduce_view` is an exempt fixture. The version stays 5.
* **v5 addendum (2026-11-13, no version bump)** — the tensor region's first
  slice (PKG-U13a, wire v67) adds `Ty::Tensor` and `Inst::TensorContract`.
  Nothing moved in the subset: both are added to the exclusion tables by name
  (`ConformanceSubset::ty_excluded` / `inst_excluded`, the mirror's `ty_name`
  / `inst_name`), the precedent for a construct that landed without a
  consumer lowering. The sections' counts become "35 of 42" and "53 of 69".
  The new golden `tensor_contract` is an exempt fixture. The version stays 5.
* **v4 addendum (2026-10-08, no version bump)** — condition 6's walk loses
  its depth budget. Both checkers resolved "carries a `Char` by value" with a
  native recursion cut off at 24 levels that answered "carries a `Char`" when
  the cut-off was reached. That made cyclic and dangling tables fail closed,
  but it also refused every char-free type whose member chain is 24 levels
  deep, as "a `Char` read from memory", and walked a shared sub-type once per
  path. Both now decide the predicate exactly, in O(the module's types) per
  check: the core classifier with `trust_ir`'s reachability memo (cycles
  found as strongly connected components), the mirror with a whole-module
  summary (`subset::CharCarriers`, cycles found by peeling). A load's type
  carries a `Char` when it reaches a `Char`, a member id that resolves to
  nothing, or a by-value cycle, which is what the budgeted walk answered as
  its budget grows. The condition's meaning did not move (a `Char` read
  from memory is refused, resolved through every member table, and dangling
  or cyclic tables fail closed). Every module either checker admitted before
  is still admitted: a load the budgeted walk admitted had an acyclic,
  dangling-free and char-free reach under 24 levels. The verdict moves only
  for a load whose char-free reach is 24 levels deep or more, now admitted.
  Precedent: the 2026-09-27 condition 4 addendum (enforcement moved, meaning
  did not). The gated `char_carrier_differential` holds both checkers to the
  old walk given a budget no acyclic path can exhaust, on random modules and
  10^5-deep chains and towers.
* **v4 addendum (2026-10-02, no version bump)** — amendment D Part 2 (wire
  v56) adds `Inst::InvokeIndirect`, `CallIndirect`'s unwinding twin, and
  makes unwinding an exit under `PanicStrategy::Unwind`; the `LandingPad` /
  `Resume` rows are rewritten ("modelled under `Unwind`; awaiting
  admission") and nothing about them moved. Nothing moved in the subset: it is added to the instruction exclusion table by
  name (`ConformanceSubset::inst_excluded`, the mirror's `inst_name`), the
  precedent for an opcode that landed without a consumer lowering. The
  section's count becomes "53 of 67". The new golden `unwind_twins` is an
  exempt fixture. The version stays 4; the v5 EXPANSION admits it with
  trust-cg's lowering.
* **v4 addendum (2026-10-01, no version bump)** — amendment D (wire v55)
  gives `Inst::Drop` a meaning (a call of its type's drop glue, through the
  new module drop-glue table) and adds `Inst::DropInvoke`. Nothing moved in
  the subset: `Drop` was never allowlisted, and `DropInvoke` is added to the
  instruction exclusion table by name (`ConformanceSubset::inst_excluded`,
  the mirror's `inst_name`); the `Drop` row is rewritten because both models
  now execute a resolved drop. The section's count becomes "53 of 66". The
  new golden `drop_glue` is an exempt fixture. The version stays 4; the v5
  EXPANSION (`INST_ALLOWLIST_V5` = V4 ∪ {`Drop`, `DropInvoke`}, structural
  condition 9: every drop resolves) comes with trust-cg's lowering.
* **v4 addendum (2026-10-01, no version bump)** — amendment P (wire v54)
  gives `Inst::Assert` a panic site and adds `Inst::AssertInvoke`. A sited
  `Assert` stays inside the subset whatever its kind and site (the site
  changes which panic a failed check is, never whether it fails), so nothing
  moved for it. `AssertInvoke` is added to the instruction exclusion table
  by name (`ConformanceSubset::inst_excluded`, the mirror's `inst_name`), as
  is the precedent for an opcode that landed without a consumer lowering.
  The section's count becomes "53 of 65" (with main's two v53 call-unwind
  boundary variants, excluded beside it). The new golden `assert_panic_site`
  is subset-clean; `assert_invoke` is an exempt fixture. The version stays 4.
* **v4 addendum (2026-09-29, no version bump)** — the v51 INST wire batch
  gives `MakeAggregate` (Inst tag 60), `MemCopy` (61), `MemSet` (62) and the
  WS3.20 sub-ops (BinOp 23..=25, UnOp 9..=12) binary tags. Nothing moved in
  the subset: the three instructions stay excluded (no trust-cg lowering; for
  `MakeAggregate` also the enum / record Lean depth), the sub-ops stay
  included, and the codec fact only drops "no wire tag" from the stated
  reasons (`ConformanceSubset::inst_excluded`, the `Inst` exclusion table,
  "Wire identity of the move"). The new golden `inst_wire_batch` is an exempt
  fixture. The version stays 4.
* **v4 addendum (2026-09-27, WS3.9/WS3.13, no version bump)** — structural
  condition 4 (closure APPLICATION, a `CallIndirect` over a `Ty::Closure`
  callee, is outside the subset) is now ENFORCED by both checkers, on the
  callee's type from the function's value typing. The condition's meaning did
  not move — it has read this way since G18-2 (2026-09-01) — but neither
  checker enforced it: the codegen refusal was the construct's only gate, and
  no subset fixture applied a closure until the v58 `closure_layout` golden
  did, which the Lean executable differential refused as a type error. A
  module that applied a closure never had a Lean-covered meaning, so no
  subset-clean emission is lost; `closure_layout` joins the exemption table.
* **v4 addendum (2026-09-27, no version bump)** — `Inst::ArraySplat` and
  `Constant::Splat` (v50, the constant-size uniform array) are added to the
  instruction exclusion table, the constant one by an explicit
  `constant_splat_excluded` check on every emitted constant (the subset
  otherwise constrains a constant only through its declared type). Nothing
  moved: no `INST_ALLOWLIST_*` ever carried them and both checkers fail
  closed on them. The section's count becomes "53 of 62" (`Inst` has 62
  variants: `MakeAggregate`, `MemCopy`, `MemSet`, `Drop` and `ArraySplat`
  landed after v3 was cut). The version stays 4; admission is a later bump
  with the trust-cg lowering.
* **v4 (2026-09-22, WS2.17) — an EXPANSION under the bump policy.** The
  three v25 B1 scalars `Isize`, `Usize` and `Char` enter the type subset
  (32 → 35 of 40), and structural condition 6 is added. Every v3 module is a
  valid v4 module: condition 6 can only fire on a `Char`, and no v3 module
  could carry one. Closes F-037's type half.
  1. `Isize` / `Usize` execute at the Lean model's 64-bit pin
     (`Ty.bitWidth .Isize = some 64`, `Ty.isSigned .Isize = true`), and every
     arithmetic, comparison and cast rule is width-generic over
     `Ty.bitWidth`, so the arms exist as emitted. No new condition is needed:
     v3's condition 5 already pins the WHOLE module to that byte model, so a
     wasm32 `usize` module is out of subset for the target, not the type.
  2. `Char` is admitted together with condition 6 plus the interpreter's
     `validChar` UB check, which are the static and dynamic halves of the
     same invariant.
  3. `FPToSISat` / `FPToUISat` are NOT admitted. Their ay bit-blast encoding
     (`crates/trust-ir-ay/src/lib.rs::encode_cast`) still fails closed, so
     the interpreter/solver cross-check WS2.17 gates their admission on
     cannot be a test yet; they stay in the cast exclusion table and are a
     later bump.
* **v3 addendum (2026-09-19, no version bump)** — closure application is
  ratified BY VALUE (`FnOnce`-shaped), and a by-reference capture is ratified
  as a pointer-TYPED capture slot, so capture mode needs no new `ClosureTy`
  field (see "Closure application"). Nothing moved: first-class closure
  application was already outside the subset under structural condition 4 and
  is still refused for codegen, so this addendum states what the existing
  rule MEANS rather than changing what it admits, and the version stays 3
  (it lands on top of the WS2.9 v3 shrink below, which it does not touch).
* **v3 addendum (2026-09-19, no version bump)** — `Inst::MakeAggregate`
  (WS3.5, the register-level aggregate seed; landed after v3 was cut the
  same day) is added to the instruction exclusion table. Nothing moved: no
  `INST_ALLOWLIST_*` ever carried it and both checkers fail closed on it
  (`ConformanceSubset::inst_excluded` names the reason: no wire tag until
  the INST wire batch lands, no backend lowering, and enum / record
  construction an honest Lean partial). The section's count becomes
  "53 of 58". The version stays 3; admission is a later bump.
* **v3 (2026-09-19, WS2.9) — a breaking SHRINK under the "soundness hole"
  clause.** Closes F-042 and the subset half of F-036/F-037. No allowlist
  name moves (`*_ALLOWLIST_V3` alias v2); three things change:
  1. **`Transmute` loses `F32`/`F64`/`Bool` on both sides** (structural
     condition 1). The Lean `semCast .Transmute` arm now refuses a
     non-integer, non-pointer *destination* as `unsupported.cast` (it used
     to bind an integer at a float/bool type), and the reference interpreter
     now EXECUTES `Transmute` on exactly the Lean set instead of refusing
     every `Transmute` (`transmute_executes_on_the_integer_pointer_scalar_set`;
     Lean `transmute_u32_to_f32_unsupported_stable` is the mistranslation
     control).
  2. **New structural condition 5: the module targets the pinned 64-bit
     little-endian byte model.** It generalizes and DELETES the v2
     fat-pointer-only target gate (`ty_contains_fat_ptr` /
     `inst_contains_fat_ptr` in the core classifier, the `FatPtr` arm of
     `check_ty` in the mirror).
  3. **The core classifier refuses `Dealloc`** (`Inst::Dealloc: dropped
     from the subset in v2 (G18-1)`). The v2 drop was recorded here and in
     the mirror only; `Module::check_conformance_subset` fell through to
     the inline-type check and admitted it, so the "verdict-identical"
     claim was false (`trust-ir-self-declared/bridge-vs-subset-dealloc-drift`).
     Not itself a shrink — the ratified boundary already excluded it.

  **Migration note.** A `Transmute` with a float or bool operand on either
  side becomes `Bitcast` (int↔float is `Bitcast` in this format; int↔bool
  is `Trunc`/`ZExt`) or leaves the subset. A module pinned to a non-64-bit
  or big-endian target leaves the subset as a whole until WS2.16. No corpus
  fixture left the subset (the two-sided gate re-derived the exemption
  table: unchanged). Census before landing (measured 2026-09-19): neither
  producer emits `CastOp::Transmute` at all — the Rust producer treats a
  MIR `Transmute` as a lowering-failure seed and drops the body
  (`rustc_mir_transform/src/trust_verify.rs`, "one per unsupported
  construct (Transmute / …)"; `git grep CastOp::Transmute` over its
  lowering crates finds only consumers), and `clean-compiler::emit_trust_ir`
  never constructs it — so no shipped module carries a float/bool
  `Transmute`. The Rust producer pins `target_info` from the session target
  (`crate_module.rs::source_target_info`: `pointer_width / 8`, the target's
  endianness), so a wasm32 or big-endian BUILD leaves the subset as a whole
  — which is the intended verdict, not a regression: the Lean semantics
  never described such a module. trust-cg already fails closed on
  `Dealloc`. Announced to tRust/Clean/trust-cg as the WS2.9 landing.
* **v2 addendum (2026-09-01, no version bump)** — `RegionHavocStore`, the
  `Inst::Store` region-havoc marker added to `ProofAnnotation` after v2 was
  cut, is recorded in the annotation exclusion table, and the section's count
  is corrected from "36 of 39" to "36 of 40". Nothing moved: the
  machine-readable `PROOF_ALLOWLIST_V2` never carried the variant and both
  checkers (`subset::module_subset_violations` and the core bridge gate
  `Module::check_conformance_subset`) already failed closed on it, so this
  addendum brings the doc up to the constants rather than the reverse, and
  the version stays 2.
* **v2 (2026-07-13)** — admits first-class `FatPtr` on the pinned 64-bit
  little-endian
  executable path after matching Rust/Lean value, trio, and 16-byte memory
  semantics landed. The checker enforces kind-canonical metadata and rejects
  non-64-bit and big-endian fat-pointer modules. The `ty_composite` and `inst_arithmetic`
  corpus exemptions are removed and now act as positive conformance fixtures.
* **v1 (2026-07-02)** — initial pinned subset, derived from the B3 depth
  ledger after name-level Rust↔Lean parity closed (all schema-parity
  allowlists empty). Excludes: `Resume`, `LandingPad`, `CoroSuspend`
  (Inst); `F16`, `FatPtr` (Ty); `ReifyFnPointer`, non-scalar `Transmute`
  (CastOp); non-`Unit` metadata on the pointer trio; `vector.fma` and all
  non-`vector` dialects (DialectOp); `Custom` (ProofAnnotation).
* **v1 addendum (2026-07-04, no version bump)** — Clean producer promotion
  ratified (see "Producer notes"): the `clean.*` dialect ops were audited
  for admission and REFUSED (no depth-ledger backing — the "not faked"
  clause of the bump policy), so no allowlist changed, no names moved, and
  the version stays 1.

### v5 — target-indexed wasm32 model (2026-10-20)

Expansion of condition5 only: canonical wasm32 uses the checked32-bit model;
all v4 construct names, exclusions and64-bit behavior remain. The v5 machine
allowlists alias the frozen v4 lists. Source-to-IR bound certificate rechecking
remains mandatory; this model expansion does not prove emitted Wasm bytes or
complete a compiler product gate.
