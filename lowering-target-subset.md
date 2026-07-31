# Lowering-target conformance subset

**Version:** v2 (2026-07-13)
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
`PtrMetadata` / `F16` / … as "Lean-lagging") is **stale**: all three Rust↔Lean
schema-parity allowlists are **empty** (`Inst`/`Ty` 2026-07-02; `CastOp`
2026-07-10) (`crates/trust-ir/tests/lean_schema_parity.rs`) — every Rust
`Inst` / `CastOp` / `Ty` variant has a Lean constructor and executable
semantics. The
honest exclusions are now the **depth-ledger partials**: constructs whose
Lean semantics execute and agree with the reference interpreter but do not
yet model the construct's full generality. The v2 subset excludes exactly
those partial regions (plus dialect ops without proven lowerings and the
by-construction-unpinned `Custom` annotation).

## What "in the subset" means

A construct is in the subset when its Lean operational semantics cover the
construct **as emitted** (not merely name-parity), so the safety and
transform proofs can reason about every instruction on the path. Claim-style
proof annotations remain claims — the subset pins which annotation
*vocabulary* is part of the contract, not that a claim is discharged (back
claims with `ProofRef` per fast-1; see the trust boundary note in
`TRUST.md`).

## Types — `Ty` (32 of 37 allowed)

Allowed:

`I8` `I16` `I32` `I64` `I128` `U8` `U16` `U32` `U64` `U128` `F32` `F64`
`Bool` `Ptr` `Vector` `Unit` `Never` `Array` `Tuple` `Struct` `Enum` `Func`
`Sequence` `Set` `Record` `Closure` `Ref` `RefMut` `PtrConst` `PtrMut` `Rc`
`FatPtr`

Excluded:

| Ty | Why (depth ledger) |
|----|--------------------|
| `F16` | Type-level only in Lean; `Value.float` is binary64, so binary16 width/rounding is unmodelled (policy-gated on the per-width rounding residue in `decisions-panic-and-ub.md`). Any `F16` use is F16-width arithmetic/memory, so the type is excluded outright. |
| `Isize` | Pointer-width scalar adoption is still outside the proven lowering path (trust-cg / B1 depth-ledger adoption pending). |
| `Usize` | Same pointer-width scalar adoption boundary as `Isize`; fat-pointer length lanes use the explicit target-canonical `U64` spelling on the admitted 64-bit path. |
| `Char` | The Unicode-scalar validity and downstream lowering contract remain outside the proven path. |
| `Error` | Producer-internal fail-closed placeholder; never wire-legal. |

`FatPtr` is admitted in v2 only on the executable model's pinned **64-bit
little-endian** target. Rust and Lean both implement a distinct `(data, metadata)` value, the
`PtrData` / `PtrMetadata` / `PtrFromParts` trio, and a 16-byte little-endian
memory image (8-byte data address followed by an 8-byte length or vtable
pointer). The checker rejects non-64-bit or big-endian modules containing `FatPtr` and rejects
metadata types that are not canonical for the kind (`U64` for slice/str,
`Ptr` for trait objects). The metadata model intentionally does not claim to
model vtable contents.

Note on `Vector`: in the subset without a shape condition. The Lean
executable proofs are discharged at `<4 x i32>` / `<2 x i64>` (+ bool
masks); `<16 x i8>` / `<8 x i16>` are covered Rust-side by interpreter
cross-checks (fast-4 "honest boundary"). Widening the Lean executable subset
lifts the proofs without changing this contract.

## Instructions — `Inst` (54 of 57 allowed)

Allowed:

`BinOp` `UnOp` `Overflow` `ICmp` `FCmp` `Cast` `Load` `Store` `Alloca`
`HeapAlloc` `GEP` `PtrData` `PtrMetadata` `PtrFromParts` `Dealloc`
`AtomicLoad` `AtomicStore` `AtomicRMW` `CmpXchg` `Fence` `Borrow`
`BorrowMut` `EndBorrow` `Retain` `Release` `IsUnique` `Br` `CondBr` `Switch`
`Return` `Unreachable` `Call` `CallIndirect` `Invoke` `ExtractField`
`InsertField` `ExtractElement` `InsertElement` `SeqMap` `SeqMapAddK` `SeqMapNot`
`Const` `NullPtr` `GlobalAddr` `Undef` `Assume` `Assert` `Copy` `Select`
`OpenFrame` `BindSlot` `LoadSlot` `CloseFrame` `DialectOp`

Sub-op enums (`BinOp`'s 20 ops incl. `FMin`/`FMax`, `UnOp`'s 9,
`OverflowOp`'s 3, `ICmpOp`'s 10, `FCmpOp`'s 12, `AtomicRMWOp`'s 10, all 5
`Ordering`s, all 3 `AllocOrigin`s) are included in full; `CastOp` is the
exception (next section).

Excluded:

| Inst | Why (depth ledger) |
|------|--------------------|
| `Resume` | "Host unwinding": in the non-throwing executable model `Resume` is a structured `unsupported.host_unwind` — it has no semantics to prove against. |
| `LandingPad` | "Host unwinding" + "Multi-result binding convention": selector dispatch on a taken unwind edge is unmodelled (a directly-entered pad binds `(null, 0)`), and the two-result binding is packed into one aggregate rather than bound faithfully. Under the normal-path contract a pad is dead code anyway. |
| `CoroSuspend` | "Coroutine resume dispatch": the suspend side is modelled, but the whole-module resume/`Switch` state-machine theorem is open, and `semCoroSuspend_is_macro_expansion` is a definitional shape lock, not a `stepInst`-sequence equivalence. |

**`Invoke` is allowed on the normal-path contract:** under the ratified
`panic=abort` policy (the UB/numerics policy and the panic/UB decision
record, internal) the unwind edge is never taken;
the Lean executable model and the reference interpreter agree on the normal
edge (result binding included). A conforming frontend may emit `Invoke`
whose unwind edge exists for ABI reasons but must not rely on unwind-edge
*semantics* (landing-pad dispatch, `Resume` transfer) — those are exactly
the excluded region.

### Structural conditions (enforced by the checker, not name-level)

1. **`Transmute` is scalar-to-scalar only.** Depth ledger "Transmute
   generality": `semCast` models scalar reinterpretation; aggregate/pointer
   transmutes are structured unsupported. Scalar means
   `I8`–`I128`/`U8`–`U128`/`F32`/`F64`/`Bool`/`Ptr`.
2. **The pointer trio uses canonical metadata.** Thin pointers require
   `metadata_ty == Unit`; `FatPtr(Slice|Str)` requires `U64`; and
   `FatPtr(TraitObject)` requires `Ptr`. `FatPtr` is additionally restricted
   to the pinned 64-bit little-endian executable target. `PtrData` rejects types outside the
   exact executable pointer-trio set.
3. **`DialectOp` payloads are allowlisted individually** (next section).

## Casts — `CastOp` (14 of 17 allowed)

Allowed:

`Trunc` `ZExt` `SExt` `FPTrunc` `FPExt` `FPToUI` `FPToSI` `UIToFP` `SIToFP`
`PtrToInt` `IntToPtr` `PtrToPtr` `Bitcast` `Transmute` (scalar-to-scalar
only — condition 1 above)

Excluded:

| CastOp | Why |
|--------|-----|
| `ReifyFnPointer` | Depth ledger "ReifyFnPointer addressability": the fn-item value is preserved but the reified pointer is not `CallIndirect`-resolvable (no fn-pointer table entry is minted), and trust-cg's backend does not support it. Emit `Constant::FnDef` (builder `fn_addr`) instead. |
| `FPToSISat` | No proven lowering yet: ay `encode_cast` fails closed on it and it is Lean-excluded (B3 depth ledger), so the subset excludes it until one exists. |
| `FPToUISat` | Same as `FPToSISat` — fail-closed in ay, Lean-excluded; outside the subset until a proven lowering exists. |

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
| every other dialect (`clean.*`, `gpu.*`, `avx512.*`, `ane.*`, `verif.*`, …) | No proven lowerings; dialect ops round-trip opaquely by design. `clean.*` (Clean's managed-runtime ops) was audited for admission on 2026-07-04 and **refused** — zero depth-ledger backing; see "Producer notes". |

## Proof annotations — `ProofAnnotation` (36 of 37 allowed)

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

The feature-gated `Goal` (`clean-expr`) is outside v1 scope by construction
(off the default zero-dep surface); the checker fails closed on any
annotation it does not recognize. `Constant` variants are not separately
allowlisted: they follow the (checked) type they inhabit.

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

The corpus's job is byte-golden **wire-format** coverage of the *entire* IR
surface — deliberately broader than the proven subset. These fixtures
intentionally exercise out-of-subset constructs; the gate documents which is
which rather than forbidding them:

| Fixture | Out-of-subset construct it exists to cover |
|---------|--------------------------------------------|
| `ty_primitives` | `F16` (full primitive-type wire surface) |
| `b1_scalars` | `Isize`/`Usize`/`Char` (v25 B1 scalar wire coverage; trust-cg has no pointer-width-int or char lowering yet — B1 adoption wave) |
| `inst_vector_crosslane` | `vector.fma` |
| `inst_dialect` | opaque `verif.bfs_step` payload (every `AttrValue` variant) |
| `proof_annotations` | `Custom` (every annotation variant) |
| `chc_batch` | `Custom` (ay CHC protocol tags) |

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
the stricter core bridge gate `Module::check_conformance_subset`.

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
(`trust_ir_conformance::subset::SUBSET_VERSION`, currently **2**; this doc's
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
