# Changelog

Notable TrustIr changes are tracked here for Trust integration and release
review.

Entries are grouped under `Unreleased` until a release is cut. The most recent
tagged release is `0.8.0`; the workspace manifest is now `0.11.0`.

**Note on 0.9.0, 0.10.0 and 0.11.0.** The workspace passed through all three,
and the module binary writer moved to v38 (`FatPtrKind::ContainerLen`), but **no
`v0.9.0`, `v0.10.0` or `v0.11.0` tag was pushed** — the same pattern as 0.7.0
below. Those windows are not yet written up here; do not cite a tag for them.

**Note on 0.7.0.** The workspace version passed through 0.7.0 (release commit
`chore(release): 0.6.0 -> 0.7.0`, 2026-08-20), but **no `v0.7.0` tag was ever
pushed** — the next cut went straight to 0.8.0 the same day. The 0.7.0 section
below records that window; do not cite a `v0.7.0` tag. The tags that exist are
`v0.2.0`, `v0.3.0`, `v0.4.0`, `v0.5.0`, `v0.6.0`, and `v0.8.0` (plus the
`v0.2.0-windows` variant).

## 0.8.0 — 2026-08-21

Cut by `chore(release): 0.7.0 -> 0.8.0` (workspace 0.7.0 → 0.8.0; the public
tag is `v0.8.0`).

### Fixed (2026-08-19 – 2026-08-21)

- Declared struct layout evidence is validated at **every** consumer, not only
  where it was minted.
- `repr(packed(N))` IS the modulus, so the validator now checks it — together
  with the field-offset alignment rule the validator had been missing (wave-SG,
  the interpreter half of the same class).
- `repr(transparent)` carrier parity is enforced.
- Target scalar ABIs the layout model does not represent are **declined**
  rather than approximated, and canonical targets are bound to pointer width.
- `validate` no longer materializes dense dominator sets.
- Dependency semver moves are transacted, not edited leg by leg.
- Four publication-boundary guard defects, each of which fired on this repo's
  own tree: the T1 check asserted a Clean `[patch]` this repo deliberately
  deleted, read the manifest as bytes and tripped over its own documentation,
  anchored its Clean note to prose that is rewritten weekly, and counted copies
  of a URL it already had a constant for.

### Changed (2026-08-19 – 2026-08-21)

- The Clean and AY authorities advanced to the release frontier: clean
  `84c9ae5e` (v0.4.0) and ay `09951c0e` (v0.15.0).
- The Clean pin is documented as **coordinated, not frozen** — the previous
  wording blocked its own bump.
- The module binary writer stays at v37; readers accept v23–v25 and v29–v37
  (v26–v28 remain rejected).

## 0.7.0 — 2026-08-20 (no tag)

Cut by `chore(release): 0.6.0 -> 0.7.0` (workspace 0.6.0 → 0.7.0). **No
`v0.7.0` tag was pushed**; the 0.8.0 cut superseded it the same day.

### Added (2026-08-18 – 2026-08-19)

- A declared struct layout is **normative** to the interpreter — the struct
  half of the ADT-offset class.
- `Borrow` / `BorrowMut` over a fat-pointer value is a verbatim pass-through.
- `stable_vtable_global_name`, the shared vtable-identity mint (vtable slice 3).

### Changed (2026-08-19)

- The local-path `[patch]` redirecting `clean.git` to `../clean` was **deleted**,
  breaking the clean pin cycle: cargo now compiles Clean at the pinned rev and
  the root `Cargo.lock` records that rev again.
- The workspace was reformatted with the canonical stage2 `trustfmt`.
- The identity mints are documented as naming BOTH collision directions, not
  only the hashed one.
- Clean and AY pins advanced atomically to clean `cbe8695a` and ay `9ff68fe0`
  (v0.12.0). The writer stays at v37.

## 0.6.0 — 2026-08-18

Cut by `chore(release): 0.5.0 -> 0.6.0` (workspace 0.5.0 → 0.6.0; the public
tag is `v0.6.0`).

### Added (2026-08-18)

- Five FP conversion nodes for the `FCVT*` semantics — **total**, with the
  saturating reading, so no conversion is a partial operation in the contract.

### Changed (2026-08-18)

- Followed Clean's owner-side 0.x demotion: the Clean-backed legs moved from
  `1.6.0` / `bfb5d33b` to `0.1.0` / `71449eaa`. The AY legs stayed at ay v0.10.0
  (`0c053832`). The writer stays at v37.

## 0.5.0 — 2026-08-17

Cut by `chore(release): 0.4.0 -> 0.5.0` (workspace 0.4.0 → 0.5.0; the public
tag is `v0.5.0`).

### Added (2026-08-13 – 2026-08-17)

- **Binary v37 — `EnumTagEncoding::Untagged`, the tag-free enum image.** This is
  the format bump behind 0.5.0 (writer v36 → v37). The new arm is read-gated
  (`version >= 37`) because it sits inside a record a v36 reader already parses:
  an ungated arm would let a v36-labelled blob decode as untagged.
  `MIN_READ_VERSION` stays 23.
- The boolean connectives `BAnd` / `BOr` / `BXor` on `BinOp`.
- `ProofAnnotation::FreshSymbolicHavoc` — an inert marker for an `Inst::Undef`
  whose consumer semantics are a fresh, unconstrained value. It proves no
  proposition, authenticates no producer, and grants no authority to import
  constraints; it is public and survives binary serialization.
- `scripts/bump-dep-pin.sh`, the atomic Clean/AY bump transaction: a partial
  six-leg pin move becomes mechanically impossible rather than merely
  detectable.

### Fixed (2026-08-13)

- The #205 defect is pinned by its own test, both halves.

### Changed (2026-08-12 – 2026-08-17)

- The symbolic proof authority is bounded by the checker envelope, and the wide
  symbolic bundle now proves — recorded as measured truth rather than an
  expectation.
- The binary-format document states that decoded source authority is inert.
- The dependency authorities moved to the released revs through the new atomic
  transaction: clean v1.6.0 (`bfb5d33b`) and ay v0.10.0 (`0c053832`), with the
  frozen `CLEAN_VERSION` guard following the manifests to 1.6.0.

## 0.4.0 — 2026-08-12

Cut by `chore(release): 0.3.0 -> 0.4.0` (workspace 0.3.0 → 0.4.0; the public
tag is `v0.4.0`). The writer stays at v36 for this release.

### Changed (2026-08-11)

- Dependency authorities converged post-release on the final single-A9 set: the
  AY legs now pin ay `b5e2523b` (v0.9.0) and the Clean-backed legs pin clean
  `4a2387da` (v1.4.0), moved coherently across every manifest and lockfile leg.
- Regenerated the live conformance corpus at the already-ratified v36 schema
  and added a ratchet requiring every current `.tmbc` golden and both normative
  format documents to track `binary::FORMAT_VERSION` exactly.

### Changed (2026-08-12)

- The authorities moved again inside the release window and settled, at the
  cut, on the mapped release pins: clean `fcc257e2` (v1.5.0) and ay `1f8238bb`
  (v0.9.0).
- The normative-document marker check is dev-tree-only.

### Fixed (2026-08-11 – 2026-08-12)

- Format-v36 conformance parity gaps closed.
- Bit-vector proof resources are bounded.
- A lockfile dedup for the stray `ay` stanzas left by the A10 re-pin sweep.

## 0.3.0 — 2026-08-11

Cut by `pub bump` (workspace 0.2.0 → 0.3.0; the public tag is `v0.3.0`).

### Added (2026-07-27 – 2026-08-08)

- Binary v34 adds the additive `ProofObligation.site` IR-position backref
  (function, block, instruction index), binding a per-check obligation to the
  one VC condition that actually backs it. A v33 blob decodes with
  `site = None`, which fail-closed consumers must treat as "not bindable to a
  VC condition", never as a wildcard.
- Binary v35 adds optional `Function.source_provenance`: compiler-source,
  non-circular semantic-body, and complete-binding digests followed by exact
  source-loop/header/name/place rows, authenticated by the validator before
  use.
- Binary v36 adds `StructPassingPolicy::Unclassified` — a producer that emits
  no `ParamAttrs` classification can now say so truthfully instead of
  claiming `NativeC`/`AlwaysMemory` or failing `TargetInfoRequired`. It is a
  declaration of ABSENCE, not a third convention: a backend that needs a
  classification must refuse the module, never infer one. `MIN_READ_VERSION`
  stays 23 across all three bumps.
- The Rust producer records panic-class proof obligations from MIR `Assert`
  terminators (`BoundsCheck` / `ArithmeticSafety` / `PanicFreedom`), always
  with status `Pending` — a recorded claim, not a proof. There is a single
  mint site and no promotion path; measured 70 obligations against 70 corpus
  `Assert` terminators, exact in both the unwind and panic=abort lanes.
- The first honest discharge route: goal-bound bv-blast proofs earn
  `Discharged` for 9 of the 385 recorded obligations. The binding is
  re-derivation, not replay — `proof/bvgoal.rs` reconstructs the goal from
  the module IR at the obligation site, and the validator re-blasts it and
  demands the payload's CNF equal the re-derived one exactly.
- `TrustVcVerificationMode::DischargeProofObligations` (append-only and
  digest-neutral) makes the native discharge request expressible, and
  `TrustVcNativeRequest.function` names the function under discharge.
- A sealed source-generation authority for the one audited in-process
  source-lowering lane: a non-Clone, non-serializable token bound to the full
  canonical bundle digest. Cloning, serde/binary round-trips, re-minting,
  equal-content reconstruction, and cross-instance transplants all fail
  closed.
- The ICmp and integer-resize validation allowlists learn `Ty::Char` (#194):
  `'a' == 'b'`, `'h' as u8`, and `0u8 as char` now validate as well-formed,
  matching what the interpreter already executed.

### Fixed (2026-07-27 – 2026-08-06)

- Three defects in the discharge path, each pinned by a test that fails
  without the fix: a positional-MessagePack corruption
  (`ProofObligation.source` kept `skip_serializing_if` after v34 appended
  `site` behind it, shifting the site record into the source slot); assert
  polarity inferred from block shape, which could invert in the unwind lane
  and prove the NEGATION of an obligation (now fails closed on a diverging
  THEN arm); and vacuous certificates — all 45 "offline-replayable"
  certificates proved `false ⊢ ⊥`, so a vacuity gate now refuses evidence
  whose goal canonicalises to a constant (honest replayable count via the
  Solver-bundle path: zero).
- The stable request digest gained the `TrustVcNativeRequest::function`
  writer arm that its own coverage test demanded.
- Validator corrections, each with accept controls: the ZST test is
  module-aware (a zero-sized STRUCT field is a ZST, unblocking
  `NonNull`/`PhantomData` transparent layouts); `repr(transparent)` takes AT
  MOST one non-ZST field, not exactly one; the `repr(Rust)` FFI-boundary
  checks (`FfiStructReprUnpinned` and `first_ffi_boundary`) require a FOREIGN
  calling convention, no longer flagging ordinary Rust cross-crate
  declarations; and a first-class closure VALUE exposes its captures as
  fields to `ExtractField`, exactly the read the interpreter performs.
- The interpreter accepts the null pointer constant (`Constant::Int(0)` at
  `Ty::Ptr`), resolving a validator/interpreter disagreement. Zero only: a
  nonzero integer at `Ty::Ptr` stays fail-closed on the type-error path.
- A Rust-2024 let chain in the workspace-excluded `frontend/` crate (edition
  2021) had made HEAD uncompilable; desugared.
- A partial Clean/AY pin move is now mechanically impossible, not just
  detectable: pin moves go through `scripts/bump-dep-pin.sh` (a six-leg
  atomic move) and the toolchain-free pin census joined
  `scripts/ci_gates.sh` gate 0.
- The bv-blast proof authority is bound to the exact AY source revision, and
  the dev gates accept linked Clean worktrees.

### Changed (2026-08-11)

- At the 0.3.0 cut the module binary writer emits v36; readers accept v23–v25
  and v29–v36 (v26–v28 remain rejected).
- Dependency authorities at the cut: the AY legs pin the released ay v0.7.0
  (`937092bb`) and the Clean-backed legs pin the clean v1.4.0 release rev
  (`4d2325a3`).

### Added (2026-07-26)

- Binary v32 adds optional per-function SSA value names. Binary v33 adds the
  optional lexical-scope tree and per-instruction scope indices. These fields
  are claim-style debug metadata. All four formats preserve them losslessly;
  the human-readable form uses quoted `#names` and ordered `#scope`
  directives.
- The v33 binary codec pins present and absent value-name/scope tables, exact
  per-node scope indices, and every stable producer-provenance variant in
  round-trip tests. Readers continue to accept v23–v25 and v29 onward while
  rejecting the ambiguous v26–v28 development formats.

### Changed (2026-07-26)

- Debug metadata now remains referentially closed through canonical SSA
  renumbering, dialect lowering, mem2reg promotion, and CLI module linking
  (including linked-file-index remapping). Validation rejects duplicate or
  dangling value names, malformed scope trees, dangling instruction scopes,
  and scope spans outside a present module file table.
- Semantic diff explicitly treats value names, lexical scopes, and source
  spans as cosmetic claim-style metadata; a regression gate pins that policy.

### Added (2026-07-22)

- Binary v31 adds per-variant source field names and optional normative enum
  layout descriptors for direct and niche tag encodings. The validator,
  layout-shape API, interpreter byte funnels, diff identity, and Lean schema
  mirror agree on the new model. V23–v30 binaries and pre-v31 positional
  MessagePack default the additions to empty/absent; pinned v30 enum fixtures
  guard that compatibility path.

### Changed (2026-07-22)

- Normative enum layout descriptors now enforce natural field, direct-tag, and
  niche-lane alignment consistently in validation, layout queries, and the
  reference interpreter.
- The optional AY adapter is pinned to AY source revision
  `023374e80725f2dcd017124d5b61e4a6f86464e0`. This keeps the coordinated
  Clean → TrustIr → TrustCg publication cycle on the final reviewed AY 0.4
  dependency line.
- Clean-backed dependencies and the standalone frontend lock now pin the
  reviewed Clean publication source revision
  `eb71e4ab8b80abcb6620210de5dcdd93f578de05`, including the closed
  Clean-to-Trust dependency boundary, the exact AY pin, and the narrowed
  constructive Farkas closure that replaces the experimental `math-overlays`
  surface with the `farkas-constructive` feature.

### Added (2026-07-13)

- The identity-development line numbered v27 added explicit
  `SpecModule.enforcement` (`DesignOnly` or `Linked`) and typed
  `SpecAnchor.projection_target` resolution; that byte-incompatible line was
  later merged into v29. `Linked` coverage no longer depends on anchor count;
  every linked anchor requires typed action and projection identities; function
  projections enforce a body, exact name, and `(&T) -> R` signature. Proof
  manifests are fail-closed for linked machines, and the explicit exploratory
  override remains machine-readably non-certifying with a nonzero CLI status.
  Legacy v23–v25 binary and old serde/text artifacts map conservatively to
  `DesignOnly` with no typed projection target. Current Rust direct-to-TrustIr
  temporal lowering emits `Linked` plus the versioned temporal field-path
  projection target.
- The v30 typed value model adds `Ty::Refine`, `Module.universes`, and
  `Module.predicates`.

### Changed (2026-07-03)

- **tSwift and tC are deprecated** (they never shipped). Producer lists across
  the live docs now name the two real producers: **tRust** (Rust) and
  **Clean** (fused proof language, via `clean-compiler`'s experimental
  `emit_trust_ir` backend — `clean compile --emit trustir|obj`). Format
  capabilities are unchanged: the ARC instructions serve Clean's
  reference-counted runtime, and the `SwiftHeap`/`CMalloc` allocation origins
  plus the `tSwift`/`tC` producer identifiers in `request::facts` stay
  wire-compatible.


### Added
- `AllocOrigin::CleanHeap` (P1 "Native ARC for Clean") — Clean's Perceus
  reference-counted heap cells (`clean_alloc_ctor` / `clean_inc` /
  `clean_dec`) are a first-class allocation origin, landed as a coordinated
  triple. Decision: a DISTINCT variant rather than `SwiftHeap` reuse — the
  refcount discipline is identical (stated in Lean:
  `cleanHeap_toAllocationOrigin` + `alloc_isInBounds_ignores_origin`, both
  `rfl` and axiom-audited, plus executable cleanHeap/swiftHeap twin-state
  parity fixtures), but origin is runtime provenance: the backend frees a
  Clean cell through Clean's RC runtime, not `swift_release`, and a
  Clean-produced module must not claim origins of the deprecated Swift
  producer. Surface: text spelling `clean_heap`, binary origin byte 3 with
  wire format VERSION bumped **21 → 22** (pre-v22 readers reject v22 blobs
  wholesale at the header version check; no read-side gate needed — the
  v16/v17/v21 wholly-new-tag rationale), Lean
  `AllocOrigin.CleanHeap`/`AllocationOrigin.cleanHeap` +
  `Retain -> IsUnique(false) -> Release -> Release` reaches-zero /
  underflow-UB `native_decide` fixtures, interpreter RC-lifecycle test
  (origin-uniform refcounting, unchanged code), and the
  `clean_rc_lifecycle` function in the `inst_borrow_arc` conformance
  fixture (regenerated goldens).
  instruction (`for x in &mut l { *x = fwd(x) }` with a first-class element
  function; Aeneas `loopFwd`), landed as a full coordinated triple
  (designs/2026-06-30-general-seqmap-instruction.md): Rust surface +
  validation (`fwd` must exist as the single-`&mut` `fn(&mut elem)` over the
  sequence's element type), reference-interpreter execution via the call
  machinery (one call-depth level for the whole map — depth bounds nesting,
  not length), Lean operational semantics (`StepResult.SeqMapReq` +
  `stepNWithContext` element runner, `native_decide` agreement fixtures), and
  give-back certification: module-threaded recursive element elaboration
  (`elaborate_give_back_in` et al.), loop certs citing ONLY the
  universe-polymorphic `listMapT_roundTrip`, fail-closed on any element
  function whose give-back is not independently certified (first milestone:
  scalar constant increment + identity). Binary tag 56; wire format VERSION
  bumped to 21 (20 is reserved for the in-flight ABI-fields branch);
  conformance fixture `inst_seq_map_general` round-trips all four formats.
- `Inst::GlobalAddr { global: GlobalId }` — take the address of a module
  global (static / `&str` literal / vtable) as an SSA value (B1).
- `Inst::HeapAlloc { ty, count, align, origin }` with `AllocOrigin`
  (`RustHeap` / `SwiftHeap` / `CMalloc`) — heap allocation is now
  representable, validated, executable, and serialized (B2).
- Function-scoped proof obligations: `ProofObligation.function: Option<FuncId>`,
  with a scope-aware inheritance validator (B4).
- Per-call proof context: `InstrNode.proof_context: Option<ProofContext>` and
  `ProofEvidence::InheritedFromCallee` for cross-language proof inheritance (B5).
- `ProofAnnotation::ProofRef(ProofId)` — backref tying an annotation to a
  specific discharged module obligation (fast-1).
- Function/parameter codegen attributes (`FuncAttrs` / `ParamAttrs`:
  nonnull/align/noalias/readonly/etc.) (fast-2).
- Value-fact proof annotations `ProofAnnotation::ValueRange { lo, hi }` and
  `KnownBits { zeros, ones }`, plus a `GEP.inbounds: bool` flag (fast-3).
- `ProofAnnotation::Wrapping` — modular-arithmetic marker (no overflow
  obligation).
- `Module.obligation_diagnostics` sidecar (`ObligationDiagnostic` /
  `DiagnosticSeverity`): actionable per-obligation verifier output (severity,
  message, optional source location + detail) keyed by obligation id, without
  changing the `ProofObligation` wire shape; validator rejects dangling refs.
- `Module.files` debug-info source-file table with `Module::intern_file` /
  `file_name`; `SourceSpan::file` now indexes it, and the validator rejects
  out-of-range indices (`SpanFileIndexOutOfRange`).
- `StructDef.repr` ABI classification (`StructRepr::{Rust,C,Transparent,
  Packed(u32)}`) for deterministic TrustCg struct layout, with
  repr(transparent)/repr(packed) validation, and `TargetInfo` consistency
  validation (pointer size, non-empty triple) when present.
- `ProofEvidence::CleanCic` and `ProofStatus::Certified` — the de Bruijn /
  kernel-checkable proof tier (strictly stronger than `Trusted`). The
  `validate_module` Certified gate requires a CleanCic certificate bound to the
  obligation (matching `clean_cic_lineage_digest`) **with a non-empty `term`**;
  an empty-term certificate is rejected (it carries no checkable content).
- `Inst::CallIndirect.calling_conv: CallingConv` — the indirect-call ABI
  declaration (a direct `Call` inherits the callee `Function`'s convention; an
  indirect call has no statically-known callee, so it declares the expected
  ABI). `#[serde(default)]` + binary version-gating default it to `C` for
  pre-v12 modules; the builder exposes `call_indirect_cc`.
- A Rust-side schema-parity gate test guarding `Inst` / `CastOp` / `Ty` against
  Lean-schema drift, with an explicit allowlist (B3 mitigation). As of
  2026-07-02 all three allowlists (`INST_ALLOWLIST`, `CASTOP_ALLOWLIST`,
  `TY_ALLOWLIST`) are **empty** — see the Verified section below.
- `Inst::SeqMapAddK` / `Inst::SeqMapNot` — structural element-wise sequence
  maps (constant increment / boolean flip), the IR carriers for the give-back
  loop certifications.
- `Inst::CoroSuspend` (binary v16, wire tag 50) — coroutine suspend
  terminator; operationally the documented macro-expansion
  `GEP(frame, state_slot)` + `Store(next_state)` + `Return(value)`.
- Exception-handling scaffold `Inst::Invoke` / `Inst::LandingPad` /
  `Inst::Resume` (binary v17, wire tags 51–53) — zero-cost table-driven
  unwinding surface: `Invoke` is a call terminator with normal/unwind
  successors, `LandingPad` is the handler-entry instruction producing
  (`Ptr` exception object, `I32` selector), `Resume` re-raises.
- `Module.spec_modules` (binary v13) and `SpecModule.proofs` / `SpecProof`
  (v14) — spec cross-reference objects and proof-name bindings.
- `Switch.exhaustive_enum_unreachable: bool` (v15) — marks a switch over an
  exhaustive enum selector whose default edge is unreachable.
- `Function.summary: Option<FunctionSummary>` (v18) — the separate-compilation
  contract: requires/ensures `ProofFormula` clauses + param names + proved flag.
- `EnumDef.discriminants` + `EnumDef.repr` (`EnumTagRepr`) (v19) — explicit
  per-variant discriminant values and tag-representation hint for the
  canonical tagged-union enum layout.
- The `trust-ir-giveback` crate and the `certify_module_give_backs` pass —
  an untrusted give-back elaborator emitting `Pending` `GiveBackRefinement`
  obligations; `Certified` is granted only after the in-process clean-kernel
  (ck0) re-check of the refinement certificate. The `giveback-anchor` feature
  is default-OFF; unsupported give-back anchors fail closed.
- `ObligationKind::ArithmeticSafety` / `ObligationKind::BoundsCheck` —
  panic-class obligation kinds matching `trust_verifier_api`; the enum is now
  `#[non_exhaustive]`.
- `ProofAnnotation::Tainted` / `ProofAnnotation::TrustedSink` —
  information-flow (non-interference) markers, enforced module-wide by the
  validator.
- `ProofAnnotation::Goal(Box<ExprObligation>)` behind the new `clean-expr`
  feature — the node's obligation carried as a Clean kernel `Expr`, stamped at
  construction (default zero-dep builds never pull clean-kernel).
- `ProofAnnotation::BranchWeights(Vec<u32>)` — `CondBr`/`Switch` out-edge
  frequency hint with placement/arity validation, completing fast-3.
- `Formula::FpToIeeeBv` in `trust-ir-contract` — the FP → BV half
  (`fp.to_ieee_bv`), exact inverse of `Formula::FpFromBits`.
- fast-4 vector dialect ops: typed `vector.reduce` (Add | Or),
  `vector.shuffle`, and `vector.fma` with decoders and validation.
  `VectorLoweringPass` gains `lower_reduce` / `lower_shuffle` core-IR scalar
  fallbacks with interpreter cross-checks; `vector.fma` deliberately has NO
  scalar fallback (the no-unfused-fallback policy is ratified in
  `docs/roadmap/fast-4-vector-crosslane-ops.md`).
- `ProofLineageManifest::append_pass` — correct-by-construction lineage
  chaining helper (allocates the next id, threads source/target digests,
  links `depends_on`), with tests.
- Diagnostics surfacing: `Module::resolve_span` + `Module::render_diagnostic`;
  the `trust-ir` CLI `validate` / `dump` subcommands now report
  `obligation_diagnostics`; new byte-golden `proof_diagnostics` conformance
  fixture across all four formats.
- B5.1 validator rule `ProofContextAssumeScopeMismatch`: a
  `ProofContext.assumes` obligation that is B4-scoped to a function other than
  the static callee is rejected — on `Inst::Call` AND `Inst::Invoke` (an
  invoke is a call with an unwind edge).

### Verified
- A Lean 4.8.0 toolchain is installed (via elan, pinned by `lean-toolchain`);
  `PATH="$HOME/.elan/bin:$PATH" lake build` is green at HEAD, including the
  `AxiomAudit.lean` `#guard_msgs` gate — the single first-party axiom remains
  `ay_sound_unsat`, and the new theorems below depend only on the Lean-core
  trio.
- B3 discharged at the name level: the Lean-schema parity gate holds with all
  three allowlists empty (`crates/trust-ir/tests/lean_schema_parity.rs`). New
  Lean semantics: `semSeqMapAddK` / `semSeqMapNot`
  (`Semantics/Aggregate.lean`) with the round-trip laws
  `seqMapAddKList_roundTrip` / `seqMapNotList_involutive`
  (`Proofs/AggregateProps.lean`); `semCoroSuspend`
  (`Semantics/Coroutine.lean`, the documented GEP + Store + Return
  macro-expansion, with a definition-shape lock); and a non-throwing
  executable `Invoke`/`LandingPad`/`Resume` model (`StepResult.InvokeReq` in
  `Semantics/Control.lean`, evaluator handling +
  `BasicBlock.terminatorResultDests` in `Semantics/Eval.lean`) with
  `native_decide` interpreter-agreement fixtures. Honest residue: the depth
  ledger in `docs/roadmap/B3-lean-ir-parity.md` (name parity is not semantic
  depth).
- B2 Lean half complete: `semHeapAlloc` (all three `AllocOrigin`s reachable)
  plus the dealloc lifecycle lemmas `semDealloc_marks_dead` /
  `semDealloc_twice_is_ub` (`Proofs/MemorySafety.lean`, AxiomAudit-pinned).
- B5 Lean landed: `proof_context_assume_sound` plus the bridging lemmas
  `stepNWithContext_callReq_eq_runCallReq` /
  `stepNWithContext_bodyCall_eq_runCallReq_bind` /
  `proof_context_assume_sound_evaluator` anchoring `runCallReq` to the real
  evaluator, and `inlining_preserving` in the frame-discipline iff form
  (`Proofs/TransformCorrectness.lean`; the full body-splice form is
  documented out of reach).
- fast-4 refinement proofs: `runsAgreeFrom_reduce` / `runsAgreeFrom_shuffle`
  (`Proofs/VectorDialectProps.lean`), with the `vectorLowerFrom_sound`
  dispatch theorem extended to cover them.
- Full default-workspace `cargo test` green (~1770 tests).

### Changed
- The module binary writer now emits v33. The reader has
  `MIN_READ_VERSION = 23` and accepts v23–v25 and v29–v33; v26–v28 are rejected
  because two development lines used those version numbers for
  byte-incompatible layouts. v29 merged `Global.align` with the spec/proof
  identity fields; v30 adds `Ty::Refine` plus the trailing `Module.universes`
  and `Module.predicates` tables; v31 adds per-variant source field names and
  optional direct/niche enum layout descriptors; v32 adds SSA value names; and
  v33 adds lexical-scope trees plus per-instruction scope indices.
  Proof-lineage sidecars remain independently versioned at v2.
- The clean sibling dependencies (`clean-kernel`, and the optional
  `clean-mathverse` / `clean-olean`) are consumed as **rev-pinned Cargo git
  dependencies** (with per-workspace `[patch]` redirection to local checkouts)
  so trust-ir is consumable as a plain cargo git dependency.
- Lean ↔ Rust numerics reconciliation: signed `SDiv`/`SRem` now use
  truncation-toward-zero (`Int.div`/`Int.mod`) in the Lean model and AY bridge
  (was Euclidean `Int.ediv`/`Int.emod`, which disagreed with the Rust
  interpreter and LLVM on negative operands); `AShr` is explicit floor
  (`Int.fdiv`); `FPToUI`/`FPToSI` trap NaN/out-of-range as UB (matching the Rust
  interpreter); the Lean `AtomicLoad` is now side-effecting (not DCE-eligible),
  matching `has_observable_effects`.
- Documentation audit-remediation pass: corrected the repo URL, the lean
  package path (`lean/trust_ir-semantics`), the backend name (TrustCg, not
  TrustIr), the binary-format version, and the instruction/type/proof tables
  in `CLAUDE.md`, `README.md`, `HANDOFF.md`, `VISION.md`, and the `docs/`
  format and roadmap docs.

### Fixed
- `ObligationDiagnostic` positional-MessagePack decode bug: `location` was a
  non-trailing `skip_serializing_if` field, so skipping it shifted `detail`
  into the location slot ("invalid type: string, expected struct SourceSpan").
  `location` is now always emitted; only the trailing `detail` may skip (the
  same R3 #5 rule as `ProofObligation::formula`).
- Corrected the stale `binary.rs` header comment (fast-5 Nit A): v4 added
  string interning + VInt (LEB128) encoding only — InstrNodes are NOT
  bit-packed; real packing remains a tracked, optional fast-5 follow-up.

## 0.2.0 — 2026-05-31

### Added
- Hardened `Ty::Vector` validation in the core IR contract: zero-lane vectors,
  unsupported element types (nested vectors, pointers), and mismatched
  `Constant::Vector` lane counts are now strictly rejected.
- Tightened `Inst::Select` validation for vectors: conditions must be logical
  same-lane `<N x bool>` masks; scalar `bool` and physical integer masks are
  now rejected.
- Tightened generic `ExtractElement` and `InsertElement` validation: mismatched
  array/result/scalar types and out-of-range constant indices are now rejected.
- Added a comprehensive negative test suite for vector operations in
  `crates/trust-ir-build/tests/vector_negative.rs`.
- Added a `ay_chc_batch_eval` conformance fixture for the x86 CHC Batch JIT
  contract in `crates/trust-ir-conformance`.

### Verified
- Discharged both vector-dialect lowering trust-boundary axioms in the Lean 4
  semantics (`TrustIr/Proofs/VectorDialectProps.lean`) with genuine
  forward-simulation proofs: `vector.pack_lanes` (lane construction) and
  `vector.mask_to_bits` (boolean-mask bit-packing) now refine their core-IR
  lowerings with no `axiom` and no `sorry`. Vector ops are now advertised as
  proof-carrying per the x86-SIMD plan's Lean-coverage gate.
- The Lean semantics package builds clean (`lake build`) with a single
  remaining trust assumption — `ay_sound_unsat`, the documented, irreducible
  external SMT-solver soundness boundary in `TrustIr/Proofs/AYBridge.lean`.

### Changed
- Performed a global architectural rename to resolve project identity
  confusion, settling the canonical names: `ty` (verification engine), `TY`
  (model-checking contract namespace), and `TrustCg` (verified backend). The
  compilation stack is documented as `tRust/tSwift -> TrustIr -> TrustCg`.
- Updated `NativeBundleIdentityContractDescriptor` to use the `trust_cg`
  downstream domain.
- Aligned Lean 4 vector Select specification (`VectorSelectPlan.lean`) with the
  hardened "no scalar-bool-select" policy.
- Tightened binary reader signatures to use explicit `Reader<'_>` lifetimes so
  TrustIr builds cleanly under `rust_2018_idioms` when embedded in the tRust
  compiler.
- Updated Trust/tRust integration documentation to describe workspace/path
  consumption instead of stale Git-revision snippets.
- Moved binary-format MessagePack support out of the public serde feature
  surface and into tests/dev tooling.

### Fixed
- Corrected a typo in `scripts/ci-self-verify.sh` for the
  `trust-ir-conformance` package name.
- Corrected stale binary-header test expectations after the current `.tmbc`
  container format became the canonical binary artifact.
