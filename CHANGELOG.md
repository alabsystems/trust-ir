# Changelog

Notable TrustIr changes are tracked here for Trust integration and release
review.

Entries are grouped under `Unreleased` until a release is cut. Read the tag
list from the release remote rather than from this file; the sentence below has
gone stale twice.

**Correction, 2026-08-30.** The preceding text said the most recent tagged
release was `0.8.0`, that the workspace manifest was `0.11.0`, and that no
`v0.9.0`/`v0.10.0`/`v0.11.0` tag had been pushed. All three statements were
true when written and are false now. Measured against
`git ls-remote --tags https://github.com/alabsystems/trust-ir.git` and the root
`Cargo.toml`: the release tags that exist are `v0.2.0`, `v0.3.0`, `v0.4.0`,
`v0.5.0`, `v0.6.0`, `v0.8.0`, `v0.9.0`, `v0.10.0`, `v0.11.0`, `v0.12.0` and
`v0.13.0`; `v0.13.0` is public `main`'s head; and the workspace manifest is
`0.13.0`. The 0.9.0–0.13.0 windows still have no written-up sections here —
that backlog is real, but it is no longer a missing *tag*.

## Unreleased

### Added

- `Inst::BoxDeref` (wire v74, Inst tag 77): a Box deref that carries a
  `BoxValidityFact` with per-conjunct evidence, its session and its explicit
  non-claims. The one admitted evidence kind is a named premise on a pinned
  root; dominating-check and obligation evidence have a wire spelling and are
  refused wherever they appear. Nine validator rules refuse a missing,
  malformed, out-of-scope or self-contradicted fact;
  `CodegenAdmission::with_require_box_validity_evidence` sets a consumer
  evidence floor that separates roots a session verified nothing behind from
  the others. The pinned roots cover no measured program; a later wire
  version extends them. The instruction is outside the lowering-target subset
  and SemR. See `docs/SPEC_RATIFICATIONS.md` §28.

### Fixed

- AY raw float-to-integer conversion uses truncation toward zero instead of
  nearest-even rounding.
- AY whole-function VCs encode integer-vector unary operations lane by lane,
  preserving carries, bit counts, and lane ordering.
- Lean binary16 now uses the typed arithmetic, cast, bitcast and byte-image
  path, with two-byte layout and exhaustive binary16 image controls.
- Lean executes `FSqrt` through the typed F32/F64 path; the unary operator
  constructor-parity axis now has no remaining drift.
- Lean executes `FFloor`, `FCeil`, and `FTrunc` at F32/F64, retaining
  signed zero and nonfinite values through the existing typed float path.
- Lean execution supports `FAbs` at the modeled F32 and F64 widths, with
  paired bit-pattern controls and explicit operator-parity debt tracking.
- Lean execution retains typed `FnDef` signature and target identities through
  indirect calls, invokes, forwarding and returns. Callable environments and
  the previously excluded indirect unwind cases now have paired Rust/Lean
  controls; raw native code-address conversion remains unsupported.
- SMT identifier printing quotes reserved tokens and every digit-prefixed
  name, including decimal-like names and integers wider than Rust's `u128`.
- SMT-LIB datatype declarations and sort references now use the same symbol
  escaping as formula terms, preserving namespaced and spaced source names in
  datatype, constructor, and selector positions, including recursive fields.

- Content-addressed weight blobs (wire v70; Trust PKG-U13e).
  `Constant::TensorBlob { digest, dims }` (Constant tag 18) names an integer
  tensor by the SHA-256 of its little-endian element bytes; the new module
  blob table `Module.blobs` (a v70 section after the closure layouts, and
  the sole trailing skipped serde field) holds each digest once with its
  bytes, strictly ascending. `Module::intern_blob` (and
  `ModuleBuilder::intern_blob`) stores identical bytes once, and a merge
  unions two tables by digest. A function body's digest reads the digest,
  never the bytes, so replacing a weight moves no body digest while the
  module's `stable_digest` moves. Text `tensor_blob<HEX>[d0, d1]` and module
  rows `blob <HEX> bytes<HEX>`. The validator refuses a row whose bytes do
  not hash to its digest or out of order (`InvalidBlobTable`), a digest no
  row holds (`MissingBlob`), and a misplaced or ill-shaped constant
  (`InvalidTensorBlob`: only the whole value of an `Inst::Const`, rank,
  extents below `2^pointer_bits`, the row's byte count); the codegen gate
  refuses the constant by name. Both engines read it (the reference
  interpreter, and SemR through a kernel-checked SHA-256 on `Nat`), and the
  `lean_schema_parity` Constant axis now judges `TensorBlob` by SemR
  (`lean/semr/CONSTANT_FRAGMENT.tsv`), credited by executed, agreeing runs.
  `docs/SPEC_RATIFICATIONS.md` §27 states the semantics. Float elements
  remain PKG-U15.
- The tensor region's gather and scatter (wire v69; Trust PKG-U13d), in
  coordinate form: one integer coordinate tensor per axis of the tensor
  indexed, each of its own integer element type. `Inst::TensorGather` (Inst
  tag 75) reads a data tensor at the coordinates, its result shaped like
  them; text `tensor_gather TY %data coords [%i, %j]`. `Inst::TensorScatter`
  (tag 76) writes a source tensor at the coordinates over a copy of an
  initial tensor, the row-major-last write winning where a coordinate
  repeats; text `tensor_scatter TY %init, %src coords [%i, %j]`. Coordinate
  tensors whose extents disagree and a coordinate outside its axis are
  undefined behaviour, spelled byte for byte by both engines; the bounds
  precondition is a `BoundsCheck` obligation sited on the instruction, which
  the WS1.8 site table now admits there. The validator refuses each static
  rule by name (`InvalidTensorGather` G1-G3, `InvalidTensorScatter` S1-S3),
  and the codegen gate refuses both. The reference interpreter executes
  them, and SemR states each as a `Step` rule with a decoder arm
  (`lean/semr/FRAGMENT.tsv`). `docs/SPEC_RATIFICATIONS.md` §26 states the
  semantics. Float elements and weight blobs are later parts.
- The tensor region's map, reduce and view (wire v68; Trust PKG-U13c).
  `Inst::TensorMap` (Inst tag 72) applies a scalar body of `BinOp`, `UnOp`,
  `ICmp`, `Select` and integer `Cast` nodes to every coordinate of
  same-shaped tensors and scalars; text `tensor_map TY (%a, ..) { add i32
  $0, $1; .. }`. `Inst::TensorReduce` (tag 73) folds a tensor over strictly
  ascending axes by one of nine integer operators in a pinned row-major
  order; text `tensor_reduce add TY %x axes [1] order row_major`.
  `Inst::TensorView` (tag 74) reads a tensor through an affine and Euclidean
  coordinate function with an optional fill (transpose, slice, pad,
  broadcast, reshape); text `tensor_view TY %x params [..] exprs [..] shape
  [..] index [..] fill %f`. Operand extents that differ, a reduction or view
  result past `usize`, an index expression that overflows or divides by
  zero, an extent that does not fit `usize` and a source coordinate out of
  range with no fill are undefined behaviour, spelled byte for byte by both
  engines. The validator refuses each static rule by name
  (`InvalidTensorMap`, `InvalidTensorReduce`, `InvalidTensorView`), and the
  codegen gate refuses all three. The reference interpreter executes them,
  and SemR states each as a `Step` rule with a decoder arm
  (`lean/semr/FRAGMENT.tsv`). `docs/SPEC_RATIFICATIONS.md` §25 states the
  semantics. Gather, scatter, float elements and weight blobs are later
  parts.
- The integer tensor region, first part (wire v67; Trust PKG-U13a, DG-52
  amended by Trust's TENSOR-REOPEN). `Ty::Tensor(elem, rank)` (Ty tag 41) is
  a tensor of integer elements whose rank is in the type and whose extents
  are runtime values; text `tensor<i32, 2>`. `Inst::TensorContract` (Inst
  tag 71) is XLA `DotGeneral`'s integer contraction over batch and contracted
  axis pairs, wrapping like `Add`/`Mul`; text `tensor_contract TY %l, %r
  batch [..] contract [..]`. Differing paired extents, and a result count at
  or past `2^pointer_bits`, are undefined behaviour. The validator refuses a
  non-integer element (`InvalidTensorType`; a float names PKG-U15) and an
  ill-formed contraction (`InvalidTensorContract`). The codegen gate refuses
  every contraction. The reference interpreter executes it, and SemR states
  it as a `Step` rule with a decoder arm (`lean/semr/FRAGMENT.tsv`, the new
  `lean/semr/TY_FRAGMENT.tsv`). `lean_schema_parity`'s Ty axis now judges
  SemR's type fragment against SemR, with every allowlist still empty.
  `tensor_contraction_equals_loop_nest` has the Clean kernel check
  `SemR.tensor_matmul_eq_loopNest`: an integer matrix multiply equals its
  loop nest for every pointer width, element type and shape. A tensor has
  no memory layout, and map, reduce, views, float elements and weight blobs
  are later parts.
- AY saturating float-to-integer casts explicitly handle NaN, infinity and
  signed/unsigned limits through 128 bits.
- AY encodes `CtPop` as an exact balanced bit-count tree, including 128-bit
  integers, without a new solver primitive or dependency-pin change.
- `lean/semr`: SemR's first memory slice (Trust proven-core RM4c; RM4 stays
  open). Stack slots: `Alloca` (a scalar slot or a counted array of them,
  optionally over-aligned; the producer's `StorageLive`), `Load` and `Store` of
  integers and `Bool`s (plain or volatile, at an optional explicit alignment),
  `GEP` over a scalar element, and `Dealloc` (`StorageDead`), in MiniRust's
  memory shape: allocations of abstract bytes (uninitialized or a byte) at an
  address, live or dead, a pointer its allocation and offset (provenance), an
  integer its little-endian bytes, poison loaded from partly uninitialized
  bytes kept byte for byte. Addresses are the reference interpreter's (a bump
  allocator from 1024), so alignment is decided as there; a `Return` frees
  nothing (level R's `StorageDead` is the explicit `Dealloc`). Use after
  `Dealloc`, a double or interior `Dealloc`, an access out of bounds or
  misaligned, a null pointer, a volatile read of uninitialized bytes, and
  poison inspected are undefined behaviour, each by the interpreter's reason;
  running out of address space is out of memory. A pointer-typed access is
  `unsupported mem.access.ty` (no pointer bytes are stored yet), and a `Bool`
  byte other than 0 or 1 is `unsupported mem.bool_byte` (the interpreter reads
  `true`, MiniRust calls it UB). `Step` gains one rule per memory instruction,
  with the memory checks stated by the relation's own rules (`Accesses`,
  `Reads`, `Allocates`, `Frees`, `Offsets`); `step_sound`/`step_complete`
  still prove the executable is the relation (closures `[propext]`). The
  decoder reads `Load`, `Store`, `Alloca`, `GEP` and `Dealloc` (tags 6–9, 39).
  `SemRMemory.lean` proves the memory laws (load after store, disjoint stores,
  use after `StorageDead` in the relation, out of bounds) and that SemR's
  integer bytes are libspecr's little-endian `Endianness::encode` of
  MiniRust's integer for every type and residue. `lean_exec_differential.rs`:
  0 disagreements over a generated memory corpus of 40,000 runs (10,440 `ok`,
  26,304 `ub` agreeing by reason across 30-odd reasons, 2,736 type errors; 520
  `mem.bool_byte` refusals pinned) and a case per memory rule; the decoder
  differential over memory blobs; ten memory-step mutants and six memory-law
  mutants fail to kernel-check, six shared-helper mutants fail the
  differential. `SemR.lean` elaborates under Clean's own elaborator again
  (360/360; VF5's `picks_complete` had stopped it at 294/298). Review fixes:
  the verdicts are the interpreter's, and `SemR.lean`'s header lists the six
  places MiniRust's differ (allocation is the bump allocator's one pick, where
  MiniRust's `allocate` picks any aligned free address and so calls a
  placement-dependent misalignment UB; a plain integer load of uninitialized
  bytes is poison, not UB; `GEP`'s `inbounds` is ignored; `Return` frees
  nothing; a dead, misaligned pointer is named by its liveness; a `Bool` byte
  other than 0/1 is refused), each pinned through both engines by
  `semr_memory_minirust_divergences_are_pinned`. `SemRMemory.lean` ties the
  memory checks to MiniRust's: `decode_minirust`/`load_decode_minirust`
  (`Endianness::decode`), `isPow2_minirust`/`checkAlign_minirust`/
  `aligned_minirust` (`Align::from_bytes`, `is_aligned`), `check_ptr_eq`/
  `accessAlloc_minirust` (MiniRust's `check_ptr` gives SemR's liveness and
  bounds verdicts) and `alloc_fresh` (an `Alloca`'s address is aligned and past
  every earlier allocation). The SemR differential compares a returned pointer
  by allocation and offset and keeps out of memory apart from out of fuel;
  eight more hand cases (a pointer slot's layout, a count wider than `u64`,
  poison and partial bytes stored at another type, a slot ending at `2^64`,
  the byte of `true`) and six more shared-helper mutants they catch.

- `lean/semr`: SemR v0, the first slice of Trust's proven-core RM4 (one
  semantics of trust-ir level R; RM4 itself stays open). One Lean
  v4.30.0-rc2 file, `SemR.lean`, holds level R's syntax for the
  scalar/control-flow fragment (integer and `Bool` operators at every width,
  the checked trio, compares, select, copy, constants, enum lanes, binding
  frames, unsited asserts, direct calls, branches), a decoder of the binary
  wire image (v38–v62, total by structural recursion), the operator layer on
  `w`-bit residues, and a step semantics with the relation `Exec`. `Exec` is
  the graph of `run`, so `run_sound`, `run_complete` and `exec_det` say `run`
  is total and deterministic, not that it is faithful: faithfulness is the
  differential's claim. No `native_decide`, no `partial def`, closures
  `[propext]`. Its executable `semr_eval` reads the module's binary image and
  is held to the reference interpreter by `lean_exec_differential.rs`'s
  `semr_*` tests under a comparison stricter than W5b's (UB agrees by reason,
  type errors by code), 0 disagreements in each: the W5b generator corpus
  (768 runs) and 2000 more seeds (3,992), 49,456 operator cells over edge
  operands at all twelve integer types (`isize`/`usize` included), 840 runs
  of out-of-range constants, the instruction budget at every value across
  four loops and at `FUEL - 1`, `FUEL`, `FUEL + 1`, sixteen poison and
  type-error paths on unvalidated bodies, every assert kind's message, the
  256/257-variant enum tag boundary, direct calls and the call-depth limit,
  frame discipline, the subset fixtures (80 runs agree; the rest refused by
  name and pinned in `SEMR_FIXTURE_UNSUPPORTED_LEDGER`), and a flipped-operator
  negative control. The decoder is compared with `deserialize_module` module
  for module (`semr_eval --decode` prints the decoded module's summary):
  61,624 truncated, extended and one-byte-changed corpus blobs, 37,593 blobs
  over the version gates (witnesses written at v38, v41, v45, v51 and v52,
  relabelled to every version v37–v63, rewritten to the layout of each later
  version of their epoch, and changed one bit at a time), and UTF-8 faults in
  the string pool; a header, trailer or string fault Rust refuses must be
  `malformed` in SemR, never `unsupported`. 49 SemR mutants (operators,
  pointer widths, constant wrapping, the budget, poison and type-error checks,
  panic messages, the enum tag width, UTF-8, every version gate, refusal
  classes, UB reasons) each fail at least one test. Clean re-checks the file
  through its reference entry (Clean `crates/clean-olean/tests/semr_reference.rs`,
  R164), every declared constant; both repositories pin its SHA-256, and Clean
  compares its copy with this file at the trust-ir revision it pins. The SemR
  scratch files live under the test target's `CARGO_TARGET_TMPDIR`, removed
  on drop.

- `scripts/ci_gates.sh` selects and scales: before any leg runs,
  `scripts/gate_select.py` maps the change since the merge-base with
  `origin/main` (or `--base REV`) through `targo metadata`, each test
  target's module closure, the run-time reads its sources and doc comments
  spell (declared in `scripts/gates/test-reads.tsv` where a test climbs to
  the repository root), Lean imports and the registries, and runs only the
  legs and test targets it reaches; a PASS is cached per leg and target under
  a key over every input, every gate script, the whole toolchain identity and
  the environment (and recorded only while the tree and refs match the plan).
  Any build, toolchain, pin or gate-script change, an unmapped path, an
  unreadable graph or a toolchain or environment other than the last green
  run's here runs everything; so does `--all`. `--base REV` gates the delta
  since a tree the gate already passed.
  `scripts/host_scale.py` sizes every Targo leg's `-j` to the cores and the
  memory available when it starts (`TRUST_IR_TARGO_JOBS` and a positive
  `CARGO_BUILD_JOBS` cap it) and waits for room before it refuses; gate
  13 runs its mutants in parallel slots when memory and load admit; Tippy has
  its own target directory. What a selected leg runs and judges is unchanged.
- Gate 0's Python checks are faster with output-identical rewrites (the
  shared Rust masker skips plain code with one regex search; pure scans are
  memoized). The dev profile also optimizes the Clean kernel's hashing and
  stack-probe dependencies (`ahash`, `hashbrown`, `stacker`, `psm`).
- **Roadmap DG-63 (WS5.5's trust-ir prerequisite): wire v62 — the
  entry-state pointee clause place.** `ClausePlace::ParamPointeeEntry {
  index }` names the value behind a `&T` / `&mut T` parameter at function
  ENTRY: the place a `requires *x > 0` or an `ensures result == old(*x)`
  binds. Before it, such a clause had no place (`Param` is the reference
  itself, which no sort reads; `MutParamExit` is the value at EXIT) and a
  producer had to carry it `trust.contract-opaque@1`. Reserved at
  `98c73c99` as v61 above the open v59 (effect summaries) and v60
  (certificate binding) reservations; moved to v62 when typed signature
  placement took v60 and certificate binding v61 first, so it lands after
  both, in number order.
  - Wire: clause-place tag 10 plus a VInt32 index, read-gated `version >=
    62` (an older header is `InvalidTag(10)`,
    `refuse/blob_param_pointee_place_below_its_version`); selected per module
    only when a binding uses it, so every other module keeps its bytes and
    digests; `RawV38` / `CanonicalV38` refuse with
    `BinaryProjectionError::ParamPointeePlaceRequiresV62`, the new head of
    the highest-wins chain. Text `pointee_entry(N)`; JSON / MessagePack the
    appended externally tagged variant. No digest domain moves: every stable
    preimage spells the place with the same fresh tag byte.
  - Typing: `clause_typing::resolve_clause_place` types it against `T` of a
    `&T` / `&mut T` parameter and refuses everything else by name
    (`ClauseTypingError::ParamPointeeNotReference`): a by-value parameter has
    no pointee, and a raw pointer (even the `*mut T` whose exit value
    `MutParamExit` reads), an untyped `Ptr`, a fat pointer or an `Rc` does
    not say its pointee exists at entry. Admitting raw pointers later is an
    additive relaxation; admitting them now would not be reversible.
  - Validation: legal on every summary role and every obligation kind that
    may bind a parameter (the entry state exists before the call); index
    within the signature; sort a faithful reading of `T`
    (`InvalidFunctionSummary` / `InvalidObligationBinding`,
    `refuse/summary_clause_param_pointee_of_by_value_param`, which takes
    `InvalidFunctionSummary` off `UNCOVERED.tsv`); a spec carrier refuses it
    by name. The Clean-expr grounder's nonneg binding rule reads it like the
    other parameter places, so `(>= x_entry 0)` over a `&u64` grounds.
  - Tests: `crates/trust-ir/src/binary/param_pointee_place_tests.rs`,
    `crates/trust-ir-build/tests/param_pointee_place.rs` (gate 9 registry,
    including the WS5.5 mutation: `*x` bound as `Param { 0 }: BitVec(64)` on
    a `&mut u64` is refused, and the same clause at this place validates),
    the `param_pointee_place` golden (the only one at header 62), and the
    clause-typing and grounder unit tests.
- **WS4.17: synthetic `<shadowed-by-` symbol names are refused (decision
  gate DG-54).** New `ValidationError::SyntheticSymbolName { function, name }`:
  a `Function.name` containing `<shadowed-by-` is refused by
  `validate_module` (module-level, so `validate_changed`'s deep filter cannot
  skip it; the linked walk's per-dependency pass inherits it). `~/trust`'s
  Clean-origin join retired a shadowed Rust declaration by renaming it
  `<name>::<shadowed-by-clean-origin:FuncId(N)>`, which validated as an
  `External` declaration of a symbol no object defines. DECIDE, Recommended
  option adopted: the producer DROPS a retired row (WS5; the format needs no
  dense `FuncId`s) rather than renaming it; the `Linkage::Retired` tombstone
  (a wire field) is declined because no consumer needs it. The rule is a
  substring TRIPWIRE for the one measured spelling, not a closure — its
  rustdoc says so and names its replacement, a symbol-alphabet rule decided
  with WS5 once F-087 moves def-paths out of `Function.name`. It lands only in
  the pin train that carries the WS5 producer change, since it refuses what
  the Clean-origin join mints today. `repair_options` is filled for it. The
  text codec is unchanged: the name still round-trips all four formats
  (`b7.names.text_refuses.clean_shadowed` now also pins the refusal by name).
  Wire impact: none. Tests (gate 9): the retired orphan, a marked definition
  and the incremental lane refused by name, a duplicated synthetic name
  reporting both rules, a near-miss name not refused (mutation control), and
  row `design-0827/no-def-owns-two-rows` ported as
  `design_0827_no_def_owns_two_rows` (the orphan refused, its un-renamed twin
  the attributed collision, the orphan dropped validates). Must-refuse corpus
  row `refuse/function_symbol_synthetic_shadowed`.

- **WS4.17: duplicate link symbols are attributed to their producers
  (cheap half of F-079).** `ValidationError::DuplicateFunctionSymbol`, the one
  "no def owns two rows" rule (`docs/SPEC_RATIFICATIONS.md` §1.1), gains
  `first_producer` / `second_producer` (`Option<Producer>`) and
  `first_display_path` / `second_display_path` (`Option<String>`), copied
  verbatim from the two holders, and its `Display` names them (`#0: producer
  trust, display path "app::program"; #1: producer clean, …`; an unrecorded
  field prints `untagged` / `unrecorded`, never a guess). Diagnostic only: the
  rule still keys on the symbol alone. Downstream code constructing or
  exhaustively destructuring the variant must add the four fields (none of
  trust, clean or trust-cg does at their `main`). Wire impact: none. Tests
  (gate 9, `validation_holes::item_identity_diagnostics`): positive (an honest
  Rust + Clean module), the Rust/Clean collision on `program` refused naming
  both producers and display paths, an unrecorded holder printed as such, and
  a mutation control (a renderer or a raise site dropping the producer tokens
  fails the attribution check). Row
  `spec-surface-0709/03-shared-namespace-duplicates` flips PARTIALLY, ported as
  `spec_surface_0709_03_shared_namespace_duplicates` (no span, no sort
  dimension yet); `spec-surface-0709/17-identity-names-are-views` stays GAP
  (the ItemKey half, WS3's gate).

- Gate 0's enforcement-link gate gains rule E5 (the D4 rung): a
  `(proved-contract)` or `(lean-theorem)` entry must say what each statement
  it cites says, in one closed vocabulary (`VERDICTS`, `NEGATORS` in
  `scripts/check_enforcement_links.py`). A law gets the verdict its `ensures`
  states, read by gate 13 (`Holding.verdicts`; gate 13 now refuses any
  contract outside `ENSURES_SHAPES` before a run). A theorem gets the verdict
  a reader of its Lean source classifies its conclusion as, and the
  identifiers its clause names must occur in its statement, negated exactly
  where the statement negates them; a conclusion outside the reader is held
  to names only, counted apart. Negated phrases (F1), closers that govern
  nothing (F2) and negated citations (F3) are refused. Every
  `(proved-contract)` and `(lean-theorem)` entry of the ratifications and
  TRUST.md is reworded to say its verdicts; no ratified rule changes. Test
  evidence about the wording, never a proof of it.
- Shared nominal I/U8, I/U16 and I/U32 byte-word codec/load/store candidates
  derive their one-, two- or four-byte extent from the exact type, not a
  caller-selected width. The existing four-byte proof composition is reused;
  legacy Four entry points still refuse non-32-bit types after charging.
  Readback names the same final memory and preserves allocation/cursor
  candidates. Independent closed kernel replay remains required. Eight-byte
  construction, evaluator vocabulary, proof limits and native/source authority
  are unchanged.

- Shared positive-remainder bound candidates accept arbitrary Nat dividends
  and a divisor predecessor, deriving the strict bound for its positive
  successor without an answer or result-fit premise. Original and explicitly
  installed total-remainder vocabulary have separate constructors; each
  charges before construction and still requires independent kernel replay.
  The operational evaluator, default vocabulary and checker limits do not
  change.
- Shared byte-machine proof candidates for nominal checked Add/Sub/Mul retain
  ordered value/overflow lanes and the original fetched binding and faults.
  Multiplication can be transported through checked Clean product and residue
  agreement without changing the operational evaluator or checker limits.
  A general value-binding adapter exposes the exact result guard, derives the
  next state only from guard/pre-world candidates, and completes a reached
  binding without adding machine fuel. Candidates require independent closed
  replay; these APIs grant no source-language or native execution authority.

### Changed (breaking)

- **A construction door refuses; it never panics on a value its signature
  admits (D1b, 2026-10-08).** The API break D1a deferred. The rule, its three
  parts and its enforcement are stated once, in the `docs/SPEC_RATIFICATIONS.md`
  section of that name; this entry does not restate them. Migration:

  | Door | Before | After |
  |---|---|---|
  | `ModuleBuilder::build`, `AYBatchBuilder::build` | `Module` | `Result<Module, BuildError>`: the first fault any builder door recorded |
  | `ModuleBuilder::peek_next_func_id` | `FuncId` (panicked once exhausted) | `Result<FuncId, IdSpaceExhausted>` |
  | `Module::add_function` | `()` (panicked) | deleted: `try_add_function` (`Result<(), AddFunctionError>`) is the one spelling |
  | `Module::{add_func_type, intern_func_type, add_closure_type, add_type, intern_import, add_struct_def, add_enum_def, allocate_struct_id, allocate_enum_id, join_preds}` | the id | `Result<id, IdSpaceExhausted>`, table unchanged on `Err` |
  | `Module::intern_file` | `u32` | `Result<u32, IdSpaceExhausted>` |
  | `Module::{intern_universe, intern_pred, intern_in_universe}` | `Option<id>` | `Result<Option<id>, IdSpaceExhausted>`; `None` means only "not canonicalizable" |
  | `serialize_module`, `ModuleBinaryPlan::to_vec`, `ProjectedModuleBinaryPlan::to_vec` | `Vec<u8>` (panicked) | `Result<Vec<u8>, BinaryProjectionError>`; a refused image is never materialized |
  | `ModuleBinaryPlan::write_to`, `ProjectedModuleBinaryPlan::write_to` | panicked on a refusal | `io::ErrorKind::InvalidData` carrying the `BinaryProjectionError`, after its one streaming pass (the partial output is not an image; discard it on `Err`) |
  | `ModuleBuilder::{sign, sign_with_lineage, try_peek_next_func_id}`, `FunctionBuilder::{try_build, try_create_block}`, D1a's `Module::{try_allocate_struct_id, try_allocate_enum_id, try_add_struct_def, try_add_enum_def, try_join_preds}` | | deleted (one spelling each; `sign` had no caller and its doc claimed a verified bundle) |
  | `BuildError` (`#[non_exhaustive]`) | `ReservationActive`, `ObligationIdSpaceExhausted(_)` | `IdSpaceExhausted { space, function }`, `NoCurrentBlock { function, emitted }`, `UnknownBlock { function, block }`, `MixedReservation { function }`, `ReservationAbandoned { function }`, `AlreadyDefined`, `DeclarationChanged` |

  Unchanged: every emitter, `create_block`, `add_block_param`,
  `FunctionBuilder::build` (still `FuncId`) and the builder's own table doors
  keep their signatures and RECORD a fault instead of panicking (a placeholder
  id, `u32::MAX` of its space, is returned and never reaches a `Module`);
  `add_struct` / `add_enum` / `add_record` cannot fail; the identity entries
  (`stable_digest`, `encoded_len`, the SHA-256 entries) stay infallible. The
  `FunctionBuilder` contract's "misuse panics" choice is reversed.
  Inside trust-ir: the text parser maps a table refusal into its `ParseError`;
  `trust_ir_build::merge` into `MergeError::IdSpaceExhausted`; template
  instantiation into `InstantiateError::AnswerConflict` (its doc now names a
  full table) and the skolem host's `HostRefusal`; the CLI's
  `convert --to bin` / `digest` / `run` into their existing refusals; the
  native bundle's binary codec into `BinaryError::Unencodable`. The
  conformance fixture builders compiled into the library stay total:
  `template_fixtures::*` return `Result<Template, IdSpaceExhausted>`,
  `corpus()` a `Result`, `instances()` `Result<_, TemplateFixtureError>`, and
  the must-refuse helpers `build_assert_kind_subject` /
  `build_panic_site_subject` `Result<Module, FixtureError>`. Test call sites
  take `.expect("<door>: test fixture")`; no production site does.
  Rung: test (`no_builder_door_panics_on_a_fault` and its siblings), type (the
  one `Result` exit; the deleted names, held by a `compile_fail` doctest) and a
  gate-0 lint (builder.rs and the plain `Module` door blocks deny panic,
  unwrap, expect, indexing, unreachable, todo, unimplemented, arithmetic side
  effects and truncating casts outside tests; a canary run turned
  `workspace-clippy` red on each of an inserted `panic!`, `+=` and `as u32`).
  Nothing is proved. Measured 2026-10-08/09: gate 15 (opt-in, `--crates
  raft-fixture,supremacy-fixture`), before (origin/main `c2ddccaa`) and after,
  both crates JUDGED with identical rows (raft-fixture 4 proved / 21 unknown /
  5 design requirement over 12 functions; supremacy-fixture 5 / 19 / 1 over
  16), so the benchmarks' `?` changed no verdict; the
  `serialize_refuses_every_construct_the_writer_cannot_encode` test's 4 GiB
  count module peaks at 8.1 MB RSS (`/usr/bin/time -l`): the blob entry
  refuses before it allocates. A census, not a verdict.

### Added

- **A construct or count with no wire image is refused by the writer's own
  arm, at every trust-ir entry point (D1a, 2026-10-08).** The rule, its four
  parts and its enforcement are stated once, in the `docs/SPEC_RATIFICATIONS.md`
  section of that name; this entry does not restate them. What changed:
  - `trust-ir convert --to bin`, `trust-ir validate --link` (a `Ty::Error` on
    the dependency or on the root), `trust-ir run` (an input with an import
    row) and the native bundle's `validate` exited 101 / panicked on a JSON
    module whose type table spells `"Error"`: all four hand-written
    pre-checks omitted the producer-internal `Ty::Error` (the CLI digest
    caught the writer's panic instead). Each is now a named
    refusal (exit 1, `ModuleHasNoWireIdentity` /
    `TrustIrModuleHasNoWireIdentity` / `BinaryProjectionError::
    ProducerInternalType`), because the one pre-check,
    `Module::wire_image_refusal` (new, with `wire_image_refusals`), IS the
    writer run over a counting check sink. `ProjectedModuleBinaryPlan::
    try_new`, `wire_identity_blocker`, the bundle and the CLI call it; the
    hand-written chains, and the CLI digest's `catch_unwind` and panic-hook
    swap, are deleted.
  - The v60 typed signature ABI joins the writer's arms: its `func_types`
    arm refuses a descriptor by `SignatureAbi::validate_encoding_limits`
    (the predicate its reader and the two v60 pre-checks used) instead of
    asserting only the byte limit, which let `serialize_module` and
    `stable_digest` write a descriptor past the node budget that
    `deserialize_module` refuses. It ranks after the four pinned carriers and
    ahead of `Ty::Error` (`try_new` had ranked it first, `wire_identity_blocker`
    last). `serialize_template` (and so `Template::digest`) runs the same arms
    over the check sink after its structural rules, so a template carrying
    `TyG::Error` (no structural rule names it), or any other construct or
    count the writer refuses, is `TemplateUnsupported`, never a panic inside
    its `Result`.
  - `BinarySink` gains `refuse` and `note_over_limit`, with no default
    bodies. `len_u32` is deleted: `write_count` spells every count as the
    `write_v64` varint of its exact value (byte-identical up to `u32::MAX`;
    every golden and pinned digest unchanged) and reports a count past it,
    so `encoded_len` and the digests are total over counts while blobs still
    refuse. String-pool ids are `u64`. `BinaryProjectionError` gains
    `ConstructAheadOfWireTag`, `ProducerInternalType` and
    `CountExceedsFormat` (additive; it was never matched exhaustively by a
    consumer), and the crate root re-exports it with `WireNodeSite`.
  - The table-id rule is stated once: `value::table_index` / `table_id`.
    The text parser's five `len() as u32` id checks, the validator's scope
    diagnostics, `intern_file`'s lookup, `first_inlined_scope_chain`, the
    inline-cycle validator, `declare_handle_runtime_roles` and the CLI
    linker use it or the exact enumeration `(0..=u32::MAX).zip(..)`; the
    canonical renumbering hands out ids from `0..=u32::MAX` instead of a
    `next += 1` counter.
  - Additive total twins on `Module`: `try_allocate_struct_id`,
    `try_allocate_enum_id`, `try_add_struct_def`, `try_add_enum_def`
    (refused at a decoded id `u32::MAX` by `FreshIds::after`, table
    unchanged) and `try_join_preds`; `join_preds` now weakens a
    non-canonical join to `Top` (its own fallback) instead of panicking on
    its invariant `expect`. The panicking spellings stayed until the API
    break (D1b, above), which retired them and the twins.
  - Cost: the pre-check is one writer walk with no hashing and no payload
    read. Measured 2026-10-08 on a synthetic module (1,000 functions of 4
    blocks, 1,004,000 nodes, 27.0 MB encoded; no trust-cg corpus module was
    on disk), release build, median of 5, machine load 30-36:
    `wire_image_refusal` 48.6 ms, `stable_digest` 122.7 ms,
    `serialize_module` 59.1 ms. The hand-written checks it replaced were
    cheap scans (not timed), so a digest-keyed entry point now walks about
    40 % more than before. The two tests over a 4 GiB zero-filled payload
    peak at 6.2-6.7 MB RSS (`/usr/bin/time -l`): no sink reads the payload.
  - Rung: test, type (the hooks without defaults) and a gate-0 lint
    (`value.rs`, `canonicalize.rs`, `validate/inline_cycles.rs` deny panic,
    unwrap, expect, indexing, arithmetic side effects and truncating casts
    outside tests). Nothing is proved; gate 15 (opt-in) was not run.
- **One bit-vector statement of integer compare (2026-09-30).** New
  always-on module `trust_ir::bv_meaning`: `icmp_holds` (one SMT-LIB QF_BV
  operator per `ICmpOp`), `vector_icmp` / `vector_lane` (lane 0 least
  significant), `concat_lanes`, generic over `BvCompare` / `BvVector`, with the
  executable instance `Concrete`. Beside the x86-64 cell reader:
  `physical_mask_lane` (the published physical mask lane, `ite(holds, 2^w-1,
  0)`), `chc_x86_vector_icmp_spec` (THE spec side of an x86-64
  vector-compare cell, `None` exactly where `chc_x86_vector_icmp_cell_status`
  is) and `chc_x86_vector_icmp_lowering_row` (an available cell's published
  row, the one list of its instruction models), all on one shared lookup and
  re-exported at the crate root. Ratified in `docs/SPEC_RATIFICATIONS.md`
  ("Integer compare has one bit-vector statement"). The `<16 x i8>` and
  `<8 x i16>` `icmp.ne` rows now publish `pcmpeqb;pcmpeqd;pxor` /
  `pcmpeqw;pcmpeqd;pxor` (the backend's all-ones is one `pcmpeqd`); the chc_x86
  manifest digest moves with them. The Lean model's executable integer
  vector shapes are stated once (`Ty.executableIntLane?`, read by the four
  shape checks) and cover every lane type of the x86-64 cells, signed and
  unsigned: an `InsertElement` into `<16 x i8>` / `<8 x i16>` was a
  `type_error`, and every unsigned-lane cell (`<16 x u8>` … `<2 x u64>`) was
  `unsupported vector_shape` (1580 of 3160 runs of the cross-engine cell test,
  which now derives each cell's lane types from the validator).
- **A Rust reference carries no permission instruction (adopted
  2026-10-08; SPEC section of that name).** `Borrow`, `BorrowMut` and
  `EndBorrow` drive an allocation-keyed permission machine, not Rust's
  reference semantics, and no Rust producer has a source for `EndBorrow`, so a
  borrow a Rust producer emitted stayed live forever and made every later free
  of its allocation undefined behaviour. A Rust producer spells every
  reference as the place's address value or a `Copy` of it; the THIR producer
  already does, and the Trust MIR bridge's respelling is the Trust half of
  this change, not yet on Trust's main. One predicate, `InstShape::uses_borrow_permissions`
  (`Inst::uses_borrow_permissions` delegates; proved per cell by gate 13,
  `laws::borrow_permission_*`, under a negated-table mutant and a neighbour
  mutant swapping `EndBorrow` for `Copy`), is read by two checks keyed on claim
  metadata: `validate_module` refuses a permission instruction in a function
  stamped `Producer::TRust` (`ValidationError::RustReferenceAsPermissionBorrow`;
  must-refuse row `refuse/rust_reference_as_permission_borrow`), and
  `NativeVerificationBundle::validate` refuses one in a `Producer::TRust`
  function (`NativeVerificationBundleError::RustReferenceAsPermissionBorrow`),
  which minting a source-generation authority inherits. The section's second
  bundle key, a `RustMir` input whatever the stamp, is applied only after the
  bridge's respelling and trust-mc's alias change are on their mains (the
  design's landing order: trust-mc's attack fixtures mint from RustMir
  bundles that carry `Borrow`). Lean gains three
  ∀-theorems in `Proofs/BorrowMemoryProps.lean`
  (`semBorrow_ub_of_uniqueBorrow`, `semBorrowMut_ub_of_not_owned`,
  `stepInst_copy_preserves_memory_and_permissions`), and the engine
  differential a decided table of the Copy-spelled Rust shapes
  (`rust_reference_spelling_agrees_across_engines`) plus two ledger rows no
  `EndBorrow` placement repairs. No wire, interpreter or Lean semantics
  change; clause 4 of the live-borrow section stays undecided. Consumers:
  trust-cg and ty refuse the new corpus row at their next pin move; a consumer
  that builds `Producer::TRust` fixtures with borrows respells them (this
  repository's batteries did: `rust_bump`, `spill_local`, the WS3.7 spill
  fixtures, which are now unstamped).

- **Typed effect summaries and world epochs — wire v59 (roadmap WS1.14,
  F-013).** `FunctionSummary.effects: Option<EffectSummary>` is the frame half
  of a contract: `reads` / `writes` as an `EffectSet` (`Nothing` |
  `Places([ParamPointee { index } | Global(id)])` | `Everything`) plus the
  `allocates` / `frees` / `may_unwind` / `io` flags. `None` is UNRECORDED (a
  caller havocs), never "pure". `ClausePlace::WorldPre` / `WorldPost` (clause
  places 8 / 9) are the entry and exit epochs of the ambient world;
  `WorldPost` is legal only on an ensures clause, and the legacy un-epoched
  `World` is now UNBINDABLE on a `proved` summary (the WS1.2 rule) — the b2
  battery's proved fixtures re-spell their world bindings accordingly. Wire:
  a presence byte appended to every summary record (then two `EffectSet`s and
  four strict bool bytes), new tag spaces `EffectSet` (0..=2) and
  `EffectPlace` (0..=1), a `Places` list that is not the ONE spelling of its
  set (empty, out of order, duplicated) refused on read by the binary, JSON
  and MessagePack decoders alike (SPEC_RATIFICATIONS §3, as `U128` / `Splat`),
  all read-gated `version >= 59` and writer-selected
  only when used, so a module using neither keeps its bytes; the v38
  projections refuse (`EffectSummaryRequiresV59`). `obligation_content_digest`
  moves to `trust_ir.obligation.digest.v8` (the effect frame changes what a
  contract means; v7 is burned). Validator (`trust-ir-build`): a DEFINED
  body is checked against its summary by a sound, syntactic trace
  (`validate::effects`: GEP / PtrData / Copy / Select / PtrToPtr / borrow to a
  parameter, a `GlobalAddr` or a local `Alloca`; anything else forces
  `Everything`; a call maps the callee's admissible summary through its
  arguments; an unsummarized, interposable (`Weak` / `LinkOnce` /
  `ExternalWeak`) or indirect call is the top summary) and an
  uncovered effect is the new `EffectSummaryViolated { function, effect,
  block, inst }`; the summary's shape (canonical sets, in-range parameters,
  declared globals) is `InvalidFunctionSummary`. A body-less declaration's
  effects are admissible at a call only when `validate_linked_module`
  authenticated its `backed_by`, whose restatement now requires a recorded
  local `effects` to equal the far summary's exactly and to name no module
  global; otherwise a caller treats them as `None`. Tests:
  `trust-ir/tests/effect_summaries.rs` (codecs, selection, both read gates,
  strict flags, digests), `trust-ir-build/tests/effect_summary_validation.rs`
  (gate 9: positives, the six named twins plus the review's (entry-block
  re-entry, a pointer loaded out of a parameter, a parameter-swapping
  self-call, `Invoke` / `Resume` and a callee's flags, a dependency whose body
  breaks its own effects, `WorldPost` on a `decreases` measure), the
  store-removal mutation control, the linked declaration rule, and the ported rows
  `goal-g1-g8/g6-state-epochs`, `goal-g1-g8/g6-effect-summaries`,
  `producer-clean/io-and-effects`), and the `effect_summaries` conformance
  golden (gate 8). Ratchet row `b2.gap.no_effect_summary_or_state_epoch_field`
  flips GAP -> PASS. Rebased onto main (2026-10-07): text carries the effect
  summary as the `; #effects:` line closing the WS4.4 summary block and the
  epochs as `world_pre` / `world_post`, refusing a second spelling of a place
  set (also a `FunctionSummary` text loss); the effect trace classifies the
  instructions main gained meanwhile — a sited `Assert` / `AssertInvoke`
  contributes its panic entry's admissible summary mapped through `(kind
  operands.., location)` (`AssertInvoke` also `may_unwind`), `CallCannotUnwind`
  maps like `Call` (callee flags still propagated), and
  `CallIndirectCannotUnwind` / `InvokeIndirect` / `DropInvoke` are the top
  summary — and reads branch targets from `Inst::successor_edges`; a module
  obligation may bind `WorldPre` on any kind and `WorldPost` only on a
  `Postcondition` / `GiveBackRefinement`, and neither when unscoped
  (`InvalidObligationBinding`). Over WS4.11 (the library module merge,
  `merge_into`) the effect summary travels with its summary: carried under
  `carry_proof_state` and stripped with it otherwise (`None`, nothing
  invented); a `ParamPointee` place is carried as is, a `Global` place follows
  the global remap and the mapped `Places` list is re-sorted into its one
  spelling; a non-canonical `src` set is `MergeError::Malformed`, never
  repaired; and two declarations differing only in effects conflict on
  `summary` under `RequireIdentical`, the earlier one's effects standing under
  `FirstStands`. Tests: the `ws1_14_*` rows of
  `trust-ir-build/tests/module_merge.rs`, whose pairwise corpus now merges
  `build_effect_summaries` against every module fixture.

- **WS3.9 / WS3.13: wire v58 — the nominal type-origin key and declared
  closure layouts (F-128 plan-of-record half; F-055).** Two additive
  features share the number reserved at `68602783` (taken to the lowest open
  number, v50, by takeover `ea68b453`; moved back to v51 by takeover
  `4a143d18` when the constant-size uniform array took v50 and landed first;
  moved to v53 when the INST wire batch (v51) and the assert panic kind (v52)
  took the lowest open numbers by takeover and landed first; moved to v58
  when the call-unwind boundary (v53), the panic site (v54), drop glue (v55),
  the unwind twins (v56) and the generic-template floor (v57) did the same;
  kept for this lane by ruling WA-1, 2026-10-02), and both are selected only
  when USED, so a module carrying neither keeps its v38–v57 bytes.
  *Nominal identity.* `StructDef.origin` / `EnumDef.origin` carry an optional
  `TypeOrigin` — `Rust { stable_crate_id, def_path_hash, args_digest }` (the
  concrete `GenericArgs` digested, so one def path at two instantiations is
  two keys: the IR stays monomorphic) or `Clean { decl, env_digest }` — that
  names the SOURCE ENTITY a definition is the image of; a Rust enum that
  MIRRORS a Clean inductive carries the CLEAN key. The key never admits: the
  cross-module comparator (`ty_structurally_eq_across`, now backed by
  `ty_equivalence_across` → `TyEquivalence`) SPLITS two structurally identical
  definitions with different keys (they used to compare equal) and reports
  one key over two shapes as a named `TypeOriginConflict`; an absent key
  compares structurally exactly as before. `validate_module` refuses a key
  claimed twice in one module (the in-module form of
  `ValidationError::TypeOriginConflict`, both module fields `None`, the
  struct and enum tables scanned as one key space; must-refuse corpus row
  `refuse/type_origin_claimed_twice`); `validate_linked_module` gains rule
  L12, refusing a one-key-two-shapes contradiction anywhere in the linked
  CLOSURE — root against dependency, two siblings, or two modules that meet
  only through a transitive import — on the root, with both modules named
  (the same variant, both module fields `Some`). One variant names both
  forms because the KIND 4 must-refuse exhaustiveness gate admits a new
  variant only with a corpus row, and the linked form needs a root plus a
  dependency no single wire artifact carries (the roadmap spelled the
  in-module form `DuplicateTypeOrigin`; the fold follows 8958b24a). `trust-ir-diff`
  fingerprints the key on both definition tables, so a re-keyed, keyed or
  un-keyed definition is a reported change.
  `Module::add_struct_def` / `add_enum_def` no longer dedupe across different
  keys. All four formats carry the key (text: the ` origin=rust(..)` /
  ` origin=clean(..)` clause before `id=N`; JSON/MessagePack: the definition's
  sole trailing skipped field); the `TypeOrigin` tag space (0 `Rust`, 1
  `Clean`) joins the wire census. *Closure layouts.* `Module.closure_layouts`
  (`ClosureLayoutDescriptor { closure, size, align, capture_offsets }`) is a
  trailing section after the v55 drop-glue table with exactly the v42 tuple
  table's
  coherence rules (one row per closure type, resolvable type, alignment,
  containment, non-overlap; a self-capturing closure fails closed by name),
  checked on decode, in `validate_module`
  (`ValidationError::TupleLayoutInconsistent`, its reason prefixed
  `Module.closure_layouts: ` — the closure table shares the tuple table's
  rules, and a variant of its own could carry no must-refuse corpus row,
  because the binary reader refuses every incoherent table itself) and by
  `trust-ir-diff`;
  `TyLayoutKind::Closure` (stable layout tag 10) and the `closure_layouts`
  diff row follow — the diff row keys a frame by the closure type's
  STRUCTURAL spelling, never its `ClosureTyId`, so renumbering closure types
  is no change and moving a frame between two closure types is one.
  `lowering-target-subset.md` §G18-2(b) (the wire half of the landed WS3.13
  ratification: application is BY VALUE, captures spread as leading
  arguments, a stateful `Fn`/`FnMut` uses the explicit environment-aggregate
  spelling) lifts the codegen refusal for `CallIndirect` over a `Ty::Closure`
  callee (and its twins `CallIndirectCannotUnwind` / `InvokeIndirect`) ONLY
  for a closure type whose declared frame is coherent — an absent
  or incoherent row keeps the refusal unchanged — and KEEPS the laundering
  refusal: a declared frame gives the closure a size, so the layout evidence
  now refuses every layout-sensitive cast that names a closure BY VALUE on
  either side (directly or inside an aggregate no pointer breaks) before any
  width is compared (`LayoutError::ClosureCast`, surfaced as
  `CastLayoutUnsupported`; a pointer or reference to a closure is unaffected),
  where a pure same-size rule would have admitted `Bitcast closure -> Ptr`.
  `closure_layouts` is APPENDED after amendment D's `drop_glue` table and is
  now `Module`'s sole trailing skipped serde field, so `drop_glue` is always
  emitted (the v41 one-trailing-skip rule; `[]` when empty), exactly as
  amendment D flipped `completeness` before it: every JSON/MessagePack
  module golden whose table is empty — the must-refuse corpus's module rows
  included — gained one `"drop_glue": []` entry (MessagePack: the array
  count + 1 and a trailing `0x90`), regenerated with the fixture-update path;
  no binary or text golden moved. Appending rather than inserting keeps a
  pre-v58 positional MessagePack blob that carries a drop-glue row
  decodable. Two new v58 goldens, `nominal_type_origin` and
  `closure_layout`. Explicit v38 projections refuse both features with
  `NominalIdentityRequiresV58`, now the head of the highest-wins chain.
  Declared closure frames lay out through main's `LayoutTable` as a fifth
  nominal node (`Node::Closure`), held to the recursion it replaced by the
  layout differential, whose oracle carries the closure arm. Ratchet
  row `b6.closure.no_layout_not_lowerable` flips GAP → PASS with its declared
  twin `b6.closure.declared_layout_is_checked`. The Lean mirror of
  `StructDef` carries neither `repr` nor `origin` (non-semantic metadata), so
  gate 1 is unchanged. The trust-cg half of F-055 stays WS7; producers stamp
  the key in WS5/WS6.
  Review pinned the rule under shapes the first cut did not: a split INSIDE
  a shared key (two `Outer`s under one key holding differently keyed
  `Inner`s) is a conflict on the outer key, never `Equal` because the bytes
  agree; every contradicted key of a pair is reported, the innermost naming
  the single-comparison verdict; an unkeyed nested definition under a shared
  key still compares structurally; the key reaches through a `Ty::Func`
  signature (the import path); a diamond reports a shared leaf's conflict
  exactly once; on the wire a forged presence byte or `TypeOrigin` tag is
  `InvalidTag`, a presence byte flipped to "absent" in place cannot decode
  to the unkeyed twin, the explicit v38 projections refuse a key and a
  closure frame by name, awkward Clean names (quotes, backslash, newline,
  non-ASCII) and extreme `Rust` key bytes survive all four formats, a
  writer-emitted closure row naming no closure type (or with no target to
  size it) is refused by the binary reader and by `validate_module`, and a
  closure captured by value inside another is sized by its own declared row
  (`nominal_type_origin`, `closure_layout`, the new gate-8
  `nominal_identity_wire`). Review also RESTORED the pre-v58 codegen refusal
  text verbatim for a closure with no layout row (the WS3.13 rule the branch
  had reworded, and the gate-9 `closure_application_by_value` test that pins
  it), appending one sentence that names the missing row. Subset structural
  condition 4 — closure APPLICATION (`CallIndirect` over a `Ty::Closure`
  callee) is outside the lowering-target subset, the Lean executable model
  having no closure-application rule — is now ENFORCED by both checkers
  (`trust_ir::bridge::CLOSURE_APPLICATION_VIOLATION`, on the callee's type
  from the function's value typing, and the conformance mirror), with a
  `bridge_subset_agreement` row and its function-pointer mutation control. It
  had read that way since G18-2 but neither checker enforced it, because the
  codegen refusal was the construct's only gate; the `closure_layout` golden
  is the first subset fixture to apply a closure, and the Lean differential
  refused it as a type error. It joins the subset exemption table (subset v4
  addendum, no version bump). The lift reads the application's APPARENT
  signature (the edge's `sig` and the closure type's `func`) as saying nothing
  about the lowered call beyond the caller's arguments, since the captures are
  spread IN FRONT of them; `closure_lift_admits_apparent_signature`
  destructures `FuncTy` exhaustively, so a future field that records a fact
  about the signature's own parameter list (a typed callable ABI, a hidden
  parameter, a convention) does not compile until its author decides — fail
  closed: not while the field records a claim — whether a declared frame still
  lifts the refusal.
- **WS2.26 (F-044, DG-08): concurrency claims never count toward a
  `Discharged` obligation, enforced by test.** The ratified
  sequentially consistent, single-threaded projection (`TRUST.md` item 8,
  ub-numerics policy §5) is now held by `validation_holes`
  (`ws2_26_concurrency_claims_discharge_nothing`, gate 9): a positive control
  (the claims beside a kernel-certified callee row and its admitted
  restatement validate, replayed authority unchanged), negative twins
  (`TemporalSafety` / `Ownership` rows sited on the `DataRaceFree` +
  `AtomicOrdering` atomic store without a certificate, and the restatement
  without its certificate, are `DischargedWithoutCertificate`; a `ProofRef`
  round trip is `ProofRefUnresolved`), mutation controls (stripping every
  claim changes no entry point's verdict; `Discharged` -> `Pending` removes
  exactly the named refusals), and the synthesis check (`DataRaceFree` mints
  one `Pending` row, `AtomicOrdering` none). No validator change.
  Review twins in the same module: forged non-kernel evidence (SMT, Lean,
  Kani, `Trusted`, translation-validation) on the concurrency rows stays
  `DischargedWithoutCertificate`; `Certified` rows without `CleanCic` are
  `CertifiedWithoutCleanCic`; unsited and unscoped rows, rows sited on a
  claim-carrying `AtomicRMW` / `CmpXchg`, and a local inheritance from a
  claim-only callee row are refused by name; builder-door claims mint no
  `Discharged` row; and a dependency carrying claim-only `Discharged` rows
  fails the linked walk as `ImportedModuleInvalid` — every verdict identical
  with the claims stripped.

- **A spawned thread starts at the std code around its callable
  (`FunctionClass::Seed::child`, `NodeOrigin::TrustIrThreadStart`; Trust
  design 2026-10-02, "C1", N-4; 2026-10-03).** std runs code on a new thread
  around the callable it was given: inherited spawn hooks before it; the
  result store, the result's drop glue and the payload's drop slot after it;
  thread-local destructors. That code runs beside the parent and is user code
  in general, so a thread model must hold it. `FunctionClass::Seed` gains
  `child: Option<PrimitiveSummary>`, the checked summary of that code. On the
  trust-ir lane the thread a seed starts now begins at one node per seed
  (`SpawnSite::entry`), which RUNs the spawned callable and carries `child`'s
  facts exactly as a primitive's. So `thread_closure(site.entry)` holds that
  code, and is modelable only when it is. Without a summary the node is
  opaque: the code is not enumerated and the thread is never modelable. The
  node is local, as a primitive is on this lane, and joins no definition.
  Nothing reaches it, so no caller's verdict reads it; its facts are
  otherwise ordinary ones, and a sink among them leaves the pools unclosed as
  anywhere else. No classifier returns a seed with a summary yet, and a seed
  without one adds no fact but the node's RUN of its callable, so no census
  verdict moves. `SpawnSite::entry` was the callable itself on this lane.
  Tested, not proved: the entry is one thread-start node per seed, with and
  without a summary, and every function's verdict is the same either way; a
  thread whose child side has a spawning hook, an unresolved glue type, an
  open principal, or a spawning hook handed to foreign code is not
  modelable while its callable alone is; a child callback that spawns is a
  spawn site and stays modelable.
- **Thread primitives as checked summaries in the reachability engine
  (`FunctionClass::Primitive`, `NodeBody::Primitive`; Trust design 2026-10-02,
  "C1", §3.2; 2026-10-02).** A classifier can now call a function a
  primitive (`thread::scope`, the two `join`s) and give its
  `PrimitiveSummary`. The summary lists the callbacks the primitive runs on
  the calling thread, the runtime services it uses, the pool INVOKEs it makes
  (`PrimitiveInvoke`, such as the drop slot of `dyn Any + Send`) and the types
  whose drop glue it runs. The trust-ir walk does not walk the primitive's
  body. It turns each item into the fact the instruction doing it adds in a
  walked body (a RUN edge, a classified service, a pool INVOKE, the glue's RUN
  or UNKNOWN(`ImplicitDestructor`) via drop), at the definition site and
  through the same service path as the body walk. The solver treats a
  `Primitive` node exactly as a walked node of the same locality: it is not
  terminal, it is never the base of a SPAWNS claim, and it invokes only the
  keys its summary lists. The trust-ir walk makes it `Local`, as the walked
  body it stands for would be on that lane, so an invoke whose pool holds
  external code is charged by rule H with what the invoke carries
  (`PrimitiveInvoke::carried`). `ThreadClosure::modelable` admits a
  primitive beside walked code and seeds; a closure that reaches an open or
  unclosed pool through a primitive's invoke still ends at an UNKNOWN sink
  and is not modelable. No classifier returns the new class yet (trust-mc's
  returns `Walk` for everything), so no census verdict moves. R9, the
  premise that a primitive's own code starts no thread and leaves only through
  its summary's facts, is the classifier's to pin. For Trust: the MIR
  adapter's exhaustive match on `NodeBody`
  (`crates/trust-mir-extract/src/concurrency_effects.rs`) needs an arm for
  `Primitive` when the gitlink moves. Tested, not proved: each summary item,
  and all of them together, give the same verdicts, witnesses, spawn sites and
  modelable closure as a walked twin body, an invoke that hands a callable to
  foreign code included; a spawn fact into a primitive, or an edge out of a
  seed into one, is a defect; T-ir3's modelable cases are covered; and random
  graphs now include primitive nodes, so the brute-force, certificate and
  tamper tests cover them.
- **Pointer roots, a public analysis (`analysis::pointer_roots`; Trust
  design 2026-10-02, "C1", §3.3; 2026-10-02).** The root analysis Trust's
  effect-conservation census (D28) computed privately (`ir_block_arg_sources`
  and `ir_roots`) is now a trust-ir analysis, so that census and ty's thread
  model read one. Each value's root is `Arg(i)`, `Global(G)` (the globals it
  may address), `Local(A)` (the function's own allocations it may address) or
  `Indirect`: a least fixpoint over every stored block, recomputed when an
  input changes. Each allocation (`Alloca`, `HeapAlloc`) carries an escape bit
  by mem2reg's rule for a scalar alloca (used only as the address of a `Load`
  or a `Store`, with no exception for a call argument), and
  `PointerRoots::is_private` is the thread model's `Priv` class. The roots are claimed for a function the
  validator accepts (unique block ids and definitions, every edge passing its
  target's parameter count, uses dominated); the analysis is total on any
  function, and an edge whose argument count is not its target's parameter
  count (an unwind edge into a landing pad with parameters, say) makes those
  parameters `Indirect`. On the census's shapes the projection onto its four
  classes is the census's root. Elsewhere four corrections apply, each at a
  place the census was optimistic: the normal edges of `AssertInvoke`,
  `DropInvoke` and `InvokeIndirect` bind their arguments, an edge into the
  entry joins into its parameters, and an undefined operand or an
  instruction's later result is `Indirect` instead of being joined as nothing.
  Trust's producer emits none of those shapes today. On functions the
  validator rejects the module docs list three more differences, not all in
  one direction: an edge with the wrong argument count, a repeated
  entry-parameter id, and a repeated block id. Nothing calls the analysis
  yet; the census moves onto it next. Tested, not proved: the tests check
  parity with a verbatim copy of the census's code on representative
  functions and on 1500 random ones, and every full root, its sets included,
  against an oracle written apart (the census's round-robin fixpoint,
  set-valued, with its own join, corrected) on those and on 1500 random
  functions outside the census's shapes. The escape bit is checked against
  mem2reg's own promotion decision on every use shape of a scalar alloca;
  mem2reg's fixed-count array subset promotes some allocations this rule
  calls escaping, which only makes fewer private.
- **Gate 16, `verified-ready` (`scripts/verified_ready.py`,
  `scripts/gates/verified-ready.tsv`; 2026-10-02).** The workspace targets
  whose advisory verified run is already clean — trust-ir-laws lib,
  trust-ir-fmt bins, trust-ir-diff bins — are now held clean by
  `scripts/ci_gates.sh`: each run must be JUDGED (gate 15's reader), carry no
  refutation and no `failed` row, and meet a floor of PROVED rows (8, 1, 4:
  about 80% of the measured 10, 2, 5). Unknown rows never count. Additive:
  gates 13 and 15 and `publish/config.sh` are unchanged. The trust-ir-diff row
  became clean when `parse_args` stopped stepping its index with a panicking
  `+=`; trust-ir-conformance's crate-side refuted rows (an `i128` widening
  sum, an unchecked `languages[0]`, two line/length arithmetic panics) are
  fixed, and its remaining six are the ledgered shape-c Box-allocation rows.
- **Amendment D, Part 2: unwinding is an exit (wire v56,
  `docs/SPEC_RATIFICATIONS.md` §21; 2026-10-02).** Rung: TEST for the format,
  codec, validator and interpreter; LEAN THEOREM for the abort-projection
  prefix law.
  - Format: `Inst::InvokeIndirect` (Inst tag 69), `CallIndirect`'s unwinding
    twin — a terminator with `Invoke`'s successors (`InstShape` +
    `is_terminator`, gate-13 law `terminator_invoke_indirect`). Text
    `invoke_indirect %f(functy.K)(..) [cc=X] to bbN(..) unwind bbM`; JSON /
    MessagePack the tagged variant. Binary tag 69, read-gated `version >= 56`;
    a module without it keeps its bytes and digests; `RawV38` /
    `CanonicalV38` refuse (`UnwindTwinsRequiresV56`). Golden `unwind_twins`.
  - Validator: `CallIndirect`'s checks plus `Invoke`'s edges (results defined
    on the normal edge only, rule (a)/(b), the unwind surface, a call node for
    proof contexts, the closure-callee codegen refusal); no new
    `ValidationError`. Must-refuse rows
    `invoke_indirect_unwind_dest_without_landing_pad` and the `none` row
    `unwind_verdict_names_its_strategy`.
  - Semantics (normative): `interpret::PanicStrategy` (`Abort`, the default:
    the panic=abort projection, every earlier outcome unchanged; `Unwind`) on
    `InterpretOptions::panic_strategy`, mirrored by the Lean evaluator's
    argument `strat` (default `.abort`) and the oracle's `panic_strategy`
    request field. Under `Unwind` a failed `Assert` / `AssertInvoke` raises a dead
    one-byte exception object; plain calls and drops propagate it;
    `Invoke` / `InvokeIndirect` / resolved `DropInvoke` / a failing
    `AssertInvoke` catch it into their landing pad (catch-all selector 1,
    cleanup 0, a typed catch refused, a pad with neither re-propagates);
    `Resume` re-raises by address; an escaping unwinding is the Abort run's
    panic. Lean `Proofs/UnwindProps.lean`: `stepNWithContext_abort_prefix`
    and `abort_projection_normal_exit` / `_ub` / `_out_of_fuel` (the Abort
    run is a prefix of the Unwind run), `plain_call_propagates_unwinding`,
    `resume_reraises_in_hand_exception`. Tests: `interpret_unwind.rs` (the
    decided matrix and the prefix law over the golden corpus) and the
    differential `unwind_paths_agree_message_for_message`.
  - Docs: `docs/ub-numerics-policy.md` §4's "Unwind surface under
    panic=abort" is replaced by "Unwinding"; §19.1 rule 9 and §20 rule 6 are
    amended; the subset rows for `LandingPad` / `Resume` read "modelled under
    `Unwind`; awaiting admission"; `InvokeIndirect` is excluded by name
    (53 of 67).

- **Amendment D, Part 1: a drop is a call of its type's glue (wire v55,
  `docs/SPEC_RATIFICATIONS.md` §20; 2026-10-01).** Rung: TEST for the format,
  codec, validator and interpreter; LEAN THEOREM for the evaluator lift.
  - Format: `Module.drop_glue` (`DropGlueEntry { glue, ty }`, one canonical
    order: strictly ascending glue, one row per type; `Module::set_drop_glue`,
    `drop_glue_for`, `drop_glue_index`, `is_registered_drop_glue`) and the
    terminator `Inst::DropInvoke` (Inst tag 68), `Drop`'s unwinding twin with
    `Invoke`'s successor discipline (`InstShape` + `is_terminator`, gate-13 law
    `terminator_drop_invoke`). `Ty::is_trivially_droppable`. Text
    `drop_glue @func.N <ty>` / `drop_invoke <ty>, %p to bbN(..) unwind bbM`;
    JSON / MessagePack `drop_glue` is the sole trailing skipped field, so
    `completeness` is now always emitted (every serde golden regenerated; old
    documents still decode). Binary: the trailing drop-glue section and tag
    68, read-gated `version >= 55`; the reader refuses a non-canonical table
    (`InvalidData`); a module without either keeps its bytes and digests;
    `RawV38` / `CanonicalV38` refuse (`DropGlueRequiresV55`).
  - Control flow: one exhaustive accessor, `Inst::successor_edges` /
    `unwind_dest`, replaces every wildcard CFG walk (dominance, the
    allocation-bound advisory, the diff's block order, the validator's
    control-flow / unwind / block-argument / refinement / binding-frame /
    memory-claim passes, the give-back loop probe); two of them missed
    invoke-family edges and are fixed by it (`cfg_edges.rs` census).
  - Validator: `InvalidDropGlue` (rows: one `(ptr) -> ()` function, not weak,
    not a pinned runtime entry, canonical order, unique keys, no refined or
    trivially droppable key) and `NonCanonicalDrop` (no drop of a refined or
    trivially droppable type; a registered glue is never called directly by
    `Call` / `CallCannotUnwind` / `Invoke` / `SeqMap` / a panic-site entry);
    the drop operand is exactly `Ptr`; an unresolved drop is well-formed but
    `UnlowerableForCodegen`; `ModuleValidationReport::unresolved_drops`;
    `DropInvoke` joins `unwind_surface`; a resolved drop is a call node for
    proof contexts and memory claims. Must-refuse rows `drop_unresolved`,
    `drop_glue_invalid`, `drop_glue_called_directly`,
    `drop_invoke_unwind_dest_without_landing_pad`,
    `blob_drop_glue_not_canonical` and the `none` row
    `drop_glue_implements_the_destructor`.
  - Semantics (normative): both engines resolve a drop through the table and
    run it as `call glue(%p)` (`DropInvoke`: `invoke`, normal edge only, the
    panic=abort projection); an unresolved drop is `UnsupportedInstruction` /
    `unsupported.destructor` (was the interpreter's `TypeError`). Lean
    `EvalContext.resolveDrop`, `Proofs/DropProps.lean`
    (`stepNWithContext_resolveDrops`: running a CFG whose drops were rewritten
    to calls IS running the original), fixtures, and the differential matrix
    `drop_glue_execution_agrees_across_engines`. The dependency census follows
    a resolved drop to its glue; the `trust-ir run` linker carries and merges
    tables (refusing two glues for one type); the diff reports a `drop_glue`
    module row. Golden `drop_glue` (exempt from subset v4: `Drop` /
    `DropInvoke` are excluded by name until the v5 expansion).
- **WS4.11: library module merge / id remap (`trust_ir_build::merge_into`,
  F-069) (2026-10-01; rebased and reviewed 2026-10-07).** Rung: TEST. `merge_into(dst, src, &MergePolicy)`
  joins one module into another and returns a `Remap` whose every lookup
  (`func`, `ty`, `func_ty`, `struct_`, `enum_`, `record`, `closure`, `global`,
  `pred`, `univ`, `import`, `proof`, `file`) is an `Option`. The merger
  destructures `Module`, `Function`, `Global`, `InstrNode`, the proof rows and
  every `Inst` / `Ty` / `Constant` / `ProofEvidence` variant with no `..`, so
  a new field or variant is a compile error in it rather than a stale id.
  Functions and globals are keyed by link-time symbol; two definitions dedup
  only on FULL equality (`MergeError::ConflictingDefinition { symbol, field }`
  names the first differing field — identical bodies under two codegen
  licenses are a `body_gate` conflict, never "keep the first"); a declaration
  resolves to its definition when signature and calling convention agree, and
  an obligation scoped to the superseded declaration is refused. Nominal types
  are never unified by name: a struct / enum / record / closure type maps onto
  a `dst` definition only when literally identical after the remap
  (coinductively), and two `Ty::Handle`s with one name and two runtimes stay
  two types. Proof state and imports are carried per policy (stripped exactly
  as the WS4.6 linker did otherwise, counted in `Remap::stripped`);
  `source_provenance` is dropped and counted (F-078); a refused merge leaves
  `dst` untouched. `trust-ir run`'s linker is now this merge
  (`MergePolicy::EXECUTION_IMAGE`) plus its own 64-bit word-pun respelling of
  declarations; its link errors are the merge's (`conflicting definitions of
  @f: blocks differs`), it no longer unifies equally named structs that
  differ, it now carries tuple layouts and `global_asm`, and it remaps
  type-valued dialect attributes it used to copy stale. The amendment D / P
  surface is merged like the rest: panic sites (`Assert.site`,
  `AssertInvoke`) remap their entry function and static-location global, the
  unwind twins (`CallCannotUnwind`, `CallIndirectCannotUnwind`,
  `DropInvoke`, `InvokeIndirect`) their callee / signature / inline type, and
  the drop-glue table is CARRIED through `Module::set_drop_glue` — a second
  glue for one type, or one glue for two types, is
  `MergeError::DropGlueConflict`, so input order never picks a destructor.
  Review (2026-10-07): signatures compare by CONTENT, not id — the signature
  table is positional and not interned, so a `src` reference landing on the
  first equal `dst` row no longer makes an identical definition, or a
  declaration and its definition, conflict over an alias; an input's refused
  empty `Partial` completeness claim survives the merge as itself, never
  upgraded to the other side's rows or to `Complete`. Fix (2026-10-07, the
  10:07 train): the file table merges STRUCTURALLY — `src`'s rows are
  appended whole and a placeholder is appended, never looked up — because a
  by-path dedup made the merged V3 identity depend on debug-only path
  strings (`module_files_strings_are_debug_only`); and two DECLARATIONS of
  one symbol follow `MergePolicy::on_duplicate_declaration`
  (`DuplicateDecl::RequireIdentical` for the verification image,
  `FirstStands` — the pre-WS4.11 linker's "a declaration adds nothing" — for
  the execution image, both still binding `ty` and `calling_conv`), which
  restores `two_language_cli`'s b4 hollow twin to its as-linked
  `EmptyFunction` verdict. Over WS3.9 (wire v58) the merge carries a struct /
  enum `origin` verbatim (part of the literal equality a `dst` match needs,
  so definitions differing only in origin stay two types) and remaps
  `Module.closure_layouts` with their closure types (a second, different row
  for one merged type is a `ConflictingDefinition`). Tests:
  `trust-ir-build/tests/module_merge.rs` (gate 9), including the identity law,
  the pairwise corpus merge over every conformance module fixture (held to the
  generator's source by a scan), the `ws4_11_review_*` adversarial twins, and
  the ported rows `design_0827_functy_interning` and
  `exec_log_and_tcb_module_merge_and_id_remap`.

- **The fresh-id rule gets verified-lane evidence: three `u32` decision
  tables, eleven proved laws (2026-10-01).** Rung: PROVED-CONTRACT for the
  three tables (gate 13), TEST for the cursor reading them. Round 11 stated
  the one fresh-id rule (`FreshIds` / `IdRun` / `IdSpaceExhausted`, r11 R1)
  generically and over `Option` cursors, and its entry below records that
  every lane row the survey printed for it was UNKNOWN. Measured on
  origin/main `d94aac6d` (trustc 321aaeda7, `targo trust check --release`): a
  law over the generic cursor stays UNKNOWN for `after([u32::MAX])`, the take
  at `u32::MAX`, a run one past the room and `IdRun::span(0, u32::MAX)` (4 of
  5 probe laws). Its decisions are now three monomorphic `pub const fn`
  comparisons in `trust_ir::value` that the cursor reads —
  `fresh_id_has_successor` (`id < u32::MAX`: the exhaustion row, read by every
  advance of a cursor), `fresh_run_fits` (`extra <= room`, the room computed
  as `!first`) and `fresh_id_below` (`id < end_exclusive`: the reserved bound,
  `after`'s max, `span`'s order) — and gate 13 proves each over every `u32`
  and at every boundary row (`laws::fresh_*`, Certified, KernelRechecked).
  The two batched trust-ir mutants carry their edits: every table negated,
  and the neighbour spellings, among them THE WRAP (`id <= u32::MAX`), which
  refutes `fresh_successor_absent_at_max`. Callers keep their paths and
  behaviour with the current tables; transport after their admitted decisions
  deliberately uses `wrapping_*`, so the tables alone decide the boundary.
  A wrong table could wrap: gate 13's wrap mutant must refute that decision;
  the tables' proofs do not prove the cursor or every minting site. Stated as
  spec in the ratifications ("A fresh id is one past the highest; an
  exhausted id space is refused, never wrapped"), whose `(proved-contract)`
  entry cites each table before its laws. NOT proved: that the cursor reads
  the tables (`the_cursor_decides_by_the_fresh_id_tables`, a test), the
  generic cursor, the guarded transport, and that every minting site goes
  through the rule. Gate 13: PASS on `8a5b57aa` (trustc
  321aaeda7, 2026-10-01, 34 min 50 s at a load average of ~70): 324 laws
  proved, Certified, KernelRechecked; 18 same-shape mutants refuted on exactly
  the laws they break (every-table-negated refutes all 11 `fresh_*` laws;
  neighbour-spellings refutes exactly the 7 it names and leaves the other 4
  proved); every run JUDGED (peak RSS at most 0.578 GiB against a 3 GiB
  ceiling, no budget stop). The commits after `8a5b57aa` change only
  `#[cfg(test)]` code, a doc comment and Markdown, which no gate-13 unit
  compiles.
- **WS8.1 remainder: the archived proof program's checks are a standing
  gate (2026-10-01).** Rung: TEST. `reports/2026-09-17-two-language-proof-program/check_archive.sh`
  (manifest, no live pin, row resolution, cited paths, publish boundary, each
  with its twin) ran only by hand; `scripts/tests/test_proof_program_archive.py`
  now runs it under gate 0's `internal-gate-tests`, and in a scratch repository
  reached through a symlink shows a one-byte edit, a `publish/manifest.txt`
  allowlisting `reports/`, and a deleted archive each turn it red (a public
  snapshot, which never ships `reports/`, skips; any other tree without the
  archive fails). Fixed beside it: the script resolved its directory
  logically while `git rev-parse --show-toplevel` is physical, so under a
  symlinked path the publish gate searched for an absolute path and passed
  vacuously (only its twin went red); it now takes the archive's
  repository-relative path from `git rev-parse --show-prefix` and refuses a
  layout git cannot place (review: `pwd -P` alone still refused a legitimate
  archive reached under a differently-cased path on a case-insensitive volume;
  tests added for that, for a `*.md` allowlist glob reaching the archive, and
  for an archive outside any repository). The archive's round-trip dumps stay
  out by design (regenerable, ~16 MB); its negative controls are WS8.8's.
- **Canonical text carries enum variant field names, the `switch`
  exhaustiveness hint and `global_asm` (WS4.5, remainder; F-072's last
  layout/linkage residue, F-065).** Text grammar only; no wire change. Rung:
  TEST.
  - `EnumVariant.field_names` prints `Name(field: ty, ..)` when the list is
    parallel to the fields (an empty name as `: ty`, a name outside the bare
    alphabet quoted); a positional variant keeps the bare type list. The parser
    refuses a variant that mixes the two spellings. A non-parallel list (which
    `validate_module` refuses) is not spelled: `TextLoss::EnumFieldNames` is
    NARROWED to that shape, decided by the one predicate
    `text_loss::enum_variant_field_names_spellable` the printer also reads.
  - `Switch.exhaustive_enum_unreachable` prints as a trailing ` exhaustive`
    on the `switch` line, bound to that line; absent means `false`.
  - `Module.global_asm` prints as one top-level `global_asm "<escaped>"`
    line per block, in order, after `target`; the escape set is the
    section string's, which the quoted-string reader inverts exactly. The
    `GlobalAsmNotConsumable` codegen refusal now survives a text round trip
    instead of being refused at the `#lossy` marker;
    `refuse/global_asm_block` records no text loss.
  - `text_losses` no longer reports `GlobalAsm` or `SwitchExhaustive`; both
    variants stay as historical kinds, like `GlobalAttrs`.
  - Ratchets flipped GAP -> PASS: `b6.text.drops_enum_layout_field_names_and_exhaustive_flag`,
    `b7.text.drops_enum_field_names`, `b7.text.drops_global_asm`; PASS rows
    re-aimed at the carried form: `b6.text.drops_niche_and_untagged_descriptors`,
    `b7.text.flip.layout_becomes_uncomputable`,
    `b7.text.flip.global_asm_refusal_laundered`, `verify.c08.L1/L2`. Ported
    rows `a.rust.struct_enum_match.roundtrip` and
    `small-designs/TREE-14-text-format-drops-enum-layout` as conformance
    tests; the round-trip fuzzer now emits all three fields.
  - After the rebase onto WS4.4 the corpus `TEXT_LOSS_RATCHET` is empty and
    the b7 surface module round-trips through text EXACTLY (same stable
    digest), which `text_drops_contract_surface`,
    `b7.text.obligation_kind.baseline_postcondition_parses` and
    `b7.text.round_trip_changes_module_identity` now assert in place of the
    `#lossy` refusal. The CLI lossy twins use the one summary shape text still
    refuses (a clause sort past `MAX_TEXT_CLAUSE_SORT_DEPTH`). Review: the
    glued `]exhaustive` is refused (one spelling).

- **`trust_ir_contract::formula_dag`: a hash-consed `Formula` DAG and
  sharing SMT-LIB printers (shared-VC plan, step 1; 2026-09-30, review
  fixes 2026-10-01).** Rung: TEST throughout (nothing here is proved; each
  property below names the test that holds it). A verification condition is
  a tree in which every row repeats its whole context, so a function's rows
  cost Θ(rows × context); `FormulaDag` stores each distinct subterm once.
  - Nodes are keyed on (shell, child ids) and compared by EXACT equality; a
    randomly keyed hash only selects candidates (formula payloads chosen to
    collide cannot degrade interning, and ids and outputs stay
    deterministic). Held by the crate's unit tests, which force EVERY hash
    to collide (round trip, identity and node counts unchanged) and forge
    wrong candidates into both indexes; deleting either exact comparison
    fails them (`formula_dag::tests`, run by the `formula-dag` gate).
  - A `NodeId` carries its DAG's process-unique brand: every operation of
    another DAG — a clone included, which gets a new brand — refuses it
    (`DagError::UnknownNode`, or a panic where documented), so an id can
    never silently stand for another DAG's node. `id_at` translates an
    index deliberately; `kids` yields branded ids.
  - A shell is the node with its children stripped; distinct shells are
    stored once, and an n-ary shell (`And`, `Or`, `Pred`, `Ctor`, `FnApp`)
    keeps an EMPTY child list beside its arity instead of a 112-byte
    placeholder per child. A node costs one shell index, a child range and
    four bytes per child. Measured on the review's ladder of n distinct
    `And` arities (n = 4,000; 8,010,000 edges): peak RSS 1.39 GB before,
    54 MB after.
  - `mk` builds bottom-up (validated arity and child ids); `intern` /
    `intern_owned` and `expand` are iterative and built on the crate's own
    exhaustive `children` / `map_children` (the borrowed `Shell::of` is the
    one other per-variant match, exhaustive and tested equal to the
    `map_children` split for every variant). Filling a shell is fail-closed:
    a missing child panics instead of becoming the placeholder `true`, a
    surplus child panics instead of being dropped. No new `Formula`
    variant, no wire, Lean or olean change; the `trust-types.Formula@1` tag
    is unchanged. `Formula::bound_variables` is the exhaustive binder
    classification (`binds_variables` is defined from it).
  - `Formula::to_smtlib` is split into the per-node spelling
    `Formula::write_smtlib_node` (one source of spelling) and an iterative
    walk: its text is byte-identical (held against the pre-split printer kept
    verbatim as a test oracle) and it no longer recurses on deep formulas.
  - `FormulaDag::to_smtlib` writes one term with `let` sharing: a compound
    node referenced twice — counting the operand that the truncating
    `Div`/`Rem`, signed `BvToInt` and saturating `FpToSbv`/`FpToUbv` spell
    3-4 times — is bound once, by dependency level. Sharing crosses
    binders exactly when it means the same thing: each node is bound in the
    outermost `let` region where every use sees the same variables (the top
    level for a node that mentions no name any binder of the DAG binds; the
    body of the innermost binder of `k` for one whose only such name is `k`;
    the region of each use for two or more such names), so a binding is
    never captured. Names are `dag!<j>_<k>` with `j` the smallest number
    whose `dag!<j>_` occurs nowhere in the formula's text, so their length
    is logarithmic in the text whatever the formula's symbols are.
    `to_smtlib_script` shares across several assertions with `define-fun`
    (not for ay's strict certification, which does not certify `define-fun`
    steps); a sort is inferred per node and never guessed: operands of two
    different known sorts (`Int` and `Real`, which ay coerces one way and
    refuses the other) give `DagError::UnsortedDefinition`.
  - Work: `PrintStats` (returned by `write_smtlib`, carried by
    `SmtlibScript`) counts the printers' work deterministically, and
    `tests/formula_dag.rs` holds every counter to x2 (within 5%) per
    doubling on wide, deep, shared and quantified inputs, so a super-linear
    regression fails instead of hanging the gate. The review's quantified
    probes, before -> after: nested binders over closed shared bodies (57
    DAG nodes) 14,680,527 -> 1,489 bytes of `let` text (it was x2 per added
    level, now +85 bytes); one closed context under k sibling binders (k =
    m = 800) 5,694,185 -> 38,889 bytes (was x4 per doubling, now x2); a
    symbol `dag!` + 100,000 digits with 3,002 shared nodes 400,163,562 ->
    163,562 bytes (the symbol once; the names no longer carry its run).
    A subterm that mentions a binder's variable is spelled once per printed
    body of that binder — the minimum any `let` text can do (see
    `LIMITATIONS.md`); `open_subterms_are_spelled_once_per_binder_body`
    pins exactly one spelling per (node, region).
  - `Formula::drop_iterative`, `Formula::binds_variables`,
    `Formula::bound_variables`, and `formula_census` (every variant from the
    serde derive, plus a witness of each and their declarations) for
    exhaustiveness tests downstream.
  - Measured: the VC ladder of n rows (row i conjoins i facts) is exactly
    `7n + 1` DAG nodes against `5n + 5n(n+1)/2` tree nodes; a chain of nodes
    that each use their child twice prints in linear size; intern, expand and
    both printers run on 10^6-deep chains (debug build: 0.89 GB peak RSS for
    the test that holds the 10^6-deep tree, its expansion and the DAG at
    once; 0.31 GB for the 10^6-node shared chain, whose tree would have
    2^(10^6) leaves). On the dumped ever-init VC rows of the shared-VC study
    (an uncommitted harness; 30/75/150/300 rows at N = 10/25/50/100 locals):
    26,966 / 167,426 / 670,476 / 2,084,105 tree nodes become 951 / 2,328 /
    4,653 / 8,805 DAG nodes; `to_smtlib` is byte-identical to the pre-split
    printer on all 555 rows and as fast; ay proves each row's `let` text and
    its `define-fun` script term equal to its tree text (N = 10 and 25, 105
    rows). The review fixes left those rows' `let` texts and scripts
    byte-identical (they hold no quantifier) and their print time unchanged
    (N = 100: 166-171 ms for every row's `let` text). The flat `And` child
    lists of such rows remain Θ(n²) edges: re-associating rows into shared
    context cells is the plan's next step, not this store's.
  - Gate: `formula-dag` beside gate 9 (`scripts/gates/formula-dag.*.tests`,
    then the crate's `formula_dag::tests`), including
    `trust-ir-ay/tests/formula_dag_ay.rs`, where ay proves
    `(not (= TREE SHARED))` UNSAT for every variant's witness used twice (85
    of 109 witnesses print a bound spelling), for random shared formulas
    whose subterms cross binders of two names that also occur free, and for
    every hoisting shape above; refutes a binding hoisted across a binder
    that captures it; compares only DECIDED verdicts (two timeouts prove
    nothing), with a floor of decided rows; and pins ay's refusal of an
    `Int`-declared `Real` `define-fun` body.

- **A wire-allocation owner resolves, or gate 0 says why not
  (2026-09-30).** The Single enum claim (wire v53, `EnumTagEncoding` tag 3)
  named a branch that had been deleted from origin, from 2026-09-27 until the
  claim was released on 2026-09-30, and every gate stayed green: nothing
  judged an owner. Gate 0 now runs `scripts/wire_alloc.py owners`, which asks
  origin and fails on an open claim whose lane was deleted from it (evidence:
  the remote-tracking ref, an earlier audit in that clone, or a merge of the
  lane from origin), and prints SKIP when origin cannot be asked.
  `wire_alloc.py pin <lane>` is the fix it names: it pins the lane's open
  claims to the commits that landed them, `<lane>@<commit>`, in both
  wire-version ledgers. `wire_alloc.py check` holds every owner to that
  grammar and, where the development history is present, requires a pin to be
  the commit in HEAD's history that introduced the claim's row (an exported
  snapshot checks form only, and says so). No allocation changes.
- **The four wire-allocation owners no remote knew are pinned, and gate 0
  now fails on the next one (2026-10-02).** `agents/rm-WS1.14`,
  `agents/rm-WS3.9`, `agents/rm-WS6.7-wire` and `mem/inst-wire-batch` named
  lanes that were never branches on origin: those lanes commit straight to
  main, so each label resolved only in the clone that wrote it, and the
  owners audit could only say `not seen here`, with every gate green. Each is
  now pinned to the commit that put its claim on main, in both wire-version
  ledgers: the three open claims with `wire_alloc.py pin`, and the INST wire
  batch, whose claims landed while its lane was being traced, by the same
  rule (a test pins that a landed row's pin is the commit that introduced its
  row, not the one that flipped it to `landed`). `wire_alloc.py check`
  resolves all 19 pins. No number, status or row moved. The owners audit now
  FAILS (`UNPINNED ON MAIN`) on an open claim that is on origin's main under
  a bare lane that is no branch on origin or here, naming the `pin` that
  fixes it; on main before these pins it failed on exactly the three open
  lanes. A claim not on origin's main yet is still listed, not failed.
  Whether to keep or release the three open claims (nominal identity, effect
  summaries, certificate binding) is the owner's decision, queued with the
  evidence in `docs/wire-allocation-decisions.md` (WA-1 to WA-3).
- **One fresh-id rule, total fixtures and a total adapter: the locally-TRUE
  refutations of the verified survey, fixed at their roots (r11,
  2026-09-30).** Rungs, per item — none of this is proved: TEST (every
  behavioural fix), TYPE (`IdRun`'s count is stored so no subtraction exists;
  `Corpus` has no `Default`; `build_bytes_constants`' closure takes bytes
  only; `AddFunctionError` returns the function), and a GATE-0 LINT
  (type-resolved, below type-level). The lane: trust-ir, trust-ir-build,
  trust-ir-cli, trust-ir-ay and trust-ir-conformance are NOT JUDGED by any
  gate-15 run to date (R3 judged 4 of 12 crates, and printed zero rows for
  trust-ir-cli; r11's own base run left all 5 NOT JUDGED, and its final-tree
  run stopped after 2 of them — trust-ir and trust-ir-ay, both NOT JUDGED —
  with trust-ir-build, trust-ir-cli and trust-ir-conformance never surveyed
  on the final tree), so an absent row is "not refuted in a run that judges
  nothing", never a verdict. Every row the final trust-ir survey printed for
  the new rule (`value.rs`, `lineage.rs`, `dialect/lowering.rs`) is UNKNOWN
  (`unsupported_mir`): the rule has no lane evidence in either direction.
  - Root R1 — unchecked fresh-id minting. `trust_ir::value::{FreshIds,
    IdRun, IdSpaceExhausted, TypedId}` state it once: one past the HIGHEST id
    in use, all-or-nothing runs, refused (never wrapped) at `u32::MAX`. The
    core (`Function::fresh_value_ids` / `fresh_block_ids` / `value_ids`,
    `Module::fresh_obligation_ids`, `try_add_function`,
    `synthesize_function_obligations -> Result`, dialect lowering,
    `append_pass -> Result`, the text parser), trust-ir-build (block, value
    and function cursors; `try_create_block`, `try_build`,
    `try_peek_next_func_id`; the reservation owns an `IdRun`;
    `add_proof_obligation -> Result` with `IdMismatch` checked in every
    profile; `mint_summary_obligations -> Result`, all or nothing) and
    trust-ir-cli (legalization, devirtualization, builtin synthesis, the
    reserved block ranges and the linker's table ids) move onto it. **Decoded
    modules:** a caller extending a decoded module must use
    `Module::try_add_function` — a decoded obligation table may already hold
    `u32::MAX`. **Behaviour change:** dialect lowering's first fresh value id
    in a function that defines NO value is 0 (was 1; id 0 is unused there).
  - Root R2 — `trust-ir run` parsed a v0 intrinsic's length prefix with an
    add (`…10intrinsics18446744073709551615x` panicked); it now slices by the
    length alone. The runner also refuses by name a function whose block ids
    lie in its reserved range `[0xE000_0000, 0xFFFF_FFFF]` and a function it
    cannot lower for lack of a fresh id (a runner limitation, not a format
    rule; lazily — a function that needs no id is never refused).
  - Root R3 — trust-ir-ay calls ay's `try_*` twins. A name scan of the
    adapter's production code (receivers matched across line breaks) finds
    six ay methods called without a `try_` spelling: four are total
    (`export_last_unsat_bundle`, `is_valid_term`, `num_scopes`,
    `set_produce_proofs`), and two — `render_term_canonical` and `term_sort`
    — have no twin at the pinned ay and panic on a handle the solver did not
    issue. The first inventory missed `term_sort` (its call was split across
    two lines) and wrongly said only one method lacked a twin. Each of the two
    keeps ONE scoped `#[allow]`, preceded by `authenticate_term` (ay's total
    `is_valid_term`, the same authentication their `require_term` runs), so
    both sites are total today; replace them at the pin move that carries
    `Solver::try_render_term_canonical` / `Solver::try_term_sort`.
    `crates/trust-ir-ay/clippy.toml` disallows the panicking methods
    (gate-0 lint), including `term_sort`'s aliases `sort_of` and `get_sort`.
    A solver frame is guarded: the session is POISONED, and every later
    condition is `Unknown`, when a frame fails to open or close, is left
    unbalanced, or when ANY solver step inside it fails. The last clause
    matters: ay's `try_check_sat` turns a panic inside the solver into
    `SolverError::SolverPanic`, after which ay says the solver is "likely
    corrupted"; without it the whole-function walk, which shares one solver,
    kept solving later conditions on that solver (a path to a false
    `Proved`, opened by turning ay's panics into errors; fixed before
    landing, r11 review H1). `verify_and_certify` and `ProofCondition::check`
    assert with no frame and now document "one solver per call; discard it
    on `Err`". `encode_cast`'s `trunc` / narrowing `ptrtoint` to width 0 is
    a named refusal (was `0 - 1`). `VcVerdict::Refuted { counterexample: Counterexample }` is
    a consumer-accepted `Model` or a typed `Unavailable`, never an empty
    stand-in; `VcVerdict::Unknown` carries its reason. **D3:** an
    `Unavailable` witness does not mint `Failed` (the obligation stays
    `Pending` with a diagnostic naming the reason) — the crate's existing rule
    "`Failed` requires a real refutation"; the owner may reverse it in
    `split_refutations`.
  - Root R4 — the conformance fixtures and the must-refuse runner are total.
    Every `build_*` / `build_refuse_*` returns `Result<_, FixtureError>`;
    the byte rows read and write varints through the codec's own
    `trust_ir::binary::{decode_varint, encode_varint}` (byte-identical
    goldens). `refuse::corpus()` / `manifest()` return `Result`, `corpus()`
    refuses a VACUOUS corpus, `Report::check` replaces
    `assert_every_row_refused`, and `Corpus::uncovered` replaces the free
    `uncovered`. **Consumer migration (two lines per file, at the next
    trust-ir pin move):** `corpus()` → `corpus().expect(..)`,
    `uncovered(&h)` → `rows.uncovered(&h)`, and drop `uncovered` from the
    `use` line — trust-cg (`trust-cg-cli` and `trust-cg-codegen`
    `must_refuse_corpus.rs`, `trust_ir_corpus_roundtrip.rs`) and ty
    (`tla-trust-cg`).
  - Correction to the stage-0 entry below: it deferred
    `build_proof_annotations`' `expect(ID_SPACE)` to "stage 1's ledger". That
    never happened (class `true` is forbidden in the ledger); the fixture now
    takes its ids through `Module::fresh_obligation_ids`, with identical bytes.
  - Gate 15's ledger loses 12 verifier-false rows whose source text no
    longer exists (8 trust-ir-build, 2 trust-ir-cli, 2 trust-ir-conformance).
  - Evidence, measured (`targo --unverified`, no proof claim). FAILING-FIRST
    on origin/main `b8f49083` (the surface unchanged; each exited 101 on a
    debug-build panic, or ran a duplicate-id image): the CLI unit test
    `v0_intrinsic_name_refuses_a_length_no_offset_can_hold`, six
    `cli_run.rs` end-to-end tests (`r11::*`), and in trust-ir-ay
    `an_ill_typed_body_is_refused_not_panicked_inside_ay` (ay panicked:
    `sort mismatch in bvadd`) and
    `a_wide_bitvector_constant_is_refused_by_ay_not_panicked` (ay panicked:
    `bv_const` width 2097152 outside `1..=1048576` — a module path the r11
    design had believed unreachable); and, from the landing review,
    `a_foreign_term_handle_is_refused_by_the_width_query_not_panicked` (ay
    panicked in `term_sort`'s `require_term`) and
    `a_cast_to_a_zero_width_integer_is_refused_not_underflowed` (`attempt to
    subtract with overflow`). Every other new test ports a kept design probe
    or pins a new seam (evidence kind ii, among them
    `a_failed_solver_step_inside_a_frame_poisons_the_session`), or is
    type/parity evidence (item 3, item 8's byte-identical goldens). MUTATION
    checks: 16 textual mutations, each turning its named test red (FreshIds
    wrap, block wrap, lowering re-seed, lineage re-seed, the intrinsic add,
    legalization's wrapped seed, allocation inside the synthesis / mint push
    loops, ignoring the poison, dropping the scope-level check, admitting
    `Unavailable` refutations, reverting `try_bvadd`, a `debug_assert`-only id
    check, a vacuous corpus accepted, dropping the poison on a failed frame
    step while keeping its message — the follow-up goal then reads `Proved`
    — and dropping `authenticate_term` before `term_sort`); three first-draft
    mutations that left the up-front id run in place were NOT faithful and
    did not go red — recorded, and replaced by the faithful ones.
  - What stays TRUE for the next judged run (owner decision D1, open): the
    designed caller-precondition panics of the infallible conveniences —
    `create_block`, `alloc_value` through every emitter, `build`'s
    reservation/declaration asserts, `add_block_param`'s mixing assert,
    unknown-block indexing, `peek_next_func_id` / `allocate_function_id`,
    `Module::add_function`, the table interners' `u32::try_from(len)
    .expect(..)`, the writer's `len_u32` and `canonicalize`'s dense
    `next += 1`. The wrap is gone from every one; the panic is not. This is
    not "fixed, 0 true left".
- **Binary v54: a failed check names the entry it calls and the location it
  reports (2026-10-01, amendment P, the second half of plan item P).**
  `Inst::Assert` gains `site: Option<PanicSite { entry, location }>`, where
  `PanicLocation` is `Global(GlobalId)` (an immutable module global, the one
  spelling of a location known at compile time) or `Value(ValueId)` (a
  `#[track_caller]` forward); the new terminator `Inst::AssertInvoke` is a
  sited check whose failure enters an in-frame landing pad. Binary: siteless
  asserts keep tags 29 / 63 and their bytes; a sited one is Inst tag 66 and
  `AssertInvoke` tag 67, read-gated `version >= 54`, so the writer selects
  v54 only for a module carrying a site and the v38 projections refuse it
  (`PanicSiteRequiresV54`); new `PanicLocation` tag space. Text `, panic
  @func.N at @global.G | %v` and `assert_invoke`. Serde now always emits
  `kind` and skips an absent `site` (re-serialized assert JSON / MessagePack
  gains the `kind` key; binary bytes and digests do not change). Validator:
  `PanicEntrySignatureMismatch`, `PanicLocationGlobalInvalid`,
  `NonCanonicalPanicLocation` (must-refuse rows), the entry resolved as a
  callee, the location typed against the entry, `AssertInvoke` under
  `Invoke`'s unwind rules and in `unwind_surface`. Both engines end a failed
  sited check in the terminal outcome (kind, operand values, entry, resolved
  location) — `InterpretPanic::site`, Lean `SemError.panic msg site` — never
  executing the entry; `AssertInvoke` is the panic=abort projection. Lean:
  `assert_true_step_independent_of_kind_and_site`,
  `assertInvoke_is_sited_assert_then_br`, `siteRewrite_not_refines`; the
  Lean-execution differential compares sites. New goldens
  `assert_panic_site` (in the subset) and `assert_invoke` (excluded by name).
  `SPEC_RATIFICATIONS.md` §19.1. Reserved as v57 and taken over to v53 on
  its branch; main landed the call-unwind boundary as v53 (Inst tags 64 and
  65) first, so at the merge it took the lowest open number again, v54 (Inst
  tags 66 and 67), moving the four open reservations up by one
  (nominal-identity 54 -> 55, typed-signature-abi 55 -> 56,
  effect-summaries 56 -> 57, certificate-binding 57 -> 58).
- **Binary v52: an assert names the Rust panic it is (2026-09-30, plan item P).**
  `Inst::Assert { cond }` became `Inst::Assert { cond, kind: AssertKind }`:
  `Overflow(AssertOverflowOp)` (Add, Sub, Mul, Div, Rem, Shl, Shr, Neg),
  `DivByZero`, `RemByZero`, `BoundsCheck { index, len }`, `MisalignedPtr {
  required, found }`, `NullPtr`, or `Unspecified`, the decode of every older
  assert (binary tag 29, serde without `kind`, text without a kind clause).
  `AssertKind::rust_panic_lang_item` names the `core` panic entry point a
  faithful lowering calls (`None` for `Unspecified`). Binary: a kindless
  assert keeps Inst tag 29 and its bytes; a kinded one is Inst tag 63 (the
  condition, an AssertKind byte, its payload), read-gated `version >= 52`, so
  the writer selects v52 only for a module carrying one and the v38
  projections refuse it (`AssertKindRequiresV52`). Text `assert %c, KIND`;
  serde skips an `Unspecified` kind. The kind's operands are `usize` SSA uses
  (`OperandTypeMismatch { op: "assert", role }`). The reference interpreter's
  panic now carries `InterpretError::panic: Option<InterpretPanic { kind,
  operands }>` and `core`'s exact message (`Unspecified` keeps "assertion
  failed"); the Lean model (`Inst.Assert cond kind`, `assertFailMessage`)
  throws the same text, and the Lean-execution differential now compares
  panic messages. New admission knob
  `CodegenAdmission::with_require_assert_panic_kinds` refuses an
  `Unspecified` assert (`ValidationError::AssertPanicKindUnspecified`;
  must-refuse row `assert_panic_kind_unspecified`). New golden `assert_kind`
  (the only one at header 52), in the lowering-target subset.
  `SPEC_RATIFICATIONS.md` §19. Reserved as v56 and taken over to v52, moving
  the four open reservations up by one (nominal-identity 52 -> 53,
  typed-signature-abi 53 -> 54, effect-summaries 54 -> 55,
  certificate-binding 55 -> 56).

- **Binary v51: the INST wire batch (2026-09-30).** Every instruction and sub-op that
  existed in the enums ahead of its binary tag now has one, so the infallible
  `Module::stable_digest` (and `executable_content_digest_v1`) can no longer
  panic on anything a producer can build: `Inst::MakeAggregate` at Inst tag 60
  (the type, the variant as a presence byte plus a v32, the lane list),
  `Inst::MemCopy` at 61 (three operands, then `overlap` as a 0/1 byte),
  `Inst::MemSet` at 62 (three operands), `BinOp::RotL` / `RotR` / `FCopySign`
  at BinOp tags 23..=25 and `UnOp::CtLz` / `CtTz` / `BSwap` / `BitReverse` at
  UnOp tags 9..=12. All ten are read-gated `version >= 51` (the sub-ops
  through `tag_enum!`'s new `read_gated` clause), so an older header carrying
  one is `InvalidTag`; the writer selects v51 only when one occurs, so every
  other module keeps its bytes and digest; the v38 projections refuse the
  batch with the new `BinaryProjectionError::InstWireBatchRequiresV51`.
  Reserved `dbd8c262` as v56 (both ledgers), moved to v55 by the v53 release
  (`73ca45ff`), then to v51 by takeover, which moved the four open
  reservations it passed up by one (nominal-identity 51 -> 52,
  typed-signature-abi 52 -> 53, effect-summaries 53 -> 54,
  certificate-binding 54 -> 55); rows flipped to landed, census samples
  added and the nine WS3.20 rows plus `MakeAggregate` deleted from
  `wire_census::UNENCODABLE` (it keeps `Ty::Error` and the feature-gated
  `ProofAnnotation::Goal`). `Inst::binary_wire_gap` — the one probe list the
  blocker, the bundle binding and the CLI consult — is now empty, so
  `trust_ir_build::wire_identity_blocker` names no instruction; the tests that
  pinned the old refusal (`make_aggregate_formats`, `bulk_memory_ops` in both
  crates, `make_aggregate`, `union_carrier`, the bundle wire-identity tests)
  now pin the lossless binary round trip, the gate and the digest instead. New
  four-format golden `inst_wire_batch` (the only one at header 51; an exempt
  fixture of the lowering-target subset, which is unchanged: the three
  instructions stay excluded for want of a trust-cg lowering, the sub-ops stay
  in). No digest domain moved: no module carrying a batch member had a digest
  before. No new `ValidationError` or `BinaryError` variant.
- **The spawn census's reachability engine (2026-09-30).** Trust refuses
  every function that can start a std thread. This adds the rustc-free engine
  that census is to move onto, in `function_dependencies`; nothing in trustc
  calls it yet (its MIR adapter is plan step P2, and trustc's trust-ir
  adapter, P4, will call `inspect_module_reachability`). An adapter feeds
  `ReachGraph` labelled edges (RUN, CREATE, READ, PARAM), UNKNOWN sinks with
  a reason, and indirect-call facts; `solve` closes the indirect-call pools
  (`analysis`: FnPool by coarse ABI shape, DynPool per principal and method,
  DynDropPool, confinement, LIFETIME-ERASE and LAUNDER demotion, LAUNDER
  collapse, upcast closure, and open principals: one no member records that
  a fact names or an upcast reaches is UNKNOWN, never an empty pool). Any
  UNKNOWN sink or open principal leaves every pool unclosed, since the code
  it stands for may have minted a callable no CREATE records: every indirect
  call is then also UNKNOWN(`UnclosedPool`). `solve` applies rule H (a local
  frame handing a callable to external code is charged only when that code's
  closure invokes the key; code with no body invokes every key; after a
  LAUNDER, data such as `f as usize` may carry any callable) and labels every
  node SPAWNS (RUN-only path to a seed, the only spawn claim), ESCAPES,
  INDIRECT, UNKNOWN or QUIET, with a per-definition join, shortest witnesses
  flagged `via_drop`, and per-thread closures, which feed a model only when
  complete (no UNKNOWN or INDIRECT node, foreign code, or PARAM edge). The
  labelling is a certificate: `check_reach_certificate` re-verifies it in
  O(V+E), plus an ordered map for the per-definition join, with well-founded
  ranks, so a self-justifying cycle is rejected, and `solve` always runs it;
  a rejected certificate or a malformed fact (including a node handle from
  another graph) makes every node UNKNOWN. `inspect_module_reachability`
  walks every function and global of a trust-ir module and classifies each
  implicit runtime service (a failed `Assert`'s panic path,
  `HeapAlloc`/`Dealloc`, reference counting) through its classifier instead
  of skipping it. `NominalTypeReachability` gains a callable axis
  (`contains_callable`) and `Module::callable_carriers` is the rule H operand
  walk. Tested, not proved: the tests compare the fixpoint with a
  brute-force path search on random graphs, reject every single-label change
  to a solved certificate, cover each pool rule, and restate trust-mc's
  reachability, `dyn_universe` and main-thread-purity cases as fact graphs.
  The checker is Rust code no kernel re-checks, and it checks the labelling
  against the graph the engine expanded: it cannot see a fact an adapter
  never emitted, nor an APPROX edge the engine failed to derive (pool
  closure, rule H and unclosed pools are trusted code).
- **The four F-066 rows are two-language ratchets (roadmap WS4.1's
  remainder, 2026-09-30).** The proof program measured the text parser's
  UTF-8 panic as four rows — Part A's `a.format.text_parser_utf8`, the Part A
  reviewer's `A.uf09`, and the skeptic claim c09's two lenses
  `verify.c09.L1` (reproduction) and `verify.c09.L2` (by design) — and each
  asserted the PANIC, in a battery outside the repo. They are now PASS rows
  of `RATCHETS.tsv`, emitted by `two_language_b7`
  (`text_parser_is_total_over_utf8`, gate 11): the Part A specimen, a
  driver-shaped module with a 2-, 3- and 4-byte character and a combining
  mark in every position the grammar admits a `;` comment (header, between top-level items, trailing an instruction;
  the ASCII run of the same shapes is the control), the reproduction's every
  input (`;é`, trailing, between-item and node comments, `parse_function`, a
  quoted non-ASCII module name and display path) and
  four validator-clean non-ASCII link symbols re-parsed from `Display` and
  `format::canonical` (WS4.3's quoted names). Each has a right-reason
  negative twin — the same character in a TOKEN position (before `module`,
  on an unknown top-level line, in the bare spelling of the symbol) is a
  located `ParseError`, never a panic and never the fallible cursor's
  `internal: cursor split`. No parser change.

- **`(proved-contract)`: a governed claim can cite a gate-13 law (2026-09-30).**
  Gate 13 proves 313 laws of the pure decision tables, and until now no
  `TRUST.md` or ratification unit could cite one: the enforcement-link gate
  (gate 0) had no class for them. The new class ranks below `lean-theorem`
  and `kernel-certificate` and above `type-level`: a law is about the table's
  OPTIMIZED MIR, and for a constant-valued law rustc's optimizer does the case
  analysis and the Clean kernel re-checks the folded constant. Its witness is
  checked, not asserted: the law must be one gate 13 HOLDS before any run,
  read from gate 13's own code (`verified_contracts.holding`, which gate 13's
  `main` now refuses on too, so the rule is stated once) — every law of
  `crates/trust-ir-laws/src/laws.rs` one call of its own table and named by
  some mutant's `flips` — and each law must follow a citation of its own
  table: the most recent table the entry cites before the law, spelled so
  that it resolves to that table's definition alone. That checks which table
  a law is cited under, not the words around it. Refused, each measured: a
  fake name, a law no mutant refutes, a mis-wired law, a law of the
  table-less `u64` family, a law read under another table the entry also
  cites, and a table cited by a name another item shares.
  **Gate 13 also holds every table over enum cells to a law at EVERY cell**
  (`cell_completeness`): it reads the operand enums' variants from the source
  and refuses, before any run, a cell no law states. Before this a deleted
  law (`ambiguous_custom`) left gate 13 green at 312 laws while the tables'
  own "PROVED, every cell" comments and a `laws::ambiguous_*` citation still
  claimed the cell, and a new `ObligationKind` would have done the same. 20
  of the 21 tables are held complete; `coverage_supports` ranges over `u64`
  payloads and is not enumerated, and a table leaves the rule only by being
  named so (`PAYLOAD_TABLES`), never because a law stopped parsing as a cell
  law. Cited from `TRUST.md` items 10, 11 and 13
  and from four ratifications (import identity, Termination/Ownership, and
  the two reference-counted-cell sections), each entry stating the ROWS
  proved and naming the rule that reads the table as code or test, never as
  proved. No unit left the no-checked-evidence ledger: the one unit on it is
  not about a table.

- **Freeing an allocation under a live borrow is undefined behaviour in both
  engines (2026-09-29).** `docs/ub-numerics-policy.md` §6 already called it UB
  and Lean's `semDealloc` already refused it (`Permission.canDealloc`), but
  the reference interpreter kept no borrow state and ran the free. The new
  SPEC section "Freeing an allocation under a live borrow is undefined
  behaviour" decides it and moves the interpreter in the same change (§4):
  each `Allocation` gains `requested` and `live_borrows`; a thin `Borrow` /
  `BorrowMut` raises the count and an `EndBorrow` lowers it (saturating), only
  while the operand's provenance allocation is live and the offset lies inside
  its requested bytes; only `Dealloc` reads it, after the base,
  known-allocation, liveness and reference-counted-origin checks ("Dealloc:
  allocation is under a live borrow"). No borrow instruction faults on this
  account. Lean semantics are unchanged; `semDealloc_borrowed_is_ub` and five
  `rfl` instances are new in `Proofs/MemorySafety.lean`, audited in
  `AxiomAudit.lean`, with two address-model pins
  (`borrow_one_past_names_neighbour_dealloc_is_ub`,
  `double_endBorrow_one_past_ends_neighbour_borrow`) for Lean's side of the
  divergences below. Tests: interpret.rs
  `dealloc_under_a_live_borrow_is_undefined_behavior` (six mutations measured,
  each fails it), the decided two-engine table
  `borrow_liveness_at_dealloc_agrees_across_engines` (19 cells), and the
  shrink-only ledger `borrow_permission_divergences_stay_as_measured`, which
  drops the now-decided `DeallocUnderBorrow` row and grows from 5 to 24 rows.
  **The rule adds ledgered divergences.** Lean resolves a borrow operand and a
  `Dealloc` operand by address over a packed allocator, the interpreter by
  provenance; where the two name different allocations they disagree in both
  directions: (a) a one-past-end or heap-slack borrow Lean moves to the next
  allocation, then that allocation's free (Lean UB, interpreter ok;
  pre-existing); (b) a second `EndBorrow` of such a borrow while the next
  allocation holds its own live borrow (interpreter UB, Lean ok; new, and it
  needs a `TRUST.md` item 12 violation); (c) a borrow through `IntToPtr` that
  lands in different allocations under the two layouts (interpreter UB, Lean
  ok; new); (d) a `Dealloc` of a zero-size slot, which Lean resolves to the
  borrowed allocation sharing its base (Lean UB, interpreter ok;
  pre-existing). A sample of each is in the ledger, with measured controls.
  Like the ARC-origin ruling, this does not meet §4's "zero new divergences"
  literally, and the SPEC says so; agreement is stated only under conditions
  (in-range operands without an integer round trip, each borrow ended at most
  once, Lean's borrow instructions fault-free, every `Dealloc` at the base of
  a nonempty allocation), as an argument, not a theorem. Closing the families
  needs Lean provenance for borrow and `Dealloc` operands. Measured and
  rejected: counting at any offset, and suspending the count after an
  unattributable `EndBorrow`. TRUST item 12 gains two enforcement rows (its
  strongest class goes from test to lean-theorem): the rule in the Lean model
  (theorem) and in the interpreter (test). The rule reaches MIR-bridge output
  run through `trust-ir run`, which maps `__rust_dealloc` to `Dealloc`: a
  hand-written module of that shape is refused until its borrow is ended
  (measured). No wire change, `VERSION` unmoved. trust-cg must add one
  `fsym_ub_map` site and re-pin the `alloc_with_slack` layout fingerprint in
  its next trust-ir pin move; every consumer pins trust-ir, so none turns red
  at this landing.

- **Nineteen more decision tables are proved contracts, cell by cell (gate 13,
  second wave).** `crates/trust-ir-laws/src/laws.rs` grows from 26 to 313
  laws. Three validator tables move into `trust-ir-laws` as local tables
  (`visibility_contradicts_linkage` for `ContradictoryFunctionVisibility`;
  `evidence_admits_kind`, WS1.8 rule (d), which
  `trust_ir_build::evidence_admits_obligation_kind` now delegates to at its old
  path; `proof_ref_kind_is_ambiguous`). Sixteen tables stay RESIDENT IN
  TRUST-IR and their laws call them across the crate boundary:
  `AllocOrigin::is_reference_counted`, `Linkage::{is_interposable,
  is_module_local, requires_contract_surface}`, `ProofStatus::
  {is_discharged_tier, is_kernel_tier}`, `Ordering::{is_legal_for_load,
  is_legal_for_store}`, `ExternRefSite::admits_shape`, `ObligationKindShape::
  {is_grounded_contract_kind, free_var_is_proved, is_assert_class}` and
  `InstShape::is_terminator` are thirteen new `#[inline] pub const fn`s, and
  `CallingConv::is_abi_surface`, `EnumTagRepr::is_abi_surface` and
  `HardwareVectorContractStatus::fail_closed` gain laws unchanged. Each rule is
  now stated once: the three interpreter RC-origin matches, the
  `Discharged | Certified` spellings in import authentication, the linked
  walk, the `proved` rule, lineage, the proof-table transform, the authority
  predicates, bundle replay and the bundle digest, the validator's six
  `Certified` kernel-tier filters (its `CleanCic` rules), the three
  module-local sites, the WS3.8 pointer-constant interposable-global check,
  the writer's v41 linkage selection, the validator's private atomic
  legality functions (deleted, with their "this crate cannot add one"
  comment), the grounder's contract and free-variable classifiers, the
  assert-class `iter().any` spelling and `Inst::is_terminator` all call the
  proved tables. A table over a data-carrying enum is stated over its new
  `Copy` shape (`InstShape`, `ObligationKindShape`, `ProofEvidenceShape`,
  generated with `shape()`, `ALL` and `name()` by the private
  `variant_shape!` from one variant list — exhaustive by construction, a
  type-level fact, not a proved one). No wire, tag or digest change: the
  shapes are never serialized. Gate 13 gains four batched mutants — two over
  a mutated COPY of trust-ir (every trust-ir table negated; one neighbour
  spelling per table, among them `core_reflection`'s `{Weak, LinkOnce}`) and
  two over the local tables — each held to a `scope` of law families, with
  `flips` globs; measured 2026-09-29 each refuted exactly its declared laws
  (226, 49, 51 and 25) and moved no other. A batch that edits every table
  flips a law WHICHEVER table the law calls (review measured a law re-pointed
  at another table: still proved, still flipped, gate PASS), so the flip only
  shows a law is not proved about a constant; gate 13 now also refuses,
  before any run, a law whose body is not exactly one call of its own table
  at the cell its name spells (`WIRING` / `law_wiring_errors` in
  `scripts/verified_contracts.py`; every law name is derived from its body).
  The inclusion "kernel tier within discharged tier" is a hand step over the
  two tables' proved cells, not a proved row. Measured and NOT carried (tested,
  nearest proved contract named in the crate docs): `EnumTagRepr::fits`
  (`i128` laws UNKNOWN), the WS1.8 site table (rows prove as trust-ir methods;
  hosting them there is an open owner decision; the dispatcher proves in no
  spelling), the x86 vector-cell reader. Open owner question:
  `core_reflection`'s byte profile does not count `ExternalWeak` as
  replaceable. Correction: gate 13 never ran in "about a minute" — every
  `targo trust check` run rebuilds its dependency graph, so its cost is about
  a minute per run (21 min 46 s for 19 runs under load, 2026-09-29).
- **Gate 13 judges a run before it reads its rows (`verified-contracts`,
  rule 4).** On the installed Trust seal (trustc 321aaeda7) the per-function
  budget trips on peak RSS, but the phase checkpoint that discards a truncated
  result reads only the step counter and the clock
  (`verify_budget::exhausted_readonly`); one such trip made strict/certify
  exit 0 with `proved: trivially panic-free` for a function that panics
  (counter-program p4, reproduced on that seal's trustc). The gate now fails
  every run — base and each mutant — as `NOT JUDGED: <reason>` unless the
  peak RSS of its process tree (`wait4` over targo) stayed below the memory
  ceiling the report records, no row or diagnostic names a budget stop, and
  every compiler request is explained — a published row kernel-rechecked, a
  request publication omitted from `report.json` (listed only in the
  terminal) only as a favorable claim withheld at publication, or either
  inside an expected refutation; a missing expected refutation is NOT
  JUDGED, never a pass, and no count is gated. Evidence class: test
  (`scripts/tests/test_verified_contracts.py` over real runs of the lane,
  `scripts/tests/fixtures/verified_lane/`, in `not_judged` and in the gate's
  `main()`), not proof.
- **Fragment-5 is decided by Clean and not minted (SPEC "A reference-counted
  cell is released by `Release`, never by `Dealloc`", clause 4).** trust-ir's
  `clean_backend_tv` refuses a `Ptr` return before the kernel, so every
  boxed-`Nat` `() -> Ptr` certificate Clean minted made `validate_module`
  refuse the whole module, certified Fragment-2 roots included. Clean
  d9f760a4d now holds every Fragment-5 body to a per-reference ownership
  balance and mints nothing for it; the clause states when minting may resume
  (a trust-ir re-checker mirroring the denotation and the balance, landed in
  trust-ir first). `crates/trust-ir-build/tests/clean_backend_tv_fragment5.rs`
  (gate 9) pins today's refusal by name, the scalar-twin control, and the
  not-minted shape.

- **The Lean proofs are a standing gate (`lean-proofs`, gate 14).** Until
  2026-09-29 no gate of `scripts/ci_gates.sh` ran `lake build` of
  `lean/trust_ir-semantics` (gate 12 builds only `trustir_eval`), and the
  build alone passed a theorem with a placeholder (a warning) and any axiom a
  theorem off `AxiomAudit.lean`'s curated list used. `scripts/lean_proofs.py`
  builds `TrustIr`, refuses a replayed "declaration uses 'sorry'", an orphan
  `.lean` file and `debug.skipKernelTC`, and runs the whole-environment census
  `lean/trust_ir-semantics/ProofCensus.lean` (every safe `TrustIr.*` constant:
  Lean-core trio plus `ay_sound_unsat`; `Lean.ofReduceBool` only in the two
  `native_decide` fixture modules, 462 theorems), which then REPLAYS every
  safe constant through the kernel with Lean core's `Lean.Environment.replay`
  (lean4checker's engine): the census reads what the environment records, and
  a `False` theorem a meta-program wrote into the environment passed the build
  and the census (measured); the replay refuses it by name. A `native_decide`
  site is replayed with its evaluation re-run; only `partial` definitions'
  `_unsafe_rec` bodies, which no safe constant may name, are skipped. The same
  kernel, run twice, not an independent checker. Required wherever
  `$HOME/.elan/bin/lake` exists; warm 9.5 s, cold 2 min 1 s.
  `check_enforcement_links.py` now counts a theorem as `(lean-theorem)`
  evidence only if that gate builds it and it is not a `native_decide`
  fixture (which witnesses `(test)`).

- **Exact-memory eight-byte Load candidates (`trust-ir-build`).**
  `Assembler::byte_load_eight` accepts the existing `ByteEightCodec`, an
  explicit pointer/address/current-memory/alignment input, and separate
  pointer, accessibility and initialized-word evidence. It shares the existing
  Store readback term constructor without changing that constructor's proof
  shape or operation charges. Canonical null is a supported loaded pointer
  value, not an accessible load address. These are untrusted proof candidates:
  consumers still check the actual fetched instruction, function metadata and
  complete closed claim through the kernel. No wire format, opcode, resource
  limit or native-execution admission rule changes.

- **`Formula::ConstArray`: the constant-size uniform array in the verifier
  vocabulary (`trust-ir-contract`).** The new variant is
  `ConstArray { index_sort, elem_sort, value }`, built with
  `Formula::const_array`. It is the array of sort
  `(Array index_sort elem_sort)` that maps every index to `value`, and it
  lowers to `((as const (Array I E)) v)`. With the existing `Select`/`Store`
  it lets a verifier state `[v; N]` with a term whose size does not depend
  on `N`, because `N` never occurs in it. Today the choice is `N` stores or a
  free base array, and the free base loses `v`. Both sorts are carried
  because SMT-LIB's `as const` needs the full array sort and a `Formula`
  has no sort inference, the same reason `Ctor`, `FnApp` and `FpToSbv`
  carry theirs. Splitting the sort into index and element means a
  non-array result sort cannot be represented. The variant is appended
  after `Rat`, so no existing variant index or JSON shape moves, and
  `size_of::<Formula>()` stays 112 bytes. `children`, `map_children`,
  `has_arrays`, `has_bitvectors` (the carried sorts count) and `to_smtlib`
  handle it. `Formula` is not on the trust-ir wire and has no Lean mirror,
  so there is no wire tag, version, digest domain or olean change. The
  opaque `trust-types.Formula@1` payload belongs to trust-types; a reader
  older than this variant refuses such a payload by name.
  `trust-ir-ay/tests/formula_const_array.rs` solves the emitted text with
  ay: a read of the constant array is its value at every index up to
  `u64::MAX`, a store over it overrides exactly one index, and the `[v; N]`
  seed proves lane `N - 1` for `N` up to 2^63 with the same statement each
  time. A test also shows that ay's in-process
  `Solver::const_array(index_sort, value)` agrees with the text. The
  Formula→ay bridge and the vcgen producer are in the superproject and
  switch in a later pin move.

- **The inline-only premise of `Linkage::AvailableExternally` is stated and
  has its must-refuse row.** A consumer MAY splice an `AvailableExternally`
  body into a direct call instead of calling the symbol (a runtime helper's
  fast path shipped beside its one out-of-line definition); doing so rests on
  the one-definition rule, which no module can check. A consumer that makes a
  proof claim must not splice such a body unless a `Module.imports`
  dependency authenticated by `Module::verify_import` exports a structurally
  equal definition, and keeps the call otherwise. It is a
  semantics-preservation premise, not a refusal, so the row is the `none`
  carrier `refuse/available_externally_inline_unauthenticated`. No wire,
  validator or IR-surface change. TrustCG consumes it in its JIT-path
  inliner (`prepare_jit_lir_module`, which withholds every inline-only body
  from a proof-producing compile).
- **`trust_ir::diff` sees every identity-bearing field; the diff tools are
  gated (roadmap WS4.13 remainder, closes F-073).** The proof channel now
  fingerprints every field it carries: a `ProofFormula`'s v41 `bindings`
  (each name's sort and IR place — a summary clause re-bound from parameter 0
  to 1, or width-stripped from `BitVec(64)` to `Int`, is a contract change
  with its text untouched), an obligation's v34 `site` (function by symbol,
  block by DFS visit index), a certificate's v41 coverage `assurance`, and a
  `CleanCic` payload's kernel re-check directive with its
  `CertificateBinding` (the island by its RECOMPUTED digest, so a stale
  stored digest cannot hide a changed island) — `kernel_recheck` was
  explicitly skipped before. `InheritedFromCallee` names its callee by symbol
  and its obligation by claim (a raw index made renumbering a spurious change
  and hid a retarget onto the old index), and so does a `ProofRef` annotation
  (review: it was rendered by raw index, so swapping two obligations' ids
  under an unchanged backref moved `stable_digest` and diffed EMPTY); an
  obligation scoped to no existing function no longer collapses onto the
  unscoped key; a clause's `Value` place resolves through the owning body's
  canonical walk. New module row `files`: the debug file table's LENGTH,
  never its strings — the portable V3 identity's own
  projection (WS4.10 / DG-16), so a checkout move is cosmetic and a file
  entering the table is not. A node's result ARITY is compared. Every
  metadata and proof-channel carrier the diff reads (the list in `diff.rs`'s
  module doc; the type tables keep their structural fingerprint) is
  destructured EXHAUSTIVELY where it is compared (the WS4.2 `text_loss`
  pattern), so a new field fails to build until it is classified, and the module doc's compared / ignored lists are rewritten to
  match. Gate legs: the new conformance target `diff_fields` (per-field
  positives, the renumbered / reordered / relocated negative twin, and a
  mutation control asserting that every `stable_digest`-moving single-field
  mutant — 139 of them over every field of every carrier the diff reads,
  each `ParamAttrs` field included, enumerated by the same token list that
  destructures each carrier exhaustively — diffs non-empty except the
  documented debug fields; the `CertificateBinding` / `SourceDefinitionRef` /
  `IslandEnvironment` fields, which have no binary carrier yet, are held to
  the same exhaustive inventory by their own diff-only mutants) and
  `diff_authority_metadata`, moved from `crates/trust-ir/tests`
  (which no gate runs, behind a cfg a feature-less run compiled to nothing),
  are on gate 8's registry; gate 3 now also runs `-p trust-ir-diff` and
  `-p trust-ir-fmt` wholesale. Ported audit rows: `scout-emit.F2`
  (`diff_fields`), `scout-lean.A4` and `crit.misw05`
  (`crates/trust-ir-diff/tests/f073_rows.rs`); the six
  `b1.gap.diff_blind_to_*` rows were already PASS in gate 11.

- **`trust-ir-fmt` and `trust-ir-diff` resolve their inputs by the ONE
  format rule the `trust-ir` CLI uses, and read all four formats (roadmap
  WS4.9 remainder).** The rule moves into core as
  `trust_ir::codec::resolve_module_format` (with `ModuleFormat`,
  `ModuleFormat::from_path` / `from_name` and the named `FormatRefusal`):
  an explicit `--format` wins, trustc's `.trust-ir.bin` / `.trust-ir.txt`
  suffixes resolve, a name the content's magic contradicts and a trust-cg
  `tMBC` container are refused BY NAME, and a name that says nothing takes
  the sniffed format. The CLI's `Format::resolve` now delegates to it with
  byte-identical messages. `trust-ir-fmt` gains `--format` and reads binary,
  JSON and MessagePack as well as text (a module text cannot carry is still
  refused with its loss list); `trust-ir-diff` gains `--format` and reads
  every transport on either side (a refusal is exit 2, never the
  differences-found 1). The resolver's table (positive rows, each refusal by
  its specific reason, and the `--format bin` mutation control that reaches
  the binary decoder instead of the named container refusal) is in gate 8's
  `sniff_format` target; the binaries' own tests are
  `crates/trust-ir-fmt/tests/formats.rs` and
  `crates/trust-ir-diff/tests/formats.rs`.

- **User theorems are certified in their ISLAND; a TV comparand is bound to
  its source declaration (roadmap WS1.13, slice 1; closes F-012 and the
  check half of F-008; DG-31 adopted as recommended).**
  `CertificateBinding` gains `environment: Option<IslandEnvironment
  { declarations, digest }>` (its sole trailing skipped serde field; `None`
  keeps every earlier certificate's meaning and bytes): the canonical,
  resource-bounded encoding of a Clean declaration closure
  (`encode_island_declarations_v1` / `decode_island_declarations_v1` —
  whole slice, byte / node / depth / declaration ceilings, canonical
  re-encoding) and its digest under the new domain
  `trust_ir.clean_cic.island.v1` (`island_declarations_digest`; reserved
  alone on main, flipped to landed here). The validator recomputes the
  digest before decoding, refuses a redeclared name (`island redeclares
  <name>`), a name under a validator-owned theorem root (`CleanTV`,
  `NNVerify`, `RustSem`, `TrustCg`, `Crownproof`: the kernel witness a spec
  `CleanTheorem` binding resolves against is keyed by name), an axiom or an
  opaque constant, and installs every declaration
  with the Clean kernel's checked `add_decl` on top of the `clean_backend_tv`
  anchor environment. New anchor `clean_island` (`Clean.Island`,
  `KERNEL_ANCHOR_CLEAN_ISLAND`) certifies only a
  `Custom { namespace: "lean.theorem", name }` row (namespace pinned in
  `ADMITTED_OBLIGATION_NAMESPACES`, owned by Clean), and such a row certifies
  through no other anchor: the cited island theorem passes the rooted audit
  and its type must be definitionally equal to the statement the new pinned
  grounder `trust_ir::clean_expr_lowering::island` derives from the row's own
  formula (slice 1: one equation, optionally under a `forall` of `Bool` /
  `(_ BitVec W)` binders, over island constants and `Nat` / `Bool`
  literals; an island constant, like a binder, is named only by a simple
  symbol no SMT-LIB theory spells as a function symbol or reserves as a
  symbol family — `fp`, `ubv_to_int`, `bv*`, `fp.*`, `str.*`, …). SYMBOL BRIDGE: every island constant the statement cites must be
  the `source.decl` of a function whose `clean_backend_tv` certificate carries
  the SAME island — so the theorem is about the code. F-008: an island-bound
  TV certificate's comparand must be definitionally equal to the value of
  `source.decl` in the island, so a certificate re-minted over a miscompiled
  comparand but keeping the island that declares the honest source is
  refused (a forger who rewrites the island too binds the code to THAT
  island, so no theorem about the honest one bridges to it; the island's link
  to the source text, `closure_digest`, is not re-derivable in-module) (and an island may not take the certificate's own
  `CleanTV.<fn>.denotes` theorem name); an island-free one keeps its mint-time meaning and is
  refused under the new `ValidationConfig::with_source_bound_certificates`
  knob (`CertificateBindingMismatch { field: "environment" }`); an island on
  the contract anchor is refused. Minters: `certify_island_theorem`,
  `certify_identity_lineage_rung_island_bound`. `kernel_certified_theorems`
  now witnesses island theorems, so a spec `ProofKind::CleanTheorem` binding
  can resolve against one. Slice 2 (a contract clause over IR places, and an
  island-bound CALLER) is refused by name. No binary wire change: the island
  rides in `CertificateBinding`, which the binary writer still refuses until
  the proof-surface wire batch — and
  `the_binary_writer_never_narrows_an_island_bound_certificate` requires that
  batch's carrier (the reserved v53 row) to round-trip `environment` exactly. Ratified in the internal spec ratifications
  §18 (and a §8 amendment naming the island bytes as the second admitted
  opaque payload); TRUST.md item 14. Ratchets flipped:
  `b3.gap.user_theorem_cannot_certify_contract`,
  `b3.gap.comparand_not_bound_to_source_definition`; Lean-home ports
  `LEAN.home.theorem_certified_tier`, `LEAN.home.kernel_only_theorems.populated`
  (format half). Tests: `crates/trust-ir-build/tests/island_theorem.rs`.
- **WS3.18: unions on the ratified byte-overlap carrier, with producer
  guidance and a refusal that names the carrier (F-050; F-030 companion).**
  DECIDE adopted (recommended): G18-3 is kept, and there is no `Ty::Union`.
  The Rust producer's measured 26-69 union-blocked bodies are the "new
  evidence" G18-3 asks for. What they show is a missing by-value move rule,
  not a missing type. `lowering-target-subset.md` "Unions" now records that
  population correction and six producer rules:
  (1) a union lives in a memory-only `Array(U8, N)` carrier, aligned on its
  `Alloca` or global;
  (2) a field place is the carrier base, with a typed `Load`/`Store` per
  access;
  (3) a by-value move is `MemCopy` between carriers, never a whole-carrier
  `Load`, which faults on the first uninitialised byte; a struct that
  contains a carrier moves the same way;
  (4) a union crosses a call edge by address: a `byval` + `pass: indirect`
  pointer to a copy the caller makes, or `sret` + `pass: indirect` for a
  result. A register lane cannot carry an uninitialised byte, because the
  interpreter refuses poison across a call boundary. A partially initialised
  union that the target classifies into registers therefore has no faithful
  spelling, and the producer must refuse that call site by name (a residual
  beside F-054);
  (5) padding stays padding (WS2.14);
  (6) the struct spelling of a union is refused by name.
  `StructLayoutInconsistent { reason: "fields overlap" }` keeps its reason,
  now exported as `STRUCT_FIELDS_OVERLAP_REASON`. Its rendered text appends
  `STRUCT_FIELDS_OVERLAP_CARRIER_HINT`, which names the carrier and the doc
  section, and the interpreter's overlapping-fields `TypeError` names them
  too. No wire change and no subset change. `MemCopy` stays excluded until
  its admission bump, so a by-value union move is off the proven path until
  then; the doc says so.
  Tests: `union_carrier` (gates 8 and 9). It ports the rows
  `goal-g1-g8/g1-unions` and the format half of
  `producer-rust-thir/union-type`:
  - field projection `bits(f32) -> u32` checked against `f32::to_bits`,
    subset-clean and admitted for codegen;
  - `MaybeUninit<[u8; 8]>` moved by `MemCopy` keeps its uninitialised bytes,
    and a stored pointer keeps its provenance;
  - `byval`/`sret` by-value passing, where the callee's write to its copy is
    invisible to the caller;
  - the register-lane residual;
  - exactly one named refusal from both `validate_module` and
    `validate_module_for_codegen`, pinned and target-free, with the rendered
    text pinned.

  Negative twins: a whole-carrier typed `Load` faults at offset 2, and a
  scalar read of never-written carrier bytes faults. Mutation controls:
  - a fully written carrier does move through an SSA `[u8; 8]`;
  - an unwritten FIELD byte faults at offset 0;
  - the padding round trip gives poison, never `0`;
  - a struct holding a partial union faults inside the carrier and moves by
    `MemCopy`;
  - `byval` on a non-pointer slot is refused by name;
  - the hint rides on the overlap reason only;
  - the disjoint twin runs.

  Ratchet flipped: `b6.union.overlapping_struct_fields_rejected` GAP -> PASS.
  It now asserts the named refusal and that both refusals point at the
  carrier. Ledger: 566 PASS / 35 GAP / 15 RATIFIED-OUT. The positive
  `build_rc_tree(3)` fixture is WS2.14's
  `b6.enum.fieldwise_init_uninit_padding_is_ub_on_load`. The producer half
  (tRust lowering union places onto the carrier) stays with WS5.17.

  Review (adversarial):
  - The guidance omitted that the move of rules 3 and 4 has no wire
    identity. `MemCopy` has no binary tag until the INST wire batch, so a
    module that moves a union by value has no binary encoding and no
    `stable_digest`, and every digest-keyed entry point refuses it by name
    (`ModuleHasNoWireIdentity`). The doc now says so under "Wire identity of
    the move". `a_union_move_has_no_wire_identity_until_the_inst_wire_batch`
    pins it on both rules' fixtures: the blocker names the `MemCopy`, the
    binary writer refuses it by name, and JSON, MessagePack and canonical
    text round-trip it exactly. The text-decoded move is also run, and it
    still keeps its uninitialised bytes. The control is the rules 1-2 module,
    which keeps its wire identity and computes the same bits after a binary
    round trip.
  - Rule 1's alignment clause is load-bearing, and a test now shows it.
    `an_under_aligned_carrier_faults_on_its_first_wide_access` puts a carrier
    without `align` after a 1-byte slot, and its first `u64` store faults as
    misaligned. With `align 8` the same body runs.
  - Rule 6 has no side door.
    `no_other_overlapping_aggregate_spells_a_union` shows that a declared
    tuple layout and a one-variant untagged enum with both fields at offset 0
    are refused too, and each has a disjoint twin that validates.
  - The "Correction to the record" paragraph credited the carrier lowering to
    "the shipped Rust-frontend". That lowering is this repo's
    workspace-excluded `frontend/src/mir_lower.rs`. The shipping tRust
    producer still refuses union places (WS5.17), and the paragraph now says
    so.
  - Rule 4's register-lane refusal now covers every union the producer
    cannot show to be fully written (`MaybeUninit<T>` included), not only a
    union it knows to be partial.
- **Text carries the proof surface (roadmap WS4.4; closes F-064, F-070,
  F-071 and the drafting finding NEW-1).** The canonical text format now
  spells, and the parser reads back EXACTLY, every proof-surface field it
  used to refuse as `#lossy` (WS4.2) or drop (before it): a function's
  `FunctionSummary` as one contiguous header block in a fixed order
  (`; #summary: proved|unproved params [..]`, one `; #requires:` /
  `; #ensures:` / `; #decreases:` line per clause, at most one
  `; #backed-by: extern <import> "<symbol>" (none | obligation N)`); typed
  clause bindings, in ONE formula spelling shared by module obligations,
  summary clauses and the v46 spec carrier (`formula "<schema>" "<payload>"
  [smtlib ..] [sort ..] [bind "<name>" <sort> <place>]*`, with `<sort>` in
  `bool | int | bv(N) | array(..) | float(EB, SB) | rm | datatype(..)` and
  `<place>` in `param(N) | result(N) | mut_exit(N) | world | unwind |
  value(%N) | spec_var(N) | spec_var_next(N)`); certificate `assurance`
  (`assurance unbounded|unwind(N)|model(N)|unrecorded digest ..`); the
  `clean_cic` kernel re-check directive (`recheck module .. anchor ..
  theorems [..] axioms [..]`, with its WS1.12a `binding env .. statement ..
  [origin ..] [source ..] callees [..]`, which text carries although the
  binary writer does not yet); the v41 obligation kinds `termination`,
  `ownership` and `custom("<ns>", "<name>")` (the diagnostic
  `custom:<ns>/<name>` is not module text and is refused); and the v46 typed
  spec carrier (`var .. sort <sort>`, `invariant .. typed formula ..`,
  `temporal "<name>" always|eventually|leads_to|weak_fair|strong_fair ..`).
  Every clause is printed only when present, so every module without these
  fields keeps its exact text; the five directives join the shared
  vocabulary (`text_directives::TEXT_DIRECTIVES`). The parser refuses a
  clause line with no preceding `#summary`, an out-of-order or split block,
  and a second `#summary` or `#backed-by`, each by name. The matching
  `TextLoss` variants stay for consumers of earlier reports:
  `CertificateAssurance`, `KernelRecheck` and `ObligationKind` are no longer
  reported, and `FunctionSummary` / `ClauseBindings` / `SpecCarrier` now fire
  only for a `ClauseSort` nested deeper than
  `text_loss::MAX_TEXT_CLAUSE_SORT_DEPTH` (64), the recursive-descent
  reader's cap. `TEXT_LOSS_RATCHET` is empty: every corpus fixture prints
  through `canonical_checked`, the `composition`, `spec_carrier` and
  `lean_library_envelope` goldens are loss-free texts (the kernel-Certified
  envelope re-certifies from text), and the new `proof_surface` fixture
  spells every clause kind, every function place, a `backed_by` citation, one
  obligation per v41 kind and one certificate per `CoverageBound`. The
  obligation digest is unchanged: `format::canonical_function` renders the
  function WITHOUT its summary block, because the digest encodes the clauses
  itself and deliberately excludes `proved` and `backed_by`. Ratchet flips
  (GAP → PASS, `RATCHETS.tsv`): `b2.roundtrip.text.measured`,
  `b2.gap.text_cannot_parse_v41_obligation_kinds`,
  `b2.gap.text_drops_function_summary_and_bindings`,
  `b2.gap.text_drops_obligation_bindings_and_certificate_assurance`,
  `b3.gap.text_drops_kernel_recheck` (its `.sole_cause_control` is now the
  roadmap's mutation control: the `recheck` clause cut from the printed text
  fails `CertifiedCleanCicKernelRecheckFailed`),
  `b3.envelope.gap.text_cannot_parse_theorem_ref_kind`,
  `b3.envelope.gap.text_drops_kernel_recheck`,
  `b4.gap.text_drops_backed_by`, `b7.text.drops_function_summary`,
  `b7.text.drops_clause_bindings` and
  `b7.text.refuses_obligation_kind.{termination,ownership,custom}`; the
  interim PASS rows `b7.text.flip.unauthenticated_import_laundered` and
  `b7.text.flip.certified_becomes_invalid` now assert the closure (the
  authority-tier refusal and the certification SURVIVE text), as do the
  ported `verify.c08` rows (`c08_flipped_*`). The must-refuse manifest's
  `text_losses` cells for `import_backed_summary_unauthenticated`,
  `custom_obligation_unpinned_namespace`,
  `summary_clause_smtlib_rendering_disagrees` and
  `spec_carrier_smtlib_rendering_disagrees` shrink to `-`.
- **NEW-1: canonicalization carries `ClausePlace::Value` bindings with the
  SSA renumbering, and every obligation binding is validated.** Before
  WS4.4 `format::canonicalize` / `into_canonical` renumbered a function's
  SSA values and NOT the bindings that name them, so a binding dangled or —
  worse — named whichever value took its old number. `into_canonical` now
  remaps the `Value` bindings of the function's own summary clauses and of
  every module obligation whose `function` scope (else its `site`'s
  function) is that function; a binding naming a value the function does not
  define is moved OUTSIDE the renumbered range, never rebound, so it stays
  refused. The streamed canonical binary projection writes the bindings
  through the same plan, so it stays byte-identical to the image of the
  materialized canonical module, and the executable-content identity stays
  invariant under canonicalization. Bindings are inside the v6 CleanCic
  lineage, so a certificate bound before canonicalization no longer matches
  the remapped row and is refused by name
  (`CertifiedCleanCicLineageMismatch`) — the fail-closed outcome. The
  validator's second half: `InvalidObligationBinding` (until now raised only
  for spec-variable places) resolves EVERY module-obligation binding against
  the owning function exactly as `validate_function_summary` resolves a
  summary clause — `Param` / `MutParamExit` / `ResultSlot` in range,
  `MutParamExit` only on a `Postcondition` or `GiveBackRefinement`, `Unwind`
  never on a `Precondition`, a `Value` the owning function defines (never on
  a body-less declaration), a sort that faithfully reads the place's IR type,
  no blank or repeated name — and an obligation with neither scope may bind
  only `World`. Producer impact measured for the pin train (review,
  2026-09-27, on each producer's `origin/main`): trust (`trust-ir-bridge`)
  mints no clause bindings at all; Clean's translation-validation rows bind
  `Param` places on a FUNCTION-SCOPED obligation (`function: Some(fid)`),
  which this rule resolves and admits; trust-cg mints none — its OPT-6b
  bounds discharge (the `trust-cg.bridge-bounds-dominated@1` row, an
  UNSCOPED `MemorySafety` obligation binding a `Value`, which this rule
  refuses) was measured on the stale primary checkout `5aca5cd4d` and is
  gone from trust-cg `origin/main` since `9c523812f`. Tests:
  `validation_holes/ws4_4_obligation_bindings.rs` (gate 9), including the
  roadmap row `ws4_new1_obligation_binding_unvalidated` born flipped.
- **WS4.4 review: NEW-1 in the cert-cache key, and the WS1.13 island in
  text.** `Module::obligation_digest` hashed the owning function as its
  CANONICAL text but a `ClausePlace::Value` binding (of the obligation's
  formula or of a summary clause) by its RAW id, so two functions with one
  canonical text whose `%9` named different values — the `const` result in
  one, the parameter in the other — shared a cache slot for `(= r 1)` (a
  stale HIT, the direction the identity contract rules out), while
  renumbering a function together with its binding moved the slot. The
  digest now writes a `Value` binding through the owning function's canonical
  plan (`FunctionCanonicalPlan::map_binding_value`, the `into_canonical`
  rewrite), so the key follows the value, not its number: canonicalization
  keeps the slot and a re-pointed binding gets a new one. The layout and the
  `trust_ir.obligation.digest.v7` domain are unchanged, and so is every
  digest of a row without a `Value` binding in a non-canonical function (the
  known-answer pins hold); no producer on trust, clean or trust-cg
  `origin/main` mints a `Value` place, so no persisted key carries one.
  Tests: `obligation_digest.rs` section (6), stale hit / renumbering /
  dangling. The
  kernel re-check directive's WS1.12a binding gained WS1.13's
  `environment` (the island) on main after this increment was drafted, so
  text now spells it too: `... callees [..] island [<byte>, ..] <digest>`,
  the digest AS STORED (the validator recomputes it from the bytes and
  refuses a mismatch; the reader never repairs one). Review twins: malformed
  sort / place / coverage bound / recheck order / island, and a `bind`
  pushed onto the next line, are each a named `ParseError`; the obligation
  binding rule's remaining places on an unscoped row, `MutParamExit` on a
  by-value parameter and on each v41 kind, and a `Value` defined only by
  another function are each refused by name. A formula's trailing clauses
  (`smtlib`, `sort`, `bind`) are now matched on the formula's OWN line: the
  `smtlib` / `sort` probes crossed the newline, so a `sort` or `bind` line
  below an obligation was silently read as ITS clause instead of being
  refused as an unknown directive (found by the next-line `bind` twin). The
  increment's own tests had not run before review; running them against
  current `main` found (and this review fixes, without relaxing any rule)
  fixtures the validator now refuses — a `&mut` parameter's entry value
  bound as `param(0)` at `bv(64)` (no sort reads a reference), body-less
  declarations without a pinned target (`TargetInfoRequired`, so
  `proof_surface` now pins `aarch64-apple-darwin`), a site-scoped
  `MemorySafety` row on a `const` (WS1.8 rule (c)) — and b2/b7 twins whose
  exact verdicts gained the new rule's named refusal: re-scoping or re-sorting
  a bound obligation now ALSO draws `InvalidObligationBinding`, which each
  twin requires by name beside the refusal it measures; and deleting a
  declaration's `#backed-by` line no longer launders the module to an empty
  verdict (main's body-less-declaration rule refuses the unbacked `proved`
  summary), which the b7 mutation control now asserts.
- **Binary wire v61: the proof-surface identity carriers WS1.12 deferred
  (roadmap WS6.7(b)) — the certificate binding and license evidence.** `CleanCicKernelRecheck.binding` now has a
  binary encoding: a presence byte after the directive's `allowed_axioms`,
  then the `CertificateBinding` in struct order (environment and statement
  digests, presence-prefixed `origin_module` and `source`, the `callees`
  symbols, and the presence-prefixed WS1.13 island — its declaration bytes
  opaque and length-framed, its recorded digest verbatim, neither decoded nor
  recomputed by the reader). Read-gated `version >= 61` (an older blob decodes every directive
  unbound; an undefined presence tag is `InvalidTag`), selected only for a
  module that carries a binding (every all-unbound module keeps its bytes),
  refused by the explicit v38 projections as `CertificateBindingRequiresV61`.
  A bound module therefore HAS a wire identity: `wire_identity_blocker`, the
  linked walk, the native-bundle envelope and validator, and the CLI's
  `convert --to bin` / `digest` carry it instead of refusing it, and the
  retired `CertificateBindingUnencodable` / `CERTIFICATE_BINDING_UNENCODABLE_MESSAGE`
  refusal is gone — no path ever narrowed a binding to `None`, and none does
  now. New golden `certificate_binding` (two bound `clean_backend_tv`
  certificates with every binding field but the WS1.13 island populated —
  the island's bytes are pinned by a binary unit test and the real-island
  round trip in `island_theorem.rs` — and evidenced licenses;
  validates under the bound-certificate and gate-evidence policies, and is
  the only golden whose header word is the carrier's version). This is what
  lets Clean mint bound TV certificates by default.
- **License evidence (WS1.12(c), wire v61 body-gate tag 3).**
  `BodyGate::Gated` gains `evidence: Option<GateEvidence { obligation,
  body_digest }>`; `Module::function_body_digest` (domain
  `trust_ir.function.body.v1`) is the executable projection of a module
  holding only the function, so stamping a license never moves the digest it
  cites. Its drop-glue table is exactly the rows the body's `Drop` /
  `DropInvoke` sites resolve to (amendment D, "Body digest"; ruling WA-3,
  SPEC §20): re-pointing, removing or registering the glue one of its drops
  calls moves the digest, a row the body does not resolve through does not,
  and a drop through a malformed table (a type two rows name, one glue for
  two of its types) leaves the body with no digest. A PRESENT evidence is checked on every lane (`GatedEvidenceMismatch`:
  the cited row must be the function's `Certified` TranslationValidation row
  and the digest must recompute), and `ValidationConfig::with_gate_evidence`
  refuses an evidence-bound license with none (`UnevidencedGate`). The text
  format spells it `gated "<authority>" evidence #<obligation> "<digest>"`.
  The CLI linker keeps a license's authority and DROPS its evidence (its
  image carries no proof claims and renumbers callees). The body digest is
  taken over the CANONICAL image, so `format::canonicalize` keeps evidence
  valid; a transform that changes that image drops the evidence and keeps the
  license (`Function::invalidate_gate_evidence`, called by mem2reg and dialect
  lowering beside their source-provenance invalidation). A proof-row
  projection that omits the row a license's evidence cites is refused
  (`RetainedReference { location: "codegen license evidence" }`), and the
  semantic diff renders evidence by the cited obligation's claim and whether
  the digest still holds, so renumbering alone reports no change. API change:
  every `BodyGate::Gated { authority }` construction gains `evidence` (or use
  `BodyGate::gated(authority)`), and patterns need `..`.

- **Proved contracts on the validator's pure decision tables (KIND 5), and
  the verified lane that holds them.** New leaf crate `trust-ir-laws`
  (depends on trust-ir only) now defines `coverage_supports` — L9's coverage
  order, moved from `trust-ir-build::linked` verbatim and re-exported there at
  its old path — and `license_admits_body`, the codegen-license ADMISSION
  table that `license_errors_against` now routes through (with
  `UnlicensedBodyPolicy`, moved and re-exported at its old paths, and the new
  `GateShape` projection of `Option<&BodyGate>`). Every row of both English
  tables is a `pub fn` wrapper in `crates/trust-ir-laws/src/laws.rs` carrying
  a Trust `ensures` contract (26 laws: reflexivity, `Unbounded` supplies all,
  same-axis magnitude order as `result == (have >= need)`, cross-axis
  incomparability and no-bounded-rung-supplies-`Unbounded` universally over
  the `u64` payloads, `Unrecorded` as supply vs as demand including the one
  enum-quantified statement that folds, the integer half of transitivity;
  gated-admitted / ungated-refused under any policy, absent refused under
  `Refuse`, absent admitted under `Permit`). Standing gate 13
  `verified-contracts` (`scripts/verified_contracts.py`) runs `targo trust
  check --release -p trust-ir-laws` — the one lane in this repo with Trust's
  verification pass ON — and requires per row: strict gate green, every law
  `proved` with `assurance Certified` and `grade.validation KernelRechecked`
  (Clean-kernel re-checked), and four same-shape mutants (`UnwindBounded`
  supplying `ModelBounded` in place of the `Unbounded` arm; `have > need` on
  the unwind arm; admitting `(Absent, Refuse)`; admitting `Ungated`) each
  refuted on exactly the laws it breaks — a non-zero exit, the runner's
  `refuted obligation` line naming each falsified law, every untouched law
  still proved. The module is compiled only under `cfg(trust_verify)`, which
  trustc sets by itself when verification is on, so stock rustc and the
  `--unverified` gates never parse the contract grammar; `rust-toolchain.toml`
  is unchanged and no RUSTFLAGS or Cargo config is added. Honest limits, on
  the crate: verdicts are about OPTIMIZED MIR (the laws are wrappers the
  inliner fills with the table's body; a body one arm heavier is declined and
  fails closed UNKNOWN, which is why the gate is per row and its mutants are
  same-shape); refutations are published as UNKNOWN; L8 transitivity, the
  enum-quantified `Unbounded`-supplies-all form and the `#[non_exhaustive]`
  unknown-variant row are NOT proved rows. Measured NOT provable in the same
  lane and left as English tables with a note: `HandleTy::validate`'s lexical
  rules (`str::chars` / closures / `split` are `unsupported MIR`) and
  `is_admitted_obligation_namespace` (`<[&str]>::contains` lowers to an
  invalid native solve input); an enum-valued license verdict (12/12 rows
  unknown in every spelling — hence the `bool` projection, with the
  two-refusals-are-different-values half staying tested). API residue:
  `UnlicensedBodyPolicy` no longer derives `Debug`/`Hash` (each is an
  unsupported row that would turn the crate's strict gate red for a
  non-law reason; `name()` renders it), and `CodegenAdmission`'s `Debug`
  prints the policy by name. No wire change: `VERSION` 46, goldens
  byte-identical.

- **Gate 13's mutation controls cover EVERY law, and the gate refuses a law
  none covers.** Review of KIND 5 measured that its four mutants flipped 6 of
  the 26 laws, so for the other 20 the gate could not tell a wrapper that
  stopped calling its table from one that proved something (`ensures result
  == false` over a body of `false` proves). `scripts/verified_contracts.py`
  now carries 14 same-shape mutants — the four above plus `Unrecorded`
  supplying each positive grade in place of the `Unbounded` arm (three
  mutants), `ModelBounded` supplying `UnwindBounded`, `have > need` on the
  model arm, the `Unrecorded` demand narrowed to one supplier, the wildcard
  column moved from the `Unrecorded` demand to the `Unbounded` one (nine
  flips at once, every one measured), `a > c` in the integer half of
  transitivity, `Gated` refused, and `(Absent, Permit)` refused — and
  `laws_without_a_mutant` must be empty before any run (measured
  2026-09-25: base 26/26 proved, all 14 mutants exit 1 with every falsified
  law named by the runner's `refuted obligation` line and every untouched
  law still proved). Also: `frontend/Cargo.lock` (the workspace-excluded leg
  gate 7 cannot see) records `trust-ir-laws`, so `--locked` commands in
  `frontend/` resolve again (they were refused since KIND 5 added the
  dependency to `trust-ir-build`).

- **The must-refuse corpus (KIND 4: a "consumer MUST refuse" sentence names
  a wire artifact).** `crates/trust-ir-conformance/tests/fixtures/refuse/`
  holds 43 byte-pinned artifacts a conforming consumer must refuse — codegen
  license and lowerability refusals (`Ungated`, unknown / evidence-less /
  refuted authorities, `global_asm`, `Dealloc`, sequence element ops, foreign
  dialect ops, unbacked claims on checks), the authority lane
  (`UnauthenticatedImport`), completeness, structural canaries, seven
  consumer-relative rows that are well-formed by every trust-ir rule and that
  a native backend must still refuse (`Unclassified` struct passing beside a
  by-value aggregate, unrecorded narrow-slot extension, `CUnwind`, unknown
  target features, the two havoc markers, an unsigned wide-lane vector
  compare), the faith-stamped `Trusted` row, and eleven poisoned byte strings
  the reader refuses — each paired in `MANIFEST.tsv` with the trust-ir verdict
  that names why, at a named entry point, with its exact text-loss set and the
  document stating the obligation; eleven `none` rows record obligations the
  corpus cannot express, and the document says so with its honest rung.
  `tests/refuse_corpus.rs` runs every pinned verdict on the module decoded
  from the checked-in bytes (gates `wire-format-goldens` and
  `validator-fail-closed`). Consumers run it through the new library module
  `trust_ir_conformance::refuse` (feature `must-refuse`, forwards only
  `trust-ir/binary`): `corpus()`, `Report::run`, `assert_every_row_refused`,
  `uncovered`. Exhaustiveness is over the enum sources: every
  `ValidationError` / `BinaryError` variant is exhibited by a row or listed in
  the exact, shrink-only `UNCOVERED.tsv` (a new variant lands with a row or
  not at all); `ValidationError` is `#[non_exhaustive]`, so the type-level
  form is out of reach from this crate and this is stated as test-rung
  evidence. `scripts/check_enforcement_links.py` gains the `(corpus)` class,
  `refuse/<row>` citations and rule R (manifest and document cite each other);
  three `ValidationError` variants no test named (`DuplicateEnumId`,
  `FuncTypeNotFound`, `PointerOpInvalid`) are named now. Measured along the
  way: `BinaryError::UnexpectedEof` is unreachable by construction
  (`reserve_checked` reports every short input as `TooLarge` first), and a
  declared tuple layout that is incoherent or target-less is refused by the
  binary READER before the validator can see it, so `TupleLayoutInconsistent`
  is reachable only for a hand-built or serde-decoded module. Ratified as
  `docs/SPEC_RATIFICATIONS.md` §16. Review-fixed before landing: the runner
  is reason-blind (`Ok`/`Err`), and every non-license module row wears the
  structural license `trust-direct-lane-structural`, which is in no default
  recognized set — so under a production set most module rows were refused
  for the license alone (for every consumer-relative row, the `Trusted`
  census row, the completeness row and the unbacked-claim row it was the
  ONLY refusal) and "refuse everything" passed. The `control` carrier
  (`refuse/control_licensed_identity`, the shared envelope with no subject)
  must be ACCEPTED, `Report::assert_every_row_refused` fails by name while it
  is refused, and `refuse::STRUCTURAL_LICENSE_AUTHORITY` names what a consumer
  recognizes for the run; `no_module_row_is_refused_for_the_structural_license_alone`
  pins that under that set only a foreign-authority row is refused for its
  license. The git-backed shrink check now distinguishes a merge-base behind
  an `origin/main` that carries the allowlist (a failure) from the two states
  git cannot decide (skipped, by name), with the rule proved on a fake git;
  it is live from the commit after this one. The narrow-slot row now records
  a `ParamAttrs` slot per parameter, and its trigger requires them.
- **Input coverage is derived by the consumer, never read off a producer
  row.** `trust_ir_build::coverage_establishment_report(bundle, CoverageInputs)`
  judges each certificate `Established { bound, basis }`, `Undetermined
  { reason }` or `Refused(ValidationError)` (any refusal is fatal for the
  bundle). Basis K: the consumer's own kernel replay of exactly that
  certificate (`NativeVerificationBundle::kernel_replayed_certificates`), of a
  classified `KernelClaimFamily` — only `ContractGroundDecision` maps to
  `Unbounded` (`bound_established_by_kernel_claim`); a family arrives
  unclassified (`ModuleProofAuthority::replayed_claim_family` and
  `ModuleCleanCicRechecker::rechecked_claim_family` default to `None`). Basis
  R: a row of the sealed `trust_ir::request::NativeCoverageAttestation`
  (digest domain `trust_ir.native.coverage.attestation.v1`, outside every
  module / request / evidence / bundle digest) cites a solver result by
  digest; the consumer recomputes every digest, resolves the result bytes,
  refuses executable-content or claim drift between the solved and the
  admitted module, and has a `NativeCoverageResultReplay` implementation
  re-verify the result; the bound is `bound_established_by_replayed_result`
  of the request's mode and the replayed strength, which must agree. Fifteen
  `Coverage*` `ValidationError` variants name the refusals. The in-module
  `ProofCertificate::assurance` row is non-authoritative: a row claiming more
  than the derived bound refuses the bundle, any other is ignored. New
  default feature `coverage-attestation` (`trust-ir/fmt`, for
  `Module::obligation_digest`). `coverage_assurance_report` is
  `#[deprecated]` (it derived coverage from a request's mode — a pending CHC
  request with no evidence "agreed" with an `Unbounded` row — and a row citing
  a module-bound request has no fixed point); it stays until trust-vc and
  Trust stop calling it. Tests: `trust-ir-build/tests/coverage_establishment.rs`.

- **Basis R is per obligation, binds the whole replay context, and maps only
  machine-semantics requests to a bound (coverage round 2).** Four findings
  of the adversarial verdict on the first cut, each closed at its root. (P1)
  The solved-to-admitted transfer compared executable content and the cited
  obligation's own claim only, so a result resting on an assumed
  `Precondition` stayed `Established` on a module that dropped it; the row
  now carries `solved_replay_context_digest` —
  `NativeVerificationBundle::coverage_replay_context_digest` (`fmt`; domain
  `trust_ir.native.coverage.replay_context.v1`: executable content, every
  obligation's (id, claim digest), the compiler facts; statuses,
  certificates and diagnostics excluded, so an honest write-back keeps it) —
  which the solved bundle AND the admitted bundle must recompute
  (`ValidationError::CoverageClaimDrift`, "the replay context drifted"),
  and the
  `NativeCoverageResultReplay` contract confines `Ok` to that context. (P4) A
  row named a certificate the result did not bind, so a `Trusted`
  certificate read as `Established`; rows now name NO certificate
  (attestation schema 2, domain `trust_ir.native.coverage.attestation.v2`;
  v1 is burned and refused), basis R is reported by
  `CoverageEstablishmentReport::for_obligation` as `ObligationCoverage` /
  `VerifiedSolverResult`, and `CoverageBasis` has no solver-result variant,
  so a certificate verdict cannot carry one; a certificate's in-module row
  is judged against its own basis-K bound only. `CoverageCertificateNotCited`
  is gone; `CoverageAttestationRowDuplicate` keys on (obligation, solved
  bundle, request). (P5) `bound_established_by_replayed_result` now returns
  `Result<Option<CoverageBound>, _>`: `None` (undetermined,
  `RequestNotMachineSemantics`) unless `request_machine_semantics_divergence`
  — exhaustive over every option field and value, no wildcard — finds the
  options mean exactly the machine semantics (TrustMc `TrustIrPlaces`,
  `FixedWidthBitvectors`, invariant source `None`/`TrustIrProofObligations`;
  TrustWp `TrustIrMemory`, `PanicFreeRequired`, no abduced preconditions).
  (P2, P3) The solved-module `Failed` branch and both wire-identity branches
  have committed negative controls. Tests: the same target.

- **A basis-R replay may assume nothing the consumer does not bind and check
  (coverage round 3).** Findings of the adversarial verdict on round 2, each
  closed by the simplest rule that cannot be evaded. (P-A) The REQUEST's
  replay atoms were an unbound premise: an `Assumption` atom the module never
  states, or an `Assertion` atom whose formula is not its obligation's claim,
  ESTABLISHED. Now `request_machine_semantics_divergence` reads
  `provenance.replay_context` (destructured with no `..`): an `Assumption`
  atom or an unsupported-mode entry derives no bound (undetermined,
  `RequestNotMachineSemantics`), and an `Assertion` atom that does not state
  EXACTLY the formula of the obligation it cites — the row's or a sibling's —
  refuses the bundle (`CoverageClaimDrift`, "the request's Assertion atom").
  (P-D) A clean-expr `ProofAnnotation::Goal` is in no wire image, and the v1
  context was an enumerated list, so anything not on it was unbound by
  omission. The default is REVERSED: `coverage_replay_context_digest` (domain
  `trust_ir.native.coverage.replay_context.v2`; v1 burned) hashes the WHOLE
  bundle's stable digest, module by wire identity, with only an explicit
  write-back allowlist erased — obligation statuses, the certificate table,
  the obligation diagnostics, and the carriers bound to the module digest a
  write-back moves (`trust_ir_module_digest` recomputed, lineage, requests,
  evidence bundles). The erasure destructures the bundle, module, function
  and obligation with no `..`, so a new field is a compile error until
  classified and "bound" is the default. It now returns
  `Result<_, NativeReplayContextUnavailable>`: `Unindexable` is refused as
  before, `UnboundGoal` (a Goal on either side) is undetermined
  (`GoalAnnotationUnbound`). (P-E) `NativeReplayedResult` gains `premises`:
  the obligations whose claims the result ASSUMED, which the replay contract
  (clause 6) requires it to name. A named premise that is `Failed` in either
  module refuses (`CoverageContradicted`), one the module does not state
  refuses (`CoverageResultReplayInvalid`), and the result is established only
  when every premise is itself established `Unbounded` in the same report (by
  basis K or another verified result), as a least fixed point — an
  assumption cycle never is (`PremiseNotEstablished`); `VerifiedSolverResult`
  names the premises. (P-B, P-C, P-F) The unindexable-context refusals, the
  refusal-wins merge, sibling-obligation renumbering, the evidence's own
  request match (the r2 survivor M11) and a relabelled row (ADV-R2-6/7) have
  committed negative controls. The report digests each candidate bundle's
  executable content and replay context ONCE (it recomputed both per row,
  the context by cloning the whole bundle); a two-row drift test holds each
  row to its own bundle's digests. No new `ValidationError` variant;
  attestation schema 2 unchanged. Tests: the same target.

- **An undetermined reason never masks a refusal (coverage round 4).** The
  adversarial verdict on 89957e87 measured a lost refusal. `transfer_check`
  returned `GoalAnnotationUnbound` as soon as EITHER bundle carried a
  clean-expr `Goal` — on any function, an unrelated one included, so no claim
  digest moved — before comparing the solved context with the row's citation,
  and `establish_row` returned it before the replay, the premise checks and
  the mode/strength check. A forged `solved_replay_context_digest`, or a
  result the replay finds invalid, was then Undetermined with `refusals()`
  EMPTY, so the bundle was admitted on its kernel-replayed certificate
  (b13f9d76 refused the same bundle). Now the transfer's undetermined reason
  is carried to the end of the row: the solved context is held to the row's
  citation whenever it recomputes, every later check that can refuse runs, and
  the first undetermined reason is the verdict only when none refuses (a
  missing replayer or an inconclusive replay still ends the row: nothing after
  them can run). The same rule moves `ObligationNotModeled` after the
  mode/strength check and runs the replay in a build without
  `coverage-attestation` (`ClaimDigestUnavailable`). Only refusals are added:
  no undetermined reason changes and nothing new is Established. Tests: the
  same target (`*_masks_no_*`, `an_unbound_goal_is_the_first_undetermined_reason`,
  and `attestation_without_claim_digest_is_undetermined` in the
  claim-digest-less build).

- **One formula text; every cited context digest checked (coverage round 5).**
  Three verdicts on 794227ad. (ONE FORMULA, a false admission measured
  end-to-end through trust-vc 59cf71c8) The contract grounder read
  `formula.smtlib.unwrap_or(&formula.payload)` whatever the schema, so a
  certificate replaying a TRUE `smtlib` rendering was kernel-replayed,
  `ContractGroundDecision`, `Established{Unbounded}` and release-admitted for
  an obligation whose `smtlib2` payload `(>= 0 5)` is FALSE, and an opaque
  `trust-types.Formula@1` payload was grounded as SMT-LIB. Now
  `ProofFormula::smtlib_text` is the obligation's ONE SMT-LIB text (an
  `smtlib2` payload whose rendering, if any, is that payload; nothing for any
  other schema), the grounder and the minter read only it,
  `kernel_replayed_certificates` admits a replay only when the text it grounded
  (`ModuleProofAuthority::replayed_claim_text`, new, default `None`) IS that
  text, and both validators refuse an `smtlib2` formula whose rendering
  differs (`ValidationError::ObligationFormulaTextsDisagree`,
  `NativeVerificationBundleError::ObligationFormulaTextsDisagree`; must-refuse
  row `refuse/formula_smtlib_rendering_disagrees`). (GOALDRIFT) A Goal on an
  unrelated function still hid a context DRIFT, and with a Goal on the solved
  side the row's cited context digest was checked against nothing:
  `coverage_replay_context_digest` now always computes the digest of
  everything a wire image binds and names a Goal outside it
  (`NativeReplayContextDigest { digest, unbound_goal }`;
  `NativeReplayContextUnavailable::UnboundGoal` is gone), and both sides are
  held to the row before a Goal can withhold the transfer. A producer cites
  that digest also when a Goal is present. (FEATURELESS) The optional
  `coverage-attestation` feature is removed — `trust-ir/fmt` is a plain
  dependency of `trust-ir-build` — so every build recomputes the claim and
  context digests and refuses a forgery of either (its doc claimed so; a
  build without it left them Undetermined); `ClaimDigestUnavailable` is gone
  with it. Tests: `a_replay_grounds_only_the_obligations_one_formula_text`,
  `two_formula_texts_are_refused_by_both_validators`,
  `a_goal_masks_no_context_drift`, `a_goal_leaves_no_cited_context_digest_unchecked`,
  `every_build_refuses_a_forged_claim_or_context_digest`.

- **One formula text wherever a formula is stated (coverage round 6).** The
  round-5 rule held only an OBLIGATION's formula. The spec linker's S3 still
  read a typed carrier's `smtlib` rendering whatever its schema and skipped a
  carrier with none, so a Linked machine whose string invariant is
  `(<= seq 7)` CERTIFIED beside a carrier whose `smtlib2` payload is
  `(<= seq 8)`; the bit-blast route's `formula_matches_goal` matched an opaque
  payload on its rendering alone, so a row whose payload states another claim
  was Discharged and accepted by `BvBlastAuthority`; and a summary clause, a
  spec carrier or a replay atom could state two texts past both validators.
  Now `Module::stated_formulas` (with `FormulaSite`) is the one walk both
  validators run: `ValidationError::FormulaTextsDisagree { site }` and
  `NativeVerificationBundleError::FormulaTextsDisagree { site }` replace the
  `ObligationFormulaTextsDisagree` variants, and a replay atom is refused as
  `InvalidReplayAtom { field: "formula.smtlib" }` (must-refuse rows
  `refuse/summary_clause_smtlib_rendering_disagrees` and
  `refuse/spec_carrier_smtlib_rendering_disagrees`). S3 reads only
  `ProofFormula::smtlib_text` and refuses a Linked carrier that states no one
  text (an opaque schema) or two. `formula_matches_goal` matches only the one
  text: an opaque schema never matches, and an `smtlib2` payload that IS the
  goal matches with or without a rendering. Removed: the round-5
  `ModuleProofAuthority::replayed_claim_text` /
  `ModuleCleanCicRechecker::rechecked_claim_text` / `contract_claim_text`
  binding, which compared the grounder's text with itself (an equivalent
  mutant under the fixed grounder); `kernel_replayed_certificates` now skips
  an obligation that states no one text, a check that does not go through the
  grounder. Tests: `a_linked_typed_carrier_is_read_by_its_one_formula_text`,
  `every_formula_a_module_states_is_held_to_one_text`,
  `the_nonneg_family_grounds_only_the_one_formula_text`,
  `only_the_one_formula_text_is_matched_to_the_site_goal`.

- **One formula text in every schema trust-ir owns; one SMT-LIB2 reader
  (coverage round 7).** The round-6 rule held only `smtlib2`. A
  `trust-ir.Pred@1` citation (`pred.0` = `(and (<= 1 self) (<= self 8))`)
  beside the rendering `true`, a citation of no predicate beside a rendering,
  and a claim schema (bit-blast goal, SAT refutation, lineage binding) beside
  any rendering all validated in both validators. New registry
  `proof::OwnedFormulaSchema` (`smtlib2`, `trust-ir.Pred@1`,
  `trust-ir.bvblast.goal.v1`, `trust-ir.satres.cnf.v2`,
  `trust-ir.ProofLineageTransformBinding@1`), matched with no wildcard;
  `ProofFormula::owned_text` / `ProofFormula::states_two_texts` (which replaces
  `smtlib_rendering_disagrees`) decide the one text per schema, a `pred.N`
  citation against the module's predicate table. Both validators, the replay
  atoms and the spec linker's S3 (which now names why a Pred or claim carrier
  is no predicate over the machine's state) decide it the same way; an
  unowned schema is never compared and never grounded. The registry is derived
  by `tests/formula_schema_census.rs` from the sources and
  `wire-allocations.toml`. Must-refuse row
  `refuse/pred_citation_rendering_disagrees`. And the contract grounder, the
  clause free-name reader (`smt_free_symbols`) and the Linked spec surface now
  read formula text through ONE reader, `proof::read_smtlib_term`
  (`proof::smtlib_source`): SMT-LIB2 whitespace only, SMT-LIB2 tokens only
  (`x'` and `007` are none), no string, quoted symbol or comment, depth
  bounded. The grounder used to split on `char::is_whitespace` and take any
  run of characters as an atom, so `(>=\u{3000}5\u{3000}0)`, VT/FF/NBSP/NEL
  spacings, `(>= 5 00)` and a nonneg clause over `x'` were kernel-replayed and
  Established{Unbounded}, and `()` panicked the grounder (`&items[1..]` of an
  empty list). The free-name grammar drops `'`: a `&mut` exit value is a
  `MutParamExit` binding under a plain name (`p_exit`).
  `kernel_replayed_certificates` replays a classified certificate once (it
  replayed each twice). Tests: `every_owned_schema_is_held_to_its_one_text`,
  `a_replay_grounds_only_smtlib2_source`,
  `a_linked_carrier_states_its_predicate_only_as_smtlib2_source`,
  `every_linked_temporal_leaf_is_read_by_its_one_text`,
  `every_formula_schema_trust_ir_spells_is_registered`,
  `every_versioned_owned_schema_is_a_landed_wire_row_and_back`.

- **Round 7's one-text check costs no more than the text it is handed, and
  the contract grounder grounds only what the one reader reads (coverage
  round 11).** Four findings, each measured on the round-7 tree and pinned by
  a test that fails there. (1) The one-text check rendered a
  `trust-ir.Pred@1` citation whole before comparing it with the formula's
  `smtlib` rendering, and the predicate DAG's rendering is not shared: the
  validator-legal table `pred.k = Conj([k-2, k-1])` renders `pred.k` to
  fib(k) leaves — 41.8 MB and ~1 s per validator at 31 entries, ~5·10^14
  bytes for `pred.64` (the depth cap) beside `smtlib = "true"`.
  `PredTable::smtlib_of_within` renders no further than a byte budget, and
  `states_two_texts` renders a citation no further than the rendering in
  hand (a longer text is not it). (2) A nonneg clause's free name may not be
  a function symbol of the theories the Linked surface draws on:
  `(>= and 0)` bound `and` -> a u64 param was minted, kernel-replayed and
  Established (so were `or`, `xor`, `not`, `ite`, `distinct`, `div`, `mod`,
  `abs`, `bvadd`, `bvnot`, `concat`), although the surface refuses each as a
  variable (`spec_surface::linked_var_name_problem`, which the grounder now
  reads) and z3 refuses `(declare-const and Int)`. (3) A formula declared of
  a sort other than `Bool` grounds nothing: `(>= 5 0)` of sort `Int` or
  `(_ BitVec 8)` was replayed and Established. (4) `and` / `or` of one
  argument ground nothing (SMT-LIB2 Core declares both `:left-assoc`, and the
  one reader refuses fewer than two arguments): `(and (>= 5 0))` was replayed
  and Established. Tests: `pred_citation_rendering_budget.rs` (both
  validators under an 8 MiB heap ceiling; an honest 339,696-byte rendering
  still states one text), `a_bounded_rendering_is_the_whole_rendering_or_none`,
  `a_clause_name_is_a_name_the_one_reader_reads`,
  `a_formula_of_another_sort_grounds_nothing`,
  `a_connective_of_one_argument_grounds_nothing`.

- **The v41 producer conformance rule is checkable (KIND 1: prose to
  enforced).** `BodyGate`'s doc stated the rule — a v41 producer MUST emit
  `Ungated` or `Gated`; wire tag 0 is legitimate only as re-emission of pre-v41
  content — under the heading "not format-enforceable", because "a decoded
  `Module` does not retain the wire version it came from". That was an
  implementation fact, not a law. Now:
  `trust_ir::binary::deserialize_module_with_wire_version(bytes) ->
  Result<(Module, WireVersion), _>` keeps the validated header version beside
  the module (`deserialize_module` is the same decoder, delegating and
  dropping it). `WireVersion` has a private field and no constructor: the
  only way to hold one is to have decoded a blob, so a fabricated provenance
  is a type error, not a runtime check.
  `trust_ir_build::validate_module_as_decoded(&module, wire_version)` is
  `validate_module` plus `decoded_provenance_errors`: at v41 or later a
  function WITH A BODY and `body_gate: None` is
  `ValidationError::ProducerOmittedBodyGate { function, name, wire_version }`
  (a producer-side variant, distinct from the codegen pass's consumer-side
  `UnlicensedBodyForCodegen`); below v41 the same `None` is grandfathered; a
  bodyless declaration is never refused (the `is_declaration()` cut
  `codegen_license_errors` makes). `trust-ir validate` applies the rule to
  every BINARY input — folded into the verdict, `--link` included — and
  prints for text / JSON / MessagePack input that it carries no wire version,
  so the rule is UNCHECKED, never silently skipped. Nothing on the wire moves:
  `VERSION` stays 46, `Module` gains no field (the version is decode
  provenance, not content — `wire_version_is_not_module_content` measures a
  v38 and a v46 spelling of one module decoding to equal modules with equal
  `stable_digest`), and every conformance golden is byte-identical.
  **Measured when the rule first ran:** 8 of the 12 conformance goldens
  written at v41+ (`abi_calling_conv`, `abi_enum_tag_repr`,
  `abi_function_symbol` ×2, `body_gate`, `composition`, `import_scheme`,
  `spec_carrier`, `text_directives` ×2) carry a bodied tag-0 function, so
  `trust-ir validate` refuses those eight blobs under the rule. The fixture
  harness is a codec-fixture generator, not a conforming producer: it stamps
  no claim — `body_gate.tmbc`'s `no_claim` deliberately, to pin that the
  three-valued tag can spell `None` at v41, the rest incidentally. Those
  bytes are frozen, so `producer_rule_census` (gate 8) pins that set exactly
  (every count derived, no literal to bump): a new golden joining it fails, a
  regenerated one leaving it drops its row. Five CLI test fixtures
  (`cli_coverage_assurance`, `cli_linked_imports`) were likewise
  non-conforming and now make the claim (`Ungated`). Residual, on the types:
  a hand-built module, a text / JSON / MessagePack parse, or a plain
  `deserialize_module` result has no `WireVersion`, so plain `validate_module`
  still accepts a bodied `None` — the format cannot hold a provenance-less
  module to a provenance-phrased rule, and says so (`LIMITATIONS.md`).
  **Review follow-up (same day):** the rule's "tag 0 is legitimate only as
  faithful re-emission of pre-v41 content" exception is RETIRED from every
  statement of it (`BodyGate` docs, `binary.rs`, `docs/binary-format.md`,
  `CLAUDE.md`, the variant's docs and `Display`): the check never honoured it
  and cannot — a header is the writer's declared version, not the content's
  history — and it does not need to, because the writer selects the minimum
  lossless version, so a faithful re-emission keeps its pre-v41 header
  (`a_faithful_re_emission_of_pre_v41_content_keeps_its_header`, library and
  CLI). `trust-ir convert` is a transcoder: a provenance-less input whose
  bodied function has no claim beside a v41+ feature converts to a v41+ blob
  `validate` refuses, while `validate` of the input reports UNCHECKED — the
  residual made visible, not a contradiction
  (`a_transcoded_module_is_first_checkable_as_binary`). `--link`
  dependencies are now decoded with their header version and held to the
  same rule (`a_link_dependency_is_held_to_the_producer_rule`); before, they
  went through the version-dropping loader and were neither refused nor
  reported. The v40 boundary is pinned in the gate-3 CLI lane too
  (`the_same_content_in_a_v40_blob_is_grandfathered`); the library twin is
  `binary`-gated and runs only under `--all-features` (`ci-self-verify.sh`),
  which its header now says.
- **Typed module completeness carrier, non-wire half (WS5.3b, F-090).**
  `Module.completeness: Option<ModuleCompleteness>` — `None` (NO CLAIM: every
  pre-carrier blob and every decoded binary today), `Complete`, or
  `Partial(Vec<UnloweredRow { symbol, display_path, reason }>)`. Three-valued
  for the v41 `body_gate` reason: a re-serialized legacy module must not
  silently claim completeness. Text carries it as `completeness complete|partial`
  plus one `unlowered "<symbol>" <"<path>"|-> "<reason>"` line per row; JSON and
  MessagePack carry it as the sole trailing skipped field (`tuple_layouts` is
  now always emitted, so every JSON/MessagePack module golden whose tuple
  table is empty gained an empty `tuple_layouts` slot — 40 JSON goldens +1
  line, 39 positional MessagePack goldens +1 byte (array16 count +1, trailing `0x90`) and the `to_vec_named`
  bundle +15 (the key too); every byte read and explained, not blessed). The
  BINARY format has no carrier yet: every
  writer refuses a claimed module by name (`CompletenessClaimUnencodable`) and
  `wire_identity_blocker` reports it; the wire part (a trailing section, tag
  0/1/2, read-gated on its version) joins the next open wire batch after a
  `docs/wire-allocation.md` reservation. Validator: `UnloweredRowNamesDefinition`,
  `DuplicateUnloweredRow`, `EmptyPartialClaim`; `validate_module_complete` →
  `CompletenessError::{IncompletenessUnclaimed, ModuleIncomplete}`; linked walk
  `ImportIncomplete` for a proof-bearing site citing a `Partial` dependency
  (call-only edges exempt). `trust-ir-diff` reports a flipped claim as the
  `completeness` module row. The CLI refuses by name where the writer would
  panic: `convert --to bin` exits 1 naming `Module.completeness` (text, JSON and
  MessagePack still convert), `digest` reports the module as not encodable, and
  `validate --link` refuses a claim-bearing dependency (`wire_identity_blocker`);
  the fallible `serialize_native_verification_bundle` returns
  `BinaryError::Unencodable` for a claimed module rather than panicking in its
  module segment. Ratified in `docs/SPEC_RATIFICATIONS.md` §15.
  Tests: gate 8 `module_completeness` (crit.unex06 port), gate 9
  `module_completeness_validation`, and `trust-ir-cli`
  `cli_module_completeness`.

### Changed

- **AY `8e7b3fe6b`: the AY adapter calls ay's introspection twins, and
  production code cannot allow a disallowed method (r11, 2026-10-09).**
  `Solver::try_term_sort` (ay `1128b49f2`) and
  `Solver::try_render_term_canonical` (`872d060fc`), on ay main since
  `a5b7768ce`, return ay's typed refusal where `term_sort` and
  `render_term_canonical` panic on a term handle the solver did not issue.
  - Pins: `scripts/bump-dep-pin.sh clean-ay` moved all six legs, Clean
    `1ad47bddc` to `625396d83` (Clean main `b8d83b671` plus Clean's own AY
    move, which co-owns this AY) and AY `630842a8` to `8e7b3fe6b` (the twins'
    branch tip; why not ay main's tip is Clean's decision record,
    `R-AY-TWINS-PIN-20261009`). `crates/clean-kernel` is byte-identical at
    the two Clean revisions, with equal inherited workspace rows and path
    closure (Trust's pin-lattice L3 checks, run on the pair), so this move
    asks no Clean gitlink move of Trust's lattice because of a kernel change.
    It still owes L3's ancestry: the Trust train that adopts a trust-ir at or
    past this move must vendor a Clean that contains `625396d83` (Trust main
    `1a7d3be9a6` vendors Clean `08084daa`, which contains neither
    `625396d83` nor the replaced pin `1ad47bddc`, so the gap predates this
    move).
  - The x86-64 vector-compare certificate rule names AY `8e7b3fe6b` and the
    certifying build's sha256 (`538b0421…`); the 32 certificate cells were
    re-certified with trust-cg's gate (run recorded in `docs/dialects.md`).
    The rule's Clean did not move.
  - `trust-ir-ay` (merge of `eaf045da`): `bitvec_width_of` calls
    `try_term_sort` and the sited VC goal renders through
    `try_render_term_canonical`; `authenticate_term` and both scoped
    `#[allow(clippy::disallowed_methods)]` sites are gone. The r11 review M1
    test now expects ay's typed `invalid term handle in term_sort`.
  - `trust-ir-ay`'s crate root carries
    `#![cfg_attr(not(test), forbid(clippy::disallowed_methods))]`, so a
    production allow of a method `clippy.toml` disallows is `E0453` under
    gate 0's tippy. Measured: an allow added to `bitvec_width_of` makes
    `targo tippy --locked -p trust-ir-ay --all-targets --all-features -- -D
    warnings` fail with `E0453`, while the test modules' inner allows still
    compile. Plain `targo --unverified build` does not see it; the lint gate
    is the enforcement, and `clippy.toml` now cites the forbid instead of
    asserting the absence in prose.

- **SPEC §17 restated: the trust-cg bridge holds its `NativeC` argument claim
  per SIGNATURE, and the check's trusted base is stated (written 2026-09-30,
  landed with trust-cg round 10 on 2026-10-09).** The
  `(prose-only)` entry said the bridge compared each argument in isolation,
  that one family (a Rust-ABI cast aggregate of 1 to 4 bytes on the Darwin
  stack) was measured wrong and open, and that closure bodies were held by a
  conservative refusal. trust-cg's round 10 replaced all three: every
  declaration the bridge emits is compared per signature against rustc's
  `FnAbi` through trust-cg's own classifier (AArch64 `classify_params_with`,
  x86-64 `x86_sysv_param_locations`), every live byte's register or stack home
  included, refusing a disagreement by name and refusing what it cannot judge;
  the narrow cast is declared as the integer rustc passes, and closure bodies
  and by-value environments follow rustc's convention. The entry now says what
  a pass establishes and what it rests on (trust-cg's classifier placing
  rustc's value alphabet as LLVM does, and the bridge's `PassMode` model, both
  shared by the two sides of the comparison, so their evidence is the
  cross-backend matrices), and states that there is no interim: an
  `extern "rust-call"` callable is declared with its argument tuple's elements,
  as rustc's `FnAbi` lists them, instead of refused where the other backend
  reaches it (trust-cg round 10, F2). The `(external)` entry cites the check,
  the 62-row family matrix at O0-O3 (aarch64-apple-darwin natively,
  x86_64-apple-darwin under Rosetta; it passed again on the tree trust-cg
  landed, merge `4e5ab2354`), the `rust-call` change with its before / after
  rows, trust-cg's ruling that its 2026-10-02 refusals of tupled `rust-call`
  crossings are not kept (those programs are rows that must compile and
  agree), and the `core` census (the same failed roots before and after,
  measured again across the `rust-call` change). No class is
  raised: the claim stays `(prose-only)` and the bridge's comparison
  `(external)`, test rung (`targo --unverified`, no proof claim).
- **One spelling of a switch case (2026-09-30; `docs/SPEC_RATIFICATIONS.md`
  §3.3).** A `Switch` case at an integer or `char` selector is now a
  constant of the selector's type, checked by the one constant funnel exactly
  as its `Inst::Const` twin is and refused as `ConstTypeMismatch` at
  `"... switch case N"`. `switch u8 [ -1: .. ]` and `switch i8 [ 255: .. ]`,
  which validated while `const u8 -1` did not, are one error; so is every
  other literal the twin refuses (a surrogate `char`, a non-canonical
  `Constant::U128`, a non-integer). A refinement selector's case is a
  constant of the refinement's base type. Must-refuse rows
  `refuse/switch_case_negative_at_unsigned` and
  `refuse/switch_case_above_signed_max`, one spelling each (exhibit
  `ConstTypeMismatch`, which leaves `UNCOVERED.tsv`). The backend-TV mirror reads a signed
  selector's case as its signed value (it admitted only `[0, 2^w)`, i.e. the
  refused spelling), and `frontend/`'s MIR driver sign-extends a signed
  `SwitchInt` case (it emitted MIR's raw bit pattern). Trust's bridge and
  THIR lowering and Clean's emitter already emit the value (read
  2026-09-30). A producer that emits a raw bit pattern at a signed selector
  is now refused.

- **Pointer-width constants have the target's width (2026-10-01;
  `docs/SPEC_RATIFICATIONS.md` §3.3).** Every `isize` / `usize` constant — an
  `Inst::Const`, a global initializer, an aggregate lane, a closure capture, a
  switch case, a verification bundle's const generic argument — is now
  range-checked at the module's target pointer width (`Module::pointer_bits`:
  `pointer_size * 8`, or the documented 64-bit default for a target-free
  module), not at 64 bits on every target. On wasm32 `0` and `2^32` were both
  admitted `usize` cases of one switch (one selector value; the interpreter,
  32-bit there, wraps `2^32` to `0`, so the second arm was dead); `2^32` is now
  `ConstTypeMismatch` exactly as `const usize 2^32` is. One rule:
  `Constant::value_matches_ty` takes the pointer width as a parameter (an API
  change: no default; the validator and the bundle pass the module's) and reads
  every integer width from `Ty::bit_width_with`, the width the exhaustive-switch
  clause and the interpreter already used. Must-refuse rows
  `refuse/switch_case_usize_beyond_target_width`,
  `refuse/switch_case_isize_beyond_target_width` and
  `refuse/const_usize_beyond_target_width` (wasm32). A module that spelled a
  64-bit-only `usize` value on a 32-bit target is now refused.

- **Gate 17, `frontend-lowering` (2026-10-01).** The workspace-excluded
  `frontend/` package's tests ran under no standing gate. Gate 17 runs the
  targets listed in `scripts/gates/frontend-lowering.frontend.tests` by
  `--manifest-path frontend/Cargo.toml` (`run_excluded_registry`); a listed
  target must pass whole. The switch-case lowering test moved out of
  `real_lowering_acceptance.rs` (four of whose tests fail on pre-existing
  drift) into `frontend/tests/switch_case_lowering.rs`, its first line, and
  gained `isize` / `usize` matches;
  `frontend/tests/mir_switch_source_width.rs` (the source-width case
  spelling, 2026-10-09) is its second line. `check_enforcement_links.py`
  counts a test of such a gated target as a `(test)` witness, so SPEC §3.3's
  frontend entry moves from `(code)` to `(test)`.

- **Gate 15 ledger: `Ty::bit_width`'s two `elem` rows are `verifier-false`
  shape c (2026-10-01).** The r11 survey found two NOT-IN-LEDGER refutations
  at `crates/trust-ir/src/ty.rs` `Ty::Vector(elem, lanes) => elem.bit_width()`
  (an `assertion` and its `hardened_panic_boundary` twin, both demoted), which
  would fail gate 15 the day trust-ir is JUDGED. A 20-line reduction of the
  function, run through `targo trust check --allow-l0-gaps`, refutes exactly
  those two rows at `elem`, and their obligation is MIR's `null reference
  constructed` check of the `Box<Ty>` deref: a Box's pointer is never null, so
  the refutation is false and the code stays. The reduction joined the
  false-refutation repro crate as `Nest::width`.

- **Lean model: one integer representation (2026-09-30).** Every integer
  value of the Lean model is now a residue in `[0, 2^w)`: integer constants
  bind `Value.intAt w i` (`i mod 2^w`) at all seven places a `Constant.int`
  becomes or meets a model value, the switch case scan compares residues,
  and the GEP index and the `Alloca` / `HeapAlloc` count read the residue
  signed (`toSigned`), as `AtomicRMW` `Max` / `Min` now do: they ordered the
  raw `Int`s, which on residues is the unsigned order (168 of the 1680
  `AtomicRMW` runs added to the test). Before, a negative literal bound the raw `Int`, and the
  unsigned compares, divisions, shift guard, `ZExt` / `UIToFP` / `IntToPtr`,
  `CmpXchg` and the switch scan disagreed with the reference interpreter on
  it (measured: 1242 of 3375 runs of the new
  `negative_literal_constants_agree_across_engines`). Theorems in the new
  `TrustIr/Proofs/IntResidue.lean`; `alloca_progress` now assumes a positive
  SIGNED count, and the vector-dialect lowering proofs discharge the lane-index
  bounds from the payload predicates. Residual (ledgered, pinned by
  `signedness_blind_operand_divergences_stay_as_measured`): an unsigned GEP
  index or allocation count with its top bit set is UB in Lean and runs in the
  interpreter. The vendored Trust oleans (`TrustIr.Semantics.Arith`'s closure)
  change: Trust's next `first-party/trust-ir` move runs
  `scripts/check_bridge_pin.sh --fix`.
- **The cast rule's reachability predicates are decided once per node, and
  the `pair` rule's lane count has no depth cut-off (2026-10-08).** The
  layout table laid out each node once, but the layout-sensitive cast rule
  it answers (`LayoutTable::layout_sensitive_cast_evidence`, behind the
  validator's cast pass and a bundle's cast facts) first asked three walks
  that were not memoized: `type_reaches_handle` (a heap walk that scanned the
  whole struct, enum or record list at every referent),
  `type_holds_closure_by_value` and `type_stores_bool_lane` (native
  recursions behind `Vec` guards, with the same scans). Measured in release:
  one cast question on a 16 000-deep struct chain took 664 ms (x4 per
  doubling), one cast per level of a 4000-deep chain took 77 s on one shared
  table, and a 100 000-deep chain overflowed an 8 MiB stack. The three are
  plain reachability (a pure disjunction, so every complete walk computes the
  same answer whatever the order), and `trust_ir::reach` decides each node's
  verdict once per memo on an explicit stack — collect the undecided nodes,
  record each member edge backwards, propagate "reaches a seed" from the
  seeded nodes — over an all-definitions index built once per kind
  (`DefIndex`). A `LayoutTable` keeps one memo for its life
  (`LayoutTable::type_reaches_handle` / `type_holds_closure_by_value` /
  `type_stores_bool_lane`; `LayoutTableStats` gains `reach_nodes`,
  `reach_steps`, `reach_rows_indexed`), so the same measurements are now
  7.3 ms, 3.0 ms and 48 ms, and 64 000 casts over a 64 000-deep chain take
  56 ms; a one-shot `Module` call costs its reach plus one pass over each
  definition table it meets. A lent `LayoutMemo` now
  also records the signature-table length, and a memo lent across a change
  of it keeps its layouts but drops its reachability verdicts (a signature
  that was missing may now reach a handle). `Module::callable_carriers` (the
  rule H carrier census) reads the same index instead of a list scan per
  referent. Answers are IDENTICAL: the new conformance target
  `by_value_reach_differential` (gate 9) keeps the old walks verbatim as its
  oracle and compares the `Module` methods, shared tables (several query
  orders, each asked twice) and, for handles, the whole-module
  `NominalTypeReachability` summary over the fixture corpus (195 modules),
  6000 random type graphs (handle, closure and bool seeds behind by-value,
  pointer, signature and capture edges; missing and duplicate ids; cycles
  through every kind; four targets) and every order of seeded and empty
  cycles, and the cast rule against the old rule over the old walks; linear
  work counters hold on 10^5-deep chains through every node kind (on a
  256 KiB stack), `P{k+1} = {Pk, Pk}` to 10^5 levels and one cast per level
  of a 10^5-deep chain, each bounded before the large run. Thirteen seeded
  mutants of the memo are each killed. `codegen_lowerability_errors` asks one
  table for the pass instead of one per closure `CallIndirect`: 4000 calls
  over a closure capturing a 4000-deep chain took 4.7 s (x4 per doubling),
  now 1.5 ms (10^5 of each: 53 ms). The `pair` placement rule's ABI lane
  count (WS3.11, `validate::abi_lanes`) was a recursion cut off at 16
  levels, which REFUSED a `pair` on a two-lane value under 16 or more
  newtypes (rustc stamps `ScalarPair` at any depth) and on `{P15, u64, u64}`
  over zero-lane `Pk`, walked a shared sub-type once per path (1000 claims
  on `P14`: 306 ms) and scanned the struct list per level. The cut-off is
  gone: the count is an explicit-stack walk with one count per struct and
  enum per validation pass (`AbiLanes`), a by-value cycle (a re-entered open
  node) has no count, and so does a count that overflows `usize`. Those
  claims are now admitted (1000 claims on `P14`: 1.0 ms; 1000 over 10^5
  newtypes: 61 ms, was 1.13 s and refused). The gated target
  `abi_lane_count` holds the validator's `pair` verdicts to the same rules
  without the cut-off, keeps the cut-off recursion verbatim and checks it
  differs only by refusing, and validates 10^5 newtypes on a 256 KiB stack.
  No wire, text or digest change.

- **Subset condition 6 has no depth budget; the census and one-shot
  reachability questions index once (2026-10-08, review of the above).**
  Both condition-6 checkers (`ConformanceSubset` and the mirror
  `trust_ir_conformance::subset`) decided "this load's type carries a `Char`
  by value" with a native recursion cut off at 24 levels
  (`CHAR_CARRIER_DEPTH_BUDGET`), which answered "carries" when the cut-off
  was reached: it REFUSED every char-free type 24 levels deep (measured in
  release: a load of `P23 = {P22, P22}` out of subset, as "a `Char` read
  from memory") and walked a shared sub-type once per path (`P22`: 34 ms per
  load, x4 per level). Both budgets are deleted (now `P23` to `P40` are
  admitted in 6-9 us a load, and `P100000` in 11 ms). The classifier asks
  `trust_ir::reach`'s memo (a fourth predicate, `Reach::CharValue`: a
  `Char`, a dangling member id or a by-value cycle reachable, cycles found
  per solve as strongly connected components; one memo per `check`), the
  mirror a whole-module summary (`subset::CharCarriers`, cycles found by
  peeling; `char_origin_violation_with`), each O(the module's types). That
  is the budgeted walk's own answer as its budget grows, so every module
  either checker admitted is still admitted, and a load whose char-free reach
  is 24 levels deep or more is now admitted (`lowering-target-subset.md`, v4
  addendum, no version bump). The gated `char_carrier_differential` holds the
  classifier's one-shot entry and module walk and the mirror's one-shot
  entry, summary and module walk to the old walk given a budget no acyclic
  path can exhaust (3000 random modules, 121k loads; missing, duplicate and
  out-of-place ids resolved as `Module::struct_def` resolves them), checks
  the old cut-off differs only by refusing, and judges 10^5-deep chains
  through every member kind and `P{k+1} = {Pk, Pk}` 10^5 high on a 256 KiB
  stack, the mirror's work counted. Nine seeded mutants of the two are each
  killed. The same review moved three costs: `AllDefs` (the all-definitions
  index of `reach`, `inhabit` and the rule H walk) builds no hash map for a
  table whose ids are their positions, which made one-shot `Module`
  reachability calls on a shallow type 16-22x slower than the list scan they
  replaced (S = 10^5 structs, 1000 calls: 1.36 s, now 69 ms; the old scan
  66 ms); `inspect_module_reachability` walks each signature's carried keys
  once per pass over one index instead of at every foreign or indirect call
  site; and `codegen_lowerability_errors_in(&LayoutTable)` is the pass over a
  caller's table, gated by `codegen_lowerability_layout_work` (N closure
  applications over an N-deep capture chain lay it out once; 10^5 on a
  256 KiB stack). New tests also pin `abi_lanes`' exact counts (3000 random
  graphs, the surviving 3-for-`None` mutant now killed), `pair` claims more
  than 16 levels deep through every wrapper kind against a second oracle,
  and the reachability memo on 160 random modules of 50-100 rows per table
  against a whole-module Kleene fixpoint.

- **The x86-64 vector-compare certificate rule is code, re-certified under
  AY `630842a8` with a Clean built from `8db0f0e61` as the checker
  (2026-09-30).** The certificate ground of
  `docs/dialects.md`'s per-cell rule was a prose clause that trust-cg's gate
  parsed and nothing here checked. It is now `CHC_X86_ICMP_CERTIFICATE_RULE`
  (`ChcX86IcmpCertificateRule`, `ChcX86IcmpCertifyingBuild`), and
  `chc_x86_vector_icmp_cell_ground` answers each cell's ground
  (`ChcX86IcmpGround`) as a projection of `chc_x86_vector_icmp_cell_status`,
  so the two cannot disagree. The API only grows. `ChcX86VectorIcmpCell` is
  unchanged, so a consumer that builds one by struct literal still compiles.
  The rule names each tool by source revision, version and build arguments,
  plus the sha256 of the binaries that produced or checked the certificates
  (evidence, not identity: builds are not byte-identical); no repository URL.
  Three tests hold it: `chc_x86_icmp_certificate_rule_is_well_formed`
  (refuses the all-zero placeholder digest; measured red with it),
  `chc_x86_vector_icmp_cells_answer_their_ground` (measured red with `sgt`
  answered as a certificate), and, in gate 7,
  `x86_icmp_certificate_rule_names_the_pinned_ay` (the rule's AY revision and
  version equal to the AY pin; measured red with the revision split from the
  pin, and with the version alone split), so an AY move that does not move
  the rule fails here instead of at trust-cg's next pin move. It cannot see
  re-certification: moving `ay.rev` alone turns it green with stale digests.
  `scripts/pin_rewrite.py static-guard` (gate 0 and every bump) mirrors the
  assertion, which it had missed while claiming to mirror every gate-7
  assertion but one (measured: it passed a rule split from the AY pin, by
  revision or by version, that gate 7 failed). Its new `GUARD_TEST_MIRRORS`
  table names every gate-7 `#[test]` with its mirror or exemption, and the
  static guard now fails on a gate-7 test the table does not name. `publish/transforms.sh` T1 projects
  the rule's two revisions into a public snapshot like the pins (the AY
  exactly as `AY_REVISION`; the Clean by `project_forward`, refused by name
  when nothing published descends from it), with cases in
  `publish/test_transforms.py`. The checker moved off the installed Clean
  0.9.0 package, which false-accepts 31 of Clean's own 46 refutations of
  satisfiable problems and a real `v16_i8` `uge` certificate with a `pbblast`
  sum cut short. Measured with trust-cg's gate as the trust-cg pin move
  rewrites it (an uncommitted diff on trust-cg `34026e3fb`,
  `targo --unverified`, no proof claim): 32 of 32 certificate cells `unsat`,
  `unproved_steps=0`, no unchecked rule, Clean fully verified; the Clean
  binary refuses the 46 and three certificate mutants. Those 32 queries are
  that diff's per-lane bytes: for the 16 unsigned cells they are not the
  two-halves queries trust-cg main generates and pins today. The rank is unchanged, and the rule's rustdoc now states it with
  what it trusts: a Carcara-checked SMT proof whose spec side is trust-cg's
  own encoding, below a kernel certificate and a Lean theorem. The certified queries spell the sign-bit bias per
  lane again: AY fixed at the root the node cap that trust-cg `7b81d2cb1`'s
  two-halves spelling worked around. This change moved the pins with
  `scripts/bump-dep-pin.sh clean-ay` (Clean `afe42324d` to `8db0f0e61`, AY
  `f28345ff` to `630842a8`, all six legs); main moved meanwhile to the same
  AY and on to Clean `3c82461` (`c20992a2`, `41452ccb`), and the merge keeps
  main's pins. The rule's Clean is not a pin and need not equal it:
  `8db0f0e61` is an ancestor of `3c82461`, and their `third-party/carcara`
  trees are identical. The rule replaces the prose clause that the
  2026-10-01 AY `630842a8` re-certification entry below describes. That run
  kept the installed Clean 0.9.0 binary (sha256 `9c594e83…`) as its checker,
  the binary this entry retires, so its "fully verified" is not this rule's
  ground.
- **WS8.12: the audit's undocumented boundaries are written down (docs
  only; no code, wire or verdict change).** The 2026-09-17 two-language proof
  program and its ratchet ledger (`RATCHETS.tsv`, landed by WS8.6; the
  archive, WS8.1) found boundaries that held in code but were stated nowhere,
  or stated wrongly. Most were closed by the increments that fixed them; this
  writes the remainder. `docs/SPEC_RATIFICATIONS.md` gains §23 "Portable
  source names" (a producer SHOULD write root-relative or remapped source
  paths: the V3 import identity drops them, but the binary bytes and
  `executable_content_digest_v1` keep them; held by
  `crit_unex03_moved_checkout_keeps_the_portable_identity`), §4 records ruling
  DG-08 (the interpreter stays normative until a Clean executable semantics is
  measured at zero disagreements), and §12 gains the 2026-10-02 deferrals
  (DG-04 level-R layout mode, DG-06 unions, DG-07 fact inventory, DG-08
  `f128` and normativity, DG-10 Clean `Nat` exports). `TRUST.md` splits the
  build-determinism claim — import identity is path-independent, byte
  identity holds only for a producer that writes portable names, and both
  shipping producers are named as not guaranteeing it yet (F-117) — and adds item-3
  rows for the Lean-execution differential and for `behaviour_refines` over
  `semantics_preserving` (F-127). `LIMITATIONS.md` states that the
  `Switch` exhaustiveness flag is a zero-authority hint (F-039), that only
  the transport text spelling (`convert --to text`) preserves
  `stable_digest` while the canonical one (`trust-ir-fmt`) can move it
  (F-072), the portable-identity / non-portable-bytes split, and `f128` as
  ruled out of scope; it no longer names an internal `docs/` path.
  `docs/ub-numerics-policy.md` §1 confines a masking shift to level S
  (DG-08); `lowering-target-subset.md` records DG-06 reaffirming the
  byte-overlap union model; `CLAUDE.md` records that Trust's pin-lattice gate
  (WS8.2, L3 strict) requires a byte-identical `crates/clean-kernel` across
  the two pins. The `Inst::Switch` field doc no longer says text drops the
  exhaustiveness flag (it is carried since WS4.5).
  Review: two tests pin the new claims — `ws8_12_canonical_text_is_not_an_identity_transport`
  (transport text keeps the import identity; canonical text of a
  non-canonical module is refused by the original's import row as
  `DigestMismatch`) and
  `ws8_12_section23_portable_names_are_a_producer_should_not_a_validator_rule`
  (an absolute path changes no verdict at any tier; a portable one keeps the
  bytes and `executable_content_digest_v1` equal across checkouts). The
  `CLAUDE.md` pin-lattice sentence now states L3 as Trust's check reads it
  (the Clean rev at the VENDORED trust-ir revision, an ancestor of Trust's
  Clean gitlink), and the `LIMITATIONS.md` switch-hint bullet names the
  argument-free default edge. After rebasing onto WS8.15's call-executing
  refinement, the `TRUST.md` item-3 `behaviour_refines` row cites the
  `TransformRefinementCtx.lean` theorems instead of saying the notion is
  stated over the intraprocedural evaluator only.

- **Wire v59 reservation released: `typed-signature-abi` (2026-10-02).** The
  reservation (never landed; no code read or wrote it) was for a stored second
  spelling of a function's signature ABI beside `ParamAttrs.pass` /
  `ParamAttrs.ext` / `FuncTy.is_vararg`, which the one-spelling rule forbids;
  a signature-ABI descriptor, if added, is a view derived from those fields.
  The row is deleted, never burned, and the open reservations above it move
  down one in both version ledgers: effect-summaries 60 -> 59 (its
  `ClausePlace` 8 and 9 `since` 59), certificate-binding 61 -> 60 (its
  `BodyGate` 3 `since` 60). No shipped version, tag or digest domain changes,
  and every blob this build writes or reads is unchanged.
- **The layout authority lays out each nominal type once: `LayoutTable`
  (2026-10-02).** `Module::ty_layout_shape` recursed through every field
  layout with no memo: a type sharing a sub-type (`P{k+1} = {Pk, Pk}`) was
  laid out once per path (161 ms at depth 20, x4 per two levels), a chain
  paid a linear struct scan and a linear cycle-guard scan per level (2.06 s at
  depth 65 536, cubic over a validator pass), and a 4096-deep chain overflowed
  a 2 MiB stack. `trust_ir::LayoutTable` (`Module::layout_table`) lays out
  each struct, enum, by-value type-table entry and declared tuple at most
  once, bottom-up on an explicit stack with hash-map id lookups and a
  three-colour cycle guard, and `ty_layout_shape` / `enum_layout_shape` /
  `struct_field_offset_bits` / `validate_tuple_layouts` are table queries. A
  table's work is O(total fields) however many questions it answers
  (`LayoutTable::stats`); the per-definition overlap test is a sort and
  sweep (O(f log f), was O(f^2)), and `EnumDef::effective_discriminants`
  finds a duplicate through a set (was O(variants^2)). Answers are
  IDENTICAL, cycle refusals included (which re-entered node a cycle names
  depends on where the walk entered; the module docs say why a memo can
  still reproduce it), except where the niche rule's inhabitedness question
  meets a cyclic reach (next entry): the new conformance target
  `layout_table_differential` (gate 9) keeps the old recursion verbatim as
  its oracle — with its own copies of every helper the change touched — and
  compares the `Module` methods and shared tables, one per query order (nine
  per graph), each asked every query twice, over the fixture corpus, 12 000
  random type graphs (missing and duplicate ids, records, duplicate tuple
  types, inline copies of declared tuples, cycles through all four node
  kinds, perturbed declared layouts, niche descriptors over uninhabited
  variants, four targets) and every query order of mixed cycles; nine seeded
  mutants of the table are each killed. A table's work counters
  (`LayoutTableStats`) also count the id-index rows read, the tuple rows
  indexed and the inhabitedness work, and the tests bound each linearly
  BEFORE any walk large enough to hang on a regression. The table is `Sync`
  (its memo sits behind a mutex) and its memo can be detached from the
  module (`LayoutTable::into_memo` / `with_memo`, `LayoutMemo`). So every
  layout question of a `validate_module` pass now asks its one table — the
  module-level passes, the tuple rows, the niche rule, the cast-evidence
  pass, the constant walk, the sealed handle slots, the exhaustive-switch
  and `MakeAggregate` rules in the parallel per-function section, and each
  backend-TV denotation; so do a bundle's compiler-fact checks, the core
  reflection, and a `FunctionBuilder`'s `Alloca` extents (one memo for the
  builder's life; a 2000-deep chain allocated top-down is 2000 nodes, was
  about 2 million). The validator's struct field-overlap rule is the sweep
  (`trust_ir::shape::any_byte_ranges_overlap`, now public), and its enum
  descriptor rule reports every overlapping pair, in the same order, through
  `overlapping_byte_range_pairs` (O(f log f + pairs), was O(f^2) with two
  layout questions per pair). The allocation-bound lint sizes enums through
  one table per module. The validator's ZST check reads the table's
  first-definition lookup, so `validate_module` on a 4096-deep struct chain
  went from 27.8 s to 4.0 ms and on `P20` from 906 ms to 0.3 ms; it is now
  linear on struct chains and zero-sized shared DAGs to 2^20 deep (1.2 s and
  2.2 s) and on enum and type-entry chains to 2^18.
  No wire, text or digest change.
- **Inhabitedness is the least fixpoint of its rules, decided once per node
  (2026-10-02).** `Module::ty_is_uninhabited` (and `variant_is_uninhabited`,
  `niche_unencoded_inhabited_variant`) was a native recursion with a fresh
  guard per variant that rescanned the whole struct, record or enum list at
  every nominal node and answered "inhabited" on re-entering its own path.
  Laying out a `Niche` enum asks it for every unencoded variant, so the
  layout table's walk was quadratic there (2.66 s for a 2^16-field payload,
  about 5x per doubling, while its own step count grew by 6) and recursed on
  the native stack (a 4000-deep zero-sized payload overflowed 256 KiB, and
  10^5 overflowed 8 MiB). It is now the LEAST solution of the same rules
  read as and-or equations over the nominal nodes (`trust_ir::inhabit`): a
  query writes the clauses of the nodes it reaches that no earlier query
  decided and propagates, on the heap, so a `LayoutTable` decides each node
  once (O(module) over its lifetime, counted in its stats), and a one-shot
  `Module` call costs O(its reach) with one all-definitions index per kind.
  Where a question's reach is acyclic — every question the validator admits
  a module with, except through a duplicate RECORD id, which it does not
  refuse — the answer is exactly the old one. Where it is cyclic the old
  answer depended on the order the walk met the cycle: a node decided while
  its own derivation was on the path was memoized "inhabited", so `E { V(G,
  Y) }` with records `X = { y: Y, n: ! }`, `Y = { x: X }` came out inhabited
  while `Y` asked alone did not. The least fixpoint is never below the old
  answer, says "uninhabited" only with a finite derivation (so the
  exemptions it grants stay sound), and answers the same in every order.
  The validator's niche, construction and exhaustive-switch rules ask the
  pass's table; the interpreter decides an enum's variants with one memo.
  `layout_table_differential` checks the memo against a naive
  iterate-to-stable statement of the fixpoint on every question of 6000
  random graphs (records, duplicates, cycles, dense `!`), and the old
  recursion against both: equal on all 96 622 acyclic questions, never
  above, below only on a cyclic reach. No wire, text or digest change.
- **An ARC operand names its cell's object base (2026-09-30).** SPEC "An
  ARC operation counts only a reference-counted cell", clause 3, decided (a
  ruling made on the owner's behalf): `Retain` / `Release` / `IsUnique` are
  defined only through a pointer at offset 0 of the reference-counted cell
  it was derived from; any other offset is undefined behaviour on every
  path. One predicate, `InterpretPointer::is_object_base`, is read by the
  interpreter's instruction path (`arc_allocation_mut`, `is_unique`, after
  the origin check) and its host path (`check_rc_cell`, which already held
  it); Lean checks it in `requireObjectBase` after `requireArcRef`. Before
  this both engines counted an RC cell at any offset, which had no lowering
  (trust-cg lowers `Retain p` to `clean_inc(p)`, a header read at `p`). The
  shrink-only ledger `arc_operand_offset_shapes_stay_as_measured` is
  deleted: its five shapes are decided cells of
  `arc_operand_provenance_agrees_across_engines`, "not at the object base"
  in both engines. Those five all `Retain`, so the table also runs the
  interpreter unit test's matrix (`RcCellAtOffset`: every operation on a
  `CleanHeap` and a `SwiftHeap` cell at offsets 4, 8, 20 and 32, the base
  as the positive control); without it a check dropped from `is_unique`
  passed the gate. With the check dropped from `is_unique` and, for
  `Release`, from `arc_allocation_mut`, the matrix's 16 off-base `Release` /
  `IsUnique` cells fail both halves (32 of 60); with `requireObjectBase`
  dropped from Lean's `semRelease` and `semIsUnique` they fail the
  agreement (16 of 60). Measured before the matrix: against the Lean model
  before this change the five cells fail (5 of 30); with the object-base check
  deleted from the interpreter they fail both halves (10 of 30) and
  `arc_operand_off_its_cell_base_is_undefined_behavior` fails; disabling
  `requireObjectBase` fails `lake build` at `requireObjectBase_off_base_is_ub`
  and the three instances. Lean: `semRetain_interior_is_ub`,
  `semRelease_interior_is_ub`, `semIsUnique_interior_is_ub` (every state),
  three instances and a positive twin; no new axiom. Producers: Clean's
  emitter applies the three to object variables, trust and ty only match
  them, and Clean origin/main `aecee3f69`'s
  `perceus_reset_reuse_semantics_tests.rs`, included into a scratch test
  against this interpreter, passes. Consumer obligation (not landed):
  trust-cg's next trust-ir pin move adds two `FSYM_INTERPRETER_UB_SITES`
  entries, `is_unique` "IsUnique: pointer is at offset {} of its cell, not"
  and `arc_allocation_mut` "{op}: pointer is at offset {} of its cell, not at ",
  both `CLASS_REFUSED`, owed like their siblings. Measured on a scratch copy
  of trust-cg `d42238c92` with `FSYM_TRUST_IR_INTERPRET_RS` at this
  interpreter: without them `interpreter_ub_sites_are_exactly_the_map` fails
  naming exactly these two; with them `fsym_ub_map` passes 12 of 12.

- **The Lean model carries pointer provenance (2026-09-30).** Ratification "A
  pointer operand names the allocation it was derived from". A Lean pointer
  value now carries the allocation it was derived from (`Value.ptr addr prov`,
  `Value.fatPtr data prov metadata`); an integer becomes an address as its
  unsigned value at its width, UB at or above 2^64 (`Sem.addrOfInt`), and an
  address — from an integer or decoded from bytes — recovers an allocation by
  the reference interpreter's rule (`Memory.provenanceAt`: containment, then
  one past the end, oldest first). Every pointer operand names its provenance:
  an access (`Sem.expectPointer` + `Sem.checkedAccess`, natural alignment when
  none is declared), a borrow (`Memory.borrowTarget`), an ARC operation and
  `Dealloc` (at the base). `Memory.alloc` places allocations exactly as the
  interpreter's `alloc_with_slack` does; that placement is a property of the
  two reference models, held equal by test, not a format rule. The
  interpreter does not change. Measured against the Lean model of `e2154f00`:
  68 of 82 cells of four new decided tables in `lean_exec_differential.rs`
  diverged, and all 82 agree now — `borrow_operand_provenance_agrees_across_engines`,
  `arc_operand_provenance_agrees_across_engines`,
  `address_layout_agrees_across_engines`, `pointer_value_rules_agree_across_engines`.
  The borrow ledger keeps only its six non-provenance rows and two controls;
  the ARC ledger is renamed `arc_operand_offset_shapes_stay_as_measured` and
  holds the five shapes that reach a reference-counted cell at a nonzero
  offset (undecided). Lean: new general theorems (`semAccess_names_provenance`,
  the `sem*_frame` family, `semDealloc_frees_its_provenance`,
  `addrOfInt_lt_two_pow_64`, `provenanceAt_inside`, `alloc_preserves_layoutWF`,
  `load_after_store_ptr_recovers_inside`) and decided instances; the
  address-model pins `retain_one_past_rustHeap_counts_neighbour`,
  `borrow_one_past_names_neighbour_dealloc_is_ub` and
  `double_endBorrow_one_past_ends_neighbour_borrow` are replaced by their
  reference-verdict twins; `semDealloc_twice_is_ub` no longer needs its
  unique-base hypothesis. Gate 14 stays green with no new axiom.
- **WS2.21 (F-033, trust-ir half): scalar Bool negation has one spelling,
  and `not bool` is refused by name (2026-09-30).** `UnOp::Not` at scalar
  `Ty::Bool` was refused as the generic `BinOpRequiresInteger`, which told a
  producer nothing (trust-clean-ir emitted exactly that and skipped `neg`).
  SPEC_RATIFICATIONS §3.2 ratifies the one spelling, the Bool connective
  `bxor %b, true` (no Lean change: `semIntBinOp .BXor` already models it), and
  the validator now refuses `not bool` as the new
  `ValidationError::UnOpNotOnScalarBool`, whose text names that spelling.
  `not` on integers, integer vectors and bool vectors is unchanged, and a
  float is still `BinOpRequiresInteger`. No wire change. Tests: the new
  conformance target `bool_negation_spelling` (gate 9's conformance registry; the proof-program row
  `a.format.unop_not_bool` ported by name: the bxor specimen validates and runs
  to the native 3, the `not` specimen is refused by name), the must-refuse
  corpus row `refuse/unop_not_scalar_bool`, and the ratchet
  `b6.bool.scalar_not_rejected` flipped GAP -> PASS "ratified single
  spelling". The text parser now reads the Bool connectives
  `band`/`bor`/`bxor`, which the printer has always written but the parser
  refused as "unknown instruction" (so the ratified spelling could not
  round-trip through text); the parser unit test
  `every_binop_display_name_parses_back` holds every `BinOp` to it. The
  producer respell (WS5.13) is a `~/trust` companion;
  `a.lean.bool_connective` flips with it. The allocation-bound lint
  (`alloc_bound`) read a guard negated only through `not bool`, the refused
  spelling; it now also reads `bxor %c, true` (and `xor` with a `Bool`
  constant, either operand order; `false` keeps the guard) as the negated
  guard, held by `a_guard_negated_by_bxor_true_bounds_the_other_edge`, and its
  interpreter differential generator negates with `bxor`.
- **The allocation-size lint has no threshold: `ALLOC_BYTE_BUDGET` is deleted
  (2026-09-30; approved by the owner 2026-09-29).** `trust_ir::alloc_bound`
  reported a provably-constant allocation of 256 MiB or more, and silenced a
  runtime count only under a bound proving it below 256 MiB — a number with no
  rationale of its own since v50 made the interpreter's allocations sparse. It
  now reports only the allocations whose byte size is NOT provably within the
  largest object the module's target can hold, `isize::MAX` at its pointer
  width (`max_object_bytes`): the target's definition of an object, the same
  for every program, and the only line a bound must clear to say anything (the
  count's own integer type is always a bound). `ConstantOverBudget` became
  `ExceedsObjectLimit` (every execution asks for more than the largest object:
  it can never succeed); `UnboundedRuntimeCount` keeps its name; the new
  `UnknownElementSize` reports an allocation whose element type has no byte
  size (a sequence, set, record, closure, dialect or error type, a missing or
  cyclic type entry, a struct with no declared size, a tuple with no layout
  descriptor), which the lint used to skip. A 512 MiB or a 64 GiB constant is
  no longer reported. `check_allocation_bounds(module)` reads the pointer
  width from the module's target (it took a caller-supplied `64`) and adds
  `object_limit` to each finding. Elements are sized on EVERY target by a
  memoized size-only query: a size needs no alignment, so a scalar is its
  width, a struct its declared size, an array its element times its length,
  in `u128` (an element of `2^61` bytes or more is judged exactly; a product
  beyond `u128` exceeds every object). Sizing through `ty_layout_shape`, which
  refuses every scalar off its canonical alignment table, would make the lint
  silent on i686, armv7, riscv32, powerpc64le and s390x — the review of this
  change measured exactly that with the CLI — and the old lint reported
  there. Aggregates and `bool` are sized (they were skipped or read as zero
  bytes), and a one-element allocation is judged by its element's size. The
  analysis is new: an unsigned interval (and a signed upper bound) for every
  integer SSA value — exact wrapping constant folding, interval arithmetic
  that keeps a bound only while the result cannot wrap, masks, remainders,
  shifts, casts, `select` (so `n.min(K)` is bounded), block parameters joined
  over their incoming edges, and the facts a dominating branch, `Switch` case,
  `Assume` or `Assert` states, including the false edge of an unsigned
  `Overflow` flag — computed in ONE walk of the shared
  `analysis::DominatorTree`. It replaces a constant folder that iterated to a
  fixpoint under an iteration backstop and dominator SETS (O(blocks^2)
  memory). Measured (release, 2026-09-30, a chain of `n` blocks stored in
  reverse order): the old lint took 8.7 s at n = 1000 and 158.8 s at n = 2000
  on a block-parameter chain (19.8 and 58.0 MB peak), and 15.3 s at n = 16000
  on a plain value chain; the new one takes 1.7 ms and 4.0 ms on the first,
  and 0.55 s / 254 MB at n = 100000 and 10.5 s / 2.9 GB at n = 1000000 (the
  input module alone is 1.13 GB there, and the shared dominator tree 0.5 GB
  and 4.9 s; that tree's Cooper–Harvey–Kennedy fixpoint grows about 26× per
  10× blocks and is now the lint's super-linear term, named in the module
  docs). A work census counts blocks, instructions, edges, joined arguments
  and element sizings, and the tests hold each to the program's own counts.
  Sound in the reporting direction: a signed comparison no longer bounds an
  unsigned count (the old lint discharged `(n as i64) < 1000` for a `u64`
  `n`, which every `n >= 2^63` passes); a loop-carried count, and a value
  computed before the guard on its operand, are reported. Only DEFINED
  executions are judged (a zero or negative count is UB at the allocation),
  and the line is the largest object, not an availability figure, so an
  unchecked `i64` count of bytes and a `u32` count of `u64`s are not reported;
  the module docs and the CLI README say so. The `validate` CLI prints every
  note (it printed five and a count). Tests, in the new gate
  `allocation-bounds` (beside gate 9; the lint's tests ran in no gate):
  `alloc_bound_tests.rs` (32 cases, one per rule, including a precision table,
  the targets off the alignment table, and a 200000-entry type chain, which
  the sizer follows in a loop rather than on the stack); `alloc_bound_property_tests.rs`,
  every transfer function checked against the reference interpreter's own
  integer arithmetic (`eval_int_*`), exhaustively at 3 and 4 bits and by
  boundary sampling at 8 to 128 bits; and `alloc_bound_differential_tests.rs`,
  the whole lint against interpreter runs of 1500 random programs (diamonds,
  parallel edges, switches, loops, selects, overflow flags, assumes, every
  cast and width, shuffled blocks; 6000 measured clean), with the verdicts
  required identical on non-canonical targets of the same pointer width.
  Mutation check: 26 hand mutants (the review's twelve, and the sizer's,
  census's and rules' own) each fail the suite. `cli_alloc_bound` runs the
  CLI on seven targets. The superproject's `trust-vcgen` keeps its own copy
  of the number (`UNBOUNDED_ALLOC_BYTE_CEILING` in its `generate/mod.rs`);
  that copy follows in a later superproject change, recorded in
  `HANDOFF.md`.

- **Sequence and set values are persistent ropes (2026-09-30).**
  `InterpretValueKind::Sequence` and `::Set` hold an `ArrayValue`, the
  structure arrays and vectors use since v50, instead of a `Vec`.
  `InsertElement` on a sequence copies one root-to-leaf path and shares the
  rest (it cloned the whole sequence); `ExtractElement` is O(height);
  `SeqMapAddK` / `SeqMapNot` map each stored value once, so a uniform run costs
  one step whatever its length; `SeqMap` still calls its element function once
  per element, in order, because that function is arbitrary code. Set has no
  insert path; it moved with Sequence because the two share payload patterns
  in this tree and in trust-cg's `e2e_aarch64_sequences.rs`. `ArrayValue` gains
  `FromIterator`, so a `.collect()` into either kind still compiles. Test:
  `a_sequence_insert_is_persistent_and_never_copies` runs an insert, both
  versions' reads and a map at 4096 and 2^16 elements, where the result
  stores exactly three values (a materializing regression stores thousands
  and fails in milliseconds), and then at 2^40 elements. No wire, Lean or
  semantic change. Downstream: a consumer that matches `Sequence(xs)` beside
  a `Vec` payload in one or-pattern stops compiling at its next pin move (the
  superproject's `trust-thir-lower/src/differential.rs` does).

- **The enforcement-links scanner finds `#[path]` test modules (2026-09-30).**
  `cfg_test_module_files` resolved `#[cfg(test)] mod name;` only to `name.rs` /
  `name/mod.rs`, so source files outside `tests/` read as live code: the test
  modules loaded by `#[cfg(test)] #[path = "..."] mod tests;`
  (`core_execution_*_tests.rs`, `term_scope_*_tests.rs`,
  `interpret_uninit_tests.rs`, …) and the ones they declare
  (`proof_assembly_let_tests.rs`, `proof_assembly_prefix_tests.rs`). Measured
  on the 2026-09-30 main tree: 15 whole-file test contexts found before, 71
  after, 34 of the new ones outside `tests/`. It now resolves every
  out-of-line module declaration by rustc's rules (`rustc_expand::module`):
  `#[path]` relative to the declaring file's directory, or inside inline
  modules to the directory they name; `#[path]` before or after `#[cfg(test)]`;
  raw-string paths; `..`. A file is a test context in full when every
  declaration that loads it is test-only — its own or an enclosing inline
  module's `#[cfg(test)]`, or a declaration inside a test file — so a test
  file's own submodules are test files and a `#[path]` helper a live
  declaration also loads stays live code. A Cargo target root (a library,
  binary, build script or example, by Cargo's discovery or a manifest
  `path` / `build`; `cargo_target_roots`) counts as loaded live, so a
  test-only `#[path]` load of a crate root cannot turn its body into test
  evidence. Linear in the sources: a declaration is found by its `mod`
  keyword and its attributes are read backward from it (a pattern that began
  with the attribute run was quadratic in a long run: 3.86 s at 8000
  attributes, now 0.031 s), inline modules are parent-linked and resolved
  through a directory tree of the sources once each (copying the brace stack
  per declaration was quadratic in nesting: 6.4 s at 2000 levels, now
  0.035 s), and a worklist decides the contexts. A `ScanWork` census lets the
  tests hold both to the input's size. The live gate's verdict is unchanged
  (39 units, 743 citations, 1 unnamed variant). Tests:
  `TestModulesAreFoundTheWayRustcLoadsThem` (nine cases, two through the
  gate: a `#[path]` test file witnesses `(test)` and hides no dead variant;
  a crate root loaded through a test-only `#[path]` stays live code).
- **Rule H reads an untyped pointer and laundered data member by member
  (2026-10-03).** `CarriedKey::Untyped` (new variant) is what an untyped
  pointer carries: everything `Any` admits but a confined member, since
  memory holding a confined erasure is reached through a raw pointer only
  after a cast or raw pointer of a type that carries its principal, which
  demotes it. `ReachGraph::add_launder_of(site, member)` records a LAUNDER of
  a known callable (`f as usize`): laundered data then holds that member,
  where `add_launder` lets it hold any callable. `ClosedPools::may_hold`
  decides both, member by member, in the hand-off derivation (every key, or
  the keys the callee's closure invokes).
- **Typed LAUNDER: laundered data holds what the LAUNDERs' keys admit
  (2026-10-03).** `CarriedKey::Laundered` admitted every key once any
  LAUNDER existed (one crate-graph-global boolean), so a crate whose only
  way of putting a callable into data was a pointer or union pun (no value
  LAUNDER) let data hold nothing, and one value LAUNDER let it hold
  everything. `ReachGraph::add_launder_keys(site, keys)` (new) records a
  LAUNDER whose reinterpreted bytes may hold callables of `keys`;
  `Laundered` now admits the union of every LAUNDER's keys
  (`IndirectCallUniverse.laundered`, `ClosedPools::laundered_keys`, new,
  each key with the first site that recorded it). `add_launder(site)` is
  `add_launder_keys(site, [Any])`, its meaning unchanged (the trust-ir lane
  and running inline assembly). `ClosedPools::may_hold(Laundered, m)` asks
  whether a laundered key admits the member's OWN key (shape matching is
  not transitive, so `admits(Laundered, Fn(_))` holds whenever a laundered
  key may be a fn pointer); `admits_principal` and the open-principal set
  read the keys; a laundered principal no member records is open. Demotion:
  a LAUNDER of `Any` or `AnyDyn` demotes every confined member, one naming a
  principal demotes it as a LIFETIME-ERASE does, and one of fn keys or
  `Untyped` demotes none. Sound only while every route by which a
  callable's bytes reach data is a recorded LAUNDER with covering keys (the
  MIR adapter's routes P, U, S, A, C; spawn-census design §10). The
  reference derivation reads the same predicates; the 3000-graph
  compressed-versus-reference test and the 300-graph brute-force path test
  draw keyed LAUNDERs. Tests: `a_keyed_launder_admits_only_its_keys`,
  `a_keyed_launder_admits_a_member_a_nontransitive_shape_matches`,
  `add_launder_is_a_launder_of_any`,
  `a_keyed_launder_demotes_only_the_principals_it_names`,
  `an_untyped_launder_holds_no_confined_member_and_demotes_none`,
  `a_principal_launder_admits_its_upcasts`,
  `a_laundered_principal_no_member_records_is_open`,
  `a_keyed_launder_in_an_unclosed_graph_reaches_the_sink`.
- **Rule H reads an untyped pointer member by member (2026-10-03).**
  `CarriedKey::Untyped` (new variant) is what an untyped pointer carries:
  everything `Any` admits but a confined member, since memory holding a
  confined erasure is reached through a raw pointer only after a cast or raw
  pointer of a type that carries its principal, which demotes it.
  `ClosedPools::may_hold` decides it, member by member, in the hand-off
  derivation (every key, or the keys the callee's closure invokes).
  `ReachGraph::add_launder_of(site, member)`, a LAUNDER of one known callable
  after which laundered data held only that callable, was added and withdrawn
  the same day, unreleased: data also comes to hold a callable with no LAUNDER
  (a pointer, union or reference-transmute pun of a fn pointer read as an
  integer), so the narrowing made spawning callables handed to foreign code as
  integers QUIET. Every LAUNDER lets data hold any callable, as before.
- **A LAUNDER no longer merges the FnPools (2026-10-02).** One `f as usize`
  anywhere in a crate graph (foldhash's global seed, reached through
  hashbrown) made every fn-pointer call reach every fn member. A member is
  filed under its own signature's shape, a call through an ABI-incompatible
  fn pointer type is undefined behaviour (R4), and the shapes are closed
  under the std `fn` ABI-compatibility rules (the same argument that keeps a
  pointee reinterpretation from being a LAUNDER), so a laundered callable
  called back is called at a shape its own pool matches. A LAUNDER still
  demotes every confined member and still lets data
  (`CarriedKey::Laundered`) carry any callable under rule H.
  `ClosedPools::fn_pools_collapsed` is renamed `laundered`.
- **The spawn census engine stores derived edges through hubs (2026-10-02).**
  `ReachGraph::solve` derived one APPROX edge per (invoking site, pool
  member) and per (hand-off, target): on real crates that was millions of
  edges (tla-cli's `ty` binary passed 26 million from local sites alone, and
  its census did not finish in 50 GB). A derivation fact now names a hub
  (`ReachNodeKind::Hub`, a new variant: an exhaustive match over
  `ReachNodeKind` needs an arm): one edge from the fact's node to the hub and
  one from the hub to each target, interned by target list, so a pool costs
  one list however many sites invoke it. Nothing a census answers changes:
  the search passes a hub at no cost and scans its facts in derivation
  order, so labels, per-definition joins, witnesses, spawn sites and thread
  closures are, edge for edge and in the same order, those of the edge-by-
  edge derivation, which is kept as a test-only reference and compared on
  3000 random fact graphs (closed and unclosed pools, LAUNDER, upcasts,
  confinement, rule H groups, `via_drop` sites). `ExpandedReachGraph::edges`
  is now the compressed graph the certificate is checked against (its ranks
  double the distance, a hub's one more); `logical_edges` lists the
  uncompressed edges, and `derived_edge_scan` lists one node's derived edges
  with their place in derivation order. Pool membership is computed once per
  key and rule H's targets once per carried set and callee component, not
  per fact.
- **Test and gate audit: one feature resolution, no duplicate runs, leaner
  debug builds (2026-10-01).** Measured on a 4-core Linux host with stock
  Cargo standing in for Targo.
  - Build profile: dev builds carry line tables only (dependencies none).
    Full DWARF made each test binary, which statically links trust-ir-build
    and the Clean stack, up to 1.5 GB; the all-features debug tree hit 27 GB.
    The Clean elaborator stack `clean-verify` pulls in (`clean-elab`,
    `clean-macro`, `clean-parser`, …) now builds at opt-level 3 like
    `clean-kernel`: the replay tests spend their time elaborating Clean's
    eval-IR prelude (`core_execution_byte_replay` 125 s -> 77 s,
    `core_execution_atomic_replay` 114 s -> 62 s).
  - `scripts/ci_gates.sh`: every compiled test gate runs `targo test
    --workspace`, one feature resolution, instead of `-p <crate>`, which
    resolved six feature sets and rebuilt trust-ir, trust-ir-build and
    clean-kernel for each; gate 9's `-p trust-ir` leg compiled
    `make_aggregate_formats` and `array_splat_formats` to nothing (they now
    run). One test run per registry gate. Build parallelism is Targo's default
    instead of `-j 1`; `TRUST_IR_TARGO_JOBS` caps it. Gate 0's script tests run
    one process per file (`scripts/run_script_tests.sh`, about 80 s -> 30 s).
  - Duplicate or vacuous runs removed: gate 5's green half (gate 3 runs
    `cli_lineage`), gate 9's conformance registry (its three targets ran in
    gate 8 as well), `giveback-stays-untrusted` (`test -p trust-ir-giveback`,
    a crate with no tests), and the script tests that re-ran gate 0's own
    live-repository checks; in `ci-self-verify.sh`, the `check` that `tippy`
    subsumes, the explicit `conformance` and `cli_discharge` re-runs, the
    separate `-p trust-ir-ay` rebuild, and the `sorry|admit` grep, which a doc
    comment's "admit" (`Aggregate.lean:95`) made fail before any build
    (`lean_proofs.py` is the check).
  - Fixed: `check_trust_default_authority.py` read a symlink's own mode bits,
    which Linux reports as 0777, so 4 gate-0 tests failed on Linux.
  - Stale or duplicated tests removed: the archived 2026-09-17 claim-repro
    ports whose flipped twins live in their parent files (the c02, c03, c05,
    c06, c07 and c12 modules, `cli_verify_repros.rs`,
    `parser_never_panics.rs`), `m0_selfhost_acceptance.rs` (a proxy checklist
    the b1/b2/b4 tests cover), `contract_surface_body_gate.rs` (the
    `body_gate` golden), the diff "ported ratchets" block and `text_losses`'
    `b7.text.flip.*` copies (gate 11 holds those rows), `scout_emit_T1`, an
    ay batch-builder subset test, tautological tests (`_tyid_smoke`,
    `catalogs_are_exhaustive`, interner duplicates), `lean/clean-test/`
    (April Clean-elaborator scratch nothing ran) and `benchmarks/data/`
    (1.3 MB nothing read).
  - Build hygiene: the conformance test targets use the library's `fixtures`
    module instead of each recompiling the 5.3k-line `generate.rs` (whose own
    target is now `test = false`); trust-ir-cli's helper moved to
    `tests/common/mod.rs` (it was an empty test binary); binaries without unit
    tests are `test = false`; the benchmark generators are no longer default
    members.
- **`trust-ir dependencies` refuses a `Drop` (2026-09-30).** The dependency
  census used to add no edge for an `Inst::Drop`, so the destructor it runs
  was a dependency nothing reported. It is now a refusal,
  `ImplicitDestructor(<type>)`, and the command exits 1 on any module with a
  reachable drop. The other implicit runtime services stay outside this
  census, as its output line now says.

- **Clean pinned at `b7689c12`, AY at `630842a8`; ByteV1 ExtractField sites
  carry their operand catalog (2026-09-30).** Clean `ee4dff170` made the
  ByteV1 `extractfield` read the aggregate's NOMINAL type from the site's
  operand catalog (`IRByteSiteV1.mkt`); at an old catalog-less `mk` site the
  step halts `unmodelled`. `reflect_core_module_v1` emitted `mk` for every
  site, so on the new pin the actual copy-then-extract program no longer
  replayed (`authored_rust_struct_copy_extract_replays_actual_three_step_whole_world`:
  kernel audit `TypeMismatch`). Every reflected ExtractField site is now
  `mkt`, its one row the actual aggregate operand and its actual SSA type;
  every other site keeps `mk`. The scalar assembler's ExtractField arm is the
  dispatcher's own `ir_byte_extract_field_v1` over the fetched site, no
  longer the untyped `ir_ef_at`. New tests: the reflected catalog (unit), the
  lane read over the reflected, absent and three forged catalogs (kernel), and
  an assembled Copy + ExtractField + return run kernel-replayed with two
  forged lane values refused. AY moved with Clean, which co-owns it.
  `b7689c12` is Clean main with its own fast local gate, fmt and clippy
  green; two red legs on Clean main were fixed there for this move (a
  self-skipping `Init.Prelude` test now fails without the pinned Lean, and a
  moved help-claim anchor was re-verified).

- **The x86-64 vector-compare certificates are re-certified under AY
  `630842a8`, and the per-cell rule names it (2026-10-01).** The AY move above
  left `docs/dialects.md`'s certificate ground naming `f28345ff`, while
  trust-cg's gate (`scripts/check_x86_icmp_certificates.py`, a
  `soundness_check.sh` leg) requires the AY its lock pins to be the rule's,
  so a trust-cg lock following trust-ir to `630842a8` failed it as
  `ay-pin-differs-from-rule`. Re-run with that gate's own recipe from two
  independent `630842a8` builds against the rule's Clean (sha256
  `9c594e83...`): all 32 certificate cells `unsat`, `unproved_steps=0`, no
  `hole`, Clean fully verified, on unchanged query bytes, every proof
  byte-identical across the builds (15 of 32 also identical to
  `f28345ff`'s). The rule now names `630842a8` and records both builds;
  `f28345ff` stays as the cells' first certifying AY. No code changes.

- **SPEC §17 restated: the trust-cg bridge's memory-placed-argument half has
  landed, as an ordinary pointer parameter; its register-exhaustion residuals
  are named (2026-09-29).** §17's `(external)` entry said the bridge's half
  "did NOT land" and that its `NativeC` claim was false for a memory-placed
  argument. Since trust-cg `15f6b78d3` (x86-64) and `27fc93a0e` (AArch64) the
  bridge declares rustc's `Indirect { on_stack: false }` argument as a `Ptr`
  parameter holding the address of a fresh caller-made copy, which is outside
  `Module::is_by_value_aggregate_slot`, so no slot is left to misclassify and
  §17 gets no second pre-lowered spelling. The retraction bullet keeps its
  2026-09-27 record and says so; the `(external)` entry names the landed lane,
  its refusals (one placement-mode table in the bridge, every cell a unit test;
  a required `FnAbi` source) and the aarch64-apple-darwin measurements (the
  `m145` rlib x bin matrix at trust-cg `a3771750c`, `8328b1068`, `0d0257f58`
  and after the 2026-09-29 change, none wrong; the scalar pairs at argument
  position 7 fixed by trust-cg `ab0b74ce0`; `targo --unverified`, no proof
  claim). The `(prose-only)` entry no longer says the bridge declines
  memory-placed arguments, and says what its gates do NOT establish: they
  compare each register-placed slot in isolation, and one family is measured
  wrong at register exhaustion and open (a Rust-ABI cast aggregate of 1 to 4
  bytes on the Darwin stack). The scalar-pair fix is stated for the callees it
  covers (direct, `fn`-pointer and `dyn` calls): a closure body keeps a pair
  as one whole slot, was measured wrong where another backend's code calls it
  by symbol, and is refused there by trust-cg since 2026-09-30 (review
  finding). The rust-call sentence names the tupled callables it is about.
  Classes unchanged (`external`, `prose-only`); no class is raised. Doc only:
  no wire change, no fixture byte changes.
- **The x86-64 vector-compare certificates are re-run by a trust-cg gate;
  `docs/dialects.md` now says what that gate checks and what it does not
  (2026-09-30).** The per-cell rule's certificate ground (clause 2.) was
  labelled `(external: measured, not gated)` and said "Nothing re-runs it".
  That stopped being true when trust-cg `803bcb5ea` (2026-09-29) merged
  `scripts/check_x86_icmp_certificates.py`, a leg of trust-cg's
  `scripts/soundness_check.sh`. The gate:
  - reads clause 2. at trust-cg's pinned trust-ir revision;
  - requires trust-cg's AY pin to be the clause's AY, and builds that AY;
  - requires the clause's Clean by sha256;
  - regenerates every cell's query from trust-cg's registered obligations,
    requires each certificate-ground query to hash to its pinned digest, and
    requires each of the eight instruction-model queries to be
    `(assert false)` with no pin;
  - on each of the 32 composite cells, requires AY `--strict-proofs` to
    answer `unsat` with `unproved_steps=0` and no `hole` step, and Clean's
    `cert verify-external` to report the proof fully verified.

  The entry is now `(external)` and names the gate, its soundness leg, its
  unit tests and its skip rule: a missing input fails, and an explicit skip
  leaves the run nonzero and is refused under `--attest`. It ranks the result
  as a Carcara-checked SMT proof, not a Clean-kernel certificate. It also
  lists what stays ungated:
  - the link from the query to this format's `ICmp`: the query's trust-ir
    side is trust-cg's own SMT encoding of the predicate
    (`encode_trust_ir_v128_compare_mask`, a boolean lane predicate carried
    as an all-ones / all-zeros lane mask), and nothing compares it with the
    Lean `semVectorICmp` or the reference interpreter. A pass shows that
    the machine composition equals that encoding;
  - the link from the lowering to the query: every per-instruction SMT model
    the 32 obligations call (`pcmpgt*`, `pcmpeq*`, `pxor`, `por`, and
    `pand` / `pshufd` in the `v2_i64` unsigned sequence), the bias
    materialization, and nothing binding the query to the bytes a compile
    emits;
  - the eight instruction-model cells;
  - landings: the gate runs only where someone runs it and its inputs exist.
    trust-cg's landing train, its opt-in pre-push hook and its release
    boundary would each require the leg, but none is in force under the
    owner's 2026-09-27 exception. Measured today, trust-cg has no
    attestation record locally or on origin, and the local checkout has no
    installed hook;
  - the compiler's own AY, which does not re-derive the certificates.

  One statement is new: clause 2. is machine input to that gate, and nothing
  in this repository checks its form. The stale "NOT LANDED on the trust-cg
  side" paragraph is replaced. trust-cg `51448e5df` moved its pin to
  `8e81e98a` and admits the four `v16_i8` cells, and it changed the three
  tests that paragraph named in the same commit.

  Measured at trust-cg origin/main `aedd224c9` on 2026-09-30 (arm64 macOS;
  every build `targo --unverified`, so no proof claim):
  - the gate passed in 208 s: 32 certificate cells, 8 instruction-model
    cells degenerate, 0 fail-closed. AY came from its 2026-09-29 cached
    build, whose sha256 the gate re-checked;
  - its unit tests passed 32 of 32;
  - `x86_icmp_manifest_cells` passed 4 of 4, `x86_vector_icmp_admission` 1
    of 1, and the adapter's `x86_vector_icmp_gate_tests` 3 of 3;
  - the Trust toolchain's own AY (0.26.0, `075a482ae`) answers a bare
    `unsat` on all 32 composite queries, and `unknown` on all 32 under
    `--strict-proofs`;
  - a `v16_i8` `ult` query rebuilt with both sides' operands swapped (lanes
    `bvult` of (rhs, lhs), the `ugt` composition) differs from the
    registered `ult` encoding at `lhs = 1`, `rhs = 2` (AY `sat`), yet with
    its pin moved to the new digest the gate's certificate phase passed on
    all 32 cells; left unpinned, it failed `query-digest-mismatch`;
  - the edited `docs/dialects.md` still parses under the gate's own
    `parse_rule` to the same AY revision and Clean sha256.

  Doc only.

- **The consumer and producer halves of the two 2026-09-27/29 release rulings
  are stated as landed (2026-09-29).** Two sections of
  `docs/SPEC_RATIFICATIONS.md` still called their other-repo halves pending.
  Both have landed on their repos' origin/main.
  - SPEC "An ARC operation counts only a reference-counted cell": trust-cg
    `b17c05f72` moved its trust-ir pin `8e81e98a` to `fca90a2c`, which
    contains `25624afd`. It adds the `FSYM_INTERPRETER_UB_SITES` entries
    `is_unique` and `arc_allocation_mut` (`fsym_ub_map.rs:884`, `:890`) and
    the test
    `interpreter_refuses_every_row_of_the_corpus_as_compiled_as_a_non_rc_arc_op`
    (`e2e_aarch64_arc_ops_linux.rs:371`). That test requires all 11
    `ORACLE` and `INTERPRETER_UB` rows of the corpus as compiled to be UB at
    an ARC op on a `CMalloc` or `RustHeap` cell. The CleanHeap twin
    (`56412d4e9`) reached trust-cg origin/main in the merge `c83bda01a`. Run
    here at trust-cg origin/main `07dc5c153`: `e2e_aarch64_arc_ops_linux`
    passed 5 of 5 and `fsym_ub_map` passed 13 of 13. The section's
    `(external)` entry is restated with file:line, and its Consumers
    paragraph no longer says the pin move remains.
  - SPEC "A reference-counted cell is released by `Release`, never by
    `Dealloc`": the Clean-side gap is closed. Clean `143e9278f` moved Clean's
    trust-ir pin from `c603897b` to `8e81e98a`, which contains the ruling
    `2a4e6eb8`. Its `assert_certifies` now calls
    `assert_pinned_trust_ir_rechecks` on every Fragment-4 heap corpus
    program (15). That helper requires the pinned `validate_module` to accept
    each Clean-minted certificate and to refuse its Release-dropped twin.
    `heap_certificate_is_rechecked_by_the_pinned_trust_ir` adds a retargeted
    `Load` and a `Release` respelled `Dealloc`. These results are Clean's
    commit record, not re-run here. Clean's own workspace `[patch]` builds
    that re-checker against Clean's `clean-kernel`, which at Clean
    origin/main `61ee09d10` is byte-identical to the one this repository
    pins (`afe42324d`). The same entry's older file:line citations are
    re-read at `61ee09d10`. `test_fragment5_certifies_boxed_nat_constant_with_a_release`
    is gone there, because Clean `d9f760a4d` stopped minting Fragment-5.
  - The ARC section's Producers paragraph now says that Clean's pin
    (`8e81e98a`) predates the ARC ruling, so at that pin Clean's
    `perceus_reset_reuse_semantics_tests.rs` has not run against the ruling.
    The file, taken from Clean `61ee09d10` and included into a scratch test
    against this repository's interpreter at `e1487cf1`, passes.

  Everything was measured with `targo --unverified` (no proof claim). Doc
  only.

- **An ARC operation counts only a reference-counted cell: one meaning in the
  interpreter and Lean.** On an allocation that is not reference-counted,
  `Retain` / `Release` / `IsUnique` had two meanings. The reference
  interpreter counted any live allocation (every allocation started at count
  1, and the checks were liveness only). Lean's `requireArcRef` called the
  operation UB, because only an RC-origin `semHeapAlloc` grants `arcRef`. The
  interpreter's own pinned-runtime path (`check_rc_cell`) already refused such
  a cell. Lean's rule is adopted, and Lean's semantics does not change
  (`docs/SPEC_RATIFICATIONS.md`, new section of that name). `arc_allocation_mut`
  and `is_unique` now refuse, after the liveness check, every allocation whose
  recorded origin is not `SwiftHeap` / `CleanHeap` — a stack `Alloca`, a
  `RustHeap` or `CMalloc` cell, a global's reservation, an interpreter-internal
  cell — as `UndefinedBehavior` naming "not a reference-counted cell". The
  `retain` doc loses its false "at its base (offset 0)" clause: the offset is
  not checked, and interior and out-of-range operands are not decided. The
  six ARC-on-non-RC cells of `release_discipline_agrees_across_engines` leave
  its shrink-only ledger (`LEDGERED_RELEASE_CELLS` is deleted) as decided
  `ub`, joined by `Retain` alone and `IsUnique` on every region: 30 decided
  cells, 12 of them non-RC `ub`/`ub`. New: `arc_on_a_global_reservation_agrees_across_engines`
  (a global's reservation: every ARC op `ub` in both, `Keep` ok 7) and
  `arc_operation_on_a_non_reference_counted_allocation_is_undefined_behavior`
  (interpreter). Lean gains `requireArcRef_non_arcRef_is_ub`, the general
  `semRetain_non_arcRef_is_ub` / `semRelease_non_arcRef_is_ub` /
  `semIsUnique_non_arcRef_is_ub` (over the permission of the live allocation
  that contains the address), four axiom-free instances (stack, `RustHeap`,
  `CMalloc`, global), and the address-model pin
  `retain_one_past_rustHeap_counts_neighbour`, all AxiomAudit-guarded; that a
  non-RC allocation holds a non-`arcRef` permission is read off the
  allocation sites, not proved. SCOPE, measured: the interpreter resolves an
  ARC operand by provenance and Lean by address, over a back-to-back
  allocator, so the agreement holds only while the pointer lies inside the
  allocation it came from. A sample of the one-past-end shapes (the `i32`
  operand `a + 4`, at most two cells) is a new shrink-only ledger,
  `arc_operand_provenance_divergences_stay_as_measured`. It holds the whole
  family THIS change turned from agreeing into diverging at that operand: a
  stack, `RustHeap`, `CMalloc` or global allocation followed by a
  `CleanHeap` or `SwiftHeap` cell, under `Retain`, `Release` and `IsUnique`
  — 24 combinations, each ok 7 in both engines with the interpreter of
  `8e81e98a` (measured) and now rust "not a reference-counted cell", Lean
  ok 7. Beside it, three shapes that diverged before too: a lone `CleanHeap`
  cell (rust ok, Lean "ARC pointer does not refer to a live allocation"),
  `CleanHeap` then `CleanHeap` (rust 2, Lean 1: Lean counts the neighbour),
  and `CleanHeap` then `RustHeap` (rust ok, Lean "requires arcRef"); an
  interior-pointer control agrees. The ledger holder now reports every cell
  that moved, not the first. The two borrow shapes the release section left undecided are now a
  ledger too, `borrow_permission_divergences_stay_as_measured` (`Dealloc`
  under a live `Borrow`: UB by ub-numerics §6 policy, not implemented by the
  interpreter; `Borrow` / `BorrowMut` of an RC cell: undecided), and the
  unconsulted `Permission.canRead` / `canWrite` columns are OPEN in
  ub-numerics §7 (`arcRef_forbids_write` / `arcRef_read_only` relabelled as
  table facts). §10's ownership-transfer rule is narrowed: the parts the
  interpreter executes are now `(test)`, the rest stays `(prose-only)`. No
  producer emits an ARC op on a non-RC allocation (Clean's perceus
  reset-reuse semantics test uses `CleanHeap` cells). The one consumer that
  relied on the old reading is trust-cg's ARC-ops corpus, whose compiled
  cells are all `CMalloc` / `RustHeap`. Its oracle already replays a
  `CleanHeap` twin (trust-cg `56412d4e9`, at its pin `8e81e98a`, landed
  before this change): measured against this change's interpreter with the
  corpus of trust-cg origin/main `6ce36a21b` in a scratch test, the twin runs
  all nine `ORACLE` rows to their closed forms and refuses both
  `INTERPRETER_UB` rows with their texts, while the untransformed corpus is
  UB on all nine rows. trust-cg's pin move still has to add the two new
  `fsym_ub_map` sites (`arc_allocation_mut`, `is_unique`) and assert the
  untransformed corpus is UB. No wire, tag, golden or digest-domain
  change. Measured with `targo --unverified` (no proof claim) and a full
  `lake build`.

- **Clean's Fragment-4 Release mirror is stated as landed.** SPEC "A
  reference-counted cell is released by `Release`, never by `Dealloc`" still
  marked Clean's half "PENDING, not landed", measured at Clean `c3a3b2d61`
  (so does the Release-discipline entry below). The mirror landed at Clean
  `b1cd6ac3d`, merged to Clean origin/main as `b2f169669`. The section's `(external)`
  entry now states it in the present tense, read at that origin/main with
  file:line: the minter's `alloc_release_balance`
  (`emit_trust_ir_tv.rs:377`), the clean-reflect walker's `Release` and
  `Dealloc` arms (`denote.rs:1096`, `:1122`), seven minter tests in
  `emit_trust_ir_tv_tests.rs` and four walker tests in `denote_tests.rs`, and
  the absence of the old `alloc_dealloc_balance` /
  `heap_refuses_dropped_dealloc`. The test results are Clean's commit record,
  not re-run here. The entry also names the gap that remains: Clean pins trust-ir
  `c603897b`, which predates the ruling `2a4e6eb8`. Read at that revision,
  its re-checker routes `Dealloc` and not `Release` to the heap walker and
  requires one `Dealloc` per cell, so it refuses a Release-spelled heap
  certificate (fail-closed) until Clean moves that pin. Doc only.

- **The four unsigned `<16 x i8>` x86-64 vector compares are available;
  no `icmp` cell is fail-closed any more (2026-09-28).** `chc_x86.v16_i8`
  `icmp.ult`/`ule`/`ugt`/`uge` were Deferred
  (`unsigned_vector_compare_proof_blocked`). They are now contract rows on
  the certificate ground of the per-cell rule, publishing the sequence
  trust-cg's `emit_narrow_unsigned_vector_comparison` emits for
  `V16I8Icmp` (`mov` `0x80808080`, `movd`, `pshufd 0`, `pxor` both
  operands, `pcmpgtb`; `ule`/`uge` OR the unbiased `pcmpeqb`), bias
  `splat_i8(0x80)`, guard `x86.sse2`. The certificate: trust-cg `7b81d2cb1`
  respelled the sign-bit bias constant as two 64-bit halves (same 128-bit
  value), and on those query bytes AY `f28345ff` `--strict-proofs` answers
  `unsat` for all 16 unsigned cells with no `hole` step, Clean 0.9.0
  `cert verify-external` fully verified, from two independent AY builds
  (binary sha256 `15908a9a…` and `dc6c3bf4…`), proofs byte-identical
  (trust-cg `reports/2026-09-27-x86-vector-icmp-cells.md`). Measured, not
  gated here. `docs/dialects.md` now gives both measured AY factors behind
  the old hole, where it first gave only the printer ("spells one rule as
  `hole`"). One is the proof checker declining a term over 4096 nodes,
  counted as a tree without sharing. The other is a printer with no external
  spelling for the declined positive-unit bit-blast lemma, which prints it as
  `hole` instead of failing. The cap alone is not the whole cause: with only
  the cap raised to 65536, `ult`/`ugt` go hole-free, but `ule`/`uge` keep the
  hole, and a counting probe shows neither the node cap nor the depth cap
  tripping for them (largest term 7524 nodes). That decline is not
  identified. It was measured twice, from independent builds with
  byte-identical proofs (`targo --unverified`, not gated).

  Corpus: `refuse/vector_unsigned_cmp_bytes_x86` is retired (manifest row,
  its three fixture files deleted, builder, `ROWS` entry and the
  `chc_x86_icmp_cell_fail_closed` trigger). Its trigger called the reader,
  and with the flip in place it failed ("the module no longer carries the
  construct"), as designed. Item 3's "an x86-64 consumer MUST refuse a
  fail-closed cell" has no subject today, so it now cites the `none` row
  `refuse/vector_icmp_fail_closed_cell_x86` and says so; a cell that turns
  fail-closed again arrives with a module row.
  `HardwareVectorContractReason::UnsignedVectorCompareProofBlocked` stays: it
  is in the published reason vocabulary
  (`HARDWARE_VECTOR_CONTRACT_REASON_CODES`) and no downstream repo names the
  variant (grep of trust-cg, ty, ~/trust, clean, ay at origin/main), but no
  row emits it now, which a new test pins
  (`hardware_vector_reason_vocabulary_keeps_the_unemitted_proof_blocked_code`).
  The request tests' fail-closed set is now an explicit per-cell table,
  empty.

  Mutation controls (unverified lane, `targo --unverified`, no proof claim;
  all restored): the `v16_i8` `icmp.uge` row flipped back to
  Deferred/proof-blocked fails 5 `trust-ir` lib tests (coverage, reader,
  narrow-SSE2, vocabulary, manifest lines) and
  `producer_owned_manifest_identity_helpers_are_public_and_self_consistent`;
  flipping `icmp.ugt` back fails those plus the two row-order checks. Dropping
  the `none` row's citation from `docs/dialects.md` fails enforcement-links
  rule R.

  No wire change; `VERSION` stays 50. The `chc_x86` manifest sha256 changes,
  so previously minted trust-cg JIT artifacts fail closed at install, as
  intended. NOT LANDED downstream: trust-cg (origin/main `3d41fc6f0`, pin
  `96e38853`) still refuses the cells. Three of its own tests hold its pin
  move, and each fails at a pin carrying this flip unless the move changes
  it. The move must carry `MEASURED_NOT_ADMITTED_QUERY_SHA256` into
  `CERTIFIED_QUERY_SHA256`, drop its must-refuse entries for the retired row,
  and restate `x86_vector_icmp_admission_is_the_manifest`'s
  `fail_closed > 0` line, which leaves that test's refusal arm with no real
  cell. The review measured all three.

- **Builds on the Trust toolchain (owner directive 2026-09-28).**
  `rust-toolchain.toml` pins `channel = "trust"` (was stock `1.97.1`); the
  lane stays with `targo` (`--unverified`, or `targo trust`). Gate 0's
  `check_trust_default_authority.py` now holds a Trust pin to two bars: the
  RAMP (one caller-owned compiler shared by the pin and the Targo lane, a real
  `targo`, launchers caller-owned along every symlink hop to the file that
  runs, and a refutation-fatal compiler default; pending owner ratification,
  see CLAUDE.md) and the DESTINATION
  (explicit strict/certify policy, one sealed read-only `trust-<commit>`
  sysroot — unchanged, except that the lane must now resolve into it too). `run-targo.sh` and `verified_contracts.py` refuse
  upstream Cargo named `targo`; lints run through `targo tippy`; the export's
  lock refresh uses `targo`. The `rustc_private` frontend builds and tests on
  the installed Trust sysroot (`frontend/build.rs` rpath, `trustc` fallback,
  trustc version-line match), and its real-lowering and soundness tests now
  fail instead of skipping when the compiler is missing — 4 of 19 real-lowering
  tests fail on drift the skip had hidden (a fifth only lacked
  `--crate-type=lib` and is fixed).

- **A reference-counted cell is released by `Release`, never by `Dealloc`:
  one meaning in the interpreter, Lean (for a scalar-typed cell) and the
  Clean-TV heap fragment.** On a
  `CleanHeap` cell the three disagreed: the reference interpreter freed it on
  `Dealloc`, Lean's `semDealloc` called that `Dealloc` undefined behaviour
  (the cell's `arcRef` permission cannot deallocate), and the Fragment-4 walker
  of the `clean_backend_tv` anchor REQUIRED it (exactly one `Dealloc` per
  `HeapAlloc(CleanHeap)`), so a kernel-anchored certificate named a body Lean
  calls UB. Lean's rule is adopted and Lean does not change
  (`docs/SPEC_RATIFICATIONS.md`, new section of that name). The interpreter's
  `MemoryState::dealloc` refuses a live `SwiftHeap` / `CleanHeap` cell as
  `UndefinedBehavior` after the liveness check; `Dealloc` of a `RustHeap` /
  `CMalloc` cell, a stack `Alloca` or a global's reservation keeps its meaning.
  Fragment-4 now routes `Release` AND `Dealloc` to the heap walker: a `Release`
  of the allocation's own `HeapAlloc` result frees the cell, and a `Dealloc` is
  refused by name as a wrong emission. The structural gate
  `alloc_dealloc_balance` becomes `alloc_release_balance`: exactly one
  `Release` per `HeapAlloc` result, a `Dealloc` of an allocation base refused,
  and a `Release` of any other value neither counted nor refused (so the Clean
  side's Fragment-5 `dec` of a call result cannot be turned into a hard error).
  A certificate records no release, so an old certificate over a
  Dealloc-spelled heap body is refused by name, never re-meant. The two
  trust-ir-build fixtures that freed an RC cell with `Dealloc`
  (`heap_alloc_counted_validates_and_executes`, `boxed_index_module`) now use
  `Release`. Lean gains `semDealloc_arcRef_is_ub`,
  `semDealloc_cleanHeap_is_ub_example`, `semDealloc_swiftHeap_is_ub_example`
  and the positive twin `semRelease_cleanHeap_after_store_load_ok_example`
  (AxiomAudit-guarded), plus the `native_decide` fixtures
  `clean_heap_alloc_dealloc_is_ub_stable`, `swift_heap_alloc_dealloc_is_ub_stable`
  and `clean_heap_alloc_release_frees_stable`; the new
  `release_discipline_agrees_across_engines` (gate `lean-exec-differential`)
  runs 14 decided cells through both engines and holds the 6 undecided
  ARC-on-non-RC cells on a shrink-only divergence ledger. SCOPE: Lean
  allocates only a type with a `Ty.byteSize`, so a struct- or array-typed
  cell — every Fragment-4 cell measured, the constructor shape the fragment
  exists for — is `unsupported.layout` there, and for it the rule and a heap
  certificate's certified value are the interpreter's alone;
  `aggregate_reference_counted_cells_are_outside_the_lean_model` pins that
  (both engines' halves mutation-controlled). The walker's two `Release`
  conditions — the liveness kill and the own-`HeapAlloc`-result operand —
  are held by `clean_backend_tv_rejects_heap_use_after_release` and
  `clean_backend_tv_rejects_heap_aliased_second_release`; before those two
  tests, deleting either condition left every heap test green while a
  use-after-release or an aliased double release certified. No wire, tag,
  golden or digest-domain change. Measured with `targo --unverified` (no
  proof claim) and a full `lake build`; every new rule has a mutation control
  that was run and failed. Not decided here: the ARC trio on a non-RC allocation, `Dealloc`
  under a live `Borrow`, `Borrow` of an RC cell, and `Dealloc` of a stack or
  global region. Consumer-relative, made visible: a licensed Fragment-4 heap
  body no longer carries a `Dealloc`, so `validate_module_for_codegen` admits
  it while trust-cg refuses `HeapAlloc(CleanHeap)` — the open
  HeapAlloc-layout follow-up. Clean's minter and clean-reflect follow in their
  own commit (pending: at Clean c3a3b2d61 the minter still requires a
  `Dealloc` per heap cell, so its heap certificates are refused here by name
  until it lands); no pin moves.

- **Gate 7 now fails when `frontend/Cargo.lock` does not resolve.** The
  workspace-`exclude`d frontend lock is the leg that keeps getting missed, and
  `dependency_pin_coherence.rs` read only its Clean rows. On 2026-09-25 a
  non-pin change (`trust-ir-build` gained the path dependency `trust-ir-laws`)
  left it stale, every `--locked` frontend command failed, and nothing noticed
  until review. The new `frontend_lock_resolves_under_locked` runs
  `metadata --locked --offline --format-version 1` on `frontend/Cargo.toml`
  through the Cargo running the test (`CARGO`, which under the gate is `targo`
  itself, so this is `targo metadata`: non-compiling, no lane, no verification
  claim). When the offline query cannot decide (a cache without every package
  the lock names, for every platform: building the root workspace does not
  fetch them, since the frontend lock pins crates.io versions the root lock
  does not use), it asks once more with the network allowed, and that answer
  is the verdict. It fails with Cargo's own message plus the fix
  (`cd frontend && targo metadata --offline --format-version 1 >/dev/null`).
  Measured on a scratch worktree (a test, not a proof): adding the path
  dependency `trust-ir-contract` to `trust-ir-build` (root lock refreshed,
  frontend lock not) turns the test red with "cannot update the lock file ...
  because --locked was passed"; running the named fix adds exactly
  `trust-ir-contract` and `rustc-hash` to the lock and the test is green again.
  On a fresh `CARGO_HOME` the offline query answers "no matching package named
  `serde`" and the networked one downloads the frontend's packages and passes;
  on a warm cache the networked query makes no request (it passes behind an
  unreachable proxy). Without a cache and without the network the test fails
  (fail closed; the message names
  `targo fetch --locked --manifest-path frontend/Cargo.toml`). It is the one
  guard assertion `pin_rewrite.py static-guard` does not mirror; that
  docstring, its `static-guard` help, the bumper's Tier 1 comment and
  `--no-guard-test` usage, and gate 7's comment in `ci_gates.sh` now say so.
  No wire change.

- **The consumer halves of the three 2026-09-27 rulings are stated as landed,
  each with the test that holds it.** Text written before the landings said
  trust-cg "is to" refuse fail-closed x86-64 vector-compare cells and "reads
  no cell status until its pin move", that it "still lowers" a
  provenance-resolved `Dealloc` and lists the row known-accepted, and that
  ~/trust "is to" stamp its native bundle `Unclassified` and admit by-value
  aggregate edges only under `Unclassified` plus the FnAbi token. Each claim
  was re-read at the consumer's origin/main (trust-cg `b720e7321`, pin
  `7b0947ee`; ~/trust `dc53a4c410`) and restated in the present tense naming
  its test: `docs/dialects.md` (the x86-64 rule's `(external)` entry), SPEC
  "Deallocation is refused for codegen" and §17 `(external)` entries,
  `lowering-target-subset.md`, and the rustdoc/comments of
  `chc_x86_vector_icmp_cell_status`, the `consts.rs` ownership note,
  `codegen_lowerability_errors`, `PinnedReleaseEntry`, the refuse-corpus
  trigger, `refuse.rs` and `dealloc_codegen_refusal.rs`. Measured on the
  unverified lane (`targo --unverified`, no proof claim): trust-cg-lower
  `trust_ir_dealloc_refusal` 5/5, `x86_vector_icmp_admission` 1/1,
  `pin_move_floor` 15/15, the adapter unit test
  `dealloc_instruction_arm_refuses_behind_no_entry_layer` 1/1; trust-cg-codegen
  `must_refuse_corpus` 2/2 and `x86_vector_icmp_feature_guard` 1/1;
  trust-cg-verify `x86_icmp_manifest_cells` 2/2; trust-cg-cli
  `must_refuse_corpus` 1/1; ~/trust trust-cg-bridge
  `module_to_lir_unclassified_aggregate_abi` 11/11. ~/trust's compiler test
  `native_bundle_target_info_stamps_unclassified` was not re-run (its commit
  records it). Stated, not closed: ~/trust's bridge classifies with its own
  fail-closed superset (`crosses_by_value_aggregate`) rather than
  `Module::is_by_value_aggregate_slot`, because its trust-ir gitlink
  (`29744d5f`) predates §17; the trust-cg rustc bridge's memory-placed-argument
  half stays not landed, as §17 says. Doc and comment only: no wire change, no
  fixture byte changes.

- **Review corrections to the consumer-halves restatement.** Two claims were
  wider than the mechanism behind them. (1) §17's `(external)` entry said
  ~/trust's `admit_struct_passing_policy` admits a by-value aggregate edge
  "only" under `Unclassified` plus the FnAbi token, and that its superset
  predicate refuses "never less" than §17 requires. Both hold only for a
  module that pins a target: the bridge returns before its scan when
  `target_info` is `None`, and the cited test file pins that
  (`an_unpinned_target_is_out_of_this_gate_s_scope` lowers a 16-byte struct
  passed by value with no policy and no token); trust-cg-lower's gate has the
  same scope. §17 now states that scope once, in a new paragraph: a
  target-less module carries no policy, `validate_module` admits it only
  without an FFI boundary (`TargetInfoRequired`), and an exported definition
  or a `CallIndirect` through a received pointer is still an edge whose other
  side nothing checks. That is a named residual, not a rule. The
  `StructPassingPolicy` rustdoc points at it. (2) The `consts.rs` ownership
  note said trust-cg reads "status and feature guard" through
  `chc_x86_vector_icmp_cell_status`. trust-cg's module-entry gate reads the
  status only. An available cell's guard is held at x86 ISel by trust-cg's own
  feature table, and a trust-cg test pins that table equal to the reader. The
  note, the reader's rustdoc and `docs/dialects.md`'s `(external)` entry now
  say that for the guard, item 4's "never re-derives the rows" holds only as
  tested agreement. The same entry no longer implies that the `trust-cg`
  binary's runner pins all three names; it pins `VectorCompareCellFailClosed`
  only. Measured by reading trust-cg origin/main `6dd784879` and the trust
  superproject's origin/main `f84c4d63c4`. Doc and comment only: no wire
  change.

- **SPEC §17: the trust-cg bridge's half is stated as NOT landed.** §17's
  external enforcement said trust-cg's rustc bridge "is to fail closed on a
  memory-placed argument whose trust-cg placement kind differs from rustc's",
  landing with trust-cg's pin move to this ratification. trust-cg's pin move
  landed its trust-cg-lower half (the Unclassified gate reads
  `Module::is_by_value_aggregate_slot`) but not the bridge half: a refusal of
  every such argument was built, measured and withdrawn before push, because
  rustc's Rust ABI passes every Memory aggregate larger than a pointer as a
  pointer to a caller copy, so it also refused all-bridge edges that agree (215
  x86-64 `core` roots measured by the bridge's lane; an in-crate AArch64
  differential measured by the landing). §17 now says the bridge still declines
  that placement, that its `NativeC` claim is false for such an argument at an
  edge rustc's own backend compiled, and that trust-cg records it as an open
  cross-backend miscompile until §17's pre-lowered crossing lands. Doc only: no
  wire change, no fixture byte changes.

- **Review corrections to the three 2026-09-27 owner decisions.** Present-tense
  claims about trust-cg that its origin/main (`b2bb3e518`, trust-ir pin
  `524d8ded`) contradicts are restated as what trust-cg is to do at its pin
  move: the cell reader's rustdoc and the corpus trigger comment (0 trust-cg
  references to the reader), and `PinnedReleaseEntry` / the Dealloc test
  header (trust-cg still lowers a provenance-resolved `Dealloc` and lists the
  row known-accepted). The Dealloc ground "no producer constructs `Dealloc` or
  `HeapAlloc`" was false for `HeapAlloc`: this repo's `frontend/` emits
  `HeapAlloc(RustHeap)` for inline `Box::new_uninit` / `Arc::new` blocks, and
  Rust drop glue frees them with `__rust_dealloc`, a pairing that rests on
  trust-cg's allocation convention because the format states no allocator
  layout. The SPEC, `lowering-target-subset.md` and the `HeapAlloc` rustdoc now
  say so and record stating that layout (or refusing `HeapAlloc(RustHeap)` for
  codegen) as an open follow-up that is due now; the Dealloc ruling stands,
  since no producer constructs `Dealloc`. The release-spelling guidance is one
  text everywhere (`Release` for an RC cell, the pinned `drop` for a handle, a
  paired call for `RustHeap`/`CMalloc`), including the `UnlowerableForCodegen`
  detail string and TRUST.md. §17 no longer says the trust-cg bridge's `FnAbi`
  gates earn `NativeC` outright: they check register-placed slots only. The
  `pass = None` rule is stated once on `PassMode`, and `ParamAttrs::pass` /
  `byval` / §17 point at it. No wire change; no fixture byte changes.

- **Aggregate passing: one slot predicate, and `StructPassingPolicy` restated
  so it is true of every producer (SPEC §17, 2026-09-27).** The policy's
  rustdoc said `NativeC` and `AlwaysMemory` "require the producer to mark
  memory-classed parameters and returns `byval`/`sret`". No real producer
  carries that marking. `byval` is the parameter memory class only on
  System V: clang uses a plain `ptr` on AAPCS64 and Win64. The validator
  enforced no marking under any value. The restated rule is that a consumer
  places a by-value aggregate slot only by a classification it establishes,
  and refuses otherwise:
  - under `NativeC` the consumer classifies, by the target's ruleset for the
    edge's convention, and a recorded `pass`/`ret` fact must agree;
  - under `AlwaysMemory` every crossing is pre-lowered;
  - `Unclassified` is a declaration of absence the consumer refuses.

  What was added:
  - The predicate is stated once as the new
    `Module::is_by_value_aggregate_slot`. It peels one `Refine` (dangling or
    nested fails closed) and admits `Struct`, `Tuple`, `Array`, `Enum`,
    `Record`, `Sequence`, `Set`, `Closure` and `Vector`.
  - The `pass = indirect` placement rule reads that predicate in place of its
    own narrower set. It now also admits `indirect` on a refined aggregate, a
    `Sequence` or a `Set`; no test pinned those refusals.
  - New `ValidationError::AlwaysMemoryByValueAggregate` refuses any `FuncTy`
    parameter or return that is a by-value aggregate slot under
    `AlwaysMemory`. It scans the whole table, so a signature only a
    `CallIndirect` names is held too.
  - The `PassMode::Indirect { on_stack }` and `ParamAttrs::byval` docs now
    state the realization (argument-area copy vs the copy's address), and
    retract the "LLVM byval" and "AAPCS stack arguments" glosses.
  - `crates/trust-ir-build/tests/struct_passing_policy.rs` (gate 9) holds 8
    tests, and `is_by_value_aggregate_slot_table` pins the predicate.
  - Five must-refuse rows, additions only: the AlwaysMemory row (refused by
    `validate_module`); the `NativeC` pass-mode contradiction (`indirect`
    recorded on a two-`u64` C struct that AAPCS64 passes in x0/x1); and the
    `Unclassified` refined, vector and closure rows. trust-cg-lower's gate
    was measured ADMITTING the last three before its fix.

  No wire change: this decision moves no wire version (it landed at 49; the
  v50 array-splat batch is separate). Every pre-existing golden is
  byte-identical (364-file shasum census), and `UNCOVERED.tsv` is untouched.
  The trust-cg and ~/trust halves land with their own pin moves.

- **x86-64 vector compares follow one per-cell rule with two named grounds
  (2026-09-27). This settles the unsigned-compare format/backend
  disagreement.** The `chc_x86` manifest marked the unsigned
  `icmp.{ult,ule,ugt,uge}` cells fail-closed, while trust-cg lowered them with
  a sign-bit bias. The must-refuse row `refuse/vector_unsigned_cmp_wide_lanes_x86`
  recorded that disagreement. The `icmp.<op>` row status is now the single
  x86-64 admission rule for each cell (`docs/dialects.md`), and an available
  cell rests on exactly one of two grounds.
  - **Ground (a), INSTRUCTION MODEL: `icmp.eq` and `icmp.sgt`**
    (`CHC_X86_ICMP_INSTRUCTION_MODEL_OPERATIONS`), 8 cells. The lowering is a
    single `pcmpeq*`/`pcmpgt*` whose backend model is the predicate, so the
    registered obligation is degenerate (`(assert false)`). These cells are
    trusted base, and NO certificate is claimed for them.
  - **Ground (b), CERTIFICATE: every other available cell.** It is certified
    against AY `f28345ff` (0.27.0; built from source twice, binary sha256
    `1f52a716…` and `c7602afb…`) plus a Clean 0.9.0 (store/clean/8606, sha256
    `9c594e83…`) `cert verify-external` replay, fully verified with no hole.
    That covers `ne`/`slt`/`sle`/`sge` on all four descriptors, and — flipped
    to available here — the 12 unsigned cells of `v4_i32`, `v2_i64` and
    `v8_i16`. Each unsigned cell publishes the bias composition trust-cg emits
    (`pxor` both operands with `sign_bit_bias`, then the signed compare;
    inclusive predicates OR the unbiased equality; `v2_i64` uses the SSE2
    dword-halves sequence), guarded by `x86.sse2`.
  - **The four unsigned `v16_i8` cells are DEFERRED**
    (`unsigned_vector_compare_proof_blocked`). AY answers unsat, but its
    Alethe printer spells one rule as `hole`.

  The new `chc_x86_vector_icmp_cell_status` is the table's one reader. It
  answers the whole published verdict, a `ChcX86VectorIcmpCell` (status,
  reason and the available cell's `feature_guard`, so a consumer cannot drop
  the `v2_i64` SSE4.1/SSE4.2 guards), and
  returns `None` for a shape no descriptor covers, which is a named gap: trust-cg
  lowers `<8 x i8>` `eq`/`ne` on x86-64 with no descriptor and no x86
  obligation. The corpus retires `refuse/vector_unsigned_cmp_wide_lanes_x86`,
  whose subject is now certified, and adds `refuse/vector_unsigned_cmp_bytes_x86`
  (`icmp ugt <16 x i8>` on x86_64). The new row's trigger calls that same
  reader, so it cannot outlive the cell's fail-closed status. The other 361
  fixture files are byte-identical (shasum census).

  Two comment fixes in `consts.rs`. It claimed ay reads the descriptors; it
  does not. It also said any change needs a schema bump; now only a grammar
  change bumps the schema, and a content change is carried by the manifest
  sha256. The `icmp` rows' status is now documented as normative.

  No wire change: this decision moves no wire version (it landed at 49; the
  v50 array-splat batch is separate). The manifest sha256 changes, so
  previously minted trust-cg JIT artifacts fail closed at install, as intended.
  trust-cg's module-entry gate lands with its pin move.

- **G18-1 re-decided: `Inst::Dealloc` is refused for codegen in every body,
  whatever its provenance, and the backend is to conform (2026-09-27).** The
  must-refuse corpus recorded one format/backend disagreement on
  `refuse/dealloc_instruction`: trust-ir refuses every `Dealloc` for codegen,
  while trust-cg lowered the subset whose pointer it could trace back to one
  same-function `HeapAlloc`. The owner-side decision keeps the format rule and
  has the backend conform. The measured facts behind it: no producer
  constructs `Dealloc`; a free must match an allocator and
  layout the format never binds; and `Dealloc` on a `CleanHeap` cell has
  three readings inside trust-ir (the interpreter releases it, Lean's
  `semDealloc` is UB, and the Clean-TV heap fragment requires one). The rule
  is now stated once in `docs/SPEC_RATIFICATIONS.md` ("Deallocation is
  refused for codegen, whatever its provenance"). It covers licensed,
  claim-less and `Ungated` bodies under any unlicensed-body policy, and says a
  backend must not recover origin or layout from dataflow. The new
  `crates/trust-ir-build/tests/dealloc_codegen_refusal.rs` (gate 9) holds nine
  well-formed provenance shapes plus a claim-less and an `Ungated` body under
  `UnlicensedBodyPolicy::Permit`. Two mutants were run: a same-function
  RustHeap/CMalloc exemption fails both tests, and a claim-less-body exemption
  fails only the second. The `AllocOrigin` / `HeapAlloc` rustdoc no longer
  describes origin-routed deallocation, and the manifest reason text for the
  row says "in every body". The validator logic and every fixture byte are
  unchanged. No wire change: this decision moves no wire version (it landed at 49; the
  v50 array-splat batch is separate). trust-cg's conformance change
  (retire `translate_dealloc`, refuse as TCG-DEALLOC, delete its three
  known-accepted entries) lands after this commit.

- **Kernel certificates are BOUND to the environment, statement and callees
  they were checked against (roadmap WS1.12a/b, the non-wire half; closes
  F-007, the F-005 residual, the F-008 carrier, the F-020 decision).**
  `CleanCicKernelRecheck` gains `binding: Option<Box<CertificateBinding>>`
  (`environment_digest`, `statement_digest`, `origin_module`, `source`,
  `callees`) as its sole trailing skipped serde field. `None` is UNBOUND —
  the pre-binding meaning every existing certificate keeps, admitted by the
  default lanes and refused as `UnboundCertificate` only under
  `ValidationConfig::with_bound_certificates(true)`. A PRESENT binding is
  never taken on faith: the validator recomputes the environment digest
  (`trust_ir.clean_cic.environment.v1`, `kernel_environment_digest` over the
  anchor environment it itself builds), the statement digest
  (`trust_ir.clean_cic.statement.v1` over the `∀`-equation / grounded goal it
  itself derives) and, for `clean_backend_tv`, the name-sorted callee link
  symbols, and refuses any difference as
  `CertificateBindingMismatch { field, .. }` — so the CONSISTENT retarget of
  a call AND its `InheritedFromCallee` row to another certified callee of the
  same arity and rank (WS1.4's residual) is refused by name. `origin_module`
  must name a declared import row. The contract path gains the named anchor
  `trust_ir_contract` (`TrustIr.Contract`; no theorems, no axioms), so a
  contract certificate can be bound too; the directive-less arm keeps its
  meaning. Lineage v8 (`trust_ir.proof.clean_cic.lineage.v8`) is keyed on
  content and LINK SYMBOL — never on `ProofId`/`FuncId` — binds the v46
  `spec` temporal backref exactly as the index-keyed v7 does, and is accepted
  beside v5/v6/v7, so a bound certificate survives a merge renumbering while
  the v6 control is refused; `DuplicateObligationContent` keeps it one-to-one within
  a function, scoped to v8-matched `CleanCic` rows (a WS1.6 restatement never
  trips it). Minters: `certify_identity_lineage_rung_bound`,
  `contract_clean_cic_certificate_bound_in`. WIRE STATUS: the binding has no
  binary carrier until the proof-surface wire batch — the binary writer
  PANICS on a bound certificate (the `Ty::Error` precedent, never narrowed to
  `None`), so a bound module travels as JSON / MessagePack; `BodyGate`
  evidence (tag 3), `ProofStatus::{RuntimeChecked, Unknown, Unsupported}`
  (tags 5–7) and the v43-blob decode goldens are deferred to that batch.
  Ratchets flipped: `b2.gap.no_kernel_environment_digest_on_clean_cic_recheck`,
  `b3.gap.composition.consistent_retarget_to_certified_callee`.
  COMPOSITION WITH WS1.15: the anchor environment a binding is taken over is
  spelled ONCE (`clean_backend_tv::anchor_environment`) — the ground prelude
  plus the Fragment-4 heap vocabulary plus the four S3 signed carrier aliases
  — and both the bound minter and the re-check use it, so widening the
  fragment's vocabulary moves the digest on both sides at once and a bound
  rung in the widened signed fragment certifies unchanged. In the other
  direction the binding CLOSES, for bound certificates, the residue WS1.15
  discloses: its carrier check binds the comparand's parameter binders only,
  but the statement digest is taken over the sorted statement whose `Eq` type
  IS the result carrier, so a result-only `u32`→`i32` relabel — a true
  equation the kernel cannot separate from its source — is refused as
  `CertificateBindingMismatch { field: "statement_digest" }`. Both directions
  are pinned in `certificate_binding.rs`.
- **A v43 opaque runtime handle may sit in a struct, tuple or enum LANE
  (WS3.6, F-047 aggregate half).** The transport-only rule is widened from
  scalars to the three register-level aggregate instructions, under exact
  lane typing: `MakeAggregate` seeds a handle-reaching lane only from an
  operand of exactly that lane's declared type; `ExtractField` reads a
  struct/tuple lane back only at exactly its declared type (a non-handle lane
  of a handle-bearing aggregate included); `InsertField` writes one only with
  a value of exactly that type. On an enum, lane 0 (the tag) is readable at
  exactly the canonical tag repr, and a payload lane only where a dominating
  `Switch` case edge on the tag of the SAME SSA value selects exactly one
  variant carrying that lane at that exact type — closing the wrong-variant
  forge (write `U64` into variant A's lane, read it as a handle through
  variant B). `InsertField` on a handle-bearing enum stays refused (build the
  variant whole). `Undef`, `Const`, `NullPtr`, `GlobalAddr`, handle-typed
  globals and the `Record`/`Array`/`Closure`/`Vector`/`Set`/`Sequence`/
  `Refine` carriers all stay refused, so the origin invariant is unchanged:
  every handle still comes from a pinned entry point. Reading a handle lane
  as an integer is refused by the same exactness rule (the `PtrToInt` leak).
  New refusal `HandleLaneNiche`: an `EnumLayoutDescriptor` may not carve its
  niche lane out of a handle-reaching field's bytes, since a handle has no
  declared valid range. A node reaching a handle AND a `Ty::Dialect` is now
  held to both rules (the handle rule used to decide it alone, which was sound
  only while its admitted set was a subset of the dialect rule's), so a
  dialect lane beside a handle lane stays `InvalidDialectType`. The reference
  interpreter still refuses `InsertField` of a runtime handle — a fail-closed
  divergence §7 records. Wire format unchanged; `docs/SPEC_RATIFICATIONS.md`
  §7 carries the amendment and `TRUST.md` item 9(c) records that an aggregate
  copy duplicates a handle exactly as a scalar copy does.
- **A v43 opaque runtime handle may be spilled to a SEALED stack slot (WS3.7,
  F-047 memory half).** The MIR-style spill of a `Nat` local
  (`let slot = v; let r = &slot; *r`) validates: an
  `Alloca { ty: T, count: None }` whose `T` is a handle, or a struct / tuple
  whose handle-reaching lanes are handles, structs or tuples, is admitted when
  its pointer — and every `Borrow` / `BorrowMut` of it — is used only by
  exact-typed `Store`s (pointer position only, value of exactly `T`),
  exact-typed `Load`s and the borrow instructions, and every `Load` is
  dominated by a `Store` into the same slot (definite initialization; a store
  on one arm of a diamond does not initialize the join — conservative by
  design). Any escape (`GEP`, a cast, `Copy` / `Select`, a branch / call /
  invoke / return argument, a store of the pointer as a value, an atomic,
  `Dealloc`, `Drop`, `MemCopy` / `MemSet`, a differently typed access) is
  `InvalidHandleUse` at the `Alloca` naming the use; a load before any store
  is "load of a handle slot not dominated by a store"; volatile and
  non-natural-`align` accesses, an under-aligned slot, a dynamic count, an
  enum slot type, and a struct / tuple slot with no declared layout (a
  struct's `size` / `align` / field offsets, a tuple's v42 layout row) are
  refused. The
  slot rule re-checks that each slot pointer's definition dominates its uses,
  because the deep SSA pass is filtered under `validate_changed` while the
  handle rule runs on every function. A `Load` / `Store` at a handle type
  through any other pointer stays refused — including a `&Nat` / `&mut Nat`
  parameter (phase 2, DG-46, gated on WS5.16 / F-094) — as do `HeapAlloc` and
  handle-typed globals, which are now a RATIFIED refusal (a Lean top-level
  `Nat` constant is a function returning a fresh handle). New module
  `trust-ir-build/src/validate/handle_slots.rs`; Lean
  `load_store_roundtrip_handle` (`Proofs/MemoryProps.lean`) proves the round
  trip as an instance of `writeBytes_readBytes_general` at the 8-byte handle
  width, guarded in `AxiomAudit` (Lean-core trio only). The reference
  interpreter still refuses to store a runtime handle — a fail-closed
  divergence §7 records and hands to WS2 F-035. Ratchets:
  `b5.gap.handle_behind_ref_or_in_memory` is split into `…spilled_local`
  (PASS, with the load-before-store twin) and `…behind_ref_param` (GAP until
  phase 2), and `b5.gap.handle_typed_global` is a PASS row asserting the
  ratified refusal. Wire format unchanged; `docs/SPEC_RATIFICATIONS.md` §7
  carries the amendment and `TRUST.md` item 9(c) notes that a reload is one
  more copy of a handle.

- **The reference interpreter executes wasm32 (WS2.16, F-036 32-bit cells).**
  The entry-time refusal of every non-64-bit target is replaced by a
  pointer-width-parametric little-endian byte model on the canonical scalar
  table: `Ptr`/`Isize`/`Usize` are `pointer_bits / 8` bytes (size and
  alignment), pointer-width integers execute and wrap at the target width,
  a pointer's memory image is one pointer word and a fat pointer's two,
  allocations must fit `2^pointer_bits` (`OutOfMemory`), and a GEP /
  `IntToPtr` / `Bitcast` result past the address space is UB. i686, AVR and
  every big-endian target keep the named `UnsupportedMemory` refusal. The
  64-bit path is byte-identical (every added check is vacuous at 64 bits).
  Entry arguments built at the 64-bit reference width are re-narrowed to the
  target width, and a `usize` that does not fit is a `TypeError`, never
  truncated; `InterpretValue::int_at` names the width explicitly. The proven
  subset is unchanged: subset v3 condition 5 still refuses every wasm32
  module, so a wasm32 run is reference execution, never Lean-backed
  evidence — `condition_5_refusals_are_never_executed_by_the_reference_interpreter`
  now pins wasm32 as executed-yet-subset-refused (big-endian and malformed
  widths stay unexecuted). New gate-8 target `wasm32_reference_execution`:
  the critic `one_module_every_target` wasm32 row (same value as x86_64),
  the i686 twin refused by name, and mutation controls (`usize::MAX + 1`
  wraps to 0 at 32 bits only; a GEP past `2^32` is UB; a `usize` stride is
  4 vs 8; a fat pointer round-trips through a two-word image).
  Review controls in the same target: `usize` subtraction and signed
  `isize` division overflow are target-width-sensitive, an `IntToPtr` past
  the address space is UB, a `dyn`-tail fat pointer round-trips two pointer
  words, the wasm32 `&str` module is validator-clean, the run's width does
  not leak out of a run (including a failed one) or out of a nested 64-bit
  run re-entered from a host model, and the WS2.9 invariant is restated in
  the form WS2.16 leaves standing — *executed AND in-subset implies the
  8-byte little-endian Lean byte model*, asserted over the target table.
- **Lowering-target conformance subset v4: the B1 scalars are in (WS2.17,
  F-037).** `Ty::Isize`, `Ty::Usize` and `Ty::Char` join the proven subset,
  an EXPANSION under the bump policy — every v3 module is a valid v4 module.
  `Isize`/`Usize` execute at the Lean model's 64-bit pin and need no new
  condition: subset v3's structural condition 5 already pins the whole module
  to that byte model, so a wasm32 `usize` module is out of subset for its
  TARGET, not its types. `Char` is admitted together with new structural
  **condition 6** — a `Char` may originate only from a range-validated
  `Const` or from `Cast ZExt` of a `U8`; a `Transmute`/`Bitcast`/`Trunc` into
  `Char`, or a `Load`/`AtomicLoad`/`LoadSlot` at a `Char`-carrying type, is
  refused in both spellings of the classifier. "Carrying a `Char`" resolves
  the module's member tables, so `load { char }` / `load [char; 2]` / a load
  of an enum with a `char` payload are refused like `load char` (a cyclic or
  dangling member table fails closed); a pointer to such a type is not, being
  a pointer. The `Char` constant range rule moved onto the typed constant
  walk's per-node funnel, so a surrogate nested in a tuple / struct / record
  / array / enum constant is refused too — it was previously checked only
  against a constant's top-level declared type. The reference interpreter now
  reports an invalid `Char` (a surrogate, or above U+10FFFF) as UNDEFINED
  BEHAVIOUR at every SSA bind site, on every module it executes — the dynamic
  half of the same invariant, mirroring the new Lean `validChar` predicate.
  The `b1_scalars` wire fixture loses its subset exemption. No wire change:
  this is a subset-contract bump, not a format version. `FPToSISat` /
  `FPToUISat` stay EXCLUDED — their ay bit-blast encoding still fails closed,
  so the interpreter/solver cross-check their admission is gated on cannot be
  a test yet.

- **Global symbol attributes survive canonical text (WS4.5, global subset).**
  Global declarations carry `visibility(hidden|protected)`, `section("...")`
  and `retained`. Quoted sections preserve Unicode and control characters;
  duplicate or unknown attributes are refused. Defaults retain their previous
  spelling, and binary/JSON/MessagePack encodings are unchanged. The two global
  attribute ratchets now require lossless text and exact module identity.
  Other unsupported text fields still produce named losses.
- **Harness inputs for the Kani lane — the entry-parameter/tape model is
  ratified; the havoc markers are placement-checked; a false `Assume` is
  `AssumeViolated` (roadmap WS2.11; closes F-034). No wire change, no new
  `Inst`.** `docs/SPEC_RATIFICATIONS.md` gains "Harness inputs" (DECIDE
  option A0): a verification harness is a function named by the verification
  request, its PARAMETERS are the nondeterministic inputs (universally
  quantified over their `Ty`'s value domain), an unbounded `any()` stream is a
  `(ptr, len)` tape parameter read through memory, and `Assume` on inputs is
  the vacuity filter. (1) `validate_module` gains
  `ValidationError::HavocMarkerMisplaced { location, marker }`:
  `FreshSymbolicHavoc` is legal only on an `Inst::Undef` node,
  `RegionHavocStore` only on a NON-volatile `Inst::Store` node, and either in
  `Function.proofs` is misplaced — the trust-mc consumer's admission check,
  now applied at validation (the producer census turns no producer red; the
  parser round-trip test that stamped both on a `return` moved them onto an
  `undef` and a `store`). A legal placement still grants nothing: the marked
  `undef` stays outside the lowering-target subset. (2) The reference
  interpreter's `Inst::Assume` on a FALSE condition is the new
  `InterpretErrorCode::AssumeViolated` (`assume_violated`) instead of
  `UndefinedBehavior` — still an error and still a refusal, named so a harness
  driver can classify "input outside the assumed domain" apart from program
  UB; a POISON condition stays `UndefinedBehavior`. It is not a claim about
  Lean: `Semantics/Step.lean` runs `Assume` as a no-op for a false condition
  and a poison one alike, the pre-existing `Assume` model split recorded in
  `docs/ub-numerics-policy.md` §4, which this change neither widens nor
  narrows. Consumers
  matching `InterpretErrorCode` exhaustively gain one arm — in-repo the only
  one is the interpreter's own `as_str`; the ~/trust sampled differential is
  the known cross-repo companion, censused in the same integration as its
  next pin bump. The validator rule is enforced on BOTH paths:
  `validate_function` on a bare `Function` refuses a misplaced marker exactly
  as `validate_module` does, and neither counts it twice. (3) Ratchets: b7.nondet.havoc_marker_placement_unchecked
  GAP→PASS; b7.nondet.no_choice_opcode, b7.nondet.interpreter_has_no_input_oracle,
  b7.nondet.fresh_symbolic_havoc_is_inert,
  b7.nondet.unmarked_undef_is_in_subset_marked_is_not,
  b7.nondet.dialect_op_is_opaque and
  b7.nondet.extern_nondet_call_is_unexecutable GAP→RATIFIED-OUT (held in
  their exact shape under "Harness inputs"); new PASS rows
  b7.nondet.assume_is_a_vacuity_filter (+ twin). Gate 9 gains
  `harness_inputs` (trust-ir-build). `docs/ub-numerics-policy.md` §4 names
  the new code.
- **Authority hygiene: certificate/status/scope consistency and claim-style
  lints (roadmap WS1.8; closes F-018, the trust-ir halves of F-021 and F-022,
  and the validator half of F-024).** Five refusals, no wire change.
  (a) `GroundCertificateStatusInconsistent` is REVIVED, narrowly: a
  non-inherited certificate on a `Failed` row is refused (the row records a
  refutation; the certificate claims the opposite). A `Pending` row with a
  certificate stays legal — it is the honest evidence-awaiting-replay carrier.
  The `trust-ir-ay` `apply_vc_outcomes` transition now drops any non-inherited
  certificate on a row it flips to `Failed`, so a re-run over a row an earlier
  pass left evidence on yields a valid module. (b) `ObligationFunctionScopeUnresolved`
  (landed upstream, 5a945757) already resolves `obligation.function` without a
  site. (c) `ObligationSiteKindMismatch`: a sited row's kind must admit its
  site's instruction — the kind→instruction table is
  `obligation_kind_admits_site_instruction` (`ArithmeticSafety`: BinOp / UnOp /
  Overflow / Cast / Assert / CondBr; `BoundsCheck`: Assert / CondBr / GEP /
  Load / Store / ExtractElement / InsertElement; `MemorySafety`: the memory,
  borrow, atomic, call and heap instructions, plus WS3.20's `MemCopy` / `MemSet`
  (a byte-range access through pointer operands, like Load / Store — the
  sited `InBounds` binding in `bulk_memory_ops.rs` depends on it); `PanicFreedom`: Assert / CondBr /
  Call / CallIndirect / Invoke / Unreachable, plus Return — the function-exit
  "returns without panicking" shape the b2 fixture already carried, folded in
  with a test rather than escaped; every other kind unconstrained). Measured
  on the archived parta corpus (28 units, 109 sited rows: 106
  ArithmeticSafety@Assert, 3 BoundsCheck@Assert): every row is admitted.
  (d) `EvidenceKindMismatch`: `ProofEvidence::TranslationValidation` only on a
  `TranslationValidation` row, `GammaCrownBound` only on `Postcondition` /
  `Custom` (`evidence_admits_obligation_kind`). (e) F-021's readnone/readonly
  rule landed upstream as `FuncAttrClaimViolated` (WS2.7, 5f28fc7e), module-wide
  rather than codegen-only — stronger than the roadmap asked. (f) F-022:
  `CodegenAdmission::with_refuse_unbacked_claims_on_checks(true)` refuses a
  `NoOverflow` / `NoWrap` / `DivNonZero` / `ShiftInRange` / `InBounds` claim on
  an `Assert` / `CondBr` node that carries no `ProofRef` to a kind-matched row
  sited on that node (`UnbackedClaimOnCheck`; the layer alone is
  `unbacked_claim_on_check_errors`). OFF by default: the shape is what both
  compilers emit today beside `Pending` obligations, and the producer fix is
  WS5. CLAUDE.md's trust-boundary text now says it: a claim on the node that IS
  the runtime check never licenses eliding that check. (g) F-024: the CLI
  census `validate --forbid-prose-only` lists every formula-less non-`Pending`
  row and exits 1 (a formula-less `Pending` row is legitimate, F-086); no
  default refusal. DECIDE 1 → A: `TrustedWithoutJustification` — a `Trusted`
  row must carry a `ProofEvidence::Trusted` certificate with a non-blank
  justification, so faith is attributed; `Trusted` still counts toward nothing.
  DECIDE 2 → A: no in-module inventory root now (the F-126 v2 FactSet gate in
  WS8 owns it). Ratchets flipped:
  `b2.gap.certificate_on_pending_or_failed_obligation_accepted` (Failed half),
  `b2.gap.site_not_related_to_obligation_kind`,
  `b2.gap.trusted_status_needs_no_certificate`; the enforcement-link ledger
  retires `GroundCertificateStatusInconsistent` from both the unnamed and the
  never-constructed sets. Tests: `trust-ir-build/tests/authority_hygiene.rs`
  (gate 9), `trust-ir-cli/tests/cli_forbid_prose_only.rs`,
  `trust-ir-ay/tests/contract_flow.rs`.
- **The verification bundle states a two-language package — schema 7 → 8
  (roadmap WS4.16; closes the language half of F-080).** `NativeBundleProducer`
  gains `Clean` (serde `"Clean"`, TMVB envelope tag 4 — reserved `8575bdb5`
  under the wire-allocation lock), `NativeSourceLanguage` gains `Lean` and
  `Clean`, and `NativeBundleProvenance` gains `source_languages:
  BTreeSet<NativeSourceLanguage>` beside the scalar `source_language`, which
  schema 8 keeps for one version as the PRIMARY. `NativeVerificationBundle::
  validate` now refuses (a) a primary outside the set
  (`BundlePrimaryLanguageUncovered`) and (b) any function of the bound module
  whose `Function.producer` the set does not cover
  (`BundleLanguageUncovered { producer, functions, .. }`, one row per distinct
  producer) under the TOTAL map `NativeSourceLanguage::candidates_for_producer`:
  `TRust → Rust`; `Clean → Lean | Clean` (either suffices); `TrustIr →
  TrustIr`; deprecated `TSwift`/`TC → Swift`/`C`; `Other(_) → Other`; and
  `None → Unknown`, which must itself be a member — an unstamped function is
  never covered by omission. An absent `source_languages` key decodes to the
  EMPTY set, which covers nothing; the default provenance carries `{Unknown}`
  (the exact set its default primary needs). The set enters the bundle digest
  under the new domain `trust_ir.native.verification.bundle.v8` (v7 is
  burned; a v7 bundle is refused by the exact-match rule,
  `UnsupportedSchemaVersion(7)`). **Cross-repo:** every bundle consumer
  (ty's `tla-petri`/`tla-trust-cg`, trust's `trust-ir-bridge`, ay/trust-vc,
  trust-cg) matches the schema exactly and moves in the WS8 pin train;
  producers must stamp `source_languages` (and exhaustive matches over
  `NativeBundleProducer` gain a `Clean` arm). F-080's second half — no typed
  ty request lane for temporal obligations — stays OPEN as the compile-time
  GAP ratchet `f080.ty_request_lane` (decision gate DG-56, after WS4.14's
  carrier): a `TemporalSafety` obligation routed to ty has no request and
  stays `Pending`. Tests: `mixed_producer` `bundle_language_set_*` (positive
  `{Rust, Lean}` / `{Rust, Clean}` over the two-producer fixture, the
  `{Rust}`-only twin refused for exactly the Clean functions, the
  `producer: None` twin needing an explicit `Unknown`, the primary-membership
  and empty-set twins, the two spelled-out validator mutants, the v7 refusal
  as a value and as a keyless JSON blob, digest binding + serde round-trips,
  `Clean` through JSON/MessagePack/TMVB); ported rows
  `b1.bundle.g8_toolchain_language_identity`,
  `b1.bundle.root_verification_bundle_two_producers`,
  `b1.bundle.native_verification_bundle` (each with a twin) and
  `f080.ty_request_lane`; the `native_request_trust_bundle` goldens regenerate
  at schema 8 (the fixture stamps its function `TRust` and claims `{Rust}`),
  while the pinned `v41-reader-compat` copy stays as published and its test
  now LEDGERS the exact rows by which today's bundle differs from it (module
  digest V2→V3, schema 7→8, the language set, the producer stamp) and asserts
  the published blob is refused on each. The bundle the language-set tests
  wrap around a module is one COMPLETE schema-8 bundle recipe
  (`generate::build_language_set_bundle`: sited obligation with public
  identity, sidecar row, rooted lineage, all three request lanes with solver
  and replay-transcript identities), so `Ok(())` there means the whole bundle
  validates and a lone refusal is the language rule. The new tests avoid the
  `native_request_bundle` substring gate 8 skips.
  **Review addendum (same schema 8):** the coverage rule does not stop at the
  module boundary. An authenticated DEPENDENCY is part of the package a bundle
  verifies, so `NativeBundleProvenance::uncovered_imports` extends the same
  total map to every `ModuleImport.producer` of `bundle.module`, refused as
  `BundleImportLanguageUncovered { import, name, producer, .. }`. Without it a
  root module whose own functions are all `Producer::TRust` but which
  authenticates a Clean-produced dependency — and inherits its discharges via
  `FunctionSummary.backed_by` / `ProofEvidence::InheritedFromCallee { external:
  Some }` — could declare `{Rust}` and validate, restating exactly the false
  claim F-080 exists to prevent one level up. `ModuleImport.producer: None` is
  UNRECORDED and is covered only by an explicit `Unknown`, as that field's own
  contract requires. Tests:
  `bundle_language_set_covers_imported_dependency_producers` (the false claim
  refused by name, both Clean-side spellings accepted, the unrecorded-import
  twin, and a spelled-out functions-only mutant shown to ACCEPT it),
  `bundle_language_set_unstamped_declaration_needs_unknown_too` (a bodyless
  `External` declaration is a function row and is covered like one, so a body
  cannot be dropped to launder an unstamped function) and
  `bundle_language_set_primary_and_membership_are_bound_separately` (the same
  set with a different primary is a different bundle digest, so a pinned
  bundle identity cannot be re-labelled).

- **One `Nat` carrier across producers (roadmap WS3.4; the carrier-agreement
  part of F-047; DG-45 option (a)).** `docs/SPEC_RATIFICATIONS.md` §7 now
  ratifies that a value of a pinned runtime's type crosses every producer
  boundary as `Ty::Handle` and nothing else, and names `trust_bignum` as the
  one runtime whose `Nat` crosses a boundary — measured false at `5b45b83b8`
  (audit c11 item 5), where one module carried the Rust lane's
  `Struct("trust_bignum::Nat")`, the Clean lane's boxed `Ptr` and the pinned
  handle as three unrelated types. Validator rule (strictly more refusals,
  no wire change — `VERSION` is untouched): in a module whose handle census is
  non-empty, a `StructDef` / `EnumDef` / `RecordDef` whose `name` equals a
  pinned row's `runtime` path is the new
  `ValidationError::HandleRuntimeSpelledStructurally { def, runtime }`, one
  per definition, keyed on every row of the deciding registry
  (`validate_handle_runtime_spellings`, with `repair_options` naming the
  handle lowering). A handle-free module is never examined: a Rust crate
  that uses `trust_bignum::Nat` natively is not a boundary. The rule is
  name-exact; the Clean `Ptr` spelling is undetectable in-format (a `Ptr`
  names no type) and is recorded in §7 as the WS6 F-102 producer
  obligation, beside the WS5 F-095 Rust lowering (option (a): lang-item
  handle everywhere; option (b) boundary marshalling rejected as a
  `PinnedTy` TCB growth). Tests: `one_nat_carrier` (gate 9: positive
  `Acct` beside the handle, struct/enum/record twins, the handle-free
  control, the unused-type-row census control, name-exactness and
  registry-row mutation controls, and the archived
  `trust-ir-self-declared/clean-objects-stay-ptr` row ported as
  `the_clean_ptr_spelling_is_invisible_here_but_never_meets_the_handle`:
  the boxed `Ptr` spelling validates beside the handle and is exactly one
  `CallArgTypeMismatch` when handed to a pinned entry); review adds the
  composed lanes — the authority tier, and the linked walk refusing a
  handle-free root's handle-bearing DEPENDENCY that carries the struct
  (`ImportedModuleInvalid` naming the rule) as well as the root's own —
  proof-program row `b5.carrier.one_nat_spelling` + three twins (`b5_16`,
  over the mixed Clean+Rust fixture; the third: the refusal survives every
  wire lane — all four transports carry the `::` path unchanged (canonical
  text too, since the WS4.3 quoted-name grammar and the WS4.5 struct half)
  and each decoded module is refused, with a one-character rename of the
  decoded struct silent on every lane as the mutation control). Review adds
  three more shapes the census gate must reach: a LIVE second spelling (a
  signature carrying `Struct("trust_bignum::Nat")` by value, the measured
  Rust shape) is still exactly one refusal with no cascade; the pinned
  bodyless DECLARATIONS alone make a module a boundary (the census walks
  `func_types`, so a crate that has declared the runtime and not yet called
  it is already covered); and the per-module scope's residual is written
  down — a handle-FREE root importing a handle-bearing dependency keeps its
  own struct on both the plain and the linked lane, while the dependency
  that holds the handle values is refused.

- **Lowering-target subset v3 — a soundness erratum (roadmap WS2.9; closes
  F-042 and the subset half of F-036/F-037).** A breaking SHRINK under the
  bump policy's "soundness hole" clause; no allowlist name moves
  (`*_ALLOWLIST_V3` alias v2), the structural conditions do.
  (1) `Transmute` is integer/pointer scalar-to-scalar on BOTH sides
  (`I8`–`I128` / `U8`–`U128` / `Ptr`): v2 also admitted `F32`/`F64`/`Bool`,
  which the Lean `semCast .Transmute` arm refused as a *source* but
  MISTRANSLATED as a *destination* (`transmute u32 -> f32` bound an integer
  at a float type; `transmute u8 -> bool` a bool whose payload could exceed
  1). The Lean arm now refuses a non-integer, non-pointer type on either side
  with the new `unsupported.cast` (`UnsupportedFeature.cast`, the mirror of
  the interpreter's `UnsupportedCast`), and the reference interpreter EXECUTES
  `Transmute` on exactly that set (int↔int at one width, int↔ptr, ptr↔ptr,
  through `eval_bitcast`) instead of refusing every `Transmute`; the
  sanctioned int↔float reinterpret is `Bitcast`. (2) New structural condition
  5: the whole module targets the executable model's pinned byte model
  (`target_info` absent, or `pointer_size == 8` little-endian) — the Lean
  memory model encodes every pointer as eight little-endian bytes, yet v2
  target-gated only `FatPtr`, so a `Ptr` store on wasm32 was inside the
  subset (`crit.unex04`). The condition is reported once, module-wide, at the
  new `SubsetSite::ModuleTarget`; `SubsetViolation.function` / `.block` are
  now `Option`s (`None` exactly there). The v2 fat-pointer-only gate is
  deleted (subsumed). (3) `Module::check_conformance_subset` refuses
  `Inst::Dealloc`, which the ratified subset dropped in v2 (G18-1) but the
  core classifier still admitted through its inline-type fallthrough
  (`trust-ir-self-declared/bridge-vs-subset-dealloc-drift`). Migration and
  the producer census are in `lowering-target-subset.md` "History". Tests:
  `bridge_subset_agreement` (dealloc, float/bool transmute src+dst, wasm32
  ptr store, big-endian i32 store; target-free and x86_64 controls; the two
  ported rows `trust_ir_self_declared_bridge_vs_subset_dealloc_drift` /
  `crit_unex04_wasm32_and_big_endian_modules_leave_the_subset`),
  `lowering_subset` (re-derived exemptions: unchanged), interpreter
  `transmute_executes_on_the_integer_pointer_scalar_set`, Lean
  `transmute_u32_to_f32_unsupported_stable` and siblings. Gate 8 now runs
  `lowering_subset` and `bridge_subset_agreement`.
- **WS2.9 review.** (1) Lean `semCast .Bitcast` no longer re-tags a pointer
  operand as `.int 64 addr` at a `Ptr` destination — the mirror image of the
  Transmute float-destination mistranslation v3 fixed; `Bitcast ptr -> ptr`
  now transports the pointer exactly as the reference interpreter does
  (`bitcast_ptr_to_ptr_stays_a_pointer_stable`, with the
  `bitcast_ptr_to_u64_is_the_address_stable` control). (2) The pointer
  member of the Transmute scalar set is pinned to be EXACTLY `Ty::Ptr` in
  both subset spellings and the interpreter: `*const T` / `*mut T` / `&T`
  transmutes are refused (`bridge_subset_agreement` rows "ptr transmute" /
  "ptr-const transmute src" / "ptr-mut transmute dst" / "ref transmute src";
  interpreter `transmute_pointer_member_is_exactly_thin_ptr`, with the
  `PtrToPtr` retag as the sanctioned-carrier control). (3) Condition 5 and
  the reference interpreter's target gate are pinned to agree in the sound
  direction — a wasm32, big-endian or malformed-pointer-size module is never
  executed (`condition_5_refusals_are_never_executed_by_the_reference_interpreter`).
  (4) `SubsetViolation`'s `Display` prints the bare `FuncId(_)` / `BlockId(_)`
  for sited violations instead of leaking the new `Option` wrapper.
  (5) The Lean `Bitcast` pointer rule covers the interpreter's WHOLE
  pointer-like set (`Ty.isPointerLike` = `is_pointer_like_ty`: `Ptr`,
  `PtrConst`, `PtrMut`, `Ref`, `RefMut`, `Rc`), on both the `.int` and the
  `.ptr` operand side — `Bitcast u64 -> &mut u8` binds a pointer, not
  `.int 64 v` (`bitcast_ptr_to_ptr_const_stays_a_pointer_stable`,
  `bitcast_u64_to_ref_mut_is_a_pointer_stable`). (6) An off-set IDENTITY
  transmute (`bool -> bool`, `f64 -> f64`) is refused by both spellings and
  both engines — the gate is on the types, never on whether the
  reinterpretation changes anything (`bridge_subset_agreement` rows
  "bool identity transmute" / "f64 identity transmute" with the
  "u64 identity transmute" control; interpreter
  `transmute_round_trips_a_live_allocation_address`, which also pins that a
  live allocation's address survives `transmute ptr -> u64 -> ptr` WITH its
  provenance; Lean `transmute_bool_identity_unsupported_stable` and the f64
  twin). (7) Condition 5 is reported ONCE per module beside the construct
  rows, not once per function, in both spellings
  (`condition_5_is_reported_once_beside_the_construct_rows`).

### Added

- **W5b: the Lean-EXECUTION differential oracle (roadmap WS2.19; closes the
  F-044 "no W5b oracle" row, proof-program row
  `arch-0804-and-spine/32-w5b-lean-execution-oracle`).** The Lean executable
  semantics is now RUN beside the reference interpreter, not only proved
  about. `lean/trust_ir-semantics` gains a non-default `lean_lib
  TrustIrEval` + `lean_exe trustir_eval`: a hand-written serde-JSON decoder
  into the Lean `Inst` / `Ty` / `Constant` mirrors (fail-closed — a Rust
  variant with no Lean constructor, such as `FMin` / `FAbs`, is a structured
  `unsupported <kind>.<Variant>`, never a default) and a batch runner over
  `evalFunctionInContext` printing one verdict per `(function, scalar args)`
  run in an engine-neutral value grammar (width + two's-complement bits;
  binary64 bits bit-exact, NaN-ness only; nullness for pointers). It imports
  `Lean.Data.Json`, so it lives OUTSIDE the axiom-audited `TrustIr` library
  and nothing under `TrustIr/` imports it. The conformance target
  `lean_exec_differential.rs` runs every validating, in-subset fixture
  function with an all-scalar signature and the seeded W5a corpus through
  BOTH engines: an Ok/Ok value disagreement, an Ok-vs-UB/panic/out-of-fuel
  disagreement, a `type_error` on either side (the module validated) or any
  two different refusal classes FAILS; `unsupported` on either side is
  counted by feature and RATCHETED (`UNSUPPORTED_LEDGER`, may only go
  down). The mutation control feeds the comparator — and the real
  executable — a flipped-`Sub` expected table and requires the mismatch.
  New standing gate 12 `lean-exec-differential` (registry
  `scripts/gates/lean-exec-differential.trust-ir-conformance.tests`) is
  REQUIRED wherever `$HOME/.elan/bin/lake` exists (`TRUST_IR_REQUIRE_LEAN=1`
  makes a missing `lake` a failure); without a Lean toolchain the oracle
  runs report SKIPPED and the harness self-tests still run — no `#[ignore]`.
  The W5a generator moved to `tests/common/exec_gen.rs` so both
  differentials measure ONE corpus, and grew shifts, the checked `Overflow`
  trio and range-edge arguments (`MIN / -1`, `MIN - 1`, shift-by-width).
- **Lean: a memory access at a type with no modelled byte image is
  `unsupported.layout`, not a type error (the WS2.19 audit).** Every "type
  has no byte size" site — `semAlloca`, `semHeapAlloc`, `semLoad`,
  `semStore`, `gepByteOffset`, the four atomics, `GlobalAddr` and the
  `SeqMap` element type — threw `typeError` for an aggregate (`Struct` /
  `Array` / `Tuple` / `Enum`), a ty-supremacy carrier, `Func`, `Never` or a
  B1 scalar, which the oracle reads as a DISAGREEMENT with the validator on a
  module the validator accepted. They now throw the new
  `UnsupportedFeature.layout`, counted as coverage. The boundary is pinned
  in `ExecutableFixtures`: each reclassified site has an
  `*_is_unsupported_layout_stable` case, and its still-UB twin (null
  dereference at a modelled AND an unmodelled type, non-positive `Alloca`
  count, negative `GEP` index) shows no real fault was demoted — the pointer
  and count checks precede the byte-image gate.
- **Lean: an RC-origin `HeapAlloc` yields the fresh RC cell (the first
  divergence the W5b oracle measured).** `semHeapAlloc` granted `owned` for
  EVERY origin while the ARC trio requires `arcRef`, so `HeapAlloc CleanHeap`
  + `Retain` — the `inst_borrow_arc` fixture's `clean_rc_lifecycle`, a
  validated in-subset function — was UB in the model and `Ok` in the
  reference interpreter (which starts every allocation at refcount 1). The
  Lean lifecycle fixtures had papered over this by starting from a hand-built
  "as the runtime leaves it" state. Now `AllocOrigin.isRefCounted`
  (`SwiftHeap` / `CleanHeap`) selects `arcRef` + refcount 1 at allocation;
  `RustHeap` / `CMalloc` stay `owned` and keep refusing the trio
  (`rust_heap_alloc_retain_is_ub_stable`). Pinned end to end from a bare
  `HeapAlloc` (`clean_rc_lifecycle_from_heap_alloc_reaches_zero_stable`,
  underflow twin, `IsUnique` on one owner, store/load round trip on the
  cell). Residual divergence, recorded as a finding rather than hidden: the
  interpreter also executes `Retain` / `Release` / `IsUnique` on a `RustHeap`
  / `CMalloc` / stack allocation (any live allocation carries a count), which
  the model refuses; no fixture or generated module exercises it, and the
  fail-closed resolution is to tighten the interpreter, not widen the model.
- **Lean: the module-context evaluator types constant lanes, checks the
  projected lane, and names a declared callee (the other W5b divergences).**
  (1) An integer leaf of a `Tuple` constant takes its lane's declared width
  (`constValueAt`; it kept the 64-bit default, so `(i8, bool)` lane 0 was
  `int64` in the model and `i8` in the interpreter). (2) `EvalContext` gains
  the module's `enums` / `structs` / `types` tables (defaults: none), and
  under the context an enum constant types its tag at the canonical tag width
  and its payload at the active variant's field types, a struct constant its
  lanes at the field types, an array literal its elements at the table's
  element type (`constValueAtWithDefs`, mirroring `constant_to_value_in`).
  A constant whose table entry the context lacks is REFUSED as
  `unsupported.enum_def_table`, never lowered at the default width. (3)
  `ExtractField` under the context checks the projected lane's width against
  the access type (`laneMatchesTy`), and `InsertField` the replaced lane's
  width against the inserted value (`lanesAgree`): a wrong-variant enum read
  or write at a different width is UB, as in the interpreter (WS2.2 item 5).
  Sound because of (2): every aggregate value the context builds carries its
  declared widths, so a VALID struct / tuple lane never trips it; the
  same-width, different-signedness access stays invisible (B3 ledger). (4) A call to a
  bodyless declaration (`EvalContext.declared`) is
  `unsupported.interprocedural_call` — the interpreter's `UnsupportedCall` —
  while an id the module does not define keeps the `Call: undefined
  function` type error. Each is pinned in `ExecutableFixtures` beside its
  twin (`ws219_*_stable`); `CallProps`'s B5 bridge lemmas absorb the second
  refusal without a case split.
- **v50 — the constant-size uniform array: `Constant::Splat { elem, len }` and
  `Inst::ArraySplat { ty, value }`.** "N copies of v" (a Rust `[x; N]`) had no
  constant-size spelling: `Constant::Array` / `Aggregate` / `Bytes`,
  `MakeAggregate` and an `Undef` + `InsertElement` chain all grow with N, which
  is how a compile's memory came to scale with VALUES in the program (the
  2026-09-21 panic). The pair costs O(1) in N in every consumer here:
  * **Wire** (reserved `ae94794d` as v54, taken to 50 by `4a143d18`):
    Constant tag 16 (one element + a fixed `u64` length) and Inst tag 59
    (`Ty` + one operand), both read-gated `version >= 50`, selected only when
    used; `RawV38`/`CanonicalV38` refuse with `ArraySplatRequiresV50`; the
    census, both ledgers and a new `array_splat` four-format golden (the only
    one at header 50, u64-scale lengths in a few hundred bytes).
  * **Text / JSON / MessagePack**: `splat[ c; n ]`, `%r = array_splat [e x n]
    %v`, the derived serde records; the stable digest (`write_constant_stable`
    tag 16) and the semantic diff see the length, never iterate it.
  * **Validator**: `validate_array_splat` is constant time (`InvalidArraySplat`
    for a non-array or dangling element type; the value consumed under
    `InsertElement`'s rule and `CheckedConsumption::FieldWrite`), a splat
    constant is checked once against the element type.
  * **One spelling, VALIDATED** (`docs/SPEC_RATIFICATIONS.md` §3.1, new
    `ValidationError::NonCanonicalUniformArray`): a constant list of two or
    more equal elements (constant list / aggregate at an array type / raw
    bytes; the two list spellings of one array, and raw bytes vs their `Int`
    list, count as equal) must be the `Splat`, and a `Splat` of fewer than two
    elements must be the list; on the register side a `MakeAggregate` whose
    `n >= 1` array lanes are all one register (ONE lane included) must be the
    `ArraySplat`, and an `ArraySplat` of zero copies must be `const [e x 0]
    array[ ]` — so every spelling `uniform_array` emits has a wire encoding
    and a digest (the first version sent `[v; 0]` / `[v; 1]` to the
    tag-less `MakeAggregate`; review 2026-09-23). Decided by one hash-consing
    pass over the constant as written (`Constant::uniform_element_lists`,
    `usize` classes, nothing allocated for a leaf); a refusal names a
    composite element by its shape label, never its subtree. Every decoder
    (binary, text, JSON, MessagePack) also refuses a constant `Splat` of
    `len < 2`. Sanctioned constructors: `Constant::splat`, `Constant::array`,
    `FunctionBuilder::uniform_array` (and the raw `array_splat`). The pin move
    must carry the validation, the producer switch (Trust's THIR
    `lower_repeat_compact` / `seed_lane_ty` / `zero_const` / bridge
    `Rvalue::Repeat`, Clean's all-NUL string globals), the trust-cg lowering
    and the subset admission TOGETHER (§3.1 "Landing order"); an `Undef` +
    `InsertElement` chain of one value is ratified non-canonical as a
    producer rule.
  * **Reference interpreter**: byte images and array / vector VALUES are
    persistent, AVL-balanced ropes with shared structure (`interpret::rope`:
    uniform runs, repeats of a shared unit, literal windows, shared
    concatenations; every whole-structure walk memoized by node, so a DAG is
    walked once). `InterpretValueKind::Array` AND `::Vector` carry an
    `ArrayValue`: `ArraySplat`/`Constant::Splat` are one node,
    `ExtractElement` is O(height), `InsertElement` copies one path instead of
    the whole array or vector (it used to clone it), and lane-wise vector
    arithmetic / compares / selects run on the operands' structure.
    Allocations are SPARSE (`ByteStore`): an `Alloca` of any size, a stored
    splat and a 4 GiB `MemSet` are each one run; a `MemCopy` stores the
    source's image as ONE run sharing its nodes (a doubling copy adds a node,
    never the bytes — literal parts are no longer copied when joined); a load
    decodes the image's STRUCTURE (`Rope::chunk_map`: a repeating run decodes
    one period, whatever element type it is read back at, and a copy DAG
    decodes once per node); a global splat initializer / BSS global is one
    run. **Deleted with it:** `InterpretOptions::mem_budget` (the 256 MiB
    allocation cap, a patch over the dense representation) and the CLI's
    `--mem-budget`; `OutOfMemory` now means address-space exhaustion (which
    also stopped being reported as UB) or a host model's incapacity. The
    review of the first version of this change found four shapes that still
    grew 5–140 bytes of host memory per byte (a doubling `MemCopy`, a stored
    splat loaded at a narrower element type, a `MemSet` vector, a copy DAG
    loaded whole); `interpreter_memory_scaling` (trust-ir-build) now holds
    each to a scaling assertion from 2^16 to 2^40 under a counting allocator
    that aborts a regression early. API: `InterpretValueKind::Vector` and
    `InterpretValue::as_vector` now carry an `ArrayValue` (use `get`, `len`,
    `iter`, `to_vec`).
  * **Lean**: `Constant.splat` / `Inst.ArraySplat` denote
    `.aggregate (List.replicate n v)`; `extract_array_splat` (ExtractElement
    i ∘ ArraySplat = v for EVERY `n`) and `getElement_ofConstant_splat`
    proved and axiom-audited; five `ExecutableFixtures`; the DCE case; parity
    gate `Constant` count 16 → 17 with every allowlist still empty.
  * **Conformance subset**: EXCLUDED by name (instruction, and a splat
    constant anywhere an emitted constant sits) until a subset-contract bump
    admits it with a trust-cg lowering (`lowering-target-subset.md` v3
    addendum 2026-09-23); `b7.nondet.no_choice_opcode` records 61 variants.
  Tests: `array_splat_formats` (trust-ir) and `array_splat` (trust-ir-build)
  at 2^32..2^40 elements (4 GiB allocations, a 4 TiB nested global) finish in
  milliseconds in a few MiB; the constant fuzzer generates splats up to
  `u64::MAX`.
  * **Pin-move preconditions** (`HANDOFF.md`, 2026-09-23): consumers in the
    Trust repository need explicit `ArraySplat` / `Splat` arms before its pin
    moves — notably the trust-mc-driver proof-authority gate
    (`native.rs`), whose per-instruction match ends in `_ => {}` and would
    otherwise admit them undecided — plus the interpreter API breaks and the
    §3.1 landing order listed there.

- **WS2.25 — Coroutine resume-dispatch theorems: the gate for admitting
  `CoroSuspend`** (F-044, the "coroutine resume theorem" row of the Lean
  depth ledger — now closed; the other F-044 rows stay open). New
  `lean/trust_ir-semantics/TrustIr/Proofs/CoroutineProps.lean`, gated by
  `AxiomAudit.lean` (Lean-core trio only, no `native_decide`).
  (1) `semCoroSuspend_step_equiv`: for EVERY machine state, stepping the
  `CoroSuspend` terminator through `stepInst` is the same computation — same
  result, same final state, same error — as stepping its literal
  `const i64; gep; const i64; store; return` expansion at the REAL fresh
  operand ids (`%n`, `%n+1`, `%n+2`, `n = nextValueId`), the wiring the
  `rfl` shape lock `semCoroSuspend_is_macro_expansion` explicitly disclaimed;
  `stepNWithContext_coroSuspend_eq_expansion` lifts it to the interprocedural
  evaluator. Backed by `semGEP_endsFresh` (a successful GEP is exactly one
  fresh pointer bind; every prefix only reads) via the `Sem.ReadOnly` /
  `Sem.EndsFresh` bookkeeping.
  (2) `CoroGen.coro_two_state_roundtrip`: a resume entry `load i64 %fp;
  switch {0 → bb_a, 1 → bb_b}`, `bb_a` ending in `coro_suspend next=1`,
  `bb_b` returning, driven twice by `stepNWithContext` with fresh registers
  and persisting frame memory (`CoroGen.resume`, the call-boundary
  discipline), yields `42` and then returns `7` — for every state whose
  frame at `a ≠ 0` is a live, in-bounds, zero-initialised `i64` cell, with
  the exit states stated exactly. Mutation control, in both forms:
  `coro_two_state_mutant_traps` (the `next + 1` mutant still yields `42`
  but its second resume takes the default edge and traps) and
  `coro_two_state_roundtrip_mutant_refuted` (its round trip is refuted as a
  theorem, not merely unproved); and, per the roadmap's Tests field, the
  mutant's round-trip statement attacked with the round trip's own proof
  script is an EXPECTED ELABORATION FAILURE pinned by `#guard_msgs` in
  `AxiomAudit.lean` (the dispatch `rfl` "state index 2 selects the
  `1 → bb_final` case" is refused as a type mismatch; an `example`, so no
  `sorryAx` enters the environment). Per-shape run characterisations
  (`sr_semLoad_ok`, `sr_semStore_ok`, `sr_semGEP_single_ok`,
  `sr_semSwitch_case` / `_default`, …) are reusable. Review controls, each
  a theorem pinned by `AxiomAudit`: the SILENT `next - 1` mutant (its second
  resume SUCCEEDS but re-yields `42`, so a round trip that only demanded
  success would accept it — `coro_two_state_mutant_loops_refuted` refutes it
  on the returned value); the initial-state hypothesis is load-bearing (from
  a frame already at state 1 the first resume returns `7` and never yields,
  `coro_two_state_from_state_one_never_yields`); and the generator whose
  suspend state is the literal five-instruction EXPANSION rather than the
  terminator, at the ids a real instruction stream receives, has the
  identical round trip and exit states (`coro_two_state_roundtrip_expanded`,
  the whole-module form of the equivalence in a block whose body is not
  empty), while the mis-wired expansion whose `store` reads the slot
  immediate `%12` instead of `%14` records state 0 and is refuted
  (`coro_two_state_roundtrip_miswired_refuted`). The generator CFG is
  `cfgWith susp` over its suspend block, so every control shares the entry /
  final / trap block lemmas. Lean only, no wire change. `CoroSuspend` STAYS excluded from the lowering-target subset
  (`bridge.rs` / `subset.rs` reason strings now say "proved, not yet
  admitted"); admission is a follow-up subset version bump with the WS2.1
  validator arm as its precondition. Ledger: the B3 "Coroutine resume
  dispatch" box is checked; `lowering-target-subset.md`'s exclusion row is
  updated.
- **Lexical-scope inlining chain, the in-memory and text/serde half
  (roadmap WS4.19, F-082; trigger-gated, non-wire part).** `ScopeData` gains
  `inlined_at: Option<InlinedAt { span, callee }>`: the CALL SITE an inlined
  callee's body was spliced in at and the callee's display path — the
  `DW_TAG_inlined_subroutine` chain a diagnostic needs to say "inlined from
  caller.rs:12" instead of attributing an inlined Clean island to its Rust
  caller's scope. One record, not two fields, because the canonical
  MessagePack codec is positional and a struct may carry ONE trailing
  skipped field; both halves are required (MIR's `SourceScopeData::inlined`
  has the same shape). `ScopeData` is no longer `Copy`; `ScopeData::new`
  builds a plain scope. The text `; #scope:` directive gains
  `inlined-at <file> <line> <col> callee "<path>"` (Debug-quoted like
  `#names`; a link without its callee is a parse error); JSON and MessagePack
  carry the link losslessly and a module without one keeps its exact prior
  bytes (a pre-WS4.19 `[parent, span]` array decodes with no link). The
  validator adds `InvalidInlinedScope` (the outermost scope cannot have been
  inlined; a link must name its callee) and range-checks the call-site span's
  file index like every span (`SpanFileIndexOutOfRange`). `trust-ir merge`
  remaps the call-site file index across the module boundary. **The BINARY
  carrier is deferred to the next open wire batch** (a reservation first,
  `docs/wire-allocation.md`): until it lands every binary writer REFUSES a
  module whose scope table carries a link — the fallible projection with the
  new `BinaryProjectionError::InlinedScopeChainUnencodable { function, scope }`,
  the infallible entry points by panicking with the same message — rather
  than dropping the chain and calling the round trip complete. The trigger
  (a producer inlining across the language seam, or trust-cg emitting DWARF
  inlined subroutines) was measured NOT fired on 2026-09-20, which is why
  no wire version is spent here. Tests: `trust-ir-conformance`
  `inlined_scope_chain` (gate 8; ports the proof-program rows
  `trust-ir-self-declared/debug-info-inlining-chain` and
  `small-designs/OMET-06-debug-and-provenance-carriers` as
  `ratchet_debug_info_inlining_chain` / `ratchet_omet06_debug_and_provenance_carriers`,
  plus the named binary refusal, the legacy serde shape, the text negative
  twin and the diff mutation control) and `trust-ir-build`
  `inlined_scope_validation` (gate 9).
  **Review:** a chain-bearing module has NO WIRE IDENTITY until the wire
  part lands, and the increment left every digest-keyed path to reach the
  panicking writer: `wire_identity_blocker` now names it
  (`ModuleHasNoWireIdentity`, the WS3.5 `MakeAggregate` precedent), so the
  linked import walk (root and resolved candidate), the bundle binding and
  `trust-ir validate --link` refuse by name instead of aborting;
  `Module::first_inlined_scope_chain` is the feature-independent probe;
  `trust-ir convert --to bin` exits 1 naming the function, scope and field;
  `trust-ir digest` names the chain in its not-encodable refusal; and
  `trust-ir run` hashes its inputs only when there is an import row to
  authenticate, so a chain-bearing module with none executes (`trust-ir-cli`
  `cli_inlined_scope_chain`; `trust-ir-diff` `cli` pins `--include-debug`;
  `inlined_scope_validation` adds the no-panic walk and an unreferenced
  scope's malformed link staying refused).
- **`trust-ir diff` debug lane (roadmap WS4.19 mutation control, a WS4.13
  remainder).** `DiffOptions::include_debug` (CLI `--include-debug`) compares
  each function's lexical scope tree — parents, opening spans and inlining
  chain links — and reports a change as the `"scopes"` function meta row.
  OFF by default: the default lane still ignores scopes as claim-style debug
  metadata, and the option never changes what the default lane reports.
- **Core bulk-memory and bit intrinsics (roadmap WS3.20, F-057; DECIDE
  DG-49 adopted as recommended: CORE ops, not a pinned `mem.*`/`bit.*`
  dialect).** Seven sub-ops and two instructions, each a coordinated triple
  (Rust + Lean semantics + validator), replace the shims and the
  `RegionHavocStore` marker a producer had to emit for a dynamic-count copy:
  `UnOp::{CtLz, CtTz, BSwap, BitReverse}` (text `ctlz`/`cttz`/`bswap`/
  `bitreverse`; TOTAL — `ctlz 0 = cttz 0 = width`, the one spelling, no
  poison operand), `BinOp::{RotL, RotR}` (`rotl`/`rotr`; the amount is
  reduced modulo the width, so unlike the shifts there is no `ShiftInRange`
  obligation) and `BinOp::FCopySign` (`fcopysign`; IEEE copySign, executes at
  `F32`/`F64` like `FNeg`); `Inst::MemCopy { dst, src, bytes, overlap }`
  (`memcopy [overlap] ptr %d, ptr %s, %n` — memmove when `overlap`) and
  `Inst::MemSet { dst, byte, bytes }` (`memset ptr %d, %b, %n`). A bulk
  copy carries every byte's VALUE, INIT STATE (an uninitialized source byte
  stays uninitialized — copy-propagates-poison) and pointer PROVENANCE (a
  copied pointer still dereferences); out of bounds, and overlap without
  `overlap`, are UB (the interpreter faults by name, Lean answers `ub`); a
  zero count is a no-op. Validator: `dst`/`src` pointer-like
  (`OperandNotPointer`), `bytes` EXACTLY `Usize` under target info / `U64`
  without (`OperandTypeMismatch { role: "bytes" }`), `byte` exactly `U8`, the
  bit ops integer-only like `CtPop` (`ctlz f32` is `BinOpRequiresInteger`),
  `fcopysign` float-only like `FMin`; a handle-typed operand is
  `InvalidHandleUse` through the existing nominal arm, so a sealed handle
  slot cannot be bulk-copied. The obligation leg is the existing machinery: an
  `InBounds` claim on the node backed by a `ProofRef` to a `MemorySafety`
  obligation SITED on it. Lean: `semIntUnOp`/`semIntBinOp` arms
  (`ctlzWidth`/`cttzWidth`/`bswapWidth`/`bitReverseWidth`/`rotlWidth`/
  `rotrWidth`), `semFloatBinOp .FCopySign` (a NaN sign is unobservable in
  Lean 4.8.0 and refuses by name), `semMemCopy`/`semMemSet`
  (Semantics/Memory.lean), the byte-level contract `memcopy_preserves_bytes`
  + `memcopy_untouched_below` (Proofs/MemoryProps.lean, AxiomAudit green),
  twenty-one `ExecutableFixtures` interpreter-agreement locks. trust-ir-ay:
  exact bit-vector encodings for the six integer ops (`fcopysign` refused by
  name: SMT-LIB's single unsigned NaN cannot carry the sign the interpreter
  copies). `FunctionBuilder::memcopy`/`memset`. Tests: `bulk_memory_ops` in
  trust-ir (gate 9; the roadmap rows `goal-g1-g8/g1-intrinsics-bulk-memory`
  and `goal-g1-g8/g3-no-symbolic-placeholder` ported by name; every
  rotate/bswap/ctlz/cttz value checked against Rust's `u8`/`u64` intrinsics
  over the exhaustive u8 set and a sampled u64 set) and trust-ir-build
  (gate 9); two-language rows `b7.intrinsics.g1_bulk_memory` and
  `b7.intrinsics.g3_no_havoc_for_bulk_copy` with negative twins.
  **DEFERRED to the wire lane (Batch INST, `docs/wire-allocation.md`):** the
  binary tags — the writer FAILS CLOSED by name on every new variant
  (`tag_enum!`'s new `unencodable` clause; `write_inst` panics like
  `Ty::Error`; nine `wire_census::UNENCODABLE` rows), the reader is unchanged
  and pinned to refuse the next free `UnOp`/`BinOp` tag, no golden changes.
  A module carrying any of the nine therefore has NO WIRE IDENTITY, exactly
  like a `MakeAggregate` module (WS3.5): the new `Inst::binary_wire_gap` is
  the ONE probe list, and both `trust_ir_build::wire_identity_blocker`
  (`ModuleHasNoWireIdentity` on every digest-keyed path — the linked walk,
  the bundle binding) and the CLI's `convert --format bin` consult it, so
  the refusal is by name, never a writer panic (pinned per variant in
  `bulk_memory_ops`).
  Also deferred: admitting `MemCopy`/`MemSet` to the lowering-target subset
  (a subset-contract bump; `bridge.rs` excludes them by name meanwhile), the
  trust-cg lowering, and the ~/trust producer replacing its havoc sites
  (WS5.17). `fma` stays out (ternary; no measured producer demand).
  Review (2026-09-21): the reference interpreter's `MemSet` bounds-checks
  BEFORE it materializes the fill image — a hostile `u64::MAX` count used to
  abort the process on capacity overflow (and a few-GiB count tried to
  allocate it) instead of faulting with the ordinary out-of-bounds UB
  (`a_hostile_byte_count_faults_and_never_allocates`); a bulk op on a freed
  allocation faults by name, a `Usize` count under target info executes, and
  the `overlap` flag is a semantic difference to `trust-ir-diff` — each pinned
  in `bulk_memory_ops`.
- **The release entry points of the pinned runtimes are named in ONE place,
  and the reference host model keys its dead-marking on it (roadmap WS3.22,
  F-060 — `Dealloc` cannot state a free).** The format half of F-060 was
  already ratified: `Inst::Dealloc { ptr }` states neither the `AllocOrigin`
  whose runtime owns the region nor the layout being released, so G18-1
  excludes it from the lowering-target subset and `validate_module_for_codegen`
  refuses it as `UnlowerableForCodegen`, while every shipping producer spells
  a free as a CALL to the owning runtime. This increment keeps G18-1 (DECIDE:
  no wire change, no widening of `Dealloc`; no producer emits it) and closes
  the finding's open edge as far as the plan of record allows: a free that is
  a call is opaque to the reference interpreter and to Lean unless the callee
  is KNOWN to be a release. New in `trust-ir-build`:
  `pinned_release_entry_points()` / `pinned_release_entry_for_symbol()`
  (`PinnedReleaseEntry { symbol, runtime, subject, calling_conv, func_ty }`,
  `PinnedReleaseSubject::{Handle, RcCell}`), DERIVED from the two pin tables
  rather than listed a third time — `HandleRuntimePin::release_entry` (the
  unique consuming-only entry, `drop`) and `RcRuntimePin::release_entry` (the
  `release` role) — so v1 names exactly `trust_bignum_nat_drop` (the `Nat`
  handle) and `clean_dec` (a `CleanHeap` cell). The WS2.13 reference model
  `PinnedHandleHost` now decides "this call is a free" by that table and by
  nothing else — the role-string `"drop"` arm of the Nat model and the
  `"release"` role mapping of the RC classifier are gone — and models it as
  the SAME dead-marking step Lean's `semDealloc` performs on the released
  subject (`HostState::release_handle` for a handle; the interpreter's own
  `Release`, dead at count zero, for a `CleanHeap` cell), so a use after
  release through a pinned runtime is an interpreter fault
  (`UndefinedBehavior`: "used after release" for a handle, "freed allocation" /
  "use after dealloc" for a cell — the latter the very fault a load after
  `Inst::Dealloc` raises) instead of an opaque call, and a release the table
  stopped naming is NOT served (`UnsupportedCall`, fail closed), never a
  silent no-op. `RustHeap` frees (`__rust_dealloc`) are pinned by no table and
  stay opaque — stated, not hidden: with or without a host the interpreter
  refuses the call by name (`UnsupportedCall`, `unhosted_callee`). Tests
  (`crates/trust-ir-build/tests/release_entry_points.rs`, gate 9): the G18-1
  state (`Dealloc` validates, executes in-format, is exactly one
  `UnlowerableForCodegen` naming the missing `AllocOrigin`/layout) with the
  close twin (the same free as a call to the pinned `trust_bignum_nat_drop`
  or `clean_dec` passes `validate_module_for_codegen`) and its mutation
  control (a release through an unpinned `trust_bignum_nat_free` is
  `HandleForeignDeclaration`); the derived-not-restated control (a registry
  whose row releases through another symbol names that symbol; a row with no
  consuming entry names nothing); and the first executable witness for
  `TRUST.md` item 9(c): under `PinnedHandleHost` a double
  `trust_bignum_nat_drop` of one handle faults, a single drop runs clean, and
  a no-op-release mutant of the model cannot see the double free
  (host-assisted, a trusted model, never in-format evidence) — with the
  `CleanHeap` twin for item 13 (double `clean_dec`, load after `clean_dec`).
  `host.rs` gains `every_pinned_release_entry_point_is_modelled_as_a_release`
  (table and model cannot drift apart). Gate 8 (`interpret_differential`)
  gains `ws3_22_pinned_release_differential`: 512 seeded release/use programs
  over Nat handles and Clean cells checked against an independent liveness
  oracle under the reference model, with the no-op mutant running every
  program to `Ok`. Ledger: five new `b5` PASS rows
  (`b5.dealloc_cannot_state_a_free` + twin,
  `b5.release_entry_points_named_once` + twin,
  `b5.double_drop_faults_under_a_release_marking_host`) port the archived
  rows `trust-ir-self-declared/dealloc-cannot-state-a-free` and
  `consumer-trust-cg/18-dealloc`. Documented in `lowering-target-subset.md`
  ("Deallocation"), `docs/SPEC_RATIFICATIONS.md` §7 and `TRUST.md` items 9
  and 13. Adversarial review hardened the derivation itself: naming a release
  by `returns.is_empty()` alone is an UPPER BOUND on "is the release", not the
  predicate — a void entry that merely REACHES a handle need not CONSUME it
  (an in-place `set_u64(H, u64) -> ()` returns nothing and satisfies
  `EntryDoesNotReachHandle`), so the weak predicate would have named a mutator
  the release of its row and a host keyed on the table would have dead-marked
  a still-live handle, faulting a legitimate program on its next use. Both
  `release_entry` accessors now require the consuming shape (`(H) -> ()`,
  `(Ptr) -> ()`) before naming an entry a release, which makes
  `PinnedReleaseEntry::func_ty`'s one-parameter/no-result claim true by
  construction and leaves the release singular (the narrower predicate is a
  subset of the one `from_pins` bounds at one per row); an entry the shape
  rejects is served by no release arm and fails closed. Four further
  adversarial rows pin the keying end to end: a release through one COPY of a
  handle kills every copy (identity, not SSA value); a pinned release reached
  through a `Constant::FnDef` function pointer is still the dead-marking step,
  while the provenance-free `Constant::SymbolAddr` spelling never validates
  (`HandleEntryPointAddressTaken` / `RcEntryPointAddressTaken`); the pinned
  `clean_dec` and `Inst::Release` are ONE count in either order; and a
  `clean_dec` of a `RustHeap` cell, or a `clean_inc` after the release, is
  `UndefinedBehavior` — each invisible to the no-op mutant.

- **`Ty::Sequence` has a validated element read and write (roadmap WS3.17
  part (a), F-051).** `Ty::supports_element_ops()` answered vector-or-array,
  so `ExtractElement` / `InsertElement` over a `Ty::Sequence` were refused
  outright (`InvalidVectorElementOp`, "operand must be vector or array")
  while the reference interpreter executed exactly that read and the Lean
  model TYPE-ERRORED on it — three engines, three verdicts on a construct
  `lowering-target-subset.md` admits. A Clean `List`/`Array` carrier could be
  built, transported and MAPPED (`SeqMapAddK` / `SeqMapNot` / `SeqMap`) but
  never indexed inside a well-formed module. The rule now shared by all
  three: `ExtractElement` over `Sequence(t)` validates with a result type
  exactly the module's `t` (`InsertElement` likewise for the inserted value;
  a refined element is decided by the WP-1B consumption rule, as a vector
  lane is), the index must be an UNSIGNED integer (a sequence's length is a
  property of the VALUE, so the index type is the only place non-negativity
  can be stated — a vector/array has the static range check instead), a
  negative constant index is refused, and an index past the end is run-time
  UB exactly as for a dynamic array index. A sequence whose element `TyId`
  is not in the type table is refused, never admitted. Fail-closed for
  codegen: `Ty::Sequence` still has NO machine layout, so
  `codegen_lowerability_errors` names both ops (`UnlowerableForCodegen`)
  instead of leaving trust-cg's layout query to fail late. Lean:
  `getElement` / `setElement` gain `.sequence` arms (a write keeps the
  sequence constructor), `semExtractElement` / `semInsertElement` answer UB
  on an out-of-range sequence index, the `TransformCorrectness` PNL lemmas
  follow, five `ExecutableFixtures` locks pin the outcomes, and
  `seqMapAddKList_length` / `seqMapNotList_length` prove the give-back maps
  preserve length (the instruction-free half of the WS3.17 `seq_len_map`
  rule). DECIDE adopted (recommended): `Sequence` stays verification-level;
  a borrowed string crosses the language boundary as `FatPtr(Str)` and an
  owned Clean `String` as a future pinned runtime handle row — never as a
  `Sequence`. Tests: `sequence_element_ops` (gate 9; positive read/write
  that validate and run, negative twins for an `f32` index, a signed index,
  a `u16` result over `seq<u8>`, a `u16` inserted value, a negative constant
  and a dangling element type, mutation controls for the scalar-operand
  refusal, the unchanged array rules, out-of-range run-time UB, the
  `SeqMapAddK`-then-read differential, and the codegen refusal with its
  array-spelling control). Ratchet flipped:
  `b6.sequence.no_validated_element_read` (GAP -> PASS: the read validates,
  runs and is refused for codegen by name; the archived row's `i64` index is
  now the `.negative_twin`, refused on the sequence and still admitted on the
  array). Deferred to the
  wire lane: part (b), `Inst::SeqLen { seq } -> Usize` (a new `Inst`, next
  free version, coordinated triple with `semSeqLen`).
- **An ARRAY element op is held to the exact element type too (WS3.17
  review).** The element-op arms said an array's element type was "checked
  elsewhere by the module-level type table", but the only module-level
  consumer engages when a `Refine` is involved, so a `u16` `ExtractElement`
  over `[u8; 3]` — and a `u16` `InsertElement` into one — validated CLEAN and
  was caught only by the reference interpreter's run-time type check (a
  backend would address the element at the wrong width). The same
  `check_table_element_ty` arm now covers `Ty::Array` and `Ty::Sequence`
  alike: exact `Ty` equality (the identity the vector-lane check, the
  interpreter and the module-level comparisons already use), the WP-1B
  consumption rule at a refinement-involving position, a dangling element
  `TyId` refused by name. Tests (`sequence_element_ops`, review section): the
  array read and write refusals with their exact-type control; a refined
  demand over the wrong base refused as a representation mismatch; a bare
  write into a refined carrier refused and a refined write into a bare one
  admitted; a parameter-carried sequence decided by the module pass and
  refused for codegen; a nested `seq<seq<u8>>` read exact and running; the
  `usize` / `bool` / oversized `u128` index spellings; the write-side index
  rules.
- **Cross-repo landing order: the integration trains (roadmap WS8.3, the
  landing-order half of F-118).** A new internal roadmap document,
  `docs/roadmap/cross-repo-integration.md`, records the order in which the
  two-language completion work crosses the trust-ir / trust-cg / clean /
  ~/trust boundaries as seven trains (T0 pin realign through T6 packaging),
  keyed by finding id and increment id, never by date. It states the rules
  every train obeys (a consumer accepts a wire feature before a producer
  emits it; a validator tightening lands before a producer relies on it; a
  certificate kind is minted only after the validator admits it; wire
  versions land in number order; every train ends with a WS8.2 lattice
  move), the T1 consumer pre-flight and its known-red baselines, and what
  must be batched per train (one pre-flight per trust-ir `main` candidate;
  one text-golden regeneration per train; one reserved wire number per
  group, never a monolith). Docs only; no wire, code or test change. The
  document is excluded from the public snapshot.
- **Termination and Ownership wired on the format side; `trust.protocol` /
  `trust.facet` pinned (roadmap WS1.9, F-011, F-023, F-025 —
  `docs/SPEC_RATIFICATIONS.md` §11, no wire change).**
  `mint_summary_obligations` mints one function-scoped `Pending`
  `Termination` row per `decreases` measure, stating the measure as its
  `formula` beside the `Precondition` / `Postcondition` rows (before, a
  `proved` summary with a `decreases` clause could never be earned through
  the minter; archived row `b2.gap.mint_summary_obligations_skips_decreases`,
  now PASS with two twins). `proof_ref_kind_can_back` learns the v41 kinds:
  `Termination` backs `Terminates`; `Ownership` backs `DataRaceFree`,
  `NoAlias`, `UniqueBorrow`, `SharedBorrow` and `ValidBorrow` (never a
  value-validity claim); both back `Custom` at either level and no kind-less
  claim; `MemorySafety` still cannot back `DataRaceFree`. DECIDE A adopted:
  both kinds are discharged by a consumer capability (ay / trust-mc) and
  never kernel-certified — `is_contract_kind` refuses them by decision, and
  `b2.gap.termination_not_kernel_certifiable` is relabelled RATIFIED-OUT,
  held in its exact shape. `ADMITTED_OBLIGATION_NAMESPACES` gains
  `trust.protocol` (the TrustIr spelling of trust's `Protocol` kind) and
  `trust.facet` (E6 facets `pure` / `deterministic` / `total` / `nopanic`),
  pinned in lockstep with trust's list — the trust half (its list and its
  bridge's `Protocol` spelling) is a listed companion; until it lands such a
  row validates here and is refused at trust's serde boundary. DEFERRED, not
  declined: the routing flip `Terminates` → `Termination` /
  `DataRaceFree` → `Ownership` in `ProofAnnotation::obligation_kind` (and the
  `Pure` / `Deterministic` → `trust.facet` routing that would take them out of
  WS1.1's attribution rule), because `Module::add_function` synthesizes a row
  of the routed kind and the `proof_annotations` golden carries every claim at
  function level, so the flip would grow that fixture's `TEXT_LOSS_RATCHET`
  row (the text format refuses a v41 kind until WS4.4, F-071) — it lands with
  or after WS4.4, changing the map and the table in one commit.
  `ProofRefKindMismatch` now names `termination` / `ownership` / `custom`
  instead of `unknown`. The b7 surface fixture sites the MINTED decreases row
  instead of hand-building one (same id, same formula). Tests: `contracts`
  unit tests (countdown positive, Liveness twin, row-deletion control),
  `fast1_proof_ref` `ws1_9_*` and `custom_obligation_namespaces` `ws1_9_*`
  (both registered in gate 9), the extended inverse-table property test.
  Review pins (WS1.9 review, four adversarial shapes): a genuine kernel
  certificate minted for a `Postcondition` twin of a minted `Termination` row
  and re-bound to it by lineage is refused on its KIND
  (`CertifiedCleanCicKernelRecheckFailed`; the identical certificate
  validates on the twin), two `decreases` measures need two rows (deletion,
  foreign scope, an extra binding and a restated measure each refused by
  name), a pinned `trust.facet` row is admitted and entails nothing
  (`total` does not back `Terminates`, `pure` backs neither `Pure` nor a
  `Custom` claim), and an `Ownership` row backs a node-level `ValidBorrow`
  only when sited on that node (`per_clause_proved` and `fast1_proof_ref`,
  both already in gate 9).
- **WS2.13: reference host models of the pinned trusted runtimes — the
  `trust_bignum::Nat` row and the Clean RC triple; `trust-ir run --host
  pinned`** (closes the model half of F-035; DG-41 adopted as recommended:
  the rest of Clean's runtime ABI — box / ctor / closure / string / nat — is
  modelled in the clean repo, not here). `trust_ir_build::host::PinnedHandleHost`
  implements `HostCalls` for EVERY entry point of `TRUSTED_HANDLE_RUNTIMES`
  (all nineteen Nat roles, over a dependency-free `Vec<u64>` little-endian
  magnitude with the pin table's Lean semantics: truncating `sub`, `n / 0 =
  0`, `n % 0 = n`, `beq`/`ble`, `fits_u64`, `to_u64` ABORTS above `u64::MAX`
  as the interpreter's `Panic`, `clone`, bitwise ops, shifts, `pow`; a result
  past the model's 2^24-bit capacity is the `OutOfMemory` incapacity, never a
  verdict) and for every entry of `TRUSTED_RC_RUNTIMES`, keyed by the SAME
  tables: a declaration is served only under the exact pinned symbol,
  signature and calling convention, otherwise it is "not mine" and the run
  stays the fail-closed `UnsupportedCall` (the `(Ptr, Ptr) -> Ptr` twin). The
  unit test `every_pinned_entry_point_has_a_host_model` fails when a pin row
  gains a role without a model arm. Handles live in the interpreter's
  per-execution `HostState`, so under the model a double `drop` and a use
  after `drop` through a `Copy` are `UndefinedBehavior` by name — the TRUST.md
  item 9(c) residue surfacing at run time under a trusted model, not a
  validator guarantee. **`HostCalls` API change (intended):** `call` now
  receives the declaration's `&FuncTy` (the interpreter resolves it anyway),
  and a new provided method `rc_op(&Function, &FuncTy) -> Option<HostRcOp>`
  lets a host CLASSIFY a declaration as the `retain` / `release` / `is_unique`
  entry of the RC runtime owning one `AllocOrigin`; the INTERPRETER then
  performs the operation on its own per-allocation refcount — the table
  `Retain` / `Release` / `IsUnique` already maintain — after checking that the
  pointer addresses a live cell of that origin at offset 0 (`HeapAlloc` now
  records its `origin` on the allocation): a `RustHeap` cell, a stack slot,
  an interior pointer or null handed to `clean_inc` is `UndefinedBehavior`
  (item 13(c), "no ownership transfer between heaps", made observable), and a
  declaration of the wrong shape is `UnsupportedCall`. The host never sees
  the pointer. `trust-ir run --host pinned` installs the model (default
  `--host none` keeps every declaration refused by name); a served run prints
  `host-assisted: N call(s) served by the pinned reference host model (...
  not in-format execution evidence)` from the interpreter's own count, and a
  handle return renders as `handle(#id, ty)`. The linker now leaves the pinned
  RC triple BODYLESS like the handle entry points: since WS3.21 pinned it, a
  trap stub for `clean_inc` DEFINED the symbol and failed `run --validate`'s
  post-lowering pass as this tool's own defect (`RcEntryPointDefinedLocally`,
  exit 3). `TRUST.md` items 9 and 13 label both models "reference models of
  trusted runtimes; a run that used them is host-assisted evidence, not
  in-format execution". No wire change. Tests: `interpret_host_models` (gate
  8: every Nat entry point executes, the Lean-semantics table, multi-limb
  arithmetic, the abort of `to_u64`, double-drop and use-after-drop, the
  mis-declared twins, cross-model handles, the RC triple on `CleanHeap` cells
  with the other-heap / stack / interior / null refusals and an over-claiming
  host), `host.rs` unit tests (`sub(2, 5) == 0` catches a wrapping model),
  `cli_run` (`--host pinned` runs the Nat program to `1`, the mis-declared
  twin is refused by name, the RC triple stays bodyless and executes). Ratchet
  flips in `RATCHETS.tsv`: `b5.gap.reference_interpreter_cannot_execute_handle_program`
  and `b5.gap.cli_run_cannot_execute_handle_program` GAP -> PASS (host-assisted,
  with the no-host twin); `b5.gap.handle_is_outside_the_proven_conformance_subset`
  GAP -> RATIFIED-OUT (a host model is not the proven subset, by design);
  `b5.gap.cli_run_without_validate_traps_at_pinned_stub` stays PASS, extended
  with the hosted run and the ordinary-extern twin under `--host pinned`.
- **`Inst::MakeAggregate` — the register-level aggregate seed (roadmap
  WS3.5, F-049 register-seed half).** `Inst::Const` was the only originator of
  an aggregate VALUE, and no `Constant` inhabits `Rc<T>` / `&T` / `&mut T` /
  `*const T` / `*mut T` (a constant reference has no provenance), so an enum or
  struct with a typed-reference lane had no register seed at all — only the
  memory lane (`HeapAlloc` + field `Store`s + `Load`) could build one, and
  `Undef` + `InsertField` executes as UB. The new instruction
  `MakeAggregate { ty, variant: Option<u32>, fields: Vec<ValueId> }` (text
  `%r = make_aggregate <ty> [variant N] (%a, %b)`) builds a fully-initialised
  struct / tuple / record / array from declaration-ordered lanes, or ONE enum
  variant by index (the tag is `discriminants[v]`, never an operand). It is
  total and statically typed — no run-time obligation; the validator rule IS
  the side condition: `validate_make_aggregate` refuses every other type
  (scalar, `Closure`, `Sequence`, `Set`, `FatPtr`, `Vector`, `Dialect`,
  `Handle`, `Refine`), a `variant` on a non-enum or missing on an enum, an
  out-of-range variant, a dangling definition and a wrong lane count by name
  (new `ValidationError::InvalidMakeAggregate`), an uninhabited variant as
  `UninhabitedVariantConstructed` (WS3.14's rule), and each lane operand
  EXACTLY as `InsertField` checks its value — `OperandTypeMismatch { op:
  "make_aggregate", role: "lane i" }` for `Ptr` or `&T` at an `Rc<T>` lane
  (equality, never `is_pointer_like`), and the refinement consumption rule
  (`CheckedConsumption::FieldWrite`) for a refined lane, so an unrefined
  operand is `RefinementNotImplied` exactly as it is there. A handle or
  dialect lane stays refused by the nominal transport whitelist. The reference
  interpreter builds the existing `[tag, fields..]` value model
  (`eval_make_aggregate`) and fails closed on every ill-shaped case an
  unvalidated module could carry; `FunctionBuilder::make_aggregate` /
  `make_enum_variant` are the builder doors. Lean: `Inst.MakeAggregate`,
  `semMakeAggregate` (`lookupLanes` then `buildAggregate`), the DCE
  nonlocal-state case, and `extract_make_aggregate` in `AggregateProps.lean`
  — ExtractField i ∘ MakeAggregate = fields[i], at the operational layer —
  proved; enum and record construction are an honest partial that fails
  closed as the new `unsupported.enum_def_table` (the Lean machine state
  carries no definition tables). Ratified as the canonical spelling for an
  aggregate with a non-constant lane (`docs/SPEC_RATIFICATIONS.md` §3, a
  producer rule); `Const` stays canonical for an all-constant one. Tests:
  `make_aggregate` (trust-ir-build, gate 9: the b6 boxed tree re-spelled with
  `make_aggregate enum.0 variant 1 (Rc<Tree>, Rc<Tree>)` validates and runs to
  42; the `Const [Int(1), Int(0), Int(0)]` twin stays exactly two
  `ConstTypeMismatch`; lane order swapped, arity off by one, variant index =
  count, `Ptr` / `&T` for an `Rc<T>` lane, variant on a tuple, missing
  variant, non-aggregate types, an uninhabited variant and the refined-lane
  rule each refused by name), `make_aggregate_formats` (trust-ir: text / JSON
  / MessagePack round trips, diff identity of the variant clause, the parser's
  refusal of a malformed lane list, the writer's refusal), the Lean parity
  gate lists `MakeAggregate`, and ratchet
  `b6.enum.typed_ref_payload_has_no_register_seed` flips GAP -> PASS.
  **Deferred, fail closed: the wire tag.** The INST wire batch (a new `Inst`
  tag byte and the format version that read-gates it) is a separate
  reservation under `docs/wire-allocation.md`; until it lands the binary
  writer PANICS on the instruction (listed in `wire_census::UNENCODABLE`,
  `trust-ir convert --format bin` refuses by name with the user exit code),
  a module carrying it has no `stable_digest`, and it is outside the
  lowering-target subset v3 (`lowering-target-subset.md` addendum
  2026-09-19; trust-cg refuses it until WS7).
  **Review:** a module with no wire identity must not CRASH a validator. The
  linked import walk (root at entry, every resolved candidate at L2) and the
  coverage-assurance bundle binding each panicked inside `stable_digest` on
  a module carrying the instruction; they now refuse by name — new
  `ValidationError::ModuleHasNoWireIdentity { location, construct }` on the
  root / bundle paths (`checked: false`, nothing authenticated),
  `UnauthenticatedImport` naming the reason on the candidate path — through
  the new probe `trust_ir_build::wire_identity_blocker`, whose arm retires
  with the wire tag. Four more adversarial rows pinned in `make_aggregate`: a
  dialect lane is `InvalidDialectType` (the transport whitelist claim,
  measured); an enum WITHOUT a layout descriptor constructs under the
  canonical layout and executes; a `Tainted` lane taints the aggregate
  (`TaintedValueReachesTrustedSink`, no laundering through the new
  spelling); a `Refine` as the aggregate type is `InvalidMakeAggregate`.
- **The kernel-TV fragment widens by five slices, on the trusted mirror
  (roadmap WS1.15, F-015).** `clean_backend_tv` in `trust-ir-build` used to
  re-derive `U8..U64` params, `Const`/`Add`/`Sub`/`Mul`, and an `ICmp` only
  when it fed the entry `CondBr`; a `Bool` result, a Bool connective, a
  `Select`, a `Switch`, an enum param, a signed width, `slt`/`ne`,
  `udiv`/`and`/`xor`/`shl` and a `ZExt` were well-formed, executable and
  never certifiable. Every fragment value now carries a SORT: `U8..U64` and
  `I8..I64` are `Nat` bit patterns (signed = two's complement over `Nat` mod
  `2^w`, the sign read only by `slt`/`sle`/`sgt`/`sge` through the
  `(x + 2^(w-1)) mod 2^w` bias), `Bool` is the kernel `Bool` (the one Bool
  spelling, DG-34 adopted as recommended), a fieldless-enum param is its
  tag. S1: Bool results/params, `Bool.and`/`Bool.or`/`Bool.xor` (also the
  `BAnd`/`BOr`/`BXor` opcodes), `Select` as `Bool.rec` at the result sort,
  `Ne` as `Bool.not (Nat.beq)`, `ICmp` anywhere. S2: an entry `Switch` over
  a machine integer as the nested `if Nat.beq v k` in case order, with a dead
  `[Unreachable]` default admitted ONLY when the selector is a fieldless
  enum's tag-lane read and the cases are exactly its discriminants. S3:
  signed widths and comparisons; `SDiv`/`SRem`/`AShr` stay out. S4:
  `UDiv`/`URem` only with a divisor that is a nonzero constant or is nonzero
  by a dominating `CondBr` on `icmp eq/ne b 0` (the eager `select`-guarded
  division is refused by name — division by zero is UB); `And`/`Or`/`Xor` as
  `Nat.land`/`Nat.lor`/`Nat.xor`; `Shl`/`LShr` as `Nat.mul`/`Nat.div` by
  `Nat.pow 2 k` (the pinned prelude's `Nat.shiftRight` is an axiom the
  rooted audit refuses), only by a constant below `w` or by `urem x, w`. S5: `ZExt`/`Trunc` as `Nat.mod` at the destination
  width, so a signature may mix widths (Fragment-4 heap cells take the
  RESULT width). A Fragment-4 `GEP` index folds only from a closed
  NON-NEGATIVE literal: a signed literal now denotes its bit pattern (`-1`
  at `I8` is `255`), but a negative index is UB in the reference semantics
  (`interpret::eval_gep`), so it is refused by name rather than folded to a
  defined cell. Callee symbols (Fragment-3b) are now typed from the callee's
  OWN signature sorts; a comparand's param binders must carry the re-derived
  sorts; an enum-RETURNING callee is refused by name (an enum is a param
  sort, never a result sort — the same rule the function itself is under). `U128`/`Usize` stay outside by ruling (no bignum scalar; no width
  without a target) and are refused by name. The recheck refusal now reads
  `(signature (Nat64, Nat64) -> Nat64, arity 2)` instead of `(width U64,
  arity 2)`. No wire change. Tests: `tv_fragment_widening` (gate 9) — per
  slice a positive certificate (also executed by the interpreter), a
  negative twin the kernel refuses (`ult`→`ule`, `ne`→`eq`, `and`→`or`,
  `slt`→`sle`, `slt`→`ult`, swapped Select/CondBr/Switch arms, `shl 3`→
  `shl 4`, `zext(a+1)` under `zext(a)+1`), and mutation controls (a width
  retype is refused by the kernel; `sdiv`, `ashr`, `sext`, an ICmp at
  `Bool`, a Bool `zext`, an unguarded or `select`-guarded `udiv`, a shift by
  `64` / `urem s 65` / an open amount, a dead `Switch` default over a plain
  integer or over an incomplete case set, a heap `GEP` indexed by a
  negative signed literal — which the reference interpreter refuses as UB —
  and an enum-returning callee are refused by name, while a non-negative
  signed index still folds and certifies). The certificate binds the
  CARRIER, not only the value: an `I<w>` position is stated at the signed
  carrier alias `CleanTV.Int<w> : Type := Nat` (a reducible definition
  installed beside the heap vocabulary; the kernel unfolds it), and the
  comparand's binders must spell it, so the increment's mutation control — a
  sign-only retype `u32`→`i32` around `Add`/`Mul`, which changes no bit and
  which the kernel alone could not distinguish from its source — is refused
  by name (`comparand param binder 0 is not `CleanTV.Int32`-typed`), in both
  directions; a relabelled comparand that also changes the width is refused
  by the kernel, and one that honestly restates an unsigned source for an
  unsigned emission checks. Stated in `TRUST.md` item 6. Ratchet: the
  sixteen `b3.gap.{bool_result, bool_connective, select.*,
  switch_terminator, enum_param, width.{i64,i32,i8}, icmp.{slt,ne},
  binop.{udiv,and,xor,shl}, mixed_width_cast}` rows flip GAP → PASS with
  hand-built source comparands and kernel-refused twins; `width.{u128,usize}`
  stay GAP with the new refusal text. Clean-side companion (WS6.6, not in
  this repo): clean-reflect's `denote` maps and the `emit_trust_ir_tv` minter
  adopt the same spellings, then clean re-pins trust-ir and turns each shape
  on (WS6.5 ordering (i)→(ii)→(iii)); DG-33 (the tier-`gate` carrier-defeq
  anchor) stays with clean.
  Adversarial review of the same slice added seven probes, all of which the
  checker already withstands and which are now regression tests: a `udiv`
  under a zero test on a DIFFERENT value, and one on the `b == 0` arm of an
  `icmp ne b, 0` diamond, are refused (the nonzero fact is keyed by VALUE, and
  `Nat.div _ 0` is total in the kernel, so denoting either would certify a
  body the machine leaves undefined); `lshr`/`udiv` at a SIGNED type are the
  bit-pattern operations the reference interpreter performs (`-1i8 >>u 1` is
  `127`, `-1i8 /u 3` is `85`, and a negative divisor literal is nonzero); an
  `icmp slt` at an UNSIGNED declared type reads the 8-bit pattern's sign bit
  exactly as the `2^(w-1)` bias states it, with the `ult` twin kernel-refused;
  and a dead-default `Switch` over a fieldless enum with EXPLICIT
  non-contiguous discriminants listed out of ascending order certifies (the
  last case, a middle discriminant, folding into the `else`), while a case set
  that is not exactly the discriminants is refused. The review also narrowed
  one overstated claim: the signed carrier check binds the comparand's
  PARAMETER binders only — the comparand carries nothing for the result and
  `CleanTV.Int<w>` is def-eq to `Nat`, so a relabel of the RESULT's signedness
  alone still checks. `TRUST.md` item 6, the `signed_carrier_declarations`
  doc comment and two new tests now state that residue (and the same reason a
  fieldless-enum param shares one comparand telescope with its bare tag);
  recording the result carrier is a clean-side companion.
- **Wire v47 — the typed spec carrier (roadmap WS4.14, F-014's carrier /
- **Wire v48 — the typed spec carrier (roadmap WS4.14, F-014's carrier /
- **Wire v46 — the typed spec carrier (roadmap WS4.14, F-014's carrier /
  codec / tooling half; DG-29: extend `ProofFormula`, no SpecCore grammar).**
  A `SpecModule`'s surface was opaque text: `SpecVar.ty` and
  `SpecInvariant.formula` were strings, a `Liveness` obligation's payload was a
  string with no link to the property it discharged, and `ProofKind` had the
  single variant `Kani`. v46 (reserved `b9755a79` as v47, renumbered to v48 by
  `113a1c82`, then taken to the lowest open number 46 by `6d3f5303` so it
  could land in number order; the three tag rows, the
  `TemporalForm` tag space, `trust_ir.obligation.digest.v7` and
  `trust_ir.proof.clean_cic.lineage.v7` flip to landed) adds, every field
  read-gated `version >= 46` and `None`/empty on an older blob:
  `SpecVar.sort: Option<ClauseSort>`, `SpecInvariant.typed:
  Option<ProofFormula>` (the SAME first-order clause carrier contract clauses
  use, bindings naming state variables through the new
  `ClausePlace::SpecVar { index }`), `SpecModule.temporal: Vec<SpecTemporal>`
  (`TemporalForm::{Always, Eventually, LeadsTo, WeakFair, StrongFair}`,
  quantifier-free first-order leaves, no binder; only a fairness form's
  action relation may bind the primed `ClausePlace::SpecVarNext { index }`),
  `ProofKind::CleanTheorem { name }`, and `ProofObligation.spec:
  Option<SpecObligationRef { machine, temporal }>` — the temporal property a
  `Liveness`/`TemporalSafety` row discharges. The writer selects v46 only when
  one is used; `RawV38`/`CanonicalV38` refuse with `SpecCarrierRequiresV46`.
  Rules: S4 `SpecTypedBindingInvalid` (undeclared index; a sort the
  variable's declared `sort` — or, when unrecorded, its parsed `ty` tag —
  contradicts (`SpecVar::effective_sort`); signature place; primed variable
  in a state predicate) and
  `SpecVariableSortMismatch` (declared sort vs parsed `ty`), in BOTH
  enforcement modes; S3 under `Linked` — `LinkedTypedCarrierUnparsed`: a
  typed carrier's `smtlib` rendering must read as one well-sorted
  quantifier-free SMT-LIB2 `Bool` term over its OWN bindings (a free symbol
  they do not bind is undeclared even when the machine declares that name;
  a bound name is an unprimed simple symbol bound once), so a garbage
  rendering beside a well-formed binding list cannot certify — the F-014
  hole one layer up; `LinkedTypedCarrierDisagrees`: a typed invariant's
  rendering, read with each bound name replaced by the state variable its
  `SpecVar` place indexes, must be the SAME s-expression as the invariant's
  string `formula` (whitespace aside), because `typed` is documented as the
  same predicate and a module carrying two predicates under one name has
  not said which one a consumer certifies against — reported only when both
  renderings read and every binding resolves, so a garbage twin is named
  once by its own rule; a function summary binding a spec place is
  `InvalidFunctionSummary`; a module obligation binding one is
  `InvalidObligationBinding` unless its `spec` backref resolves, and then it
  is checked against that machine; `UnresolvedObligationSpecRef` for a
  backref on a non-temporal kind or naming no / more than one machine or
  property. **`CleanTheorem` resolves only against a `KernelCertifiedTheorems`
  witness** minted by the new `trust_ir_build::kernel_certified_theorems`
  from the certificates the validator's in-process CleanCic re-check replayed
  (`link_spec_modules_with_theorems`; `link_spec_modules` passes none, so a
  Linked machine's binding is `CleanTheoremUnresolved` and the exploratory
  option makes it `clean-theorem-unverified`) — never against a status byte,
  so `Certified` is still earned by the Clean kernel alone; `trust-ir
  spec-link` validates the module to mint the witness whenever a
  `clean-theorem` binding is present. The backref enters
  `obligation_content_digest` (domain `v6` → `v7`) and, presence-gated, the
  CleanCic lineage (`…lineage.v7`; every v5/v6 lineage keeps its bytes).
  Text carries `kind "clean-theorem" theorem ".."` and `spec "<machine>"
  "<temporal>"` and reports `sort`/`typed`/`temporal` as the new
  `TextLoss::SpecCarrier` (WS4.2; WS4.4 owns the binding spelling);
  `ProofObligation.site` stops being a skipped serde field so the appended
  `spec` is the sole trailing skip; `trust-ir-diff` fingerprints the new
  fields. Tests: `trust-ir/tests/spec_carrier.rs` (codecs, gates, S4 twins,
  witness, digests), `trust-ir-build/tests/spec_carrier_validation.rs` (gate
  9: the two `ClausePlace` leaks, backref resolution, the witness minter, the
  three ported proof-program rows `goal-g1-g8/s3-g6-tla-temporal`,
  `spec-surface-0709/33-temporal-spec-modules`,
  `trust-ir-self-declared/speccore-serialized-clause-carrier`), the
  `spec_carrier` conformance golden (gate 8, the only v46 header; text
  `#lossy` ratchet row) plus a `back_compat` gate test, `cli_spec_link` (the
  typed ring reports `spec-link-status: certifying`, three S4 twins exit 1,
  a `clean-theorem` binding without a kernel witness is non-certifying), and
  the ratchet rows `b7.spec.formula_and_var_type_are_strings` and
  `b7.spec.temporal_obligation_is_untyped` flipped GAP → PASS. Adversarial
  review adds one rule to S4, in both enforcement modes and on both surfaces
  (a machine's own carriers and a temporal obligation's bindings): a bound
  name that SPELLS a different state variable of the machine is refused
  (`SpecTypedBindingInvalid` / `InvalidObligationBinding`). The binding is
  what resolves the name, so such a carrier "means" the indexed variable —
  but every reader that puts the carrier's text beside the machine's `vars`,
  the `LinkedTypedCarrierDisagrees` check included, reads it as the variable
  it spells, and one name with two readings is the hazard that check exists
  to refuse. Binding a name to the variable it spells stays legal. Deferred:
  text spellings for `sort`/`typed`/`temporal` (WS4.4).

- **The reference interpreter executes binary16 and calls variadic
  declarations (roadmap WS2.15, F-036's f16 and vararg parts).** Every `F16`
  arithmetic, comparison, constant, cast, bitcast and memory-image site was
  `UnsupportedFloat`, so no differential evidence existed for any binary16
  body (critic `crit.unex05`); and `check_function_args` refused EVERY call
  into a vararg-typed function — including a bodyless `printf`-shaped
  declaration, the shape that blocked the repaired Clean general-lane module
  (`GENERAL.interpret`). Now (1) binary16 is computed at binary32 and rounded
  ONCE by the new `interpret::f64_to_f16_bits` (integer-arithmetic RNE,
  gradual underflow, overflow to `±inf` at the 65520 tie; `f16_bits_to_f64`
  is its exact inverse), which is the exact IEEE result because 24 ≥ 2·11 + 2
  makes the intermediate rounding innocuous; `FNeg`/`FAbs` are sign-bit
  operations, and so is `FCopySign` (WS3.20; the first cut refused it at
  `F16` as a `TypeError` "integer binop", and a signalling NaN keeps its
  pattern); an integer → `F16` cast's `f64` intermediate is exact below
  `2^53` and overflows to `inf` above it either way. (2) A call to a variadic
  DECLARATION is a host call (WS2.12) carrying the full argument list — the
  fixed prefix checked as before, the variadic tail refused only a runtime
  handle (`TypeError`: no exact type to transport it at) — through `Call`,
  `Invoke` and a `CallIndirect` whose pointer signature agrees on
  variadicity; a variadic DEFINITION stays refused with the unchanged, named
  `SignatureMismatch` "non-executable vararg signature" (no instruction reads
  a variadic argument), which `LIMITATIONS.md` ratifies out of scope along
  with `f128` (no `Ty`; the WS8 F-127 decision gate owns float widths). A
  variadic declaration of a symbol the installed host models at a FIXED
  arity is refused the same way (`SignatureMismatch`, "non-executable vararg
  signature") before the host is asked to serve it. The host says so through
  the new defaulted `HostCalls::models_fixed_arity`, and `PinnedHandleHost`
  answers it for every pinned `Nat` and Clean RC entry point. This keeps the
  WS2.13 ratchet: a variadic forgery of `clean_inc` is named for what it is,
  not reported as "no host model". The
  proven subset keeps `F16` excluded (the Lean model still refuses binary16;
  WS2.23 wires the binary32 rounder at p = 11), `InterpretErrorCode::
  UnsupportedFloat` stays as the Lean mirror with no current producer, and
  `trust-ir run` renders an `F16` return at binary16 instead of as a binary64
  reinterpretation of its pattern. Pinned by the new gate-8 targets
  `interpret_f16` (a 50-row bit-exact edge table — max+8 → 65504, max+16 →
  `+inf`, ties to even both ways, sticky bits, the subnormal floor, signed
  zeros — plus five rounding mutants each caught by the table, an
  exact-integer-oracle differential over thousands of seeded operand pairs,
  and a four-codec round trip of narrowed constants) and `interpret_varargs`
  (declaration served with every argument at its own type, function-pointer
  edge, definition refused by name through direct/indirect/entry, prefix
  arity and type still checked, handle in the tail refused). Row ports:
  `crit.unex05`, `producer-rust-thir/f128-and-f16`,
  `producer-rust-thir/c-variadic-body`, `goal-g1-g8/g1-foreign-calls-varargs`,
  `goal-g1-g8/g4-reference-interpreter-differential` (binary16 half),
  `trust-ir-self-declared/interpreter-unsupported-constructs` (f16 half).
- **A `Nat`-typed function can be imported: import-backed handle
  declarations in linked validation (roadmap WS3.3, F-048).** A dependency
  could define and export `dep_double: Nat -> Nat`, but no importer could
  declare it: v43 rule 6 admitted only pinned entry points, so the root's
  body-less declaration was exactly one `HandleForeignDeclaration` in every
  lane, `validate_linked_module` included. The binding is the existing v41
  spelling (DG-26, no wire): the declaration carries `backed_by: ExternRef {
  module, symbol: <its own name>, obligation: None }`. `validate_linked_module`
  gains rule L11: every body-less, non-pinned declaration reaching a handle
  that carries a `backed_by` is resolved through the new
  `Module::resolve_handle_declaration` at the new
  `ExternRefSite::HandleDeclaration` — R1–R6 with R4 HARDENED to a far
  DEFINITION that is not an `AvailableExternally` copy (new
  `ImportVerificationError::FarSiteIsAvailableExternallyCopy`), or a far
  declaration the dependency's OWN linked verdict authenticated (so a chain of
  entity-only re-declarations must bottom out in a checked definition; the
  generic `resolve_extern_ref` refuses every far declaration at this site).
  The outcome is recorded in `AuthenticatedImports`
  (`authenticated_handle_declarations()`), and rule 6 admits exactly those
  declarations under the linked walk. `validate_module`, the authority tier
  and plain codegen keep refusing (fail closed); a consumer that compiles such
  a root uses `validate_linked_module_with_config` with `codegen` set.
  `ValidationError::HandleForeignDeclaration` gains a `detail` field that
  names the applicable case: no `backed_by` (the fix is named), a
  `backed_by` outside the linked walk, or the L11 refusal. Tests:
  `handle_types` (gate 9) `ws3_3_*` (positive pair, negative twin in
  `validate_module` / the authority tier / codegen, the unbound mutation
  control, and controls for a bare far declaration, a skewed signature, a
  recompiled dependency, a producer mismatch, a pinned symbol, chain
  laundering and an `AvailableExternally` copy) and `verify_import`
  (the hardened R4). Ratchets flipped: `verify.c11` (3) in
  `c11_nat_handle_limits` and
  `b5.gap.cross_crate_user_fn_over_nat_is_foreign_declaration` (GAP -> PASS,
  with a twin row asserting the single-module refusal). Residual, fail closed:
  the text codec drops `summary` (F-064), so such a root cannot travel through
  text; trust-cg admits a handle `Call` only to a pinned declaration or a local
  definition until WS7 lowers an import-backed one.

- **L11 shadow rule: an import-backed handle declaration's body must be the
  only one a direct import exports (roadmap WS3.3 review).** A re-declaration
  is not an exporter, so when the root bound `dep_double` through a chain
  (`mid` re-declares, `leaf` defines) the call-edge ambiguity rule could not
  see a DIRECT import `rogue` that also defined `dep_double` — at any
  signature, never checked against the root's declaration — and L11
  authenticated the binding. L11 now records, per authenticated handle
  declaration, the module its binding bottoms out in, and refuses the
  declaration (`HandleForeignDeclaration`, detail "is also exported by import
  #N") when the single direct exporter of the symbol is a different module;
  the honest diamond (the root also imports `leaf`) still links. Review tests
  (gate 9, `handle_types`): the shadowed chain and its diamond control, a
  binding naming another link symbol, an `ExternalWeak` local declaration, a
  `Weak` far definition, and a dangling binding.
- **WS2.22 (F-056(b), the review half): an enum tag lane's SIZE and its
  ALIGNMENT are two facts, and only the size is target-free.** A declared
  `EnumLayoutDescriptor` places a `Direct` tag or a `Niche` lane at a byte
  offset, and three engines judge that placement. The validator and the layout
  authority (`shape`) read the lane's alignment off its byte COUNT
  (`tag_offset % tag_size`, `tag_size > layout.align`), while the reference
  interpreter ASKED the target (`byte_align_in`). Reusing the size is a guess:
  the i386 System V ABI aligns `i64` to 4, and rustc aligns `i128` to 16 on
  x86_64/aarch64 while other data layouts use 8 — which is why the 128-bit tag
  reprs could not be added until the alignment came from the target. The two
  facts are now split: `EnumTagRepr::size_bytes` is the repr's own width
  (replacing two private `enum_tag_repr_bytes` helpers), and
  `Module::enum_tag_repr_align` asks the layout authority for the lane type's
  alignment on the module's target. On a pinned target outside the canonical
  scalar table the answer is refused instead of guessed: the validator names
  it `ValidationError::EnumTagTargetScalarLayoutUnavailable` (the enum sibling
  of the struct rule's `TargetScalarLayoutUnavailable`, one per enum, for a
  lane that exists — an `Untagged` descriptor asks nothing) and `shape`
  propagates `LayoutError::TargetScalarLayoutUnavailable`, so all three
  engines now take the alignment from the same place. Review: the authority's
  descriptor-LESS canonical enum layout had made the same guess — its
  alignment was `max(tag SIZE, payload align)` where the interpreter's is
  `max(tag ALIGN, payload align)` — so a fieldless enum with no descriptor on
  i686, having no field to draw the scalar-table refusal, laid out with an
  alignment read off its tag's width, and a declared struct holding it
  validated there; both now ask and are refused by name. The ask is scoped to
  the lane that EXISTS, the same `lane_repr` in both engines — the canonical
  tag when no descriptor is declared, the placed tag under `Direct`, the niche
  type under `Niche`, nothing under `Untagged` — so a tag-free image lays out
  where the validator accepts it and a struct holding one is not refused for
  the alignment of a tag it does not store. On every target TrustIR
  tabulates, every repr spellable today is naturally aligned, so no accepted
  module changes verdict. Gate-9 test `enum_tag_lane_alignment`: positive
  fixture (`u32 @ 4` validates and lays out target-free, on x86_64 and on
  wasm32; `riscv64`/`aarch64`/`wasm64` are the struct rule's table, `riscv32`
  / `aarch64_be` / `avr` are not), the negative twin (the same descriptor on
  i686 refused by name at both engines, even at offset 0; a forged `x86_64`
  with 32-bit pointers likewise, naming the forged triple), the
  descriptor-less twin and its struct-field sibling, the `Untagged` twin laid
  out by both engines off the table, a `Direct` descriptor with no canonical
  tag refused for the missing tag and never for the lane, and mutation
  controls (same offset, two lane widths, two verdicts; over-alignment and
  overrun stay separate clauses for the direct tag and for the niche lane;
  the canonical alignment is the max of tag and payload alignment). No wire
  change; goldens unchanged. The wire batch —
  `EnumTagRepr::{I128, U128}` (`fits` over `0..=i128::MAX` for `U128`, the
  64-bit cap kept for `smallest_for` inference, the projection error, the
  Lean constructors) — is owned by WS3.14(b) at its WS8.5-reserved version,
  and row `producer-rust-thir/enum-repr-128` stays a GAP ratchet until it
  lands.
- **Per-argument and return-slot ABI facts (wire v45, roadmap WS3.11,
  F-054).** `ParamAttrs` gains `ext: ArgExt` (`None` / `ZeroExt` / `SignExt`,
  flag bits 5 and 6) and `pass: Option<PassMode>` (`Ignore`, `Direct`,
  `Pair`, `Cast { pieces }`, `Indirect { on_stack }`), and `FuncAttrs` gains
  `ret: ParamAttrs` — the RETURN slot, which did not exist before, so a
  `u8`-returning C declaration could not say `zeroext` and a returned
  aggregate could not say how it comes back. Names and variants are the v2
  `FnAbiDescriptor` subset verbatim, so that descriptor extends rather than
  renames them. `None` is UNRECORDED on both, never "no extension needed" or
  "Direct": a consumer that needs a classification still refuses.
  `validate_module` checks PLACEMENT (`InvalidAbiSlotFact`): an extension
  only on a sub-64-bit integer / `Bool` / `Char` slot, `Pair` only on a
  two-scalar-lane aggregate or fat pointer, `Cast` lanes closed scalars that
  cover the slot, `Indirect` only on an aggregate or the `byval`/`sret`
  pointer standing for one, `Ignore` only on a zero-sized slot, `byval`/`sret`
  in agreement with the pass mode, and no fact on a slot the signature does
  not have. Review: `Indirect` in its BY-VALUE spelling (the aggregate in the
  signature, no `byval` — what rustc's `FnAbi` stamps for `fn(Big)` and
  `fn() -> Big`) was unreachable, because the rule demanded `byval` on the
  parameter (v20 admits it only on a pointer slot) and an `sret` parameter
  for the return slot (v20 admits it only with an empty return list); both
  now validate and round-trip, the pre-lowered `byval` pointer still does,
  and `indirect` on a scalar is still refused. The return slot refuses the
  parameter-only `byval` / `sret` / `readonly` and `indirect(true)`
  (`on_stack`); `Pair` counts ABI LANES (non-zero-sized scalar fields), so
  `struct { u64, (), u64 }` is a pair and `struct { u64, () }` is not; a
  `cast` lane of `()` has no width and is refused. Second review: `Pair` on
  an ENUM was refused outright, but rustc's `FnAbi` stamps `Pair` on every
  `ScalarPair` argument and `Option<u64>` / `Result<u32, u32>` (tag lane +
  one payload lane) and the niche-encoded `Option<(&T, u8)>` (the dataful
  variant's two lanes) ARE `ScalarPair` — so every FnAbi-stamped enum
  argument was a legitimate module wrongly refused. Lanes are now counted
  under the enum's tag encoding (`Untagged`: the sole variant; `Niche`: the
  dataful variant when every other variant has no lanes; `Direct` or no
  descriptor: one tag lane plus a payload of at most one lane) and through
  nested tuples / structs (`struct { (u32, u32) }` is a pair; arrays never
  are), depth-bounded. A tag beside a two-lane payload, a fieldless enum,
  and three lanes through nesting stay refused. The text reader now refuses
  a slot line that RESTATES an extension or a pass mode (`zeroext signext`,
  `pass=pair pass=direct`) and a second `#ret_attrs:` line — the binary
  reader already refused both extension bits, and the text form let the
  later token win. Whether a claim is the one the target's classifier would
  make stays trust-cg's cross-check. Wire-checklist item 7 lands with it:
  `read_param_attrs` now REFUSES a flag bit that is not allocated at the
  blob's version (and refuses both extension bits at once) instead of
  silently dropping it. Text: `zeroext` / `signext` / `pass=<mode>` on
  `; #param_attrs N:` plus a new `; #ret_attrs:` line. Serde: `sret` and
  `target_features` are now always emitted, with `pass` and `ret` the sole
  trailing skips. `ParamAttrs` is no longer `Copy` (`Cast` carries lane
  types). `signatures_compatible` (import resolution, rule R6) now compares
  `ext` and `pass` on every parameter and on the return slot beside
  `byval`/`sret` — an unrecorded fact against a recorded one is a
  disagreement, never a wildcard — and the semantic diff reports a slot fact
  change as an `attrs` change, never as cosmetic. The randomized
  round-trip fuzzer decorates ~1-in-3 functions with admissible slot facts
  and asserts the text round-trip keeps them injectively. New golden
  `abi_param_facts` (every `PassMode` tag); ratchets
  `b6.abi.no_zeroext_signext_slot` and `b6.abi.no_pass_mode_slot` flipped
  GAP -> PASS.

- **128-bit enum tag lanes (wire v45, roadmap WS3.14(b) / WS2.22, F-056).**
  `EnumTagRepr` gains `U128` (wire tag 9) and `I128` (tag 10), read-gated
  `version >= 45`, so a `#[repr(u128)]` / `#[repr(i128)]` enum stops being
  unrepresentable. `U128` spells only `0..=i128::MAX` (a discriminant is an
  `i128`; a larger value is refused, never truncated) and `smallest_for`
  keeps the 64-bit cap, so only an explicit repr hint selects a 128-bit lane
  and no existing module moves. The validator and `shape` now SPLIT the tag
  lane's size from its alignment: 16 bytes wide, with the alignment read from
  the target scalar table (`Module::ty_layout_shape`) — rustc aligns `i128`
  to 16 on x86_64/aarch64 while other data layouts use 8 — and a target with
  no canonical scalar table refuses the descriptor instead of guessing. The
  Lean `EnumTagRepr` mirror moves with it, and `lean_schema_parity` gains an
  `EnumTagRepr` axis (with a mutation control) that would have caught the
  drift. New golden `abi_enum_tag_repr`; `producer-rust-thir/enum-repr-128`
  ported as a test, with a v44-reader `InvalidTag(9)` twin and a
  tag-at-offset-8 mutation control.

- **Seven foreign calling conventions (wire v45, roadmap WS3.12, F-059).**
  `CallingConv` gains `CUnwind`, `SysV64`, `Win64`, `Aapcs`, `EfiApi`,
  `VectorCall` and `RustCold` (wire tags 5..=11, read-gated `version >= 45`),
  so `extern "C-unwind"`, `extern "win64"` and the rest stop collapsing to
  `C`. There is deliberately NO `Other(String)` escape: it would break `Copy`,
  and an ABI this enum cannot name must be a producer refusal rather than a
  string a consumer lowers as `C`. Under the ratified panic=abort policy
  `CUnwind` is RECORDED, not given unwind semantics. Text keywords
  `c_unwindcc` / `sysv64cc` / `win64cc` / `aapcscc` / `efiapicc` /
  `vectorcallcc` / `rust_coldcc`, printed and parsed through one
  `CallingConv::ALL` table — the module-level "is this a function?" prefix
  test is now derived from it, so a new convention can no longer be silently
  dropped by the text parser. The Lean `CallingConv` mirror and the
  `core_reflection` code (the wire tag) move with it. New golden
  `abi_calling_conv`; `goal-g1-g8/g1-calling-conventions` ported as a test,
  with a v44-reader `InvalidTag` twin and a pinned-handle-entry-point
  `CUnwind` refusal.

- **Functions carry visibility, section and retention (wire v45, roadmap
  WS3.10, F-053).** `Function` gains `Global`'s v41 symbol triple:
  `section: Option<String>`, `visibility: Visibility` and `retained: bool`.
  Rust's default for a non-exported cross-CGU function, `(External, Hidden)`,
  finally has a spelling, so a consumer can read a function symbol's export
  surface from the module alone. Binary: appended to the function record after
  `display_path`, read-gated `version >= 45` (reserved `79783f80`); the writer
  selects v45 only when a function uses one, and `RawV38`/`CanonicalV38`
  refuse with the new `AbiSurfaceRequiresV45`. Text: `; #section: "<escaped>"`
  (the `#display-path` quoting, injective for `"`, `\`, `;` and newlines),
  `; #visibility: hidden|protected`, `; #retained: true` — all three in the
  WS4.2 directive table, so a text that spells one parses it or is refused;
  each is stated at most once (a second `#visibility:` / `#retained:` line is
  refused, not read as a correction — review). Every v45 fact (the symbol
  triple, the calling convention, each slot fact) moves both
  `stable_digest` and `executable_content_digest_v1`, pinned by a review
  test so a codegen license earned by one ABI image can never stand for
  another.
  Serde: `display_path` is
  now always emitted and `retained` is `Function`'s sole trailing skipped
  field, so every JSON / MessagePack golden gained the always-emitted keys
  (no binary golden changed). The semantic diff reports all three.
  `validate_module` refuses `Hidden`/`Protected` with `Internal`/`Private`
  linkage (`ContradictoryFunctionVisibility`), a blank or NUL section
  (`InvalidFunctionSection`), and a pinned handle entry point that is not
  `Default` or carries a section (`HandleEntryPointSignatureMismatch`). New
  golden `abi_function_symbol`; `tests/abi_surface.rs` (gate 8) and a
  back-compat test that the `>= 45` gate is load-bearing both ways; the
  round-trip fuzzer now draws symbol attributes, hostile section strings
  included. Ratchet `b6.abi.no_function_visibility_slot` flipped GAP -> PASS.
- **WS3.13: first-class closure application is ratified BY VALUE, and capture
  mode is the capture slot's type (F-055, part).** G18-2 made `Ty::Closure`
  eliminable and stated the spread ABI (captures supplied as leading
  arguments), but never said what that implies for a `Fn`/`FnMut` closure
  whose state must persist across calls. It is now ruled, in
  `lowering-target-subset.md` §G18-2: application is `FnOnce`-shaped — the
  captures are ARGUMENTS, so a body's write to a capture reaches neither the
  caller's closure value nor a later application — and a BY-REFERENCE capture
  is a capture SLOT WHOSE TYPE IS A POINTER, so capture mode needs no new
  `ClosureTy` field. By-reference APPLICATION is not expressible and is not
  assumed: a `Ty::Closure` value is an SSA register with no address, a
  `Borrow` result is a thin `Ptr`, and making it coherent would need a new
  call-through-pointer form (a coordinated triple), which is left as a
  decision gate. A stateful `Fn`/`FnMut` uses the spelling the codegen refusal
  already prescribes — an environment aggregate in memory plus a `Ty::Func`
  taking the environment pointer — which validates, lowers and persists today.
  The producer that instead emits a first-class closure for
  `FnMut`-with-state gets by-value semantics; the ruling makes that the
  producer's error. No wire change and no validator change: the
  `UnlowerableForCodegen` refusal for a `Ty::Closure` callee is unchanged, and
  lifting it needs the declared closure-layout table (`Module.closure_layouts`,
  the wire half of WS3.13, not in this change). Tests: the new
  `trust-ir-build` `closure_application_by_value` (gate 9) builds ONE source
  program — a counter bumped twice, reported as `first * 10 + second` — in
  three spellings, so the returned number reads the capture discipline off
  directly: the env-pointer spelling returns `12` and is lowerable (positive
  fixture); the by-value capture returns `11` and is refused twice by the
  named reason (negative twin); the pointer-typed capture returns `12` and is
  still refused (the by-reference mode, with no new field). Mutation controls:
  removing one application removes exactly one refusal, so closure
  INTRODUCTION and capture PROJECTION are not over-refused; the env-pointer
  fixture applies a `Ty::Func` value through the same `CallIndirect` twice and
  is not refused at all; and the closure literal's physical signature is
  checked to be `captures ++ apparent`. Review pinned more shapes: the
  ruling and the refusal hold for every ROUTE a closure value takes to the
  application site (function parameter, `Call` result, `Select`+`Copy`,
  loop-carried block parameter, `ExtractField` out of a tuple — one refusal
  per STATIC site, sited in the applying function); a `Select`ed/`Copy`ed
  `Ty::Func` callee is not refused; a closure round-tripped through memory
  (an `Alloca`, or a global's initializer) is still refused for application
  and fails closed in the interpreter (`has no byte layout`); every cast
  LAUNDERING of a closure into a `Ptr`/integer callee (`Bitcast`,
  `Transmute`, `PtrToPtr`) is refused structurally (`CastLayoutUnsupported`,
  the same absent layout); and a callee TYPED `RefMut(Closure)` — the draft's
  by-reference spelling — is never a closure application (no closure refusal,
  and refused at run time as a non-function type). The ratification text was
  corrected accordingly: such a callee CAN be declared, it just is not one.
  Review also RECORDED (pinned, not fixed — outside F-055) that
  `validate_module` has no callee-type rule for a `CallIndirect` outside the
  nominal-type path: a `U64`-typed callee is structurally admitted and not
  refused for codegen; only the reference interpreter refuses it.
- **One artifact, one name across the import table; the identity, visibility,
  taint and vocabulary decisions are written down (roadmap WS1.16, F-077,
  F-084, F-027, F-085, F-026).** `trust_ir_build::validate_module` refuses two
  `Module::imports` rows that carry the same digest under different names as
  the new `ValidationError::ImportIdentityConflict`, in every tier; the
  ratified two-producer shape (same digest, same name) still validates. A unit
  tripwire (`f084_tripwire_a_domain_bump_is_a_new_identity_scheme`) pins each
  scheme's domain literal, so a module-identity domain cannot move without a
  new `IdentityScheme` variant carrying it.
  The ratchet row `b4.gap.no_proof_only_marker` moves GAP → RATIFIED-OUT as a
  named non-task (compiler-side erasure; the trigger is a cross-crate
  white-box proof). An internal spec ratification (§12) records the deferred
  F-027 / F-085 / F-026 decisions and their triggers. No wire change.
- **The Lean library envelope's facts have in-format homes, and a conformance
  fixture pins them (roadmap WS4.15).** The standalone Lean lane emits a
  `trust.lean.ir-library/v1` JSON envelope whose gate facts (per-body kernel
  payload and subject digests, carrier, method, kernel-only theorems) lived
  only on the envelope side. A new internal spec ratification (§9) rules that
  trust-ir gains NO envelope-shaped carrier: the envelope is a sidecar and not
  identity, and every load-bearing fact maps onto an existing or WS1-planned
  carrier. A body becomes a `Gated{"clean-kernel-tv"}` function with a
  function-scoped `Certified` `TranslationValidation` obligation and a
  kernel-re-checked `CleanCic` certificate. Carrier and method become that
  obligation's lineage-bound formula (`clean.tv-binding/v1`). A kernel-only
  theorem becomes a `Custom{"trust.proof_item", ..}` obligation whose formula
  is a `clean.theorem-ref/v1` REFERENCE, never the statement. The source
  closure digest waits for F-008's source-definition digest (WS1.12). The new
  corpus fixture `lean_library_envelope` (binary / JSON / MessagePack goldens,
  written at v41; no existing golden changed) validates under
  `validate_module_with_authority` and the codegen gate, and re-certifies after
  each lossless transport. Gate-8 tests pin that result, that the same
  certificate refuses a miscompiled body, and that the reference carriers grant
  no authority (a TV certificate re-minted for the theorem reference is
  refused by the anchor-to-kind guard; a proof term for another body, an
  unscoped TV row and a second body's miscompile are refused; a multi-body
  envelope certifies). Seven `b3.envelope.*` rows join the ratchet ledger: two
  PASS rows and five GAP rows, which flip with F-008, F-006 (the TV row
  dropped, or kept as `Failed`) and the two text-codec findings (F-071, then
  F-070). No wire change.

- **WS1.10: a `Linked` spec module's surface fails closed (F-014).**
  `SpecVar.ty` and `SpecInvariant.formula` are strings on the wire, and under
  `SpecEnforcementMode::Linked` — a certification claim — nothing read them:
  garbage syntax, an undeclared variable and an ill-sorted comparison validated
  and certified like a meaningful invariant. Under `Linked` only, the new
  `trust_ir::spec_surface` reads both. A variable type must be `Bool`, `Int`,
  `BitVec(<w>)` or `<lo>..<hi>`, and a variable name an unprimed SMT simple
  symbol that does not shadow a surface operator. An invariant must be one quantifier-free SMT-LIB2 term of sort
  `Bool`, read with the WS1.1 clause reader (`smt_free_symbols`) and then
  sort-checked over the core, integer and bit-vector operators. Every free
  symbol must be a declared variable, and a primed `x'` is refused because
  primes belong to actions. The surface is the SMT-LIB2 subset `ProofFormula`
  shares (DECIDE option A); a `Linked` module written in TLA+ surface syntax is
  now refused. The rule is the new S3 obligation
  (`trust_ir::validate_linked_spec_surface`, `SpecLinkViolation::
  LinkedFormulaUnparsed` / `LinkedVariableUnparsed`). It runs in
  `link_spec_modules`, so `trust-ir spec-link` cannot certify an unreadable
  invariant, and in `validate_module` as the named refusals
  `ValidationError::SpecLinkedFormulaUnparsed { module, invariant, detail }` and
  `SpecLinkedVariableUnparsed { module, variable, detail }`. `DesignOnly` is
  untouched. No wire change. Tests: `trust-ir-build`'s `spec_linked_formula`
  (gate 9, with `spec_module_semantics` and `spec_anchor_function` now
  registered) holds the positive fixture: an embedded `Linked` machine with a
  typed anchor, a `(&T) -> R` projection and a manifest-resolved proof
  validates and links as certifying (`crit.unex07`). It also holds the
  garbage, undeclared-variable and ill-typed twins, each refused by name, and
  the `DesignOnly` mutation control. `trust-ir-cli`'s `cli_spec_link` runs the
  same fixture through the binary (`spec-link-status: certifying`) with its
  twins exiting 1 on `[S3 linked-surface]`. The Linked fixtures that used TLA+
  text (`seq <= 7`) now carry SMT-LIB2 (`(<= seq 7)`). Review hardening: a
  formula nesting deeper than 256 levels is refused (it used to abort the
  validating process with a stack overflow), as is any character outside
  printable ASCII and SMT-LIB2 whitespace (a no-break space or vertical tab
  was admitted as a separator no SMT-LIB2 reader splits on); a variable may
  not take the name of any `Core`/`Ints`/`FixedSizeBitVectors` function symbol
  (`concat`, `bvcomp`, … — undeclarable downstream); and an `<lo>..<hi>` range
  is compared as unbounded decimals, so a bound beyond `i128` is admitted.
- **WS2.18 — the Lean mirror closes `FatPtrKind`, `Constant` and `Inst`
  fields, and the parity gate checks all three.** Name parity was "all three
  allowlists empty" while a fourth axis (`FatPtrKind`) carried
  `ContainerLen`/`ContainerVtable` as debt, `Constant` had no axis at all (the
  Lean `Constant` lacked `U128`, `Bytes`, `Array`, `FnDef`, `SymbolAddr`,
  `PhantomData`, so no Lean statement about a string literal, a vtable or a
  fn-pointer table was expressible), and nothing compared FIELDS
  (`Switch.exhaustive_enum_unreachable` and the indirect-call convention had
  no Lean binder). Lean: both container-tail kinds, classified by what their
  metadata means (`ContainerLen` on the `U64` length lane, `ContainerVtable`
  on the `Ptr` vtable lane, never a length); the six constants, with
  `Value.ofConstant` arms mirroring the interpreter's `constant_to_value`;
  a link-time `symbolAddr` has no compile-time value and is refused
  fail-closed at the `Const` step, the global-initializer path and a
  `Switch` case the in-order scan reaches (`unsupported.link_time_address`,
  any nesting depth; theorem `const_symbolAddr_refused`), and a canonical
  `u128` switch case is matched by a width-128 scrutinee exactly as the
  interpreter compares it (review fix: the Lean scan used to skip the first
  and miss the second, running a different block than the interpreter);
  container-tail fat pointers are pinned through Store/Load too; `Alloca`/`HeapAlloc` `align`,
  `Switch.exhaustiveEnumUnreachable` and `CallIndirect.callingConv` (a new
  `CallingConv` mirror) as binders, carried without changing evaluation,
  exactly as the reference interpreter does. `const_always_succeeds` now
  states its one precondition (no `symbolAddr`). Gate 1
  (`lean_schema_parity`): empty `FatPtrKind` allowlist, a new `Constant`
  axis and a new field-level `Inst` axis (in-order binder comparison through
  an explicit name map; both parsers fail loudly, naming the variant), all
  with empty allowlists, plus mutation controls (removing `Constant.bytes`
  from Lean, adding a Rust `Inst` field without a binder, reordering fields,
  dropping the `Switch` binder) and the ratchet rows
  `trust_ir_self_declared_lean_mirror_name_debt` and
  `small_designs_omet_13_lean_schema_parity_field_half`. Lean + test only: no
  wire change, every golden byte-identical, `lake build` green with the
  axiom audit extended. Closes F-043 (the OMET-13 extern-semantics half is
  not this increment).
- **Wire v44: portable module identity and the `ModuleImport.scheme`
  discriminator (WS4.10).** `Module::stable_digest` is now the V3 identity
  (`trust_ir.module.v3`): the canonical encoding with every `Module.files`
  path string projected to `""` (table length kept, so span indices, lines and
  columns stay identity). A crate compiled from two checkout paths — which
  differ only in that debug path — is one module, so a dependency built on one
  machine authenticates on another. The legacy V2 identity
  (`trust_ir.module.v2`, `MODULE_IDENTITY_DOMAIN_V2`) stays computable through
  the new `Module::stable_digest_under(IdentityScheme)`, and every import row
  now names the scheme its digest was recorded under (`ModuleImport.scheme`,
  one tag byte per row, read-gated `version >= 44`; `ModuleImport::new`
  records V3, `with_scheme` spells another). The verifier hashes the candidate
  under the ROW's scheme, so every pre-v44 row (decoded as V2) keeps
  authenticating exactly what it did. The writer selects v44 only when a row
  is not V2; `RawV38`/`CanonicalV38` refuse with `ImportSchemeRequiresV44`.
  `HashedModule` caches each scheme lazily (`digest_under`), `ModuleSet` keys
  on every scheme, and the linked walk memoizes by `(scheme, digest)`. Text
  spells ` scheme v3` (V2 by omission); serde always emits `producer` and
  skips a V2 `scheme`. `trust-ir digest` prints the legacy digest too and
  gains `--portable-check [--remap-prefix P]…`, refusing a debug file table
  that embeds a non-remapped absolute path (named by JSON pointer).
  **Consumers:** every value minted from `stable_digest` moves — a
  `NativeVerificationBundle` / lineage / table-transform / source-provenance
  record minted under V2 fails closed and must be re-minted (the bundle
  identity-contract census now names `trust_ir.module.v3`); the source
  provenance seal moved to `trust_ir.source_provenance.semantic_function.v2`.
  `executable_content_digest_v1` is unchanged and keeps the debug paths. A
  conformance tripwire (`module_files_strings_are_debug_only`) fails the build
  if a validator rule or digest projection starts reading a `files` string.
  New `import_scheme` golden (the only v44 header); the native request bundle
  golden is re-minted (its module digest is the only delta). Review
  hardening: a text import entry must end after its clauses (an unknown token
  such as `producer trust junk scheme v3` used to be skipped with the rest of
  the line, silently reading a V3 row as V2), the scheme label is a delimited
  token (`v3x` is refused), and `--remap-prefix` covers a path by component
  (`/rustc` no longer covers `/rustc-evil/…`, and a `..` component climbing out
  of the prefix is refused).
- **WS5.4: a sited `Inst::Assert` is a recognised assert shape, and the
  discharge loop has a trust-ir end (F-091; F-022 producer half is ~/trust).**
  Every direct-lane obligation is sited on an `Inst::Assert`, and every one
  died on "Assert, not a CondBr" — 0 of 10 real obligations could reach a
  verdict. `trust_ir::proof::lowered_assert_condition` now reads
  `Inst::Assert { cond }` as `(cond, true)`: the ratified proof-carrying
  instruction states its own obligation, with no polarity to infer. The
  bit-blast goal language admits the direct lane's spelling — `add.overflow` /
  `sub.overflow` (value and flag, per signedness; `MulOverflow` stays refused
  as `Mul` is) and `select` — using only existing nodes, pinned by an
  exhaustive width-8 comparison against Rust's `overflowing_*`. Guards, each
  with a named refusal: (1a) one constant, `ASSERT_CLASS_OBLIGATION_KINDS`
  (`BoundsCheck`, `ArithmeticSafety`), gates every route — a `Postcondition` or
  `LoopInvariant` sited on a provable assert is `Unsupported` ("is not an
  assert-class obligation") on the SMT sited VC, never certified on the
  bit-blast route, refused by `BvBlastAuthority`, and refused by
  `derive_site_goal` itself (`GoalDeriveError::KindNotAssertClass`); sited-VC
  conditions now back only the row they were generated for. (1b) A discharge
  route never overwrites a producer formula: a formula-bearing row discharges
  only when `formula_binds_site_goal` holds (the bit-blast claim, or
  `formula_matches_goal` — canonical SMT-LIB2 rendering equality with the
  re-derived goal, `bindings` naming exactly its leaves at their widths);
  otherwise it stays Pending, byte-identical, with "producer formula disagrees
  with the site goal", on the bit-blast route, at authority replay, and on the
  SMT route (which previously refused every formula-bearing row). (2) A
  single-block body whose whole-function walk refuses (`UnsupportedOp` /
  `UnsupportedType`) falls back to the sited VC, keeping the refusal in
  `FunctionVc::whole_function_fallback`; `FunctionVc::all_proved()` is
  `false` for such a fallback, so a refused walk never reads as a vacuous
  pass over the unsited asserts it dropped. (3) A block parameter with no solver
  sort (a fat slice) is left undeclared, so only a condition that reads it is
  Unsupported. A sited refutation is reported "not provable locally" and never
  mints `Failed`. (5) `trust-ir discharge --bvblast IN OUT` (feature `ay`)
  runs the route, validates under `BvBlastAuthority`, and writes a separate
  artifact, never over its input. Measured: the vendored real p01/p04/p05
  modules now reach real verdicts on all 8 rows and discharge 0 of them — each
  needs a hypothesis (caller precondition, dominating branch, callee result)
  a block-local goal does not have; the `>0` ratchet is the ~/trust Part A row.
  Tests: `trust-ir-ay` `ws5_4_discharge_loop` (gate 9 registry), `trust-ir-cli`
  `cli_discharge` (`--features ay`, self-verify ay lane).
- **WS2.12: the reference interpreter's host-call hook; a bodyless declaration
  is `UnsupportedCall`, never `MissingBlock`** (closes the hook half of F-035).
  A call to a bodyless declaration used to ENTER it and trap `MissingBlock
  "block 0 not found"` — a structural code on IR the validator accepts, which
  `interpret_differential`'s property 2 forbids. Now `Interpreter::with_host(&dyn
  HostCalls)` installs a host model; without one, or when it returns `None`,
  the call is `UnsupportedCall "call to bodyless declaration @name: no host
  model (declarations are not executable in-format)"` (a bodyless ENTRY point
  too). A host's results are checked against the declared return types
  (`SignatureMismatch`) and must inhabit them (a `TypeError` otherwise; pointer
  and aggregate results are refused, since a host has no interpreter memory).
  Runtime handles get a value kind, `InterpretValueKind::Handle { id }`, typed
  at the exact `Ty::Handle` it was minted at: transport-only (copy, select,
  branch, call, return), a `TypeError` anywhere else (a binding-frame
  `BindSlot` and the identity `Bitcast` included), never stored. The
  per-execution `HostState` mints ids from ONE counter shared by every model and
  records each id's `HandleTy` and owner, so a handle of one runtime reaching
  another runtime's entry point is `UndefinedBehavior "handle of runtime R1
  passed to R2"`, as are a foreign model's handle, an unminted id, a relabelled
  type and a use after release; an entry argument AT a handle type is refused
  whatever its payload, since no handle exists before a run. A host's `char`
  result must be a Unicode scalar value, and an error a host returns is
  re-worded `host model for @name: ...` so a host's `UndefinedBehavior` is never
  read as the module's own. `InterpretOutcome` gains `host_calls` (counted by
  the interpreter): a run with `host_calls > 0` is HOST-ASSISTED and is not
  in-format execution evidence — host models are trusted-base rows (TRUST.md
  item 9; labelling them is WS2.13), and `bridge.rs` keeps `Ty::Handle` outside
  the proven subset. **API break (intended):** `InterpretOutcome` has a new
  public field, so external struct literals of it stop compiling.
  `Interpreter`'s `Debug` is now hand-written. No wire change. Tests:
  `interpret_host_calls` (gate 8: positive, the no-host and wrong-type twins,
  declining host, cross-model confusion, transport-set mutation controls, a
  validated Nat program under a test model, and the ported proof-program row
  `b7.nondet.extern_nondet_call_is_unexecutable`, whose shape flips from the
  structural `MissingBlock` trap to `UnsupportedCall`, fail-closed and named),
  plus a bodyless-callee corpus in `interpret_differential` checked with and
  without a host. The two-language ratchet ledger (`RATCHETS.tsv`) moves with
  it: `b4.link_and_interpret.negative_twin.root_alone` stays PASS, now pinned to
  the `UnsupportedCall` naming `@dep_scale`; `b7.nondet.extern_nondet_call_is_unexecutable`
  and `b5.gap.reference_interpreter_cannot_execute_handle_program` stay GAP
  (F-034 has no nondeterministic-choice carrier yet, and F-035's Nat host model
  is WS2.13), re-pinned to the exact `UnsupportedCall` payload so neither can
  drift silently. `trust-ir run` (WS4.6's linker, which read the old
  `MissingBlock` at a reserved entry id to name a pinned trusted-runtime entry
  point) now reads the new, structured `InterpretError::unhosted_callee()` —
  the one parser of that message, owned by `interpret.rs` — and prints the same
  named refusal only for a name its synthesis pass recorded as pinned; `run`
  installs no host model, so `b5.gap.cli_run_cannot_execute_handle_program`
  stays GAP in its exact shape (the Nat model is WS2.13).
- **WS3.21 (F-061): the Clean RC runtime is a pinned table, not a
  convention.** `Retain` / `Release` / `IsUnique` carry only a pointer, and
  trust-cg routed them to Clean's runtime by the mere presence of a bodyless
  `clean_inc` / `clean_dec` / `clean_is_exclusive` triple — so a module could
  declare `clean_dec(Ptr) -> I32`, define `clean_inc` locally, bind the name
  to a global, or reach the runtime through a `SymbolAddr` at a forged
  signature, and every one validated `[]`. `trust-ir-build` now owns
  `TRUSTED_RC_RUNTIMES` (re-exported with `RcRuntimePin`, `RcEntryPoint`,
  `rc_entry_for_symbol`): the row `(AllocOrigin::CleanHeap, "clean_runtime")`
  pins `clean_inc(Ptr) -> ()`, `clean_dec(Ptr) -> ()` and
  `clean_is_exclusive(Ptr) -> (U8)`, C calling convention, each tagged with
  the ARC role it implements so a backend reads its routing from the table.
  The pinned namespace is guarded on every module in all three spellings of a
  link-time symbol, the v43 handle-guard shape, with four new named refusals:
  `RcEntryPointSignatureMismatch`, `RcEntryPointDefinedLocally`,
  `RcEntryPointShadowedByGlobal`, `RcEntryPointAddressTaken`. The pinned
  declaration may also carry no claim about the runtime's effects (review):
  `readnone` / `readonly`, a parameter attribute or `Pure` is a signature
  mismatch, because the WS2.7 attribute check admits a callee carrying its
  caller's own claim — a `readnone` `clean_dec` otherwise laundered a false
  `readnone` onto a defined caller that frees a Clean cell. Ratified with it:
  ownership transfer between `RustHeap` and `CleanHeap` is NONE — a Clean
  object crossing into Rust stays Clean-owned and is released only through the
  pinned `clean_dec` (`TRUST.md` item 13, a new trusted-base row). Tests:
  `crates/trust-ir-build/tests/rc_runtime_pins.rs` (validator-fail-closed
  gate) plus `validate::rc_runtime_pin_tests`. Not closed here, stated: the
  rest of Clean's runtime ABI (`clean_alloc_ctor`, `clean_ctor_get`,
  `clean_box`, ...) stays convention, and Perceus reuse tokens are deferred.
  Validator-only: no wire change, `VERSION` is still 43, goldens are
  byte-identical. The Clean emitter already declares exactly the pinned shape;
  trust-cg's routing should read the table after its next pin bump.

- **The enforcement-link gate: a normative claim names its enforcement, and a
  machine checks that the name resolves.** First rung of moving in-text claims
  to mechanically verified proof, and it says so: it proves no claim, it makes
  an unbacked or rotted one a gate failure. `scripts/check_enforcement_links.py`
  (ci gate 0, toolchain-free) requires every section of the internal spec
  ratifications and every numbered trusted-base item of `TRUST.md` to carry an
  entry with an evidence CLASS — `kernel-certificate`, `lean-theorem`,
  `type-level`, `test`, then the three that are not checked evidence, `code`,
  `external`, `prose-only`. Every backticked token in an entry must RESOLVE (a
  cited test is a real `#[test]` fn in a workspace crate, a cited file exists),
  and the class must be WITNESSED by a citation of the matching kind, so a
  class cannot be raised by rewording. `scripts/gates/enforcement-ratchet.txt`
  lists BY NAME the units with no checked evidence and the `ValidationError`
  variants no test names or nothing constructs; the set only shrinks. Measured
  at landing, 2026-09-18: 20 units, 98 citations, 3 units without checked
  evidence; of 177 `ValidationError` variants, 9 are named by no test and one
  (`GroundCertificateStatusInconsistent`) is constructed by nothing. The
  backfill DOWNGRADED two ratifications whose entries named enforcement that
  was not there; one of them, the duplicate-link-symbol rule, then got the tests
  it had been credited with (`function_symbol_identity.rs`, whose refusal tests
  were seen to FAIL with the rule disabled), taking the ledger to 2 units and 7
  variants; and `TRUST.md` item 7 now records that lowering-resolution
  artifacts have stayed `Pending` since 2026-07-12, so the trust-ir → machine
  step is not kernel-certified at HEAD. No wire change: `VERSION` is still 43
  and every golden is byte-identical.
  *Corrected the day it was written, by an adversarial review that broke it by
  execution:* the ratchet refused an HONEST downgrade (relabelling one entry
  `(prose-only)` after reading its cited test turned gate 0 red, so the cheap
  ways back to green were the gaming ones), and a `not-normative` comment could
  retire a debt — the unit left both the count and the debt list, and the
  ledger recorded the "gain". The ledger now has CORRECTION rows, the one way a
  count rises (by one, with a reason, for a unit that existed with checked
  evidence at the merge-base); a unit that was normative at the merge-base
  cannot be marked not-normative; `check` prints every opt-out and correction;
  a gate NAME or a fixture no longer witnesses `(test)`, and a Cargo feature
  witnesses `(type-level)` only when the manifest shows it off by default —
  which turns the one live row that leaned on a feature's mere existence into
  a checked fact. The gate and its tests now also hold in the public snapshot,
  where the ratifications are absent by design (the shipped self-verify script
  had been broken by this gate's own test file).
- **Two ledgers, one counter: the wire-version lock was built twice the same
  day, and the two are now bound.** `wire-allocations.toml` (this series) and
  `crates/trust-ir/wire_versions.tsv` (roadmap WS8.5) each reserve a binary
  wire version by a pushed `reserved` row; neither line could see the other.
  Each is sound alone. Measured together on the merged tree: v44 given to two
  different owners, one per file, left every live check of both gates green
  (two pushes to different files are no conflict, and neither tool reads the
  other's file) — the race both exist to close, back. And one BY-THE-BOOK
  reservation turned BOTH gates red on their own protocol
  (`wire_version_ledger` 7 passed / 5 failed; this series' census 2 failed):
  fixtures that append a literal next-number row to the live file collide with
  the first real one. Now: both halves of the gate refuse any number the two
  files tell differently (a row in only one, a status told two ways, an open
  number with a different owner or constant); `wire_alloc.py reserve version`
  and `takeover` write both files and `wire_alloc.py sync` copies a
  reservation made in one; fixture baselines have open reservations cut out
  (in `binary.rs` at compile time, so no fixture was touched); and the
  `wire-version-ledger` gate, selected by name from a feature-gated module,
  must be seen to run (`0 passed` exited 0 with `--features binary` dropped).
  Re-measured with a real reservation in all three namespaces on the real
  files: every gate and suite green. Which ledger survives is left to the
  owner. No wire change: `VERSION` is still 43, goldens byte-identical; all of
  it executed tests on the `--unverified` lane, none of it a proof.
- **Wire allocation: the push is the lock.** "The next format version", "the
  next tag of a wire enum" and "the next `vN` of a digest domain" are linear
  counters, and a counter shared by parallel lines of work had no lock: it
  collided six times in one quarter (wire v26..=v28 — refused on read forever;
  v39 twice; v41; v42; `trust_ir.obligation.digest.v5`). `wire-allocations.toml`
  (repo root, shipped) is now the allocation registry — 43 format versions, 401
  tag bytes across 47 wire enums, 64 versioned identity strings, backfilled
  from the code — and a number is allocated by PUSHING a one-line reservation
  to `main` before work starts (`scripts/wire_alloc.py reserve …`); a refused
  non-fast-forward push means the number may be gone. The registry is
  load-bearing: `trust-ir`'s `binary::wire_census` tests (new ci gate 10) run
  every variant through the real writers and read the tag byte back, probe the
  real reader with every version header, and scan the sources for version
  constants and version-suffixed identity strings; a version, tag or identity
  without a row fails, and a reserved row with no code passes. No wire change:
  `VERSION` is still 43 and every golden is byte-identical.
  *Corrected the day it was written, by an adversarial review that broke it by
  execution:* the backfill had been made by reading the writers and missed a
  live tag space (`DiagnosticSeverity`; a wire-breaking re-tag of it passed
  every check), and the identity scanner matched one spelling and missed ten
  live names, the root separator of every `sha256_domain` digest among them.
  Which enums are tag spaces is now cross-checked by a scan of the codec source
  (refusal arms, writer arms, `tag_enum!` heads); the identity scan is
  closed-world and suffix-anchored, so a hyphen spelling or a `concat!`
  fragment is a finding; gate 10 requires the census tests to be SEEN to run
  (a name filter matching nothing exits 0 — measured with the hook line
  dropped); and the protocol now says what it costs: wire versions land in
  number order, `wire_alloc.py takeover` is the way through, and an abandoned
  reservation is deleted, never `burned`. All of it is executed tests and
  source scans on the `--unverified` lane: none of it is a proof.
- **Names, not numbers.** Test and fixture file names no longer spell a wire
  version, so a renumber stays a one-line change: goldens `body_gate_v41.*` →
  `body_gate.*` and `ty_handle_v43.*` → `ty_handle.*`; tests
  `v41_{body_gate,abi_residue,clause_bindings,cross_crate_identity,obligation_kinds}.rs`
  → `contract_surface_*.rs` (all `git mv`, 100% similarity; the two in-blob
  module-name strings are frozen golden content and unchanged). A new
  `names_not_numbers` conformance lint forbids new `vN` file names; existing
  ones are an explicit grandfather list, mechanically closed to any number
  above the v43 freeze (it was described as "shrink-only", which its test never
  established).
- **WS3.2: the pinned `Nat` row is the Clean kernel's native `Nat` surface
  (F-052).** `TRUSTED_HANDLE_RUNTIMES` pinned only `from_u64` / `add` / `sub`
  / `is_zero` / `drop`, so a Lean `Nat` using `*`, `/`, `%`, `decEq`, `<`,
  `toUInt64` or a copy of a handle had no carrier: every other declaration
  reaching a handle is `HandleForeignDeclaration`. The row gains fourteen
  roles — `mul`, `div`, `mod`, `beq`, `ble`, `fits_u64`, `to_u64`, `clone`,
  `land`, `lor`, `xor`, `shift_left`, `shift_right`, `pow`
  (`trust_bignum_nat_<role>`, C convention) — exactly the Clean kernel's
  closed `NAT_BINOPS` allowlist plus the projection and `clone`, each
  specified by the kernel reducer's semantics (`n / 0 = 0`, `n % 0 = n`). The
  projection is two pins, never a wrapping one: `fits_u64` is total and
  `to_u64` aborts when the value does not fit; Lean's `n.toUInt64` is spelled
  `to_u64(land(n, from_u64(u64::MAX)))`. `cmp`, `to_u64_wrapping`, `eq` and
  `lt` stay refused, and a Lean `Int` row stays deferred (F-129). The role is
  the Lean name and the `def_path` the Rust item the shim wraps (`mod` pins
  `trust_bignum::Nat::rem`). Validator-only: no wire change, goldens
  byte-identical (the `ty_handle` fixture declares only the roles it calls).
  Each new row is a trusted-base row (`TRUST.md` item 9); the shims, their
  `Nat` methods and the Lean-vs-kernel differential land in `trust-bignum`,
  and until they do a module calling one validates and fails to LINK. Tests:
  new `nat_kernel_surface` (gate 9) — per role the `b5_10` shape validates on
  the plain and codegen lanes and every role is callable; a wrong signature,
  a wrong def-path and each off-table spelling are exactly one named
  refusal; removing a role from the row refuses its declaration (mutation
  control); `from_pins` still refuses a second release entry; the proof
  program's `b5.gap.pin_table_is_exactly_four_entry_points`,
  `b5.gap.entry_point_not_pinned.{mul,div,mod,pow,to_u64,clone,drop}` and
  `…no_in_format_compare_project_or_release_of_a_nat` flipped to PASS, the
  `eq`/`lt` rows re-spelled to `beq`/`ble`, and `cmp` ported as a PASS row
  asserting it stays refused. WS3.1's staged-row tests move from `mul` (now
  pinned) to the unpinned `gcd`; `handle_types` derives function ids from the
  row length instead of spelling them. The stale "`trust_bignum_nat_drop` is
  NOT yet exported" doc sentence in `validate.rs` is gone (`78f64c500e`
  exports it). Review adds three adversarial controls to `nat_kernel_surface`:
  the signatures a producer mirroring Rust would guess (a `u64` shift amount,
  a `u32` exponent, `to_u64` as a two-result `Option`, a `Usize` result, a
  `div_rem` pair, a second release spelled through `clone`) are each exactly
  one `HandleEntryPointSignatureMismatch`; a weak / `ExternalWeak`,
  Rust-convention, variadic or naked kernel-surface declaration is refused by
  name; and in a handle-free module the new symbols are guarded like the v1
  ones (declared over `Ptr`, defined locally, shadowed by a global, address
  taken), against an unpinned twin that validates. `declare_handle_runtime`'s
  doc now steers a partial-row producer to `declare_handle_runtime_roles`,
  since a grown row would otherwise add declarations it never calls.
  Rebased onto WS8.6 / WS8.7, the increment flips their ratchets in the same
  change: in `RATCHETS.tsv` the nine `b5.gap.entry_point_not_pinned.*`
  rows and `b5.gap.no_in_format_compare_project_or_release_of_a_nat` go
  GAP → PASS (closing `WS3.2`; `eq` / `lt` pass on the kernel's `beq` /
  `ble` with the archived spelling as the twin that stays exactly one
  `HandleForeignDeclaration`, `cmp` passes by staying foreign, and the
  in-format `ICmp` / `PtrToInt` / `Release` twin keeps its exact
  `InvalidHandleUse` shape), `b5.gap.pin_table_is_exactly_four_entry_points`
  now asserts the nineteen-role row, and the b5 staged-role rows (and
  `b5.declare_handle_runtime`) move from `mul` to the unpinned `gcd`; the
  CLI's `b5.gap.cli_run_*` rows keep their WS4.6 shape (no trap stub, every
  declared pinned entry point stays bodyless, the run refuses by name at
  `trust_bignum_nat_from_u64`) with the `N trusted-runtime entry point(s)`
  count now derived from the row length instead of spelled `5` — there, in
  `cli_run.rs`'s F-083 handle positive, and in the CLI synthesis unit test. c11
  row (1) splits into `c11_flipped_kernel_surface_nat_operations_are_pinned`
  (the archived hand-written `mul` / `div` / `mod` / `pow` / `to_u64` /
  `clone` declarations validate on the plain and codegen lanes and are
  callable; a `u64`-for-handle twin is exactly one
  `HandleEntryPointSignatureMismatch`) and
  `c11_bydesign_off_kernel_nat_operations_stay_foreign_declarations`
  (`eq` / `lt` / `cmp`), and the c11 control now names `nat_double` as the
  foreign declaration instead of accepting any.
- **WS3.1: `ValidationConfig`, one composed lane for every validation entry
  point (F-009, registry half).** Only `validate_module_with_handle_registry`
  took a handle registry; the codegen, authority and linked lanes hard-wired
  `HandleRegistry::pinned()`, and the codegen lane could not take an authority,
  so a pin row staged ahead of `TRUSTED_HANDLE_RUNTIMES` (F-052) had no
  codegen or linked lane. `trust_ir_build::ValidationConfig` carries the proof
  authority, handle registry, optional dialect-schema registry and codegen
  intent; `validate_module_with_config` and
  `validate_linked_module_with_config` run it, and every existing entry point
  (`validate_module[_report]`, `_for_codegen`, `_with_authority`,
  `_with_dialect_schemas`, `_with_handle_registry`, `validate_changed`,
  `validate_linked_module`) is now a thin wrapper over
  `ValidationConfig::pinned()`, with unchanged verdicts. `codegen: true`
  appends the license, lowerability and `global_asm` layers after the
  structural errors, exactly as `validate_module_for_codegen` does;
  `with_authority` keeps the authority tier's refusal of unauthenticated
  proof-bearing imports. The linked walk validates the root and every
  dependency under the SAME config, and its per-digest memo is local to one
  call, so a dependency admitted under a permissive registry is refused by a
  later `pinned()` walk. Both reports expose `handle_registry_is_pinned()`: a
  non-pinned registry is a caller-owned TCB extension, and a consumer that
  compiles must check the bit. Tests in `handle_types` (positive staged `mul`
  row, pinned twin = exactly one `HandleForeignDeclaration`, `add`-retyped
  registry mutation on the codegen/authority/linked lanes, no verdict leak
  between walks) flip `b5.gap.no_codegen_or_authority_entry_point_takes_a_handle_registry`.
  The authority/evidence half of F-009 (`CodegenAdmission` policy, evidence
  binding) is WS1.5 and is not included.
- **WS2.7: `readnone` / `readonly` and borrow structure are checked**
  (F-021, F-040). `FuncAttrs.readnone` / `readonly` were claim-style, so a body
  that executed a `Store` could be stamped `readnone` and validate. On a
  DEFINED body they are now checked (`ValidationError::FuncAttrClaimViolated
  { function, attr, block, inst }`), matching LLVM `memory(none)` /
  `memory(read)`: no write — and under `readnone` no read — through an address
  that does not root at the function's own `Alloca`; no `AtomicLoad` stronger
  than `Relaxed` under `readonly` (it synchronizes), no synchronizing atomic
  write, `Fence`, `HeapAlloc`, `Dealloc`, `Retain`/`Release`/`IsUnique`,
  `CallIndirect` or opaque `DialectOp` under either; a `Call`/`Invoke` (and
  `SeqMap`'s element function) only to a callee carrying `readnone` (or, for a
  `readonly` caller, `readonly`). The alloca root trace follows ONLY a `GEP`
  base, `Copy` and `Cast PtrToPtr`; `Select`, block parameters, `IntToPtr`,
  `Load`/call results and `PtrFromParts` are roots, so none launders a
  parameter pointer into the exemption. Module validation runs the rule among
  the cross-function checks, so it re-runs whenever a callee changes;
  standalone `validate_function` fails a claiming body's call edges closed.
  Declarations keep the attributes as a claim. Borrow STRUCTURE:
  `BorrowMutThroughSharedRef { block }` when a `BorrowMut` operand is typed
  `&T` / `*const T` or may root at a shared `Borrow` result — the same trace,
  widened for this ANY-root question by both `Select` arms and every
  block-parameter incoming argument (review: stopping there let
  `select %c, %r, %r` or a block parameter launder the upgrade); a thin
  borrow's result is typed `Ptr`, so a type-only rule would miss
  `%r = borrow %x; borrow_mut %r` — and `EndBorrowOfNonBorrow { block }` when
  an `EndBorrow` operand is not directly a `Borrow`/`BorrowMut` result. Borrow
  LIVENESS is ratified as a producer obligation (`TRUST.md` item 12,
  `LIMITATIONS.md`): discharged by rustc for tRust, unchecked for Clean and
  hand-built producers. No producer sets either attribute and no in-repo,
  Clean or tRust emission shape trips the borrow rules; no wire change,
  goldens unchanged. Tests: `validation_holes::claim_attrs_and_borrows`
  (gate 9), including the ported ratchets
  `b2.gap.readnone_claim_on_a_storing_function_accepted` (flipped) and
  `b6.ref_refmut.borrow_discipline_unchecked` (split: structural half flipped,
  liveness half RATIFIED-PRODUCER-OBLIGATION).
- **WS8.6: the two-language proof battery lands as conformance ratchets.**
  The 2026-09-17 builder-API battery (archived under
  `reports/2026-09-17-two-language-proof-program/partb/`) is ported into
  `trust-ir-conformance` as the targets `two_language_b0` .. `two_language_b7`,
  `two_language_field_ratchets` and `two_language_harness`, plus
  `trust-ir-cli`'s `two_language_cli`, and runs in the new CI gate 11
  (`two-language-ratchets`, registry-backed:
  `scripts/gates/two-language-ratchets.*.tests`). The 330 archived feature
  entries expand to 588 emitted rows: 460 PASS (each with a right-reason
  negative twin), 122 GAP ratchets and 6 RATIFIED-OUT rows, every one listed in
  entries expand to 581 emitted rows: 455 PASS (each with a right-reason
  negative twin), 120 GAP ratchets and 6 RATIFIED-OUT rows, every one listed in
  entries expand to 581 emitted rows: 457 PASS (each with a right-reason
  negative twin), 118 GAP ratchets and 6 RATIFIED-OUT rows, every one listed in
  entries expand to 581 emitted rows; with the rows later increments added
  the ledger holds 588: 462 PASS (each with a right-reason negative twin),
  120 GAP ratchets and 6 RATIFIED-OUT rows, every one listed in
  `crates/trust-ir-conformance/tests/two_language/RATCHETS.tsv` with its
  finding, closing increment and producer reachability. The ledger also
  carries the 71 v2-architecture rows as `v2-decision` lines pointing to the
  WS8.16..WS8.25 decision gates. They are never test rows, so they stay out of
  the format count. The harness defects are fixed rather than ported. Verdicts
  are recorded as data, not grepped from stdout, so the first row of a test is
  no longer lost. A GAP row states its expected OUTCOME: an exact acceptance, or
  a refusal variant with a payload predicate and exact follow-ons. Any change of
  outcome therefore fails the row, including one refusal turning into another.
  Each target checks a bijection with the ledger, so flipping a row requires
  editing the ledger in the same commit. The field-absence ratchets are
  compile-time exhaustive destructurings, which JSON key sets could not be
  because they miss a skipped field. The CLI rows run `CARGO_BIN_EXE_trust-ir`.
  The re-measure at the port found eight archived GAP rows closed upstream,
  and they are now PASS rows with twins: the six `b1.gap.diff_blind_*` rows
  (f3c07824, d71950bf) and the pin-table and `entry_point_not_pinned.drop`
  rows (the RELEASE entry point, 454ed396). Two more closed while the port
  was in review and are PASS rows too: `b2.gap.dangling_function_scope_accepted`
  (`ObligationFunctionScopeUnresolved`, 5a945757) and
  `b6.eh.landingpad_placement_unchecked` (`UnwindDestWithoutLandingPad` /
  `MisplacedLandingPad`, 5a945757 and b3a1b963). WS1.4 (795f57f8) closed the
  three `b3.gap.composition.*` rows, which are PASS rows now. The Fragment-3b
  baselines carry their `InheritedFromCallee` grounding row. The residual
  that WS1.4 leaves open, `b3.gap.composition.consistent_retarget_to_certified_callee`,
  is a GAP row owned by WS1.12a. `b3.fragment3b.clean_calls_rust_opaque_callee`
  certified a Clean caller over an ungrounded Rust callee. It is RATIFIED-OUT,
  per WS1.4 item 4: such a caller is emitted Pending, and the row holds that
  shape. WS1.1 (0aeae341) closed the two F-001 rows
  (`b2.gap.kernel_certifies_nat_nonneg_ignoring_bindings_and_ir_type`,
  `b2.gap.kernel_certificate_ignores_clause_binding_sort`): each forged nonneg
  certificate is refused by exactly the binding rule's named reason, and the
  fixtures that certify `(>= result 0)` now mint through the module-bound
  `contract_clean_cic_certificate_in`. WS4.7 (42d9db73) closed
  `b4.gap.duplicate_import_rows_admitted` (`ImportTableNotInterned`) and
  `b4.gap.computed_digest_is_caller_asserted` (`DigestMismatch` through
  `verify_import_hashed` and the deprecated caller-digest form), and it
  ratified the two-row shape of `b4.gap.one_import_row_per_producer`
  (`docs/SPEC_RATIFICATIONS.md` §6), which is now RATIFIED-OUT. WS3.15
  (dc416921) closed the two F-058 rows `b1.gap.extern_weak_declaration_refused`
  and `b5.related.gap.extern_weak_bodyless_declaration_is_empty_function`: a
  bodyless `ExternalWeak` import validates and is an FFI boundary, with the
  negative twins `DirectCallToWeakDeclaration` (a direct call of it) and
  `WeakDeclarationAsFnDef` (a `Ty::Func` global over it), each against the same
  shape over the `External` import. WS2.1 (d8e403d4, e1c09924) closed the
  three F-028 `CoroSuspend` rows: `b6.coro_suspend.yield_type_unchecked` and
  `b5.gap.UNEXPECTED.coro_suspend_value_not_checked_against_return_type_forges_a_nat`
  are exactly `ReturnTypeMismatch`, the finding the `Return` spelling of the
  same yield gets, beside a well-typed suspend that validates; and
  `b6.coro_suspend.frame_operand_unchecked` is exactly `OperandNotPointer`
  (`op: "coro_suspend"`). WS1.2 (31814e51) closed the three F-004
  binding-typing rows: `b2.gap.clause_sort_unchecked_against_ir_type` (six
  re-sorted u64 places, each exactly one named `InvalidFunctionSummary`, with
  `Int` as the control that stays valid), `b2.gap.mut_param_exit_on_by_value_param_accepted`
  and `b5.gap.clause_sort_bitvec64_accepted_on_nat_param`. The b2 fixture's
  `out` parameter is now the `*mut u64` its doc always said it was (a bare
  `ptr` gives `MutParamExit` nothing to type against), with the caller
  retyping its alloca through `PtrToPtr`. The archived PASS row
  `b5.contract_over_nat_param.int_sorted_bindings` is RATIFIED-OUT per roadmap
  DG-19 ("refuse the handle place now, admit it in the WS3 Nat increment"): a
  `handle<Nat>` place admits no sort, so the `Int` contract is held as exactly
  its three named refusals while the summary still round-trips losslessly.
  WS2.2 (aa74e1eb, cb3a011c, d35d4723) closed `b6.enum.payload_projection_unchecked`
  (F-029, static half): the leaf arm's `u64` projection of lane 2 is exactly one
  `OperandTypeMismatch` naming the only candidate `node: ptr`, and the
  interpreter reports the lane as belonging to no field of the active variant.
  WS1.6 (c3819f64) closed the two F-010 rows: with no capability,
  `b2.gap.local_inheritance_not_admitted_without_capability` raises nothing
  about the same-module restatement #11 under `validate_module` or
  `validate_linked_module`, and each single change of #11 in
  `b2.gap.local_inheritance_restatement_unchecked` (formula, no formula, kind,
  owner) is exactly the named `LocalInheritanceRestatementMismatch`, even with
  the stand-in admitting the certificate. As WS1.6 ratified, the b2 fixture's
  #11 is now scoped to the callee `b2_countdown`, not the caller.
  WS2.7 (5f28fc7e) closed `b2.gap.readnone_claim_on_a_storing_function_accepted`
  (F-021): a storing body stamped readnone is exactly one
  `FuncAttrClaimViolated`, and the same stamp on a pure function stays valid.
  WS2.7 also split `b6.ref_refmut.borrow_discipline_unchecked` (F-040) into two
  rows. The `.structural_half` row is a PASS row, exactly
  `BorrowMutThroughSharedRef`. The `.liveness_half` row, a `Borrow` with no
  `EndBorrow`, is RATIFIED-OUT (`TRUST.md` item 12) and is held as accepted.
  WS2.3 (3014ce2c) closed `b6.union.overlap_is_not_a_validation_error`
  (F-031): the overlapping struct is exactly one `StructLayoutInconsistent`
  under both `validate_module` and `validate_module_for_codegen`, and the
  disjoint baseline validates.
  WS1.7 (da6ff616, c3a1594e) closed `b4.gap.call_only_import_never_authenticated`
  (F-068): under `validate_linked_module` a call-only importer whose row names
  a garbage digest with no module supplied is exactly one `ImportUnavailable`,
  and a declaration skewed against the far signature is exactly one
  `UnauthenticatedImport { site: "call" }` (signature mismatch). The honest
  baseline links and authenticates its one uncited row.
  WS1.10 flipped `b7.spec.unparsed.linked_mode` (F-014): under `Linked` the
  archived garbage, TLA+ and undeclared-variable invariants and an ill-sorted
  comparison are each exactly one `SpecLinkedFormulaUnparsed`, a type that is
  not a type is `SpecLinkedVariableUnparsed`, a blank formula is still the S0
  refusal, and the same garbage under `DesignOnly` validates. The three
  `b7.spec.unparsed.*` DesignOnly rows stay GAP by design.
  WS4.6 closed the three CLI rows of F-067 and F-083:
  `b4.gap.linked_image_of_proved_modules_fails_validation` (the honest proved
  pair validates as linked and after lowering and prints 48; the twin with a
  hollowed `dep_scale` (body and summary removed) is exactly one
  `EmptyFunction`, as linked, never
  `internal:`), `b4.gap.cli_linker_ignores_import_digest` (the rebuilt
  dependency is refused because its digest "matches no linked input"; with
  `--unauthenticated-imports` it prints 32 and both rows UNCHECKED) and
  `b5.gap.cli_run_without_validate_traps_at_pinned_stub` (a named refusal at
  `@trust_bignum_nat_from_u64`; an ordinary extern still traps at its stub).
  `b5.gap.cli_run_cannot_execute_handle_program` stays a GAP row, reshaped to
  F-035: the `Nat` module now passes both `--validate` passes and is refused by
  name at its first trusted-runtime entry point (WS2.12 / WS2.13).
  WS1.3 (`proved` is per-clause; F-002, F-003) closed
  `b2.gap.kernel_certified_row_backs_an_unrelated_false_clause`,
  `b2.gap.no_per_clause_obligation_backref` (field target: the backref is the
  validator's formula match, the carriers are unchanged) and
  `b4.gap.backed_by_reearns_a_count_not_a_clause`: the false clause is exactly
  one `InvalidFunctionSummary` naming it ("ensures clause 0 `…` has no
  Discharged/Certified Postcondition row scoped to this function stating
  exactly this clause …"), and the linked walk takes the lying dependency's
  own refusal as `ImportedModuleInvalid` and re-earns nothing. Rows that stay
  open keep their shape under the new wording:
  `b2.gap.mint_summary_obligations_skips_decreases` now mints rows
  that state their clauses, and `b2.gap.unbindable_clause_still_earns_proved`
  strips the bindings from each clause AND the row stating it, so it still
  measures unbindability, not a clause mismatch. The b2 binding twins that
  mutate a clause now also carry that clause's per-clause refusal, and the
  `b2.proved.*` twins name the clause the removed row stated.
  As WS2.5 specifies,
  `b6.eh.invoke_never_takes_unwind_edge` and
  `b6.eh.resume_unsupported_by_interpreter` are re-labelled RATIFIED-OUT
  (panic=abort, `docs/ub-numerics-policy.md` §4), a new harness verdict. It is
  held in its exact shape like a gap but counted as neither PASS nor GAP. The
  resume row now reaches `Resume` through the one shape that still validates,
  a shared cleanup block that the normal path also enters. A harness self-test
  requires every ledger target to be a declared test target that gate 11's
  registry runs, so a target dropped from the gate cannot leave its rows
  unchecked, and `run_target` checks that the token it is handed is the one
  bound to the running target's Cargo name (`two_language_bN` -> `bN`), so two
  `[[test]]` entries pointing at one file cannot leave the other target's rows
  unchecked either. `Outcome::all` never pools a MIXED set of mutants (some
  accepted, some refused) into one refusal list: that is a measurement no
  expectation equals, so a mutant that stops being refused cannot hide behind
  another that gains a second refusal of the same variant. The three function-pointer
  forgeries the battery claimed but never ran are now real rows (all refused
  by name). `trust-ir-build` re-exports `clean_kernel` `#[doc(hidden)]` as test
  plumbing, so the b3 kernel comparands need no seventh Clean pin leg. The dev
  profile compiles `clean-kernel` at opt-level 3, which took `two_language_b3`
  from 370 s to about 25 s.

- **WS4.18: refusals enumerate repair options (F-081).** v7 D3 makes the
  reader of a fail-closed refusal an AI programmer, but no refusal enumerated
  a way forward (`grep 'Options:'` was 0 in `validate.rs`, `linked.rs` and
  `imports.rs`). New `ValidationError::repair_options(&self) -> &'static
  [&'static str]`, a `match` with an empty default, filled for
  `DischargedWithoutCertificate`, `UnauthenticatedImport` (per site: `call`
  gets its own list), `ImportUnavailable`, `InvalidFunctionSummary`,
  `UngatedBodyForCodegen`, `GlobalAsmNotConsumable`,
  `HandleEntryPointDefinedLocally`, `TargetInfoRequired` and
  `UnpinnedCustomObligationNamespace`; `ImportVerificationError` gains the
  same method, filled for `DigestMismatch`. `trust-ir validate` (and
  `--link`) prints `      options: a; b` under each refusal that has any,
  and nothing for one that has none. No variant, verdict, exit code or wire
  byte changes. The options are advice text, never authority: no option
  suggests weakening a status, faith-stamping a codegen license or borrowing a
  privileged namespace, and `repair_options_have_no_reader_outside_the_cli_printer`
  (gate 9) fails on any reader in `crates/*/src` other than the one CLI
  printer. Row `spec-surface-0709/23-refusals-carry-repair-options` is ported
  as `spec_surface_0709_23_refusals_carry_repair_options`; the in-module
  residue it names (a structured repair list on `ObligationDiagnostic`, carried
  through every format) is a wire change and stays open. Review: the reader
  scan matches the `repair_options` identifier in code, not the
  `repair_options(` token, so a function-path reader
  (`.map(ValidationError::repair_options)`) or a call split across lines is
  named; `UnlicensedBodyForCodegen` is filled too; `ImportUnavailable` names
  the wrong-file-under-`--link` case, `UnauthenticatedImport` the exact
  restatement a supplied-but-refused `backed_by` needs, and
  `DischargedWithoutCertificate` the replaying-capability route; and
  `no_repair_option_steers_toward_a_faith_tier` refuses any option naming a
  stronger status label, the faith floor or an affirmative non-license.

- **WS4.12: builder API doors.** `ModuleBuilder` had no door for enums,
  records, closure types, imports, spec modules or `global_asm!`, and
  `FunctionBuilder` none for linkage, summaries or a per-instruction proof on
  an emitter without a `*_proven` twin, so producers called `mb.build()` early
  and mutated the tables by hand. New, all thin unchecked pass-throughs (the
  validator stays the authority, and each door builds exactly the module the
  hand spelling builds):
  * `ModuleBuilder::{add_enum, add_record, add_closure_type,
    intern_func_type, intern_import, add_spec_module, add_global_asm}`, plus
    the core `Module::intern_func_type` (structural, idempotent;
    `add_func_type` stays always-appending);
  * `FunctionBuilder::{set_linkage, set_summary, clear_summary,
    add_function_proof, annotate_last}`. `annotate_last` attaches to the node
    `last_emitted_position` names and returns
    `BuilderError::NoEmittedInstruction` when there is none (fresh block, or no
    block selected); it never falls back to `Function::proofs`. It also
    refuses with `BuilderError::LastEmittedInAnotherBlock` when the cursor was
    moved back to a block after something was emitted elsewhere, because that
    block's last node is not the instruction just emitted (adversarial
    review: without this the claim silently landed on the older node);
  * `FunctionSummary::decreasing(ProofFormula)` appends a termination measure
    and does not set `proved`.

  **Deprecated:** `FunctionBuilder::add_proof`, an alias of
  `add_function_proof` whose name hid that it writes FUNCTION-level proofs.
  In-repo callers are migrated; producers building with `-D warnings`
  (~/trust, clean) will see the deprecation on their next pin move. No wire
  change. Test: `trust-ir-build/tests/builder_doors.rs` (gate 9).
- **WS8.7 (F-120): the 2026-09-17 proof program's claim repros c01..c15 are
  in-repo regression tests (the trust-ir rows).** Each claim crate under
  `reports/2026-09-17-two-language-proof-program/verify/cNN_*/` is ported,
  on its exact modules, into the test target that owns it: c02, c06 and
  c15 into `trust-ir-build/tests/validation_holes.rs`; c03 and c11
  into `handle_types.rs`; c05 legs (a, b) into `g3_codegen_license.rs`; c07
  into `struct_repr_and_target.rs`; c12 into
  `linked_import_authentication.rs`; c08 into
  `trust-ir/tests/format_canonical.rs`; c09 into a new
  `trust-ir/tests/parser_never_panics.rs`; and the CLI legs of c11 and c12
  into a new `trust-ir-cli/tests/cli_verify_repros.rs`. Each claim has a
  positive fixture (`cNN_bydesign_*`), the repro as a GAP ratchet
  (`cNN_gap_*`) asserting today's wrong acceptance (or, for c11's
  capability gaps, today's refusal) exactly, and mutation controls
  (`cNN_control_*`) — the neighbouring single mutations that ARE refused by
  name, so no ratchet passes vacuously. The fixing increment (WS1.3,
  WS1.5, WS1.8, WS2.6,
  name, so no ratchet passes vacuously. The fixing increment
  (WS1.5, WS1.8, WS2.6, WS3.2,
  WS3.3, WS3.6, WS3.7, WS2.13, WS4.2..WS4.6) owns each flip; each module's
  doc names its flipper. Rows already closed upstream land as flipped twins
  only: c09 (WS4.1, `7f03a92e` / `414b4f6a`), c15's EH placement and
  `Br`-entered pad (WS2.5, `5a945757` / `b3a1b963`) and c15's dangling
  function scope (`5a945757`), and c12 row 3 (duplicate import rows, F-075,
  now refused as `ImportTableNotInterned` in every tier; WS4.7 `42d9db73`),
  whose row 6 (one producer per row) WS4.7 ratified and is by design, and
  c12's rows 1a/1b/1c (WS1.7 = WS4.8, `da6ff616`, F-068): the linked walk
  refuses the garbage-digest call-only row as `ImportUnavailable` (and, via
  a name resolver, as the digest mismatch it is), the `u32`/`u64` call-edge
  drift and the obligation-free `backed_by` naming `no_such_symbol` as
  `UnauthenticatedImport { site: "call" }`, while the single-module tiers
  still take a call-only row on faith by design, and
  c03's two rows (WS2.1, `d8e403d4` / `e1c09924`): the yield that retypes a
  `ptr` or `u64` into a `handle<Nat>` is `ReturnTypeMismatch`, and the
  scalar scope row is `ReturnTypeMismatch` / `ReturnArityMismatch` /
  `OperandNotPointer { op: "coro_suspend" }` in every tier, and c06's five
  statically decidable rows (WS2.2, `aa74e1eb` / `cb3a011c` / `d35d4723`):
  a lane beyond every variant is `FieldAccessInvalid`, a wrong payload
  type is `OperandTypeMismatch` (`role` `field` / `value`), a lane-0
  `insert_field` is `FieldAccessInvalid` (and interpreter UB, no longer a
  silent re-tag), a tag read at `u64` is `OperandTypeMismatch { expected:
  "u8" }`, and a non-aggregate or STRUCT result type over an enum is
  `OperandTypeMismatch { role: "result" }`, and c07's four rows (WS2.3,
  `3014ce2c`): the `b@0` overlap, the union-shaped struct, the partial
  overlap and the target-free overlap are `StructLayoutInconsistent
  { reason: "fields overlap" }`, and a target-free field past the size is
  `StructLayoutInconsistent { reason: "field offset is outside the declared
  struct size" }`, and c15's structural borrow and memory-effect rows (WS2.7,
  `5f28fc7e` / `6f3fbcdc`): 3a and 3g are `BorrowMutThroughSharedRef`, 4a
  and 4b are `FuncAttrClaimViolated` naming the store, while 3b-3f (borrow
  LIVENESS) land as positive fixtures under the ratified producer
  obligation (`TRUST.md` item 12) and 4c (`Pure` on a storing body, outside
  WS2.7's `FuncAttrs` rule) stays a ratchet. c01
  and c04 are closed upstream by WS1.1 (`0aeae341` / `b961642d`) and WS1.4
  (`795f57f8` / `a78918c9`), whose `contract_clause_binding.rs`
  (`verify_c01_l1` / `verify_c01_l2`) and `tv_callee_binding.rs`
  (`verify_c04_*`) already carry the flipped twins, so WS8.7 adds no c01 or
  c04 rows; c02's fixture mints through the module-bound
  `contract_clean_cic_certificate_in`, the only nonneg door since WS1.1.
  c02 (F-002, F-003) is closed by WS1.3: its two rows flip to
  `c02_local_false_ensures_is_refused_per_clause` (the exact per-clause
  `InvalidFunctionSummary` under the structural, codegen, authority and
  report tiers) and `c02_cross_crate_backed_by_cannot_re_earn_a_false_clause`
  (`ImportedModuleInvalid` carrying that refusal; nothing authenticated). Gate 9's registry now also runs
  `g3_codegen_license` (`struct_repr_and_target`, which carries c07, since
  WS2.3; `handle_types`, which
  carries c03 and c11, and `g5_contract_clause_bindings` are already there
  since WS2.1 / WS3.1 and WS1.2). Tests only: no wire, golden or validator
  change. The trust-cg (c07 consumer refusal, c13) and ~/trust (c14) rows
  are companions in those repos; c10 is the decision-gated `b7.nondet.*`
  rows of WS8.6. Review added two archived rows the first port omitted,
  each a false claim accepted at port time: c06's `insert_field` on the TAG lane re-tagging an enum
  value that then runs unrefused, and c12's obligation-free `backed_by`
  naming a far symbol nobody checks. It also pinned the two mutation
  controls that asserted only "some error" to their named variants. A
  second, adversarial review added five more rows from the archive the port
  had not covered: c06's wrong-TAG-type read (`extract_field u64` of the
  `u8` tag lane, F-029's third statically decidable class) and its
  `insert_field` declaring a STRUCT result over an enum value (then
  accepted everywhere, refused only by the interpreter's dynamic typing;
  both flipped by WS2.2 before landing), plus the wrong-variant-but-valid-lane read as a positive
  fixture that must stay accepted, so an over-broad WS2.2 fix flips it;
  c07's partial overlap and target-free overlap, so WS2.3's rule cannot be
  an equal-offset or target-pinned test alone (both flipped by WS2.3 before
  landing); and c08's headline laundering
  through the shipped CLI (`convert` bin -> text -> bin, exit 0 throughout,
  turns `GlobalAsmNotConsumable` into an admitted module). c05's leg-a
  control names `InvalidBodyGate` (the enforcement ledger's
  `validation-error-variants-unnamed` census had already tightened 7 -> 6
  for it when WS8.6 landed, so WS8.7 keeps WS8.6's ledger row); c15's
  attribute fixture states its function-level `Pure` claim through
  WS4.12's `add_function_proof` door.
- **WS1.5 (F-006 validator half, F-009, F-017 key half) — the codegen license
  is bound to evidence; policy/authority/registry-taking entry points.**
  `codegen_license_errors` matched `Gated { .. }` and never looked for the
  certificate the authority string names, so a body wearing
  `Gated{"clean-kernel-tv"}` with zero obligations (the c05 baseline) was
  admitted for codegen. Now:

  * `EVIDENCE_BOUND_GATE_AUTHORITIES` (`("clean-kernel-tv",
    GateEvidenceRule::KernelTranslationValidation)`, byte-exact) binds an
    authority to evidence. A bodied function claiming it must carry EXACTLY ONE
    `TranslationValidation` obligation scoped to it, `Certified`, whose
    `CleanCic` certificate cites `KERNEL_ANCHOR_CLEAN_BACKEND_TV` and is in the
    kernel-tier set replayed in the same pass. The recheck re-derives the
    emitted side from the current body, so an edit after minting keeps the
    `body_gate` and loses the license. Refusal:
    `ValidationError::GatedWithoutEvidence { function, authority, detail }`.
    It is not a recognition registry: other authorities keep their standing on
    the policy-free entry points.
  * Revocation for EVERY `Gated` body: a `Failed` `TranslationValidation`,
    `Postcondition` or `Precondition` row scoped to the function is
    `GatedFunctionRefuted { function, obligation }`; two or more TV rows are
    `GatedWithoutEvidence("ambiguous: …")`. "Scoped" reads the row's
    `function` scope or, for a row with none, its `site`'s function (review:
    a site-only `Failed` row or second TV row otherwise sat beside a license
    unrevoked). Measured before landing: 0 of the
    118 module dumps archived by the 2026-09-17 proof program carry a `Failed`
    TV/Pre/Post row or a second TV row scoped to a `Gated` body; the only
    bodies the evidence rule newly refuses are the 11 c05-repro bodies that
    stamp `clean-kernel-tv` over zero obligations (the defect itself).
  * `codegen_license_errors_with(&ModuleValidationReport)` reuses the report's
    replayed set (no second kernel pass); the bare form re-runs the
    certified-evidence pass only when some body claims an evidence-bound
    authority.
  * Composed entry points, built on WS3.1's `ValidationConfig` (the one
    structural options struct): `CodegenAdmission` = a `ValidationConfig`
    (authority, handle registry, dialect schemas) plus the two license knobs
    a config does not carry — an optional recognized-authority set
    (→ `UnrecognizedGateAuthority { function, authority }`) and an
    `UnlicensedBodyPolicy` — with `validate_module_for_codegen_with`;
    `validate_module_with_bundle_with_authority`;
    `validate_module_report_with_authority_and_registry`;
    `validate_linked_module_with(root, resolver, authority, registry)` (a thin
    wrapper over `validate_linked_module_with_config`: one registry for the
    whole closure). The config lane's codegen layers
    (`ValidationConfig::with_codegen`, single-module and linked) now read the
    license evidence from the kernel tier their own structural pass replayed,
    so no module is kernel-rechecked twice.
  * Disclosure keys: a `fn:N` row of
    `@trust-internal::clean-origin-disclosure-v1` must name a bodied function
    of the module (`ReservedSpecModuleName { detail: "disclosure row fn:999
    names no bodied function" }`), and a key may appear only once (review:
    two contradictory rows for one body were accepted); row CONTENT stays an
    unauthenticated producer claim (`LIMITATIONS.md`).

  Residual, stated so nobody over-reads it: the `clean-kernel-tv` license is
  bound to a TV certificate (emitted == recorded comparand), not yet to the
  Clean source (F-008, WS1.13). No wire change (the evidence slot on
  `BodyGate` is WS1.12c). GAP rows flipped as in-repo tests in
  `g3_codegen_license`: `b3.gap.kernel_tv_license_not_bound_to_certificate`,
  `b2.gap.no_authority_taking_codegen_or_bundle_entry_point`,
  `b5.gap.no_codegen_or_authority_entry_point_takes_a_handle_registry`,
  `b1.gap.disclosure_rows_unbound_to_module` (key half);
  `b1.gap.gated_authority_unpinned` re-scoped (PASS for the evidence-bound
  authority; unknown authorities stay a consumer decision). Gate 9 already
  runs `g3_codegen_license` (registered by WS8.7) and `handle_types` (WS2.1).
  In the WS8.6 ratchet ledger (`two_language/RATCHETS.tsv`) the same rows
  flip to PASS with negative twins — `b1.gap.gated_authority_unpinned`,
  `b2.gap.no_authority_taking_codegen_or_bundle_entry_point`,
  `b3.gap.kernel_tv_license_not_bound_to_certificate`,
  `b3.envelope.gap.license_survives_dropped_tv_obligation`,
  `b3.envelope.gap.license_survives_failed_tv_obligation`,
  `b5.gap.no_codegen_or_authority_entry_point_takes_a_handle_registry` — and
  the key half of the disclosure row lands as the new PASS row
  `b1.disclosure.fn_key_names_a_body`; `b1.gap.disclosure_rows_unbound_to_module`
  stays GAP for the content half (WS1.12c). WS8.7's c05 repro flips leg (b)
  and re-scopes leg (a). Hand-built fixtures that wore `clean-kernel-tv` as an
  unrelated grant with no TV certificate now wear the evidence-free
  `trust-direct-lane-structural`, and the codegen lane's kernel-rejection
  rows expect the one license follow-on a rejected recheck now carries.
- **WS8.15 (remainder): behaviour refinement with calls executed.** The
  refinement notion `behaviour_refines` is stated over the intraprocedural
  `stepN`, where every call is an `unsupported` behaviour, so a transform
  that changed WHICH function a call runs was a proved refinement. The new
  Lean module `TrustIr/Proofs/TransformRefinementCtx.lean` states
  `behaviour_refines_in` over `stepNWithContext` in every module context, with
  block fuel and call depth both quantified (`BehavesIn`; `diverges` is
  `outOfFuel` at every pair), and `program_refines` over
  `evalFunctionInContext` with the context's `maxCallDepth` quantified.
  Proved: `id_refines_in`, `compose_refines_in`, `behavesIn_nonempty`,
  `unreachableToReturn_refines_in` (the UB-top rewrite, panic=abort, calls
  executed), `inlining_outcome` / `inlining_behaves_iff` (a resolved call's
  behaviours are exactly its inline body's behaviours mapped through the call
  boundary `callBoundary`: divergence and traps verbatim, a return arity- and
  poison-checked with the caller frame restored), and the whole-program
  `id_program_refines`, `compose_program_refines`,
  `withMaxCallDepth_program_refines`. Refuted: `assertElim_not_refines_in`
  (negative twin), and `callRetarget_not_refines_in` while
  `callRetarget_refines` holds, so `behaviour_refines_not_imp_refines_in`.
  Fifteen `AxiomAudit.lean` entries pin the new theorems to the Lean-core
  trio. Not proved, and documented as residue: the `.unwind` strategy,
  lifting a transform over every function of a context (blocked because the
  context-aware constant lowering `constValueAtWithDefs` is a `partial def`
  over the whole context), and the splice form of inlining. Lean only, no wire
  change.
- **WS8.15 review: divergence controls with calls executed.** The in-context
  notion `behaviour_refines_in` had no divergence mutation control. Added:
  `loop_not_refines_in` and `panicToLoop_not_refines_in` (the in-context
  twins of `loop_not_refines` / `panicToLoop_not_refines`),
  `recursion_not_refines_in` (replacing a returning body by unbounded
  self-recursion is refused: running out of call depth at every budget is
  `diverges`), and `withMaxCallDepth_not_fixedDepth_refines` (the mutant
  that reads the depth budget from the context refuses a depth-only change,
  as the `withMaxCallDepth_program_refines` docstring claimed without a
  theorem). Four `AxiomAudit.lean` entries, Lean-core trio. Lean only.
- **WS8.15: behaviour refinement in `TransformCorrectness.lean`.** The Lean
  framework's only transform-correctness notion, `semantics_preserving`, said
  "if the source RETURNS at fuel n, the target returns the same at fuel n" and
  nothing else. Under panic=abort a panic is a defined trap, so deleting a
  failing `Assert` (source `panic`, target `ok`) satisfied it, and so did
  turning a panic into an infinite loop. The new `behaviour_refines` compares
  observable behaviour sets: for every source run that is UB-free at every
  fuel, every behaviour of the target (a return, a panic, a type error, an
  unsupported refusal, UB, or divergence = `outOfFuel` at every fuel) is a
  behaviour of the source. Divergence is an outcome, so a looping target
  cannot refine vacuously, and UB is a target outcome too, so a transform
  cannot introduce it. Proved: `id_refines`, `compose_refines`,
  `block_transform_lifts_to_cfg_refines` (under the exact-on-non-UB block
  hypothesis), `constant_fold_refines`, and the trap half of inlining
  (`inlining_error_transfer` / `inlining_error_cases`). Counter-models:
  `assertElim_not_refines` (while `assertElim_semantics_preserving` holds),
  `loop_not_refines`, `panicToLoop_not_refines` (while
  `panicToLoop_semantics_preserving_weak` holds), `divToRet_not_refines` (a
  diverging source made to return, while `divToRet_semantics_preserving`
  holds), `trapClass_not_refines` (a panic made a type error),
  `ub_introduction_not_refines`, and `block_transform_lifts_to_cfg_not_refines` /
  `semantics_preserving_not_imp_refines` for the theorems that do not carry
  over. UB is top by design: `unreachableToReturn_refines` admits a rewrite
  that changes only UB runs. `semantics_preserving` stays, documented as
  forward and `.ok`-only.
  No axioms: the new theorems are gated in `AxiomAudit.lean` at the Lean-core
  trio. Lean only, no wire change. Closes the plan-of-record half of F-127
  (`core-arch-0916-a/24`, `core-arch-0916-b/46`).
- **WS4.9 (F-074 remainder) — CLI ergonomics: producer artifacts, magic
  sniffing, `run --arg`, `digest`, `handles`.** The 2026-09-17 scout
  (`scout-emit.T1`) found trustc's `CRATE.trust-ir.bin` refused without
  `--format bin` (its trailing extension `bin` is unknown) and `run` limited to
  nullary entries. Now:

  * `trust_ir::codec::sniff_format(&[u8]) -> Option<SniffedFormat>` — new,
    always-on, zero-dep core API (byte checks only), shared by every TrustIr
    tool. `TRUST_IR` magic ⇒ `Binary` (the binary codec now reads its magic
    from the same `codec::TRUST_IR_BINARY_MAGIC` constant), a first
    non-whitespace `{` ⇒ `Json`, a leading `;` or `module "` ⇒ `Text`, and
    trust-cg's `tMBC` container magic ⇒ `TrustCgContainer`. MessagePack is
    never sniffed.
  * `Format::resolve` order: an explicit `--format` wins and is never
    second-guessed; a `tMBC` container is refused BY NAME under any extension
    — `.tmbc` included, since that extension is TrustIr's own and only the
    magic disambiguates; a recognised name (`.trust-ir.bin`, `.trust-ir.txt`,
    then `.tmbc`/`.trust_ir`/`.json`/`.msgpack`) is cross-checked against the
    sniff and a disagreement (or a binary name without the `TRUST_IR` magic)
    is refused naming both, never fallen through; a name that says nothing
    (stdin, `.bin`) takes the sniffed format. Resolution refusals exit 1,
    decode failures 2, as before.
  * `run --arg <v>` (repeatable): each value is parsed against the entry
    signature's param type — integers in decimal or `0x` hex, range-checked for
    width and signedness BEFORE `InterpretValue::int` (which masks, so an
    unchecked `256` would silently run as `0`), `true`/`false` for `bool`,
    float literals for `f32`/`f64` (a finite literal that rounds to infinity,
    or a nonzero one that rounds to zero, is a range error too — `1e39` at
    `f32` would otherwise run as `inf`). Any other param type — `char`
    included — is refused naming it
    (`param 1 has type ptr; only scalar entry arguments are supported`), and
    the arity must match exactly.
  * `trust-ir digest <path>…` prints each module's name, `stable_digest`
    (under `MODULE_IDENTITY_DOMAIN` — what `ModuleImport.digest` records),
    `executable_content_digest_v1`, and the minimal binary wire version the
    writer selects. An unencodable module (`Ty::Error` from JSON) is reported,
    with no panic banner, and the remaining inputs are still digested.
  * `trust-ir handles` lists `TRUSTED_HANDLE_RUNTIMES` read-only: runtime,
    calling convention, handle type, and every entry symbol with its exact
    pinned signature (the five `trust_bignum_nat_*` entry points).

  Tests: `crates/trust-ir-cli/tests/cli_ergonomics.rs` (25, including the
  ported `scout_emit_T1` row now asserting the closed behaviour, the
  `.tmbc`-over-`tMBC` and `.json`-over-`TRUST_IR` twins, `--arg 256` for `u8`,
  `--arg` on a `ptr` param, the sniff-mutant control, and the review
  adversaries: a text/msgpack name over JSON content, every golden resolving
  under its own name, float overflow/underflow, `isize`/`u128` ranges, a
  `char` param, and a `Ty::Error` digest), the extended
  extension-contract unit test, and
  `crates/trust-ir-conformance/tests/sniff_format.rs` — the table test over
  the whole golden corpus, added to gate 8's `--test` list because core
  `trust-ir` tests run in no gate. No wire change; goldens unchanged.
- **Non-null pointer constants at typed-reference and fat-pointer positions
  (WS3.8, F-049, constant half).** The only `Ty::FatPtr` constant was the
  null pair and `Constant::SymbolAddr` fit only `Ty::Ptr` / `Ty::Func`, so
  `static S: &str = "…"`, a `[&str; N]` table, a `&'static T` field of a static
  initializer and an `Option<&'static str>` enum seed had no spelling except
  erasing the fat type to a `(ptr, u64)` tuple. The module-table-aware
  constant walk (`validate_constant_against_ty`; the table-free
  `Constant::shape_matches_ty` is unchanged) now admits exactly two spellings,
  in body `Const`s and global initializers, nested aggregates included:
  `SymbolAddr { symbol, addend: 0 }` at `Ref(T)` / `PtrConst(T)` / `PtrMut(T)`,
  naming one module global of type `T` (immutable at `Ref`, mutable at
  `PtrMut`); and `Aggregate[SymbolAddr { G, addend: k }, Int(n)]` at
  `FatPtr(Str)` / `FatPtr(Slice(t))`, a window of one IMMUTABLE array global —
  `[u8; m]` initialized by `Bytes { utf8: true }` whose bytes `[k, k+n)` are
  valid UTF-8 for `str`; `[t; m]` with `k` element-aligned and
  `k/size + n <= m` for a slice. The global must be DEFINED here (an
  initializer-less global is the linked walk's extern data declaration),
  non-thread-local, and not interposable (`Weak` / `LinkOnce` /
  `ExternalWeak`; the `*Odr` linkages stay admitted as in WS8.14), and no other
  module item may carry its symbol. Every other shape of those two spellings
  is the new `ValidationError::PointerConstantRefused` naming a
  `PointerConstantRefusal` reason; `SymbolAddr` at `Rc` / `RefMut` and any
  non-null `TraitObject` / `ContainerLen` / `ContainerVtable` constant stay
  `ConstTypeMismatch`, and a pinned handle symbol is still
  `HandleEntryPointAddressTaken`. The reference interpreter resolves an
  admitted constant to the global's own allocation (provenance kept; the
  global is now cached before its initializer is evaluated, so a
  self-referential static terminates), and fails closed on a missing, repeated
  or thread-local global or an out-of-bounds window. The closure-capture pass
  defers these two spellings to the typed walk instead of refusing what it
  admits. Tests: `crates/trust-ir-build/tests/pointer_constants.rs` (gate 9:
  positive `&'static str` in a body and a global reading `'h'`, its `Int(6)`
  twin, mid-UTF-8, `utf8: false`, wrong pointee, undeclared / function /
  declared-only symbols, `Rc` / `RefMut`, mutability twins, TLS, addend,
  linkage, ambiguity, slices, the null-only kinds, and the ported rows
  `b6.fatptr.non_null_constant_rejected` (GAP → PASS; the gate-11 ratchet
  row in `two_language_b6` flips in the same change, its negative twin the
  `Int(7)` window refused as `PointerConstantRefused { WindowOutOfBounds }`
  at both positions, and `RATCHETS.tsv` records it as `PASS` closed by
  WS3.8), `exec-log-and-tcb/fat-pointer-constants` and
  `producer-rust-thir/fat-pointer-constant`) and
  `crates/trust-ir-conformance/tests/pointer_constant_formats.rs` (gate 8: all
  four formats round-trip at the unchanged v38 header). Review added:
  self-referential and two-static-cycle statics validate and terminate, a
  `*mut` constant aliases `GlobalAddr` of its global in both orders, a
  `&refine<u64, nonzero>` over an unrefined zero global and a `&Other` over a
  same-shaped struct of another name are refused, a `[&u64; 3]` constant is
  refused per element at its own path, a `&[&str]` over a `[&str; 2]` table
  executes (its half-element offset is refused), a bad fat constant in a
  closure capture is still refused by the typed walk, and gate 8's
  `interpret_differential` runs validated pointer constants
  deterministically to their values. No wire change;
  goldens unchanged. Deferred: the Lean `Constant.SymbolAddr` mirror and fat
  constant decoding (needs WS2.18, F-043); trust-cg must emit data relocations
  for the new spellings and the Rust producer must emit them (companions).
- **Niche enum layouts may leave an uninhabited variant unencoded (WS3.14(a),
  F-056).** rustc lays out `enum E { A(char), B(!), C }` in 4 bytes with
  `niche_variants = 2..=2`: `B` has no value, so it gets no encoding. The
  niche-coverage rule demanded that the interval plus the untagged variant
  cover EVERY variant, so the Rust producer had to decline the descriptor and
  fall back to the canonical tagged layout, which is not rustc's (row
  `producer-rust-thir/enum-niche-uninhabited-variant`). The rule is now: every
  INHABITED variant is the untagged variant or lies in the niche interval. It is
  checked at the three sites that each re-derive it — the validator, `shape`,
  and the reference interpreter — through one shared helper,
  `Module::niche_unencoded_inhabited_variant`, over the new sound (never
  complete) predicates `Module::ty_is_uninhabited` /
  `Module::variant_is_uninhabited` (`!`, an enum all of whose variants are
  uninhabited, a struct/record/tuple/non-empty array/refinement containing one;
  cycle-guarded and memoized; unresolvable or cyclic answers "inhabited"). A
  `!` payload field is size 0 / align 1 under a producer descriptor only; the
  canonical layout still refuses it, and the validator now refuses any other
  alignment-free descriptor field (`[!; 2]`, a struct holding `!`) by name, as
  `shape` and the interpreter already did — otherwise an exempt variant spelled
  that way validated a layout no consumer could compute. Constructing an
  uninhabited variant through `Inst::Const` or a global initializer is the new
  `ValidationError::UninhabitedVariantConstructed`, and the interpreter refuses
  to construct, store, or decode one (a direct tag or niche value naming it is
  an invalid value). No wire change; goldens unchanged. Part (b),
  `EnumTagRepr::{I128, U128}`, is a binary-version batch and stays deferred to
  its reserved version (WS8.5); its row `producer-rust-thir/enum-repr-128` is
  kept as a GAP ratchet. The `MakeAggregate` construction clause waits for
  WS3.5.
- **Build identity in every tool's `--version` (roadmap WS8.4, F-118's
  version-string half).** `trust-ir --version` printed the bare `0.14.0`, which
  dozens of commits share, so no measurement could say which build it ran.
  `crates/trust-ir/build.rs` now resolves the source sha in a fixed order.
  First comes the packaging override `ALAB_BUILD_GIT_SHA` (12–40 lowercase
  hex) with `ALAB_BUILD_GIT_DIRTY=0|1`. A malformed (including non-Unicode) or
  half-set override FAILS the build and names the variable. The roadmap's
  draft spelling `TRUST_BUILD_GIT_*` is REFUSED by name wherever it is
  visible: verified Targo (`targo trust build`) removes every `TRUST_*`
  variable from a build script's environment (measured: the script sees it
  absent), so that spelling would silently degrade every verified-lane build
  to `.local`/`unknown`. Next comes `git rev-parse HEAD`, but
  only when `--show-toplevel` is the crate's OWN root and that root's `HEAD`
  records `crates/trust-ir/Cargo.toml`. This fallback cannot attest the working
  tree, so its label is always `.local`. Otherwise the label is `unknown`, and
  a missing `git` never fails the build. The new `pub const
  trust_ir::BUILD_IDENTITY` carries the package version, the source label, sha
  and attestation, the wire `VERSION`, the read range
  (`MIN_READ_VERSION..=VERSION` minus the refused 26..=28), and
  `MODULE_IDENTITY_DOMAIN`. Consumers (trust-cg, clean) read it from the
  COMPILED crate, never from a manifest string. `trust-ir`, `trust-ir-fmt` and
  `trust-ir-diff` print `<name> <MAJOR.MINOR.0>+<source>`, and each
  const-asserts that it shares trust-ir's package version.
  `trust-ir --version --verbose` and `trust-ir version [--json]` add the wire
  range and digest domain. The `rustc-env` keys are `TIR_BUILD_*`, because
  authenticated Targo refuses a build script that sets a `TRUST_*` variable.
  No wire change, and the goldens are byte-identical. Tests are in
  `crates/trust-ir-cli/tests/cli_version.rs`:
  `version_names_wire_and_domain`, the malformed-override negative twin, and
  the `unknown` / vendored-in-unrelated-repo / uncommitted-change mutation
  controls, driven through the exact file the build script runs.
- **Wire-version reservation ledger (`crates/trust-ir/wire_versions.tsv`,
  roadmap WS8.5).** Binary versions v39 and v42 each collided because two
  development lines wrote the same unreserved number into read gates and
  goldens. Every version now has a ledger row — 2..=22 `retired` (below the v24
  read floor), 26..=28 `refused` (ambiguous lineage), 23..=25 and 29..=43
  `shipped` — and a v44+ number is taken by pushing a `reserved` row to main
  before development writes it anywhere, one number per feature group in
  reservation order (DG-14 option (a), not a single v44 monolith: the writer
  already selects the minimum lossless version per module, so additive groups
  never wait on each other). The in-crate `binary::wire_version_ledger` test
  refuses, by name: a `VERSION` with no `shipped` row, a `MIN_READ_VERSION`
  that is not the lowest readable row, a row whose status contradicts the
  reader's real accept/refuse verdict (e.g. v27 flipped to `shipped`), a
  duplicate or missing number, a reservation at or below `VERSION`, a
  post-ledger row without a reserving commit and owner, a shipped version above
  the v38 baseline that no `*_FORMAT_VERSION` writer constant selects, and — by
  a source scan of `binary.rs` — any `*VERSION*` constant or static the ledger
  does not bind, whatever its type, visibility or line wrapping
  (`NATIVE_BUNDLE_VERSION` / `PROOF_LINEAGE_VERSION` are separate version spaces,
  excluded by name), and any literal read gate (`r.version >= N`) spelling a
  number with no ledger row, i.e. development writing an unreserved number.
  The `refused` rows are bound to `AMBIGUOUS_LINEAGE_VERSIONS` (the reader's
  in-window refusal that `BUILD_IDENTITY` reports) in both directions. Runs as the `wire-version-ledger` gate beside standing gate 8 in
  `scripts/ci_gates.sh` (an in-crate `--lib` test, so it cannot be a line in
  gate 8's `trust-ir-conformance` registry); gate numbering is unchanged. No
  wire change; goldens unchanged.

- **`trust-ir validate --link <DEPENDENCY>` — the shipped-binary half of import
  authentication.** `validate_linked_module` has had its own suite since the
  authority tier landed, but no binary could run it: `validate` called
  `validate_module_report`, the faith floor, which checks that a cross-crate row
  RESOLVES and nothing more. The flag is repeatable, takes any supported format,
  and runs the closure walk under `RejectingModuleProofAuthority`, so the
  binary replays nothing on its own account. The dependency is bound by CONTENT
  — `ModuleSet` keys on `Module::stable_digest` and ignores `ModuleImport::name`
  — so the same bytes under a lying filename pass, and a dependency rebuilt
  under the same name does not. The digest the CLI measured is printed, so an
  operator can compare it with the one the producer recorded rather than
  trusting either.

  Two decisions: WITHOUT the flag, a module carrying import rows reports them
  UNCHECKED with each name/digest/producer (`UNRECORDED` when absent) and the
  exit code is unchanged — the `None`-is-not-a-wildcard rule applied to a whole
  table, the shape `--bundle` already uses. WITH the flag the linked verdict
  REPLACES the structural one instead of being folded in with `.max()`, because
  `validate_one` runs `validate_module_filtered` on the root as its own step L8
  and the walk is therefore a strict superset; folding it in made a correctly
  linked client permanently red, since a cross-crate `Discharged` row is
  ungrounded by construction at the faith floor and that is the refusal the walk
  exists to discharge. Nothing is softened: every error the floor raises, L8
  raises. Six tests (`crates/trust-ir-cli/tests/cli_linked_imports.rs`), whose
  fixtures are real — the dependency's `Certified` row carries a `CleanCic`
  certificate the in-process Clean kernel re-checks.

- Binary **v43** — `Ty::Handle(Box<HandleTy>)`, the nominal opaque runtime
  handle (type tag 38, `HANDLE_TYPE_FORMAT_VERSION`), read-gated on
  `version >= 43` and selected by the writer only when a handle occurs, so
  every existing golden keeps its bytes — the remote's pushed v42 tuple
  goldens included, which is why the handle number moved: this batch was
  developed as v42 while origin shipped its own v42 (declared tuple layouts),
  the second version collision of this program after v39, and the pushed,
  goldened tuple layouts keep 42. NO new section: a handle is a row of the
  TYPE table, written ahead of both the v41 imports section and the v42 tuple
  table, so a module carrying both writes v43 with nothing reordered.
  Explicit `RawV38` / `CanonicalV38`
  projections refuse it (`HandleTypeRequiresV43`). Identity is the exact
  `(name, runtime)` pair (`("Nat", "trust_bignum::Nat")`), spelled
  `handle<"Nat", "trust_bignum::Nat">` in text and preserved by JSON and
  MessagePack. One pointer word at the machine level, NOT pointer-like and
  never equal to `Ptr`. `trust-ir-build` pins the trusted runtimes
  (`TRUSTED_HANDLE_RUNTIMES`, `HandleRegistry`,
  `validate_module_with_handle_registry`) and refuses every forgery by name:
  `InvalidHandleType`, `UntrustedHandleRuntime`,
  `HandleEntryPointSignatureMismatch`, `HandleEntryPointDefinedLocally`,
  `HandleEntryPointShadowedByGlobal`, `HandleEntryPointAddressTaken`,
  `HandleForeignDeclaration`,
  `InvalidHandleUse`; `ModuleBuilder::declare_handle_runtime` emits the pinned
  declarations. `NominalTypeReachability` (dialect + handle bitsets in one
  pass) generalizes `DialectTypeReachability`. Lean mirror `Ty.Handle`;
  conformance goldens `ty_dialect_v39` and `ty_handle_v43`. Ratified in
  `docs/SPEC_RATIFICATIONS.md` §7.
- Binary **v42** — `Module.tuple_layouts`, the declared tuple-layout table
  (`TUPLE_LAYOUT_FORMAT_VERSION`), an additive TRAILING section after the v41
  imports table: a descriptor count, then per descriptor the tuple `TyId`, its
  `size`, its `align`, and one `field_offsets` entry per element in LOGICAL
  order (which may differ from physical order). A nonempty table selects v42
  and nothing else does, so a module with no descriptors keeps its prior exact
  bytes; read-gated on `version >= 42`, and the explicit `RawV38` /
  `CanonicalV38` projections refuse it (`TupleLayoutRequiresV42`). It is the
  sole trailing conditionally-skipped serde field, which is why `imports`
  stopped being skipped in the same change.
  **Why the format needed it:** a structural `Ty::Tuple` had no declared memory
  layout, and the interpreter's natural-C computation is not rustc's — the test
  compiler lays `(u8, u64, u8)` out differently in both offsets and total size —
  so the Rust producer had to DECLINE every tuple-bearing enum payload rather
  than assert a layout it could not back. The table carries the producer's
  concrete source-order offsets instead of inviting a consumer to recompute
  them. Structural coherence is NOT a source-layout refinement certificate: a
  producer must separately bind a descriptor to its source, and absence of a
  row keeps the old layout-evidence refusal rather than licensing a guess.
  Consumed by `Module::tuple_layout_descriptor` / `ty_layout_shape` and the
  reference interpreter's byte funnels; carried losslessly by all four formats
  (text: the `tuple_layout ty.N size= align= offsets=[…]` directive) and
  included in `stable_digest` / `executable_content_digest`. Semantic diff
  compares descriptors, their structural type identity, unused rows and
  descriptor multiplicity, and its CLI rejects a malformed table.
  `validate_module` refuses an incoherent one as
  `ValidationError::TupleLayoutInconsistent` — a descriptor whose `tuple_type`
  is absent or is not a `Ty::Tuple`, or two rows for structurally equal tuple
  types (`tuple_layout_descriptor` never picks the first of two conflicting
  declarations) — with the type-table and declared-tuple recursion guards both
  failing closed independently. Conformance goldens `declared_tuple_v42.{tmbc,
  trust_ir,json,msgpack}`.
  **Downstream state, measured 2026-09-16** (the field's own design note
  predates all three and said none of it had happened yet). The Rust producer
  MINTS descriptors: `trust-thir-lower` reads rustc's own
  `layout.fields.offset(i)`, re-checks each field against
  `Module::ty_layout_shape` before pending the row, refuses a conflicting
  second observation of one tuple type, and `tuple_layout::merge` preserves
  and re-interns the rows across the crate-assembly splice (refusing a target
  mismatch or an unmappable type) rather than dropping them. No NATIVE code
  generator consumes them: trust-cg's shared adapter floor REFUSES a nonempty
  table outright (`AdapterError::DeclaredTupleLayoutUnsupported`, naming the
  row count) because its legacy declaration-order tuple lowering does not read
  physical offsets — which is the correct fail-closed posture, since the
  hazard is a backend that accepts a descriptor and then lays the tuple out in
  natural C order. No G1-G8 acceptance gate is claimed for the table. This
  bullet was written after the fact: the wire ledger jumped v41 → v43 and v42
  was named only in passing inside the v43 entry, because the two versions
  were developed on lines that collided (see the v43 bullet's numbering
  note).
- `trust_ir::imports` (`Module::verify_import`, `Module::resolve_extern_ref`,
  `ty_structurally_eq_across`, `signatures_compatible`) and
  `trust_ir_build::validate_linked_module` (with `ImportResolver`,
  `ModuleSet`, `LinkedValidationReport`, `AuthenticatedImports`): re-earned
  cross-crate verdicts. Every `proved` `backed_by` and every
  `InheritedFromCallee { external: Some }` is authenticated against the
  dependency module's `stable_digest` under the fixed domain
  `MODULE_IDENTITY_DOMAIN` (`trust_ir.module.v2`, ratified with its bump path
  in `docs/SPEC_RATIFICATIONS.md` §6), never a name; the dependency is
  validated under the same rules; an inheritance must restate a
  kernel-grounded far obligation and is admitted into the `Discharged` tier
  only. `validate_module_with_authority` /
  `validate_module_report_with_authority` now refuse unauthenticated
  proof-bearing imports (`ValidationError::UnauthenticatedImport`);
  `validate_module` is unchanged (structural faith floor).
  `ModuleValidationReport::proof_bearing_imports()` lists the imports a
  consumer must supply. New `ValidationError` variants: `UnauthenticatedImport`,
  `ImportUnavailable`, `ImportedModuleInvalid`, `ImportCycle`,
  `ImportClosureTooDeep`, `ExternInheritanceRestatementMismatch`. No wire
  change: `VERSION` stays 41 and every golden is byte-identical.
- `trust-ir-contract`: the SMT-LIB `Real` sort (`Sort::Real`, with
  `Sort::is_real`) and the exact-rational literal `Formula::Rat(RatLit)`
  (`RatLit { num, den }`: canonical decimal strings — arbitrary precision,
  zero new dependencies — whose syntax is enforced by the only constructor
  `RatLit::new` AND on deserialization via `serde(try_from)`, so a decoded
  literal always parses exactly; the checked constructor `Formula::rat`,
  `Formula::rat_from_int` and `Formula::rat_parts`; renders as the
  `Reals`-theory term `(/ num den)`). Both are APPENDED after the last
  existing variant, so no existing `Sort`/`Formula` variant index moves, and
  the newtype payload encodes exactly as a two-string struct variant would.
  Motivation: a `Real`-sorted variable ranges over ℝ, so a consumer must not
  apply integer reasoning (strict-bound tightening, integrality cuts) to an
  ordering atom over it. Trust's `trust-ny-bridge` previously encoded ny-cert's
  real-valued Farkas systems over `Sort::Int`, which certified integer
  infeasibility of systems that are feasible over the reals; the `Real`
  vocabulary is what lets that bridge state — and the clean kernel check — the
  real claim.
- BREAKING (additive wire): binary v41, the two-language contract surface. The
  writer selects v41 only when a module uses one of these features; every other
  module keeps its exact v38/v39/v40 bytes, and every v41 read is gated on
  `version >= 41`. Explicit `RawV38`/`CanonicalV38` projections refuse v41
  content with `BinaryProjectionError::ContractSurfaceRequiresV41`.
  - **Codegen license:** `Function.body_gate` is a mandatory three-valued tag
    (`None` / `Ungated` / `Gated` + authority), and `Function.display_path` is
    split out because `Function.name` is normatively the link-time symbol
    (enforced by `DuplicateFunctionSymbol`).
    `trust_ir_build::validate_module_for_codegen` refuses unlicensed and
    ungated bodies.
  - **Typed contract clauses:** `ProofFormula.bindings` gives each free name a
    sort and an IR place; empty bindings mean unbindable, never a wildcard.
    Also added: `FunctionSummary.decreases`, `ObligationKind::{Termination,
    Ownership, Custom}` (tags 13–15), and `ProofCertificate.assurance`.
  - **Cross-crate identity:** the `Module.imports` table, `ExternRef`,
    `FunctionSummary.backed_by`, and cross-crate
    `ProofEvidence::InheritedFromCallee` at new evidence tag 8. A v40 reader
    refuses it rather than misreading it as local.
  - **ABI/linkage residue:** `Linkage` tags 5–8, a `Visibility` enum,
    `Global.{section, visibility, retained}`, `FuncAttrs.{naked,
    target_features}`, and `Module.global_asm`.

  Obligation formulas now share the single formula encoder.
  `obligation_content_digest` moves to domain `v6`, which carries both the IR
  `site` and the new contract content (`decreases`, `bindings`, `Custom`
  namespace/name). This batch was developed as an unpushed "v39" on a diverged
  line, so no blob carries that labelling. The conformance corpus gains the
  `body_gate_v41` golden (header 41).
- BREAKING (additive wire): binary v40 adds `FatPtrKind::ContainerVtable` at
  fat-pointer-kind tag 4, read-gated on `version >= 40` — the `dyn`-tail
  sibling of v38's `ContainerLen` (`*const ArcInner<dyn Any>` inside
  `Arc<dyn Any>`), with `PointerMetadataShape::ContainerVtable`, text spelling
  `fatptr<container_vtable>`, stable digest tag 4, and the new projection
  refusal `BinaryProjectionError::ContainerVtableRequiresV40`. The writer
  selects v40 only for modules carrying the kind; legacy modules keep their
  exact v38 bytes and dialect-only modules their v39 bytes. Historical
  seal-line "v39" blobs carrying fat-kind tag 4 are NOT readable (they were
  never released; v39 means nominal dialect types only). The conformance
  corpus gains the `ty_container_vtable` golden (header 40).
- Structural dialect schemas accept module-independent exact function-signature
  operand patterns. `FunctionBuilder::dialect_results` provides checked,
  allocation-efficient fixed-result emission. Typed callbacks and the API
  migration are in the internal doc `docs/dialect-function-operands.md` (not
  in the public snapshot).
- Nominal `Ty::Dialect` identities and a shared allocation-free-on-unary-path
  type inventory support semantic IR in ordinary calls and CFGs without
  inventing machine representations. Module validation rejects malformed
  identities, mismatched transport, scalar/cast/memory use, and nominal
  indirect callees. Binary v39 adds type tag 37; legacy-only modules retain
  their exact v38 bytes and hashes. Text/JSON/MessagePack preserve the same
  exact namespace/name/nonzero-version identity. Nominal types require
  explicit legalization before Core and carry no proof authority themselves.
- `format::into_canonical` canonicalizes a producer-owned module without a
  full-module clone, enabling one-time canonical preparation before proof and
  cache identities are bound.
- `FunctionBuilder::reserve_block_params` provides a move-only, checked
  construction scope for frontends that know future join-parameter counts. It
  lets them allocate the canonical block-parameter ValueId prefix before
  instruction emission, avoiding fallback value remapping caused solely by
  late parameters when result order is otherwise canonical, while granting no
  validation or proof authority.
- `ProofCertificate::assurance` is RE-DERIVED, not merely carried.
  `trust_ir_build::coverage_assurance_report` + `validate_module_with_bundle`
  (and `trust-ir validate --bundle <b.json>`) check a module's recorded
  `CoverageAssurance` rows against the `NativeVerificationBundle` they cite:
  the bundle must be this module's (`NativeBundleNotForThisModule`), the
  `request_digest` must equal `NativeVerificationRequest::stable_digest` for
  some request in it (`CoverageAssuranceRequestUnknown`), that request must
  carry the certificate's obligation
  (`CoverageAssuranceObligationNotRequested` — the cross-wiring a digest alone
  does not catch), and where the bundle DETERMINES a bound (a TrustMc
  `BoundedModelCheck`'s `unwind_limit`) the recorded bound must equal it
  (`CoverageAssuranceBoundMismatch`). The row's rustdoc had stated that
  contract since v41 while nothing in the repo read the digest outside the
  codec, so a `UnwindBounded { depth: 1 }` certificate and an `Unbounded` one
  were operationally indistinguishable. With NO bundle nothing is checked and
  `CoverageAssuranceReport::is_checked()` is `false`, `agreed()` is 0 and
  `summary()` says UNCHECKED in words — absence is never agreement (the
  `Unrecorded`/v34-`site` precedent). CHC/PDR/TrustWp/TrustVc record a METHOD
  rather than a bound, so their bound is deliberately left unchecked instead
  of guessed at; such a row is counted by
  `CoverageAssuranceReport::undetermined()` and NOT by `agreed()`, and
  `summary()` names it, so the same absence-is-never-agreement rule holds at
  ROW granularity too. `recorded() == agreed() + undetermined() +
  errors().len()` on every checked report, and a consumer that needs the bound
  ESTABLISHED admits only on
  `is_checked() && errors().is_empty() && undetermined() == 0`. No wire
  change. The remaining half — a
  `validate_linked_module` rule refusing an IMPORT whose cited discharge is
  bounded where the importer's claim needs unbounded — stays open.
- `ObligationKind::Custom`'s namespace is admitted from a PINNED list.
  `ADMITTED_OBLIGATION_NAMESPACES` + `is_admitted_obligation_namespace`, with
  `ValidationError::UnpinnedCustomObligationNamespace` reachable from
  `validate_module`; membership is byte-exact, never a prefix or case-folded
  test, so `trust.vc.hardened.evil` cannot inherit the hardened lane's routing
  capability. `name` is deliberately not sealed. `CLAUDE.md` had called the
  namespace authority-bearing while every `Custom` site in the crate was codec
  or digest. The seed is a MEASUREMENT of the sibling crate that owns the
  vocabulary (`trust_verifier_api::ADMITTED_OBLIGATION_NAMESPACES`, six
  namespaces) rather than a preference, and WHICH namespaces are pinned stays
  an owner-revisable decision; measured the same day, no producer in the
  constellation constructs a `trust_ir` `Custom` obligation at all, so the
  fixture strings in use (`trust.concurrency`, `vendor`) are deliberately
  unpinned and are exactly what the rule refuses.
- `Module::global_asm` is refused with codegen intent.
  `codegen_global_asm_errors`, composed into `validate_module_for_codegen`,
  reports `ValidationError::GlobalAsmNotConsumable { blocks }`; `validate_module`
  keeps ACCEPTING such a module, because carrying opaque assembly is
  well-formed — the `body_gate` split exactly. The normative "a consumer must
  refuse rather than silently drop" rule had no enforcement point in this repo
  (zero `global_asm` references under `crates/trust-ir-build/src`); this puts
  the refusal at the format boundary where it can name the reason, beside the
  one trust-cg's adapter floor already makes
  (`AdapterError::GlobalAsmUnsupported`).
- `docs/SPEC_RATIFICATIONS.md` §1.1 names the def identity a module-level
  uniqueness rule may key on: the LINK-TIME SYMBOL, via
  `DuplicateFunctionSymbol`. A duplicate-`display_path` rule is explicitly
  DECLINED rather than deferred — §1 makes generic function identity the
  monomorphic pair *(definition path, concrete GenericArgs)*, so
  `Vec<i32>::push` and `Vec<u8>::push` share a def-path by ratification and
  must be two rows. The same boundary is now stated on the variant's rustdoc,
  so the residual cannot later be re-read as asking for the rule §1 forbids.
- `docs/SPEC_RATIFICATIONS.md` **§8 — the opaque kernel-`Expr` obligation
  carrier**, which reconciles a documentation incoherence rather than changing
  code. The §9 restatement in the Trust repo's two-language design of record
  (`2026-08-27-two-language-direct-to-trust-ir.md`) forbids
  *"no `Π`/`λ`/`Prop` carrier … in trust-ir"*, while
  `ProofAnnotation::Goal(Box<ExprObligation>)` has carried `clean_kernel::Expr`
  values since the 2026-06-20 fusion design and is reachable in the DEFAULT
  `trust-ir-build` build (`default = ["clean-tv-anchor"]` →
  `trust-ir/clean-expr`). §8 ratifies the carrier as a NAMED EXCEPTION with its
  boundary instead of weakening the rule: the ruling §9 claims to restate
  (08-04 §2) forbids a *dependent CIC core*, and TrustIr has none — no `Prop` /
  universe / `Π` / `λ` in `Ty` or `Inst`, no typechecker and no reducer in
  either crate; `trust-ir-build` INVOKES `clean_kernel`'s `TypeChecker`
  in-process. The boundary table is measured, not asserted: the term is
  filtered out of the canonical binary wire and the digest domain
  (`write_proof_annotation_list`, whose per-annotation `Goal` arm is
  `unreachable!`), renders as `goal(N hyps)` in text/`Display`, is refused off
  the pinned proven subset in `bridge.rs`, and does not exist at all in the
  default `trust-ir` build — it reaches serde JSON/MessagePack and nothing
  else. The opposite resolution (making `clean-tv-anchor` default-off) is
  recorded as considered and REJECTED: the feature's own Cargo comment says the
  anchor then FAILS CLOSED, so it would trade the only in-process kernel
  re-check of Clean's backend translation validation for a restatement broader
  than its own ruling. The one-line §9 amendment §8 names is the owner's to
  make in the Trust repo; nothing outside TrustIr was edited here.

- **Linked rule L9 — cross-crate coverage monotonicity**, the half the
  residual ledger named as deliberately left open beside the v41
  coverage-assurance re-derivation: *"the `validate_linked_module` rule
  refusing an IMPORT whose cited discharge is Unrecorded/bounded where the
  importer's claim needs unbounded is a different table and a separate rule."*
  `validate_linked_module` now compares what a cross-crate claim NEEDS against
  every `CoverageBound` the dependency's certificates record for the cited far
  obligation, and refuses a shortfall by name
  (`ValidationError::ImportCoverageBelowClaim`, carrying the import, the site,
  the far obligation, the demand with its justification, and the far bounds
  actually found). No wire change; `validate_module` cannot check it because it
  holds no dependency module, and the rustdoc that used to say this stayed open
  now points at where it landed.
  **The demand per site kind.** A `backed_by` summary needs
  `CoverageBound::Unbounded`: `FunctionSummary::proved` is a bare bool whose own
  rustdoc says a caller may ASSUME the `ensures`, with no restriction on inputs,
  so a re-stated `proved` claims all of them — a producer wanting to publish a
  bounded contract leaves `proved` false or carries the claim as an inheritance
  certificate. An inheritance needs exactly the bound its own `assurance`
  records; `assurance: None` claims no grade and so demands none, which is
  sound as a REFUSAL rule because a fail-closed consumer already reads that row
  as UNKNOWN rather than as `Unbounded` — but it is not free: such a site is
  counted as UNRECORDED, never as supported, so omitting the field buys silence
  and never standing.
  **The supply is every recorded bound, and every one must meet the demand.**
  An obligation may legally carry several certificates — uniqueness is only
  over `(obligation, prover)`, and `Certified` needs one matching `CleanCic`
  row — so an `any` quantifier would let a producer LICENSE a stronger
  downstream claim by ADDING a decorative certificate nothing replays: a
  depth-1 kernel discharge beside an `Unbounded` sibling would re-earn
  unbounded standing across the edge. The weakest-link reading is monotone in
  the safe direction (adding a row can only refuse more), and an obligation's
  recorded coverage is therefore its weakest certificate's.
  **"At least as strong" is a PARTIAL order, spelled per pair**
  (`trust_ir_build::coverage_supports`, with the full table in its rustdoc and
  all sixteen pairs plus the magnitude cases pinned by
  `coverage_supports_is_the_ratified_partial_order_over_every_pair`):
  `Unbounded` supplies every demand; same-axis compares by magnitude
  (`UnwindBounded { depth: 9 }` supplies a depth-7 demand, not the reverse);
  the two bounded rungs are INCOMPARABLE at every magnitude, because a
  loop-unwinding depth is not evidence about a finite model size — folding them
  into one integer is the bug the rule exists to prevent; neither bounded rung
  supplies an unqualified claim; and `Unrecorded` IS NOT A WILDCARD as a
  supply — it supplies no positive grade, not even `UnwindBounded { depth: 0 }`,
  which is still an affirmative statement about what was explored. A demand of
  `Unrecorded` is met by anything, including itself: the asymmetry between the
  row and the column is the point. A `CoverageBound` variant this build does
  not enumerate fails closed in the supply position, on the discipline
  `ExternRefSite::admits` already sets for an unknown `ObligationKind`.
  **The grandfather state is counted, not silently accepted.** A far obligation
  whose certificates record NO bound at all is distinguished from an explicit
  `CoverageBound::Unrecorded`, which is refused against any POSITIVE demand —
  the v41 `body_gate` three-valued precedent, where "no claim" and
  "affirmatively none" are different states. Nothing in the fleet stamps
  `assurance` yet, so refusing the absence would fail every module produced
  today, and reading its silence as support would be the unsound half of the
  same choice. New
  `LinkedValidationReport::{coverage_supported, coverage_unrecorded,
  coverage_refused, coverage_summary}` make it visible on the
  `CoverageAssuranceReport::undetermined` precedent, and the admission rule is
  stated: a caller that needs coverage ESTABLISHED admits only on
  `report.is_ok() && report.coverage_unrecorded() == 0`.
  `coverage_unrecorded()` counts BOTH not-established states — no far record,
  and a local row with no grade of its own — and spans the whole import
  CLOSURE, not just the root: a dependency's unrecorded site is not an error,
  so unlike an insufficiency it can never arrive folded into
  `ImportedModuleInvalid`, and a root-only counter would report a closure as
  fully established while the root's standing chained through a dependency's
  unqualified `proved` whose own far coverage was never recorded.
  **What L9 does not check.** It compares the dependency's SELF-REPORTED
  `assurance` against the local demand and structurally cannot re-derive it: an
  `ImportResolver` yields a bare `Module`, never the `NativeVerificationBundle`
  a bound is projected from. Faithfulness of a recorded bound stays
  `coverage_assurance_report`'s rule over a different table, run per module
  with the bundle in hand. L9 closes the laundering edge — recorded coverage
  does not grow across an import — not the far producer's honesty about its own
  discharge.
  A refused site records `SiteOutcome::Reported`, so an inheritance with
  insufficient coverage is not admitted and cannot ground its own restatement —
  pinned by a test that checks `authenticated_certificate_refs()` and
  `validated_root()` are both `None`, because an error that left the claim
  admitted would be a report rather than a rule.
- **The handle RELEASE entry point** — `trust_bignum_nat_drop: (H) -> ()`, a
  fifth row on the pinned `("Nat", "trust_bignum::Nat")` runtime, retiring
  §7's *"v1 handles are never released … recursion-shaped `Nat` code is
  correct-by-leak"* non-ratification. Validator-only: **no wire change**
  (`VERSION` stays 43) and every conformance golden is byte-identical (212
  fixture files, SHA-256 unchanged), because the `ty_handle_v43` fixture now
  declares the four roles its body CALLS through the new
  `ModuleBuilder::declare_handle_runtime_roles` instead of the whole row — a
  producer declares the symbols it calls, so a pin-table addition it does not
  use cannot move its bytes. The empty return list is deliberate: `(H) -> ()`
  and `(H) -> Unit` are different `FuncTy`s and the real
  `extern "C" fn(*mut Nat)` shim has no result.
  **Two of the three rules needed no new code, which was measured before it
  was claimed.** (1) A call to the pinned release symbol was already admitted:
  the transport rule keys on the DECLARATION being pinned, not on which
  direction a handle flows, so `Call` to `trust_bignum_nat_drop` goes through
  the same arm as `add`. (2) `Retain`/`Release`/`IsUnique`/`Dealloc`/
  `HeapAlloc` at a handle type were already refused as `InvalidHandleUse` by
  the handle arm's whitelist catch-all (`HeapAlloc` via an inline type,
  `Dealloc` via an operand); `Retain`/`Release`/`IsUnique` were already pinned
  by test, and `Dealloc`/`HeapAlloc` are pinned now. (3) An off-pin release
  declaration is `HandleEntryPointSignatureMismatch` and a second
  release-shaped symbol (`trust_bignum_nat_free`) is
  `HandleForeignDeclaration`, so the pinned symbol is the only way out.
  **Singularity is by construction.** `HandleRegistry::from_pins` refuses a
  row carrying two consuming entry points as
  `HandlePinError::MultipleReleaseEntries` — without it the two tests that
  assert "the release entry point" is singular were the only thing holding
  that property, a second `(H) -> ()` row built a valid registry, and both
  SPEC §7's "the pinned release symbol is the ONLY way out" and TRUST.md item
  9's single trusted at-most-once row quietly became false.
  **Double release and use-after-release are NOT detectable in TrustIr, and
  that is now stated rather than implied.** A handle is an opaque word with no
  IR provenance and §7's transport set admits `Copy`/`Select`, so handle
  values are deliberately non-linear — two SSA values may denote one
  allocation. Deciding "released exactly once" would need a linear discipline
  plus a per-parameter "consumes" contract the format does not have, and a
  release inside a callee is invisible to an intraprocedural rule anyway. Two
  tests PIN the non-guarantee (a double release and a use-after-release each
  validate), `TRUST.md` item 9 grows a part (c) for handle lifetime, and the
  trusted base is one row larger rather than one guarantee stronger.
  The shim side is a cross-repo contract: measured 2026-09-17, `trust-bignum`
  exports the original four and not yet `trust_bignum_nat_drop`, so a module
  calling it validates and fails to LINK — the same loud state the other four
  passed through, never a silent mis-execution.
- **The 2026-09-17 two-language proof program is under version control
  (roadmap WS8.1).** Its battery, evidence and 131-finding inventory existed
  only in a cache directory whose own report named `rm -rf` as the cleanup
  step. The sources and small text outputs are now archived in the private
  `reports/2026-09-17-two-language-proof-program/` directory, about 14 MB of
  text. That covers Part A, Part A-Lean, Part B, the 15 claim repro crates
  with their skeptic notes, the only G8 measurement, the scouts, the HEAD
  re-run and the raw evidence JSON. No build products are archived, and
  `repair_fndef.py` is left out because it corrupts correct modules. The
  directory is excluded from the public snapshot. Its `check_archive.sh` runs
  three gates, and each gate runs a twin that must fail:
  - the `MANIFEST.sha256` check, where a one-byte edit must fail;
  - a row-resolution check, which maps all 586 cited row ids to archived
    evidence (without `evidence/verify.json`, every `rerun.*` row must come
    back unresolved), and a cited-paths check, which requires every cache
    path an evidence document names to be archived or to be a named
    not-archived row (without `critic/targets/`, that path must come back
    unresolved);
  - the publish-manifest export, which must contain no archived path (with
    `reports/` allowlisted, it must contain all of them).

  Every archived `Cargo.toml`/`Cargo.lock` is stored as `*.archived`,
  byte-for-byte: under live names those historical Clean pins are tracked
  build inputs that the undeclared-pin census (gate 0) refuses. No crate, wire
  format or golden changes.

### Fixed

- **Stage 0 of turning Trust verification on: the locally-true refutations the
  2026-09-29 verified survey found are fixed where they live, all but the
  conformance fixture's id-space panic (below), and gate 0's authority
  checker stops misreporting (2026-09-29).** Each fix is backed by a test,
  not a proof; the verified-lane row census before/after is recorded in the
  commit.
  - `trust-ir-ay`: a bit-blast certificate whose `goal_digest` was not a
    digest (21 euro signs and a `0` are 64 bytes; byte 16 is inside a
    character) PANICKED the validator in gate (8)'s refusal message instead
    of being refused. `BvBlastCertPayload::from_bytes` now refuses every
    spelling but 64 lowercase hex with the typed
    `BvBlastPayloadError::MalformedGoalDigest`, against the core's one
    spelling rule `trust_ir::proof::is_bvgoal_digest_hex`, and every digest
    prefix in a message goes through the total `digest_prefix`.
    `MemoryModel::encode_alloca` is a checked bump allocator returning
    `Result`: the fixed 0x1000 stride overlapped any alloca larger than 4 KiB
    with the next one (a `<1024 x i64>` slot in the whole-function VC), the
    counter product wrapped at 2^52, and a wrapping size asserted a false
    no-wrap constraint. `encode_store` refuses a value wider than a `u32`
    bit width before any solver work; the three `eb + sb` copies are one
    checked `sort_bit_width`; a vector's concatenated width is checked; and
    `encode_vector_binop` refuses zero lanes (an index panic before) and
    folds lanes instead of pre-allocating `lane_count` slots.
  - `trust-ir`: `Module::next_obligation_id` is the one checked "one past the
    highest id" rule, and `Module::add_function`, `trust-ir-build`'s
    `mint_summary_obligations` and the conformance fixture
    `build_proof_annotations` allocate through it. What that changes is
    narrower than a fix. `mint_summary_obligations` wrapped silently in
    release before (an unchecked `+ 1`, minting ids that can collide with
    existing rows) and now panics by `add_function`'s name; both still panic,
    rather than return an error, when a row holds `u32::MAX`, which a decoded
    module can carry. The fixture's refuted `index() + 1` is NOT fixed: the
    same panic, under the same condition, moved to a named `expect` the
    verified lane has not examined (the function exhausted its per-function
    budget in both measured runs); the condition cannot arise in the table
    the fixture builds from scratch, so it is a fixture invariant for stage
    1's ledger. The fixture's bytes are unchanged.
  - Gate 0 (`scripts/check_trust_default_authority.py`): rustup is found in
    `$CARGO_HOME/bin` / `~/.cargo/bin` and its absence is the one failure
    `rustup not found` (four misleading FAILs before, in any shell without
    `~/.cargo/bin` on PATH); policies are compared as DISTINCT values (ay's
    host/target/rustdoc copies of one certify policy were "ambiguous"); only
    `-Ztrust-verify=` is read as the activation flag and every other
    `-Ztrust-*` flag is held to the closed table
    `AUDITED_STRENGTHENING_FLAGS` (ay's `-Ztrust-verify-level=2` and two
    other knobs were nine false "disables verification"; `-Ztrust-dump=
    mir-only:`, which skips solver dispatch, was admitted); and a configured
    policy is printed with its scope — it binds rustup-proxied builds only,
    `targo trust` ignores it (measured on 321aaeda7). Red on the old checker,
    green now, in `scripts/tests/test_trust_default_authority.py`.

- **A bool-lane `Bitcast` / `Transmute` is refused by name in both validator
  entry points and by the layout authority (F-161).** A trust-cg session
  measured `Ty::bit_width(<8 x bool>) = 8` against
  `Module::ty_layout_shape(<8 x bool>).size_bits = 64` and read the 8× as
  the function-only validator and the module-level layout gate disagreeing.
  They answer two spec questions — the VALUE width (Lean `Ty.bitWidth`:
  `Bool ↦ 1`, a vector ↦ lanes × element) and the STORAGE size (Lean
  `Ty.byteSize .Bool = 1`; the normative interpreter's `byte_size` is one
  byte per lane, all-ones per true lane) — scalar `bool` carries the same
  1-vs-8, and `bool` is the only element type for which the two differ.
  Neither sizing path changed. What did change is the one consumer that
  conflated them: `validate_function` admitted `bitcast <8 x bool> -> u8`
  (and `<64 x bool> -> ptr`) on value width while `validate_module`
  admitted `bitcast <8 x bool> -> u64` on storage size, and the reference
  interpreter (`eval_bitcast`), the Lean `semCast .Bitcast` arm and trust-cg
  refuse every one of them. Now a non-identity `Bitcast`/`Transmute` with a
  bool lane stored by value on either side is
  `LayoutError::BoolLaneReinterpret`, reported as `CastLayoutUnsupported`
  with that one spelling from both entry points; by-value table references
  (`Array`, `Refine`, struct/enum fields, tuples) are followed as the layout
  walk follows them, pointer edges are not. No producer emits such a cast
  (trust-ir-bridge emits no vectors; trust-cg's adapter refuses every vector
  bitcast). Pins: `trust-ir/tests/bool_lane_width_vs_layout.rs` (both
  numbers for `<n x bool>`, n ∈ {1, 2, 4, 8, 16, 32, 64}; every non-bool
  type agrees; the authority's refusal and its identity / pointer / non-bool
  controls) and `trust-ir-build/tests/bool_lane_bitcast_refusal.rs` (both
  entry points in both directions, the interpreter's own refusal, the
  controls); both registered in gate 9.
- **WS4.6 — `trust-ir run`: authenticated imports, no proof claims in the
  execution image, validation as linked and after lowering, pinned handle
  entry points never stubbed** (F-067, F-083; source rows b4.uf10, b5.uf06).
  Four holes in the CLI linker, none on the wire.
  *Import digests were ignored.* The linker bound by function NAME and never
  read `Module.imports`, so a root pinning one dependency ran against a rebuilt
  one and printed its value. Every input is now hashed once
  (`HashedModule`); each import row must match the `stable_digest` of a linked
  input and then pass `Module::verify_import_hashed` (name, producer, target).
  A row no input matches is refused, naming the row, its digest and every
  input's digest; a C4–C6 failure prints the `ImportVerificationError` text.
  `--unauthenticated-imports` skips the check and prints
  `imports: N row(s) UNCHECKED (execution only; this is not agreement)`.
  *The image kept claims it had dropped the backing for.* Obligations and
  certificates were dropped by design but `Function.summary` was copied, so any
  honest `proved` module failed `run --validate` with `InvalidFunctionSummary`,
  even alone. The image now carries no proof claims: summaries, every
  `ProofRef` (function- and node-level) and every call `ProofContext` are
  stripped and counted (`stripped K summaries / J ProofRefs / C call proof
  contexts`); claim-style annotations, `body_gate` and `display_path` are still
  copied. The call-context strip goes beyond the roadmap's text for the same
  reason: each would otherwise dangle as `ProofContextUnknownObligation`.
  *Validation ran only on the lowered image.* `--validate` now checks the image
  AS LINKED first (the artifact verdict: exit 1,
  `linked image is well-formed (as linked)`) and KEEPS the check after
  devirtualization, compare legalization and builtin synthesis, relabelled
  `internal: CLI interpreter lowering produced an invalid image` with the new
  exit code 3 (`EXIT_INTERNAL`). Moving the check instead would have left the
  image the interpreter executes unvalidated.
  *Pinned entry points were stubbed.* Builtin synthesis gave every bodyless
  extern a trap-stub body, pinned handle entry points included, which made the
  image define a pinned symbol (5x `HandleEntryPointDefinedLocally` under
  `--validate`) and made the run trap. They now stay bodyless (only their
  entry id moves into a reserved range), and reaching one is the named refusal
  `error: reached trusted-runtime entry point @trust_bignum_nat_from_u64 — the
  reference interpreter has no host implementation (TRUST.md item 9; host hook
  is WS2/F-035)`, exit 1. Executing the program is still open (F-035).
  One exception keeps a valid input valid: a contract-only bodyless declaration
  with non-external linkage (valid ONLY because it carries a summary, audit F4)
  keeps the claim-free EMPTY summary — no clause, not `proved`, no backing — so
  the linker's own strip never turns it into an `EmptyFunction` as linked.
  Naming the entry itself as a pinned entry point is the same named refusal.
  Review additions (`cli_run.rs`): rows of EVERY input are authenticated (a
  rebuilt leaf under an unchanged mid is refused naming mid's row); a
  digest-matched row with no recorded producer is the C5 refusal, not "no
  match"; the honest pair authenticates through JSON and MessagePack as
  through binary; a forged pinned symbol is refused AS LINKED (exit 1,
  `HandleEntryPointSignatureMismatch`), never `internal:`; the Internal
  contract-only declaration runs under `--validate` while its summary-free twin
  is `EmptyFunction`. The WS8.7 CLI repros c12 rows 2 and 4 and c11 row 4
  (`cli_verify_repros.rs`) are flipped. Tests: `cli_run.rs` (honest proved pair,
  single proved module, stale-digest twin, the escape flag, a name-mismatch
  row, the `ProofRef` / `ProofContext` strip, the `Nat` program with and
  without `--validate`, its handle-free analog); `run.rs` unit tests (the
  synthesis skip and its id mapping, the post-lowering pass refusing
  re-stubbed pinned entries with exactly five `HandleEntryPointDefinedLocally`,
  the strip counts); the flipped `two_language_cli` rows. Mutation controls, each run
  and reverted: re-copying `summary` fails the honest pair with two
  `InvalidFunctionSummary`; re-stubbing pinned entries makes the post-lowering
  pass report five `HandleEntryPointDefinedLocally` (`internal:`, exit 3);
  deleting the pre-lowering pass drops the `(as linked)` line; keeping
  `ProofRef`s gives `ProofRefUnresolved`; skipping authentication runs the
  stale pair.
- **WS2.6 — `Switch.exhaustive_enum_unreachable` has a validator reader and an
  honest doc** (F-039; proof-program row `b6.switch.exhaustive_claim_unchecked`,
  audit `verify.c15` 2a/2b). Nothing read the flag, so a switch with a LIVE
  default arm, or one over an enum whose case set omitted an inhabited variant,
  could carry it and validate for codegen — and a consumer that conjoins
  `selector ∈ {cases}` into the default arm makes such an arm vacuously
  provable. Two rules (`trust-ir-build` `validate::exhaustive_switch`), each
  stating only what it checks. Rule 1, function-local (so `validate_function`
  and `validate_module` agree): a flagged switch's default edge carries no
  arguments, its default block has no parameters and is exactly
  `[Unreachable]`, and its case values are distinct as selector values (`0`
  and `256` at `u8` are one case, as are `0` and `2^64` at `usize` and `65`
  and `2^32 + 65` at `char`; a syntactic repeat stays
  `DuplicateSwitchCase`, never doubled) — else
  `ExhaustiveSwitchDefaultReachable { block, reason }`. Rule 2, module-level:
  when the selector is — through `Copy` and `zext` / `sext` / equal-width
  `bitcast` widenings, the Trust bridge's `Rvalue::Discriminant` shape — the
  tag lane (`ExtractField` field 0) of a `Ty::Enum` value in the same function,
  every case value is the selector value of one of the enum's effective
  discriminants and every omitted discriminant belongs to a variant
  `Module::variant_is_uninhabited` (WS3.14, the predicate that also refuses
  constructing one) PROVES uninhabited — else `ExhaustiveSwitchCasesIncomplete
  { block, enum_ty, reason }`. A rustc-vetted match may omit an uninhabited arm, so "case set ==
  all discriminants" would refuse legitimate modules; anything not proven
  uninhabited (behind a reference, in an empty array) is still refused. When
  the selector's provenance does not resolve only rule 1 applies, and the
  `inst.rs` doc now says so: the flag is a producer-asserted, zero-authority
  hint, and a verifier must not use it as a fact without re-deriving the case
  set. The mutation control holds: the flag on a plain `u8` switch whose
  default is `[Unreachable]` still validates. The b6 row flips GAP → PASS; the
  c15 2a/2b ratchet becomes `c15_flipped_switch_exhaustive_flag_is_read`, with
  per-clause twins beside it and three review twins (`c15_review_*`: aliases
  at pointer width and `char`, a cast-widened selector, an all-uninhabited
  enum field). Validator-only: no wire change, goldens
  byte-identical. Producer note: a producer whose default block has
  parameters or instructions beyond `unreachable` must clear the flag, not
  relax the rule.
- **WS2.23 (stage 1) — the Lean float model fails closed instead of
  fabricating float memory and computing `F32` at binary64** (F-044; ratchet
  rows `review/lean-float-memory-placeholder` and the float row of
  `trust-ir-self-declared/lean-semantic-depth-ledger`). `F32`/`F64` and
  `Load`/`Store`/`BinOp`/`Cast` are in the proven subset, but the Lean
  `encodeValue` wrote eight zero bytes for ANY float and `decodeValue` answered
  `0.0` for every 4-byte F32 or 8-byte F64 image, so a stored `1.5` loaded back
  as `0.0` and a theorem proved about a float that went through memory could be
  false of the real program; `F32` arithmetic, `FPTrunc`/`FPExt` and
- **WS2.23 — the Lean float model computes `F32` at binary32 and gives floats
  real IEEE memory images** (F-044; ratchet rows
  `review/lean-float-memory-placeholder` and the float row of
  `trust-ir-self-declared/lean-semantic-depth-ledger`, both PASS). `F32`/`F64`
  and `Load`/`Store`/`BinOp`/`Cast` are in the proven subset, but the Lean
  `encodeValue` wrote eight zero bytes for ANY float and `decodeValue`
  answered `0.0` for every F32/F64 image — a stored `1.5` loaded back as
  `0.0`, so a theorem about a float that went through memory could be false of
  the real program — and `F32` arithmetic, `FPTrunc`/`FPExt` and
  `UIToFP`/`SIToFP` ran at binary64, which `docs/ub-numerics-policy.md` §2
  forbids. Landed in two commits, fail closed first. Every width-sensitive
  float rule now routes through `Semantics/FloatFormat.lean`: `roundDyadic`
  rounds an exact dyadic to binary32 once (RNE, gradual underflow, overflow to
  `±inf` past `(2 - 2^-24)·2^127`), `checkFloatAt` refuses an `F32` operand
  that is not a binary32 value as a type error, and
  `encodeFloatAt`/`decodeFloatAt` are the IEEE interchange images, used by
  every memory access through the typed `encodeValueAt`/`decodeValueAt`
  (plain, atomic, global initializer, `SeqMap` cell — which now maps float
  elements instead of refusing them). A float `Bitcast` reinterprets the IEEE
  pattern instead of re-tagging an int as an int-shaped value of type `F32`.
  New `SemError.unsupported .float` (`unsupported.float`, the mirror of the
  interpreter's `UnsupportedFloat`) for what stays refused: `F16` arithmetic,
  images and bitcasts, and every path that would expose a NaN's bits — a
  float→int bitcast, a float `CmpXchg` comparison, and a NaN store (Lean 4.8.0
  has no `Float.toBits`, so NaN payloads are unobservable; the residue is on
  the B3 depth ledger). Proofs restated
  over the typed codec (`semStore_characterize`, `semStore_writes`,
  `load_after_store_program`, `load_after_store_decode`, the
  `TransformCorrectness` load/atomic-load/cast `pnl` lemmas); `AxiomAudit`
  stays Lean-core only. Locked by `Semantics/FloatFixtures.lean` and the
  shared `F32_CROSS_ENGINE_TABLE` in `crates/trust-ir-build/tests/numerics_policy.rs`
  (now in gate 9), whose test checks both halves name the same rows with the
  same bits. **Interpreter fix found by the table:** `UIToFP`/`SIToFP` to `f32`
  went `int as f64 as f32`, a double rounding (`2^60 + 2^36 + 1` gave `2^60`,
  not `2^60 + 2^37`); it now rounds the integer once. The Lean `F64`
  int-to-float conversion likewise rounds once (the old `Float.ofNat`
  truncated 128-bit magnitudes to 64 bits first). **Review hardening**, three
  wrong answers the model still gave, each pinned by a Lean fixture and its
  interpreter half (`ws2_23_review_*`): (1) a NaN STORE wrote the canonical
  quiet NaN, so `bitcast i32 0x7f800001 → f32; store; load i32` answered
  `0x7fc00000` where the program reads `0x7f800001` — a NaN store now refuses
  (`unsupported.float`); (2) a `Const` materialized float leaves inside a
  tuple / vector / struct constant at binary64 whatever the field width, so
  `(0.1, 0.1) : (f32, f64)` carried a non-binary32 `F32` field out through
  `ExtractField`/`Return` — tuple fields and vector lanes are now rounded at
  their declared width, and a float leaf whose width the step rule cannot
  resolve (struct / array / enum / sequence / set / record / closure field)
  refuses unless it is binary32-exact (`const_always_succeeds` now states
  that hypothesis; `const_width_ambiguous_refused` is its twin); (3) `CmpXchg`
  at a float type never compared equal, so a matching expected value reported
  failure and skipped the write — it now compares IEEE bit patterns, as the
  interpreter does.
- **WS2.14 — a whole-aggregate `Load` ignores never-written padding, and a
  typed aggregate `Store` no longer fabricates it** (F-030; proof-program row
  `b6.enum.fieldwise_init_uninit_padding_is_ub_on_load`, flipped to PASS).
  The reference interpreter held every aggregate `Load` to "every byte
  initialized", so rustc-style field-wise construction (field stores plus a
  discriminant store, padding never written) followed by a whole-value move was
  undefined behaviour although the module validates for codegen. A
  whole-aggregate `Load` of a struct, tuple, enum or array (plain or volatile)
  now requires exactly the bytes a LIVE field of the decoded value covers:
  struct/tuple fields at their declared or canonical offsets, array elements,
  and for an enum the tag lane (direct tag or niche lane) plus the ACTIVE
  variant's fields. Padding and the inactive-variant tail are don't-care, since
  the decode never reads them. An uninitialized covered byte is still
  `UndefinedBehavior "Load: reading uninitialized byte at offset N"`. The
  `Array(U8, N)` union carrier covers every byte, so a by-value move of a
  partially initialized carrier stays undefined (the F-050 decision is
  separate). The store side changes in the same commit: a typed aggregate
  `Store` writes every byte no live field covers as UNINITIALIZED instead of
  the zeros `encode_value` fills it with. A typed aggregate value has no
  padding, and without this a whole `Load` of never-written padding followed
  by a `Store` would turn uninitialized bytes into defined zeros that a later
  `u8` load returned as `Ok 0`. Byte-level reads of padding after a typed store
  are therefore stricter than before (they were reading fabricated zeros) and
  no covered byte is looser. Lean has no aggregate memory path
  (`encodeValue`/`decodeValue` give `none` for every aggregate), so this is
  interpreter-only; the B3 depth ledger gains the row "whole-aggregate memory
  images unmodelled in Lean". Global initializers keep their zero-filled image
  (the loader's bytes are real). No wire change. Tests: gate 8
  `aggregate_padding_load` (struct and enum field-wise positives, the
  never-written-field / active-payload / tag negative twins at their exact
  offsets, a volatile whole load over padding and over a covered byte, the
  `Array(U8, 8)` carrier move, the load-then-store laundering control and the
  memset-then-typed-store control), and gate 11 `two_language_b6`
  (field-wise `Rc<Tree>` node returns 42; the twin that skips the `right` store
  is the uninit fault at offset 8).
- **WS4.2 — text fails closed until it is total: `text_losses()`, the
  `#lossy` refusal and a strict parser** (finding F-065; interim guard for
  F-064 / F-070 / F-072). The text round trip silently DROPPED fields it
  could not carry — `global_asm` among them, so `validate_module_for_codegen`
  said `[GlobalAsmNotConsumable { blocks: 1 }]` before a text round trip and
  `[]` after (the permissive laundering; proof-program rows
  `b7.text.flip.global_asm_refusal_laundered`, `verify.c08.L1/L2`), and the
  parser skipped any unknown top-level line, `; #` directive or node clause.
  Now: `trust_ir::format::text_losses(&Module) -> Vec<TextLoss>` names every
  field the grammar cannot carry, with its location (`FunctionSummary`,
  `ClauseBindings`, `CertificateAssurance`, `KernelRecheck`, `ObligationKind`,
  `EnumLayout`, `EnumFieldNames`, `EnumDiscriminantsTail`,
  `StructFieldNames`, `StructFieldOffsets`, `RecordFieldOffsets`,
  `GlobalAttrs`, `GlobalAsm`, `SwitchExhaustive`, `UnspellableName`,
  `FunctionId`, `EntryBlock`, `ParamAttrsTail`, `UnspellableFloat`,
  `KernelGoal`), written as an exhaustive,
  `..`-free destructure of `Module` / `Function` / `Global` / `StructDef` /
  `EnumDef` / `ProofCertificate` (and the records they hold), so a new field
  fails to compile until it is classified. `format::canonical_checked`
  returns `Err(TextLossError)` listing every loss. `Display` (hence
  `format::canonical`) still prints, but adds `; #lossy: <summaries>` right
  after the header, and the parser REFUSES it ("this text was printed
  LOSSILY (…); it cannot be parsed back — re-emit from the binary/serde
  artifact"). The parser is STRICT: an unknown top-level line, an unknown or
  misplaced `; #<word>` directive, and an unknown node clause are each
  `ParseError("unknown directive `#<word>` — refusing rather than dropping
  it")`; plain comments are still skipped. The directive vocabulary is ONE
  table, `trust_ir::text_directives::TEXT_DIRECTIVES`, which the printer
  spells through and the parser dispatches on. `trust-ir convert --to text`
  and `trust-ir-fmt` use `canonical_checked` and exit 1 with the loss list;
  `dump` keeps `Display` and prints the marker. **Behaviour change:** a text
  that used to parse by dropping a line is now refused, and every module
  with a named struct field (the ordinary Rust case) prints `#lossy` until
  WS4.5 carries layouts — WS4.2–WS4.5 must reach producers in ONE pin move.
  The marker is a tripwire, not integrity: text is unauthenticated, and a
  human who deletes the line gets the lossy module. Tests: the conformance
  `TEXT_LOSS_RATCHET` pins the exact loss kinds of the five lossy fixtures
  (`composition`, `func_param_abi`, `ty_composite`, `ty_container_vtable`,
  and WS4.15's `lean_library_envelope` — `KernelRecheck` + `ObligationKind`,
  still text-skipped because the `custom:` kind is unparseable even with the
  marker deleted; rows only shrink), the two `b3.envelope.gap.text_*` rows
  keep their GAP but now expect the `#lossy` refusal and pin the old
  consequence on the marker-deleted copy, every other fixture and every fuzzer seed must
  round-trip EXACTLY (no field normalization), each lossy fixture must equal
  its canonical form with exactly the reported losses erased (the loss list
  is complete), and a new `text_directives` fixture proves every table entry
  parses back; `crates/trust-ir-conformance/tests/text_losses.rs` ports the
  proof-program rows. The false `global_asm` rustdoc in `validate.rs` and the
  incomplete `LIMITATIONS.md` list are corrected. Adversarial review added
  two kinds the landing list missed, each pinned by a `review_*` test in
  `text_losses.rs` with an exact-round-trip twin: `UnspellableFloat` — a
  `Constant::Float` NaN whose sign/payload is not `f64::NAN`'s printed as
  `NaN` and parsed back as `f64::NAN` with NO error (a silent bit change a
  `Bitcast` observes), and a non-finite `bounded_output` bound or
  `gamma_crown` epsilon printed a text the finite-only reader refused while
  `canonical_checked` said `Ok`; and `KernelGoal` — a `clean-expr`
  `ProofAnnotation::Goal` printed as an opaque `goal(N hyps)` with no parser
  arm, likewise `Ok` yet unparseable.
  Two-language ratchets (gate 11, rebased onto WS8.6): the harness's text
  leg now records the `#lossy` summary and the marker-deleted copy
  (`FormatTrip::lossy` / `unmarked` / `carried()` / `parse_unmarked()`), so a
  row can still pin exactly what the grammar drops. Five consequence rows
  flip GAP -> PASS (closing increment WS4.2): `b7.text.flip.global_asm_refusal_laundered`,
  `b7.text.flip.unauthenticated_import_laundered`,
  `b7.text.flip.certified_becomes_invalid`,
  `b7.text.flip.layout_becomes_uncomputable` and
  `b7.text.round_trip_changes_module_identity` — the round trip is refused at
  the marker, and each detail records what the marker-deleted copy would
  still say (tripwire, not integrity). The `drops_*` / `refuses_*` / names
  rows stay GAP in their new shape — the exact `#lossy` refusal naming the
  field, with the old drop or parse error pinned on the marker-deleted copy —
  until WS4.3 / WS4.4 / WS4.5 give the field a spelling. PASS rows that said
  "survives all four codecs" measure text on what its grammar carries.
  WS8.7's claim ports (rebased onto WS8.7): c08 T1 flips and lands as its
  twins `c08_flipped_text_refuses_global_asm` (`format_canonical.rs`) and
  `c08_flipped_convert_through_text_refuses_the_global_asm_module`
  (`cli_verify_repros.rs`: `convert --to text` exits 1 naming
  `global-asm(1 blocks)` and writes nothing, the `dump` image is refused on
  the way back, JSON keeps the refusal); c08 T2 / T3 / T4a / T4b stay GAP in
  the same new shape (the exact `#lossy` summary, the old drop or parse
  error on the marker-deleted copy; T4b's struct field is now positional so
  the name is the only loss) until WS4.4 / WS4.3; and c09's unknown
  top-level line, skipped before, is now a located `unknown directive
  `zzz`` refusal.
- **WS2.24 — Lean multi-result binding: `Overflow` / `CmpXchg` bind two
  destinations as Rust does** (F-044, the "multi-result packing" row of the
  Lean depth ledger). The Lean executable model packed a two-result
  instruction into ONE `Value.aggregate`, and `bindInstrResultDests` refused
  any node with two destinations ("instruction result count mismatch"), so a
  Rust-shaped `%v, %o = add_overflow i8 127, 1` could not be evaluated
  verbatim. `InstrResult.values` is now the one spelling: `semOverflow` /
  `semCmpXchg` bind their components as two fresh SSA values
  (`Sem.bindFreshPair`), and the binder assigns them positionally, requiring
  the destination count to match exactly (an absent row included — a
  multi-result node has no fresh-result fallback). The packed form is deleted.
  `LandingPad` no longer binds a fabricated `(null, 0)`: a directly-entered pad
  fails closed with `unsupported.host_unwind` "landingpad entered without an
  unwind edge", completing on the Lean side what WS2.5 did in the interpreter.
  New theorems (Lean-core axioms only): `Sem.bindFreshPair_ok`,
  `semOverflow_eq_bindFreshPair`, `semOverflow_binds_components`,
  `semCmpXchg_binds_components`; `semOverflow_pnl` / `dce_pure_inst` re-proved
  over the unpacked form. Fixtures: `overflow_binds_two_destinations_positionally_stable`
  (positive), `overflow_one_destination_is_count_mismatch_stable` (twin,
  named reason), `overflow_swapped_destinations_swap_the_components_stable`
  (mutation control; an order-insensitive or dest-ignoring binder fails it),
  the `cmpxchg_*` quartet, and `landing_pad_direct_entry_fails_closed_stable`.
  Lean only, no wire change; the subset contract is unchanged (`LandingPad`
  stays excluded for selector dispatch). Review hardening: the multi-result
  binder RETIRES the fresh component ids that are not themselves destinations,
  so the node defines exactly its declared results — a later read of a stale
  temporary is now the undefined-SSA-value error Rust raises instead of
  silently succeeding (`overflow_fresh_component_ids_are_not_defined_stable`);
  further fixtures pin non-adjacent destinations (which a dest-ignoring binder
  fails), the flag driving a `CondBr` directly, refusal of a packed-form
  `ExtractField` consumer, value-then-flag order for `SubOverflow` /
  `MulOverflow` at the residue boundary, and the absent-row / three-destination
  `CmpXchg` twins.
- **WS3.19 — the container-tail fat-pointer LANES are pinned, not just the
  names** (the `FatPtrKind` half of F-043, on top of WS2.18, which landed the
  two Lean constructors and their `metadataTy` / `metadataTyMatches` /
  `decodeValue` arms). A name-parity match would also accept a Lean model that
  swapped the lanes, so `fat_ptr_kind_metadata_lanes_agree_with_rust`
  (`lean_schema_parity.rs`) parses both Lean definitions and requires each
  kind's lane to equal Rust `FatPtrKind::metadata_ty(64)`: `ContainerLen` on
  the `U64` length lane, `ContainerVtable` on the `Ptr` vtable lane, and no
  extra `true` arm in `metadataTyMatches`. New executable fixtures pin the
  projection half WS2.18 left out: `PtrMetadata` of a `ContainerLen` pointer
  yields a `U64` (`ptr_metadata_container_len_yields_u64_stable`), of a
  `ContainerVtable` pointer a `Ptr`, and `PtrData` projects the container
  header, with every lane-swapped twin (declared type, stored value) refused
  as `type_error`. Review added the edges those missed: a null vtable word
  round-trips as `ContainerVtable` metadata (never a length 0) and is refused
  as `ContainerLen` metadata, a 32-bit length and the `Usize` spelling are
  refused, and the Rust half (`container_tail_pointer_metadata_lanes_are_exact`,
  trust-ir-build) refuses every swapped lane on `PtrMetadata` and
  `PtrFromParts` as `PointerMetadataTypeMismatch` naming the exact lanes. No
  wire change. Deliberately NOT done: a pointee id on either kind — the
  container has an unsized tail no `StructDef` describes; that is the F-123 /
  AD-1' decision gate.
- **WS2.10 — `Undef` is poison in both engines** (F-034; proof-program row
  `b7.nondet.undef_executes_as_ub`, flipped GAP → PASS "Undef is poison;
  inspection is UB"). ub-numerics-policy §4 has always said `Undef` denotes a
  poison value, and Lean bound `.undef ty`, but the reference interpreter
  trapped the moment it executed an `Undef` ("executing undef would read an
  undefined value") — a "known interpreter limitation" the policy disclosed.
  Both engines now follow the policy. **Interpreter:** `Inst::Undef` binds the
  existing copy-propagates-poison value (`PartialBytes`, every byte
  uninitialized) at the `partial_load_ty` scalars, so it transports exactly
  where a partially-initialized load does (`Copy`, a `Select` arm, a plain
  `Store`, a block argument) and is UB exactly where that is inspected
  (arithmetic, comparison, cast, a branch/switch/select condition, a field
  projection, a call argument or return, a volatile/atomic store). A
  non-scalar `Undef` FAILS CLOSED ("undef of non-scalar type {ty} is not
  executable (aggregate poison unmodelled)") rather than executing as a
  "complete" aggregate. A `LoadSlot` of a never-bound slot reads the same
  scalar poison (it was UB "read before bound"; Lean's `initFrame` seeds
  `.undef`), with the same non-scalar refusal. **Lean:** `Sem.rejectPartial`
  now throws UB on `.undef` as on `.partial`; `semStore` of an `.undef` writes
  `byteSize` uninitialized bytes (strict stores refuse it); atomic store,
  atomic RMW operand and a successful `CmpXchg`'s `desired` refuse poison as
  UB (they were type errors); and the call
  boundary — `Call`, `CallIndirect`, `Invoke` and the entry of
  `evalFunctionInContext` — refuses poison arguments and returns through the
  new `Sem.rejectPoisonValues`, mirroring the interpreter's
  `check_signature_values` (this also closes the same pre-existing divergence
  for `.partial`). `undef_always_succeeds` still holds; new
  `undef_inspect_is_ub`, `undef_binop_operand_is_ub` and `undef_condbr_is_ub`
  are pinned in `AxiomAudit.lean`, and the inlining / ProofContext theorems
  (`inlining_preserving`, `inlining_error_*`, `runCallReq_ok_*`,
  `runInvokeCall_ok_decomp`) now state the poison-free boundary they rely on.
  Tests: gate 8 gains `undef_poison` (positive `store undef; ret 7` → 7,
  negative twin `add undef, 1` → UB, mutation controls `undef struct` and
  `condbr (undef bool)` → UB, transport/inspection/unbound-slot cases, and the
  ported row `b7_nondet_undef_executes_as_ub`); Lean gains the
  `undef_*_stable` executable fixtures. The WS2.8 unbound-slot tests now pin
  poison-then-inspection UB. Residue, disclosed: Lean binds an `.undef` of
  any type, so an unused non-scalar `Undef` runs in Lean and is refused by the
  interpreter (`undef_tuple_unused_runs_in_lean_stable`); and a poison
  POINTER operand is UB in the interpreter but a type error in Lean (both
  refuse). No wire, validator or golden change.
  **Review hardening (same increment):** poison may no longer HIDE inside a
  defined value. `insert_element` of a poison element used to succeed in BOTH
  engines, and the array (or, in the interpreter, the SIMD vector — also via
  `vector.insert_lane` / `vector.pack_lanes`) was returned from the entry
  `Ok` with a poison lane, because the call-boundary check sees only
  top-level values; embedding is now an inspection, as `insert_field`
  already was (interpreter `insert_element value` / the dialect op's name;
  Lean `semInsertElement`'s array path). A `CmpXchg` with a poison
  `expected` compared "unequal" and ran on in both engines; the comparison is
  an inspection and is UB now. `PtrFromParts` / `PtrData` / `PtrMetadata`
  over a poison thin pointer relabelled it and ran on in the interpreter
  (`store` then `ret 7` → `Ok(7)`) where Lean refused; the interpreter
  refuses it now. `assume (undef bool)` is pinned as UB in the interpreter
  and disclosed as part of the pre-existing `Assume` model split (Lean's
  `Assume` is a no-op). Tests: `ws2_10_review_*` in `undef_poison.rs` (each
  with a defined-value mutation control) and Lean
  `undef_insert_element_into_array_is_ub_stable`,
  `partial_insert_element_into_array_is_ub_stable`,
  `undef_cmpxchg_expected_is_ub_stable` plus their defined controls. The
  WS8.6 ratchet ledger landed meanwhile, so the row is flipped there too:
  `RATCHETS.tsv` `b7.nondet.undef_executes_as_ub` GAP → PASS (closing
  increment WS2.10), its `two_language_b7` probe now a PASS check that the UB
  names the inspection and never the retired "executing undef".

- **WS1.11 — an `Unbounded` coverage row is re-derivable beyond TrustMc BMC**
  (the module-level half of F-020; proof-program row
  `b2.gap.unbounded_coverage_claim_not_rederivable`). `coverage_assurance_report`
  re-derived a bound from a TrustMc bounded-model-check request only, so an
  `Unbounded` assurance row was UNDETERMINED against every request that could
  honestly back it. `bound_determined_by_request` now derives `Unbounded` from
  the request shapes that name an unbounded procedure, and nothing else:
  TrustMc `Chc` and `Pdr` (a CHC model / PDR inductive invariant proves the
  query unreachable at every depth; `pdr.max_frames` caps the search, and a
  capped run returns unknown, so it never changes the derivation), and TrustWp
  `WeakestPrecondition` under frame policy `FullHeap` for each of
  `RequireInvariants` / `InferInvariants` / `Havoc`. Fail-closed qualifier:
  `Minimal` and `BorrowRegions` frames may assume a written location unchanged,
  so WP under them stays undetermined until trust-wp documents that they
  over-approximate every written location; `StrongestPostcondition`,
  `Abduction` and every TrustVc mode stay undetermined too. The match is now
  exhaustive over every mode/strategy/frame enum, so a new variant must choose
  its arm. Equality still governs, so an `UnwindBounded` / `ModelBounded` /
  `Unrecorded` row citing one of the unbounded shapes is now refused with
  `CoverageAssuranceBoundMismatch`. A new check 4 keeps the producer's choice
  of citation from promoting an over-claim: when another request in the bundle
  lists the same obligation and fixes a bound that does not
  `coverage_supports` the claim (an `Unbounded` row citing PDR beside a
  depth-1 BMC request, or a depth-10 row beside a depth-1 sibling), the row is
  counted `undetermined`, not agreed, because the bundle records no verdict
  saying which run discharged the obligation. Before WS1.11 that move landed in
  `undetermined` anyway; without check 4 it would have landed in `agreed` and
  passed the strict admission gate. Under-claims still agree. No wire change
  (`Exhaustive { domain }` is WS1.12e). Each arm has its own named test in
  `coverage_assurance`, which joins gate 9 (`validator-fail-closed`) through
  its registry.
- **WS1.6 — same-module inheritance is admitted, with the cross-crate
  restatement check** (finding F-010). A Rust caller restating a same-module
  Clean callee's kernel-certified contract through
  `InheritedFromCallee { external: None }` was `DischargedWithoutCertificate`
  under `validate_module` AND `validate_linked_module`: only `external: Some`
  rows were ever admitted. And when a consumer capability did admit it, the
  local rule related the two rows by the callee's `FuncId` alone — a
  restatement saying `(= result 12345)`, carrying no formula, of kind
  `MemorySafety`, or owned by the caller left the error list byte-identical,
  while the cross-crate rule refuses exactly these. `validated_authority_refs`
  now admits such a certificate into the `Discharged` tier — never the kernel
  tier, so never `ProofRef` currency, a proof context or another inheritance's
  ground — iff the callee exists, the inherited row is kernel-grounded (a row
  discharged by an inheritance never is: no chain) and scoped to the callee,
  and the discharged row passes `inheritance_restatement`: scoped to the
  callee, same kind, same formula with bindings. That function is factored out
  of `linked::check_inherited`, which now calls it, so the two edges share one
  check and the cross-crate refusal details are byte-identical. It needs no
  capability, because every input is re-checked in-process (DECIDE adopted:
  plain `validate_module` admits it). A restatement failure is the new
  `ValidationError::LocalInheritanceRestatementMismatch`, reported whoever else
  admits the certificate; failures an existing error already names keep that
  name (`InheritedProofCalleeNotFound`, `InheritedProofNotDischarged`,
  `InheritedProofCalleeScopeMismatch`). The rule reads only certificates on a
  `Discharged` row, so the WS1.4 composition rows on a caller's `Certified`
  TV obligation are never routed through it. The rule-#9 doc now says what the
  code enforces: a `Discharged` obligation needs a certificate in the
  validator's authority set (kernel-replayed `CleanCic`, a capability replay,
  or an admitted local or authenticated cross-crate inheritance), not a
  "non-inherited" one. No wire change. Tests:
  `crates/trust-ir-build/tests/local_inheritance.rs` (gate 9), including the
  ports of `b2.gap.local_inheritance_not_admitted_without_capability` and
  `b2.gap.local_inheritance_restatement_unchecked`, and the A0 scope-split pin
  in `tv_callee_binding.rs`. Review added the two conditions only the
  same-module edge can state, each refused under the same error: the
  restatement is unsited or sited exactly where the inherited row is (the
  callee has a body here, so a site names one of its checks, and restating a
  claim must not move it onto another), and linked rule L9 applies — the
  inheritance certificate's own `assurance` must be supplied by every bound
  the inherited row's certificates record, so coverage does not grow across
  the edge (the first cut admitted an `Unbounded` claim over a depth-1
  discharge). Also pinned: the admitted row is not proof-context currency,
  and an importer cannot inherit it across a crate edge (a dependency exports
  its kernel tier and authenticated inheritances only).
- **A pointer-like indirect call can no longer originate a nominal dialect
  value, and codegen refuses an unknown dialect namespace by name (WS2.20,
  F-046 `trust-ir-self-declared/dialect-laundering-path`).** The v39 nominal
  transport rule admitted a `CallIndirect` over any pointer-like callee that
  did not itself spell a dialect type, without looking at the signature's
  RETURNS — so an untyped code address could mint a `Ty::Dialect` value the
  exact-typed rules never saw originate. The callee is now admitted only if
  `func_types[sig].returns` reaches no `Ty::Dialect`; otherwise
  `InvalidDialectType` ("a pointer-like indirect callee cannot originate a
  nominal dialect value"). This is the closure the v43 handle rule already
  made; a dialect-typed ARGUMENT through a pointer callee is transport and is
  unaffected. Separately, `codegen_lowerability_errors` (and so
  `validate_module_for_codegen`) refuses a `DialectOp` whose namespace is not
  one of the in-tree decoded dialects (`vector` / `gpu` / `avx512` / `ane` /
  `trust_rust`) as `UnlowerableForCodegen` ("unknown dialect namespace …: no
  registered lowering"). `validate_module` is unchanged for opaque round-trip
  (Clean's Dialect debug mode). Validator-only; no wire change. Tests:
  `dialect_types` (now a gate-9 member).
- **A type that contains itself by value is refused, and no longer crashes
  the interpreter (WS2.4, F-045 `exec-log-and-tcb/by-value-struct-cycle-robustness`).**
  No validator pass looked at by-value containment, so `struct Node { next:
  Node }` validated, and the reference interpreter's `byte_size` →
  `struct_layout` → `aggregate_layout` → `byte_size(field)` chain recursed on
  it until the host stack overflowed (`shape` has a guard, but a size-less
  struct never reaches it). `validate_module` now runs a by-value containment
  DFS (iterative Tarjan) over the type tables — struct / record fields, enum
  variant fields, closure captures, tuple and vector elements, and the `TyId`
  of `Array` and `Refine` (a refinement is representation-preserving) —
  stopping at every pointer, reference, `Rc`, function, `Sequence` / `Set`,
  `Handle` and `Dialect`, and refuses each cycle once per strongly connected
  component with the new `ValidationError::InlineAggregateCycle { ty }`. The
  interpreter threads a visiting stack (struct / enum / `TyId`, the shape of
  `shape::ty_layout_shape_inner`) through `byte_size` / `byte_align` /
  `struct_layout` (declared and synthesized) / `tuple_layout` /
  `aggregate_layout` / `enum_layout`, so an UNVALIDATED module gets a
  fail-closed `TypeError` "type {ty} contains itself by value (no finite
  layout)" instead of a crash (`Refine` needs no interpreter key: the
  interpreter gives a refinement no byte layout at all, so it never recurses
  through one). No wire change. Tests: gate 9
  `by_value_struct_cycle_robustness` (positive `*mut Node`, negative twin,
  tuple/row, enum, `Refine`, declared-size and two-struct cycles caught;
  `Rc` / `&` / `*const` / `Sequence` not flagged) and gate 8
  `interpret_differential` `ws2_4_*` (every case on a 1 MiB thread stack).

- **An interposable site can no longer carry a cross-crate proof (WS8.14,
  F-126 `core-arch-0916-b/18-fact-link-bound`).** `Module::resolve_extern_ref`
  refused only `Internal` / `Private` far linkage, so a far definition spelled
  `Weak` / `LinkOnce` — which the linker may replace with a definition nobody
  proved anything about — or `ExternalWeak` — which may bind to null — backed a
  `backed_by` citation and an `InheritedFromCallee { external: Some }`
  certificate exactly like an `External` one. The importer's own local
  declaration had the same hole from the other end: spelled `ExternalWeak`, the
  body the proof is about need not be the one called. Both legs now refuse with
  the new `ImportVerificationError::InterposableFarSite { symbol, linkage, side
  }` (`side` is `"far"` at R4, after the export check, and `"local"` at the end
  of R2), and `validate_linked_module` surfaces it through `check_backed_by` /
  `check_inherited`. `WeakOdr`, `LinkOnceOdr` and `AvailableExternally` stay
  admitted under the one-definition-rule premise (how Rust generic instances
  link) — a disclosed assumption, not a verified one (`TRUST.md` item 10,
  ratified with the rule in the spec ratifications §6). Check order is pinned: an
  unexported far symbol is still `SymbolNotExported`, and a bare far
  re-declaration spelled `ExternalWeak` is still
  `FarSiteIsUnbackedDeclaration`. `verify_import` now runs in a standing gate
  (`import-verification`, beside gate 7), and `linked_import_authentication`
  joins gate 9.
- **WS1.4 — a kernel-certified `clean_backend_tv` caller is bound to the
  callee it actually calls** (finding F-005). A Fragment-3b statement is
  parametric in its callees — each `Call` is an anonymous `∀`-bound symbol at
  its name-sort rank — so retargeting `top`'s call from `plus` to the
  same-signature `minus` left the equation byte-identical: `validate_module`,
  `_report`, `_with_authority`, `_for_codegen`, `validate_changed`,
  `validate_linked_module`, lineage closure and `trust-ir validate --lineage`
  all still said `Certified` while `top(20,15)` went 327 → 287. Nothing
  required an `InheritedFromCallee` row, and the B5 inheritance validator never
  compared a row's callee with the body's calls. The Certified-evidence pass
  now runs a composition post-pass over every TV obligation whose recheck
  passed: (a) exactly one `InheritedFromCallee` row per called function and none
  for a function the body does not call; (b) each row cites the callee's OWN
  kernel-rechecked `clean_backend_tv` obligation (another anchor, a
  `Discharged`/`Trusted` row, or a failed recheck does not qualify, so a callee
  with no TV — a runtime declaration, a non-Clean body — leaves its caller
  uncertifiable); (c) an `external: Some` row on a TV obligation is refused
  ("cross-crate TV composition is authenticated only by
  validate_linked_module"); (d) the composition graph is acyclic, self-calls
  included ("clean_backend_tv composition cycle: f → f; recursive composition is
  not grounded"). Each failure is a `CertifiedCleanCicKernelRecheckFailed` on
  the caller, so the all-or-nothing rule empties the kernel-tier authority set.
  `scan_callees` additionally refuses one symbol name shared by two distinct
  called functions. The in-tree `clean_backend_tv_rejects_miscompiled_composition`
  fixture, which certified a caller with no grounding row, now carries one.
  RESIDUAL, pinned as `b3.gap.composition.consistent_retarget_to_certified_callee`:
  retargeting the call AND rewriting the row to another honestly certified
  callee of the same arity and rank is still accepted — the certificate records
  no callee list until WS1.12a (`CertificateBinding.callees`). A rename that
  changes a callee's rank still refuses an honest certificate (fail-closed).
  F-016 is decided as option (A): the anchor is producer-agnostic, documented on
  `trust_ir::Producer` and in `TRUST.md` item 6. Tests:
  `crates/trust-ir-build/tests/tv_callee_binding.rs` (now in gate 9 beside
  `lineage_authority`) and the CLI twin in `cli_lineage.rs`. The Clean minter
  already emits one row per callee and never certifies a recursive caller.
- **The contract grounder binds a clause to its sort, place and IR type
  (WS1.1, finding F-001, critical).** `contract_goal` mapped any single-symbol
  `(>= s 0)` / `(<= 0 s)` clause to the CLOSED kernel goal
  `∀ x : Nat, Nat.ble 0 x = true`, discarding the symbol, and neither the
  minter nor `KernelCleanCicRechecker` read `ProofFormula.bindings`, the
  `ClauseSort`, the obligation's function or its `FuncTy`. Measured (audit rows
  `b2.gap.kernel_certifies_nat_nonneg_ignoring_bindings_and_ir_type`,
  `b2.gap.kernel_certificate_ignores_clause_binding_sort`, `verify.c01`):
  `fn level() -> i64 { -1 }` with a `proved` `ensures (>= result 0)` reached
  kernel-`Certified` under `validate_module`, the authority tier, the codegen
  tier and `validate_linked_module` while the interpreter returned -1; so did
  i8/f64/Bool results, Bool/RoundingMode/BitVec/absent bindings, a symbol that
  was not the bound name, and `(>= -5 0)`. Grounding is now split:
  `contract_goal` / `contract_clean_cic_certificate` / the module-free
  `CleanCicRechecker` impl are LITERAL-ONLY; the new `contract_goal_in`,
  `contract_clean_cic_certificate_in`, `contract_nat_nonneg_obligation_in`
  (replacing `contract_nat_nonneg_obligation`, which had no sound module-free
  form) and the new `ModuleCleanCicRechecker` trait are the only paths that
  may produce the tautology, and only after `bind_nat_nonneg` binds the symbol
  to a `Param` / `ResultSlot` / `MutParamExit` place whose IR type is
  `u8`..`u128` (or `usize` under a `target_info`), read at sort `Int`. The
  validator's directive-less contract arm and the native-bundle authority
  (`native_authority_replayed`) run the module-bound path; a refusal reads
  `contract clause does not bind to a Nat-valued IR place: <reason>`. The
  shared place/sort/symbol vocabulary is the new
  `trust_ir::proof::clause_typing` (`resolve_clause_place`,
  `clause_sort_admits`, `smt_free_symbols`, `is_smt_simple_symbol`). The
  residual denotation lemma is TRUST.md item 11. A `Nat` literal in a
  contract clause is now ASCII digits only: `u64::from_str` also took `+1`,
  which SMT-LIB2 reads as a SYMBOL, so the literal-only path used to certify
  `(>= +1 0)` module-free while its binding named `+1` as an `i64` result
  (found in review; `plus_signed_atom_is_neither_a_numeral_nor_a_bindable_symbol`).
- **`ProofRef` backing cuts the category link, not only the position (WS1.1).**
  `proof_ref_kind_can_back` let every category-ambiguous kind (Pre/Post/
  LoopInv/TypeInv/Refinement/TranslationValidation/TemporalSafety/Liveness)
  back ANY claim, so the freely-mintable `(>= result 0)` Postcondition above
  backed `DivNonZero` on `1 sdiv 0` — also after being re-sited onto the sdiv
  node. A safety-class claim is now backed only by its own obligation kind (or
  a specific kind covering its category); an ambiguous kind backs only
  `Custom` and kind-less claims (`Pure`, `Deterministic`, hints, value facts),
  at function level — attribution, not entailment (TRUST.md item 11); and a
  node-level `ProofRef` must cite a row sited on that very node, else the new
  `ValidationError::ProofRefSiteMismatch`. The `fast1_proof_ref.rs` fixtures
  that backed `NoPanic` with a Postcondition were rewritten to kind-matched
  rows. Tests: `crates/trust-ir-build/tests/contract_clause_binding.rs` (28,
  including the four flipped audit rows), now in gate 9
  `validator-fail-closed`.
- **Summary clause bindings are type-checked against the IR (WS1.2, finding
  F-004 — the always-on half).** `validate_function_summary` resolved binding
  indices and place legality only, so a summary validated with a u64
  parameter bound as `BitVec(8)` / `Bool` / `Float` / `RoundingMode`, a u64
  result or SSA value bound as `Bool`, `BitVec(64)` on a `handle<Nat>` place,
  and `MutParamExit` on a by-value `x: u64`. Now a binding's sort must be a
  faithful reading of its place's IR type under the WS1.1 helper
  `clause_sort_admits` — `Bool` ⇐ `bool`, `BitVec(w)` ⇐ a `w`-bit integer
  (`isize`/`usize` only under `target_info`) or `char` at 32, `Int` ⇐ any
  integer or `char`, `Float{eb,sb}` ⇐ exactly `f16`/`f32`/`f64`; pointer-like
  places, `Ty::Handle` and every other `Ty` (the default arm) admit NO sort;
  `MutParamExit { i }` requires a `&mut T` / `*mut T` parameter and types
  against `T`; `Value(v)` is typed through the SSA type map. The rule is always
  on (an ill-typed binding is malformed whether or not the summary is
  `proved`); every refusal is an `InvalidFunctionSummary` naming clause,
  binding and reason (no new error variant), and an unresolved index keeps
  exactly its pre-existing arity error. Validator-only, no wire change.
  Tests: `contract_clause_binding.rs` (positive bound `bump`, named negative
  twins, mutation controls, and the flipped audit rows
  `b2.gap.clause_sort_unchecked_against_ir_type`,
  `b2.gap.mut_param_exit_on_by_value_param_accepted`,
  `b5.gap.clause_sort_bitvec64_accepted_on_nat_param` — the last also refuses
  the `Int` reading the b5 PASS row carried, since a handle admits no sort;
  and the adversarial-review cases — pointer-width integers bind as `BitVec`
  only at the target's exact pointer width, `MutParamExit` reads only a
  `&mut` / `*mut` pointee, requires / ensures / decreases are all typed with
  no refusal masking another, the `char` and IEEE rows are exact, and each
  result of a multi-result node is typed on its own);
  `g5_contract_clause_bindings.rs` (the MutParamExit fixture moves to a
  `&mut i64` parameter), now in gate 9. DEFERRED: the `proved`-only half
  (empty bindings, free-name closure, binders, uninterpreted heads,
  World/Unwind); it refuses the published `composition` conformance fixture,
  and `b2.gap.unbindable_clause_still_earns_proved` stays a GAP ratchet until
  it lands.
- **`proved` is per-clause; `backed_by` re-earns a clause, not a count
  (WS1.3, findings F-002 and F-003).** For a definition,
  `validate_function_summary` COUNTED Discharged/Certified contract rows scoped
  to the function and never read a row's `formula`, so `fn f() -> u64 { 7 }`
  with `proved ensures (= result 42)` validated under every entry point beside
  one genuinely kernel-rechecked `(>= result 0)` row (audit c02 R1, row
  `b2.gap.kernel_certified_row_backs_an_unrelated_false_clause`). Now every
  clause must be matched by a Discharged/Certified row scoped to the function,
  of the kind its role maps to (Precondition↔requires, Postcondition↔ensures,
  Termination↔decreases), whose `formula` EQUALS the clause — schema, payload,
  smtlib, sort and bindings. A formula-less row matches nothing; a clause
  repeated within one role is refused ("ensures clause 1 duplicates clause
  0"); an unbacked clause reads "ensures clause 1 `(= result 42)` has no
  Discharged/Certified Postcondition row scoped to this function stating
  exactly this clause (rows stating other clauses do not count)". Declarations
  keep the §6 `backed_by`-only rule and the `Failed` refutation is unchanged.
  Cross-crate, `check_backed_by` now takes the dependency's verdict (the
  `check_inherited` model) and additionally requires the cited far row to be
  GROUNDED there (kernel-tier replay or authenticated inheritance — a
  capability-replayed `Discharged` row is refused as "not grounded") and its
  formula to be one of the restated clauses of its role ("cited far obligation
  #N states `…`, which is none of the restated ensures clauses"); a dependency
  publishing a false `proved` clause is now `ImportedModuleInvalid` from its
  own pass (audit c02 R2, row `b4.gap.backed_by_reearns_a_count_not_a_clause`).
  `mint_summary_obligations` attaches each clause as the row's `formula`.
  CAPABILITY LOSS, fail-closed: the trust-ir-ay adapter reports a
  formula-carrying row `Unsupported`, so a minted contract row is never
  ay-discharged or ay-refuted and ay-earned `proved` is unavailable until
  WS5/F-091 (`contract_flow.rs` now pins that, and keeps its refutation flow on
  a hand-built formula-less row). No wire change: `proved` stays a derived
  `bool` the validator re-checks. Tests:
  `crates/trust-ir-build/tests/per_clause_proved.rs` (new, gate 9: positive
  fixtures, the c02 R1/R2 mutants, duplicate / one-row-two-clauses /
  formula-less / wrong-kind twins, the `Int`-vs-`BitVec(64)` bindings mutation
  control, the flipped `b2.gap.no_per_clause_obligation_backref` and
  `b2.gap.kernel_certified_row_backs_an_unrelated_false_clause` rows);
  `linked_import_authentication.rs` (the flipped
  `b4.gap.backed_by_reearns_a_count_not_a_clause` row, the "not grounded" and
  unrestated-claim refusals); the g5 counting fixtures now state their
  clauses, and `the_counting_rule_cannot_bind_a_clause_to_its_own_obligation`
  flipped to a refusal (renamed
  `a_row_about_another_clause_does_not_back_proved`).
  Review hardening (same increment): a DEFINITION that also carries a
  proof-bearing `backed_by` no longer skips the per-clause match (the
  structural tier otherwise re-admitted c02 R1 once an import row sat beside
  the false clause; a citation authenticates only from a declaration anyway),
  and for a far DEFINITION every restated clause — not only the cited one —
  must be stated by a grounded far row ("far ensures clause 1 `…` is stated by
  no Postcondition row grounded in the dependency …"), so citing one
  kernel-grounded row cannot carry a sibling clause backed only at the
  capability tier. Pinned by the `review_*` tests in `per_clause_proved.rs`
  (also: a far row of the wrong role, and a `backed_by` chain through a
  declaration that still links).
  Second review pass: L9 compared the recorded coverage of the CITED far row
  only, so a sibling clause whose only grounded far rows recorded a depth-1
  bounded discharge rode on the cited row's `Unbounded` record into an
  unqualified `proved` (`is_ok()` with `coverage_unrecorded() == 0`). The site
  is now judged on the least-covered of the cited row and each restated
  clause's best-covered grounded row, and `ImportCoverageBelowClaim` names the
  sibling row; an unrecorded sibling counts `coverage_unrecorded`. Pinned by
  `review_a_bounded_sibling_clause_cannot_ride_on_the_cited_rows_coverage`,
  `review_a_clause_is_covered_by_its_best_grounded_row` and
  `review_a_grounded_row_of_another_far_function_grounds_no_sibling_clause`.
  Rebase onto WS8.6 / WS8.7: the ported c02 claim rows
  (`validation_holes.rs`) and the two-language ratchets
  `b2.gap.kernel_certified_row_backs_an_unrelated_false_clause`,
  `b2.gap.no_per_clause_obligation_backref` and
  `b4.gap.backed_by_reearns_a_count_not_a_clause` flip to PASS with their
  negative twins (`RATCHETS.tsv` edited in the same commit); rows that stay
  open are re-recorded in their per-clause wording.

- **Every import row and every call edge is authenticated (WS1.7 = WS4.8,
  DG-78; F-068).** `validate_linked_module` walked only the rows a
  proof-bearing site cites, so a CALL-ONLY importer was checked against
  nothing: a row recording a garbage digest validated with an EMPTY resolver,
  and a declaration `g(u32)` against a far `g(u64)` validated, even when it
  named the far entity with an obligation-free `backed_by` (audit rows
  `b4.gap.call_only_import_never_authenticated`, `verify.c12.L1`/`L2`, c12
  repro 1a/1b). Now, unconditionally — there is no scope knob, because one
  would be a way back to unauthenticated rows:
  *every* row of `Module::imports` runs L1–L4 (resolve, cycle/depth guard,
  `verify_import_hashed`, recursive validation), cited or not; an unsupplied
  row is `ImportUnavailable`, a wrong module `UnauthenticatedImport { site:
  "import" }`. New rule L10 resolves every CALL EDGE — a body-less declaration
  with a claim-free `backed_by` (`ExternRef { obligation: None }`, the
  explicit spelling, no wire change), or with no `backed_by` whose link
  symbol an authenticated dependency defines and exports — through
  `resolve_extern_ref` with no obligation (symbol, export linkage,
  interposability, producer via the row of the far definition's producer,
  `signatures_compatible`), refusing as `UnauthenticatedImport { site: "call"
  }`. A symbol defined and exported by two or more distinct dependency
  artifacts is the new `ValidationError::AmbiguousImportedSymbol { symbol,
  imports }` (artifacts keyed by digest, so the ratified two-producer shape
  is one exporter). A declaration no dependency exports is an FFI extern —
  legal, and counted by the new
  `LinkedValidationReport::unbound_declarations()` /
  `call_edge_summary()` (`UnboundDeclaration`), which `trust-ir validate
  --link` prints on green and red verdicts alike; the CLI's "all N import
  rows authenticated" line is now true of every row.
  `authenticated_call_edges()` counts the resolved edges. The walk still
  cannot make a producer RECORD a row: that half of F-068 closes with WS5 /
  F-093. `docs/SPEC_RATIFICATIONS.md` §6 amended. Tests:
  `linked_import_authentication.rs` (positive, garbage-digest and signature
  twins, missing symbol, ambiguity with its `Internal` control, libc,
  two-producer rows, interposable call edge, uncited rows), CLI twins in
  `cli_linked_imports.rs`, and `back_compat.rs` (c12 repro 3 after a binary
  round trip).
  *Review hardening (same increment):* call edges resolve at the new
  `trust_ir::ExternRefSite::CallEdge`, which admits no obligation kind and
  admits a local `ExternalWeak` import, so a WS3.15 weak import of a
  dependency symbol is signature-checked instead of wrongly refused as
  interposable; a declaration whose symbol the dependency exports as DATA (an
  initialized global) is refused rather than counted as an FFI extern, and a
  function export beside a data export of one symbol is
  `AmbiguousImportedSymbol`; and a `Constant::SymbolAddr` naming a function a
  dependency exports, with no local declaration, is refused ("no local
  declaration") — it was a call edge compared with nothing and not even
  reported unbound. L10 is pinned to run inside dependencies too. Tests:
  `ws1_7_review_*` in `linked_import_authentication.rs`.

- **Import-table hygiene (WS4.7; F-075, F-076, F-077).** Three changes to the
  v41 import surface, none on the wire.
  *Interning is enforced.* `Module::intern_import` said "never `push`" and
  nothing checked it: a pushed clone of `imports[0]` validated in every tier
  and `validate_linked_module` passed (audit row
  `b4.gap.duplicate_import_rows_admitted`). `validate_module` now refuses two
  EQUAL rows as `ValidationError::ImportTableNotInterned { first, duplicate,
  name }`, mirroring `PredicateTableNotInterned` — in the structural,
  authority, codegen and linked tiers and after a binary decode. The key is
  the whole `ModuleImport` compared with `==`, never a hand-listed field
  tuple, so a future row field (the v44 `scheme`) joins it automatically.
  Producers that intern (clean `e0f43ffaf`'s link emitter) are unaffected.
  *Hash-once is type-enforced.* `verify_import_with_computed_digest(id,
  candidate, actual)` trusted the caller's `actual`; handed the RECORDED
  digest it authenticated a tampered dependency that `verify_import` refused
  (`b4.gap.computed_digest_is_caller_asserted`). The hash-once form is now
  `Module::verify_import_hashed(id, &HashedModule)`: `trust_ir::HashedModule`
  has private fields and one constructor, `HashedModule::new(&Module)`, which
  computes `stable_digest` over the module it stores (a `compile_fail`
  doctest pins that the struct literal does not compile outside the crate).
  The linked validator's memo stores `HashedModule`s. The old name is
  `#[deprecated]` for one release and now ALWAYS recomputes the digest — in
  every build profile — returning `DigestMismatch` when the supplied one
  differs. *One row per `(artifact, producer)` edge is ratified*
  (`docs/SPEC_RATIFICATIONS.md` §6): a mixed Rust+Clean dependency is two rows
  sharing one digest, both authenticate, and consumers deduplicating
  ARTIFACTS key on `digest`; `intern_import`'s rustdoc is reconciled with it
  (`b4.gap.one_import_row_per_producer` and
  `small-designs/LCR-08-import-producer-is-module-level` pass by ratification).
  A `trust-ir-doctests` gate beside gate 9 now runs the `trust-ir` doctests.

- **A bodyless `Linkage::ExternalWeak` function is a declaration (roadmap
  WS3.15, F-058).** `ExternalWeak` is documented as "a weak DECLARATION", yet
  the validator treated a bodyless function as a declaration only at exactly
  `External` (`is_bodyless_external_declaration`), so the one shape the linkage
  exists for — a weak optional import — was `EmptyFunction`, while it validated
  only through the linkage-agnostic contract-only summary door; and
  `Module::first_ffi_boundary` did not count it, so such a summary-carrying
  import was silently target-independent. Both predicates now admit a bodyless
  `ExternalWeak` (new `Function::is_weak_declaration`), so it is an FFI
  boundary (`TargetInfoRequired` without `target_info`; the boundary text reads
  `bodyless external_weak declaration`). Because its symbol may resolve to NULL,
  its address is admitted in exactly one spelling — `Const SymbolAddr { symbol,
  addend: 0 } : Ptr`, which the producer compares against `NullPtr` before a
  `CallIndirect` through the `Ptr` — and three new refusals close the others:
  `DirectCallToWeakDeclaration` (a direct `Call` / `Invoke` of it, or a
  `SeqMap` naming it as its element function `fwd`),
  `WeakDeclarationAsFnDef` (`Constant::FnDef` or a `Constant::Closure` code
  pointer naming it, anywhere in a constant tree: a `Ty::Func` value claims a
  callable non-null function), and `WeakDeclarationAddressNotNullable` (a
  `SymbolAddr` naming it at a non-`Ptr` type or with a nonzero addend, which
  would move a null address off null). A bodyless `AvailableExternally` stays
  `EmptyFunction` (that linkage is a body copy); pinned handle-runtime symbols
  stay `External`-only (`HandleEntryPointDefinedLocally`), and a weak
  declaration reaching a handle stays `HandleForeignDeclaration`. No wire
  change. Rows `b1.gap.extern_weak_declaration_refused`, `b1.uf09` and
  `b5.related.gap.extern_weak_bodyless_declaration_is_empty_function` are ported
  closed in `crates/trust-ir-build/tests/extern_weak_declarations.rs`. The
  null check itself is a PRODUCER rule the validator does not dataflow-check.
  Adversarial review closed two more doors: because the null-checked
  `CallIndirect` is the only way to call a weak import and its `Ptr` callee
  carries no signature, an edge whose callee is a weak `SymbolAddr` (directly or
  through `Copy`) must now declare the declaration's own convention and
  structural signature (`CallEdgeConvMismatch` / `CallEdgeSignatureMismatch`,
  the checks a direct `Call` gets; a pointer laundered through a block
  parameter, `Select` or memory stays trusted as declared, the `FnDef`
  ABI-pinning boundary); and `Switch` case values — constant trees the typed
  walk never visits — may not name a weak declaration in any spelling.
- Declared struct layouts have ONE coherence rule, shared with the layout
  authority and run with or without `target_info` (roadmap WS2.3, F-031; audit
  claim c07). `Pair { a: u32 @ 0, b: f32 @ 0 }` was refused by
  `Module::ty_layout_shape` (`StructLayoutIncoherent`) and by the interpreter
  ("declared layout has overlapping fields"), yet every validator entry point
  returned `[]`, pinned or not; without a target even `offset 12 > size 8` went
  unchecked. The struct-layout pass (renamed `validate_struct_layout_rules`) now
  runs on EVERY module and gains the pairwise-overlap rule it never had
  (`StructLayoutInconsistent { reason: "fields overlap" }`, the same
  `byte_ranges_overlap` predicate `shape` and the interpreter use — zero-sized
  fields never overlap, field order is not a rule). A new
  `validate_declared_struct_layouts` then asks `ty_layout_shape` itself for
  every struct declaring `size` and `align` that no precise rule already named:
  `StructLayoutIncoherent` becomes `StructLayoutInconsistent` with the new
  public reason `STRUCT_LAYOUT_INCOHERENT_REASON` (extent past `size`, packed /
  transparent rule, ...), `TargetScalarLayoutUnavailable` stays itself (it can
  fire only under a pinned non-canonical target), and `MissingFieldOffset` is
  deliberately NOT refused yet (a partial layout stays refused at use time).
  One struct gets one error. The `StructLayoutInconsistent` message drops "in a
  target-pinned module". **Behaviour change:** the premise "target-independent
  IR may carry placeholder layouts" is withdrawn — a declared layout is
  normative wherever it appears and a target-free module is judged against the
  canonical reference layout, exactly as `shape` judges it, so a target-free
  producer whose declared layout is incoherent at that layout is now refused.
  Gate 9 now runs `struct_repr_and_target` and `-p trust-ir
  union_byte_overlap_model` (registry lines in
  `scripts/gates/validator-fail-closed.{trust-ir-build,trust-ir}.tests`); gate 8 gains the differential property
  `struct_layout_validator_agrees_with_shape` over every conformance module.
  The ratified byte-carrier union model is unaffected.
- `trust_ir::diff` / `trust-ir-diff` no longer diff authority metadata as
  empty. The per-function metadata comparison read exactly `producer` and
  `source_provenance`; nothing read `Module.globals` or `Module.spec_modules`,
  and `target_info` was compared only when a tuple-layout table was declared.
  Measured (audit rows `b1.gap.diff_blind_to_{body_gate,display_path,
  function_linkage,calling_conv,globals,spec_modules_and_target}`): a Clean
  body going `Gated` → `Ungated`, an exported symbol going `internal`, a
  global's initializer changing the program's result, or a retarget all
  produced an EMPTY diff and exit 0 while `stable_digest` moved. Each is now a
  `MetaChange`, never gated by `--ignore-proofs`: per function `body_gate`,
  `display_path`, `linkage`, `calling_conv`, `signature` and `attrs`; per module
  `target_info` (always), `global_asm`, `imports`, `global @<name>` (keyed by
  symbol) and `spec_module <name>` (keyed by machine name). `GlobalAddr` is
  fingerprinted by symbol, so global reordering stays cosmetic; likewise a
  spec anchor's `function` / `Function(..)` projection target is resolved to
  the function's symbol, so `FuncId` renumbering stays cosmetic while an
  anchor re-pointed onto another function's old index is still reported. JSON is
  additive in shape; one row is RENAMED — the old `tuple_layout_target` row is
  now the unconditional `target_info` row.
- The text parser is total over UTF-8 (roadmap WS4.1, finding F-066; audit
  row `a.format.text_parser_utf8`, skeptic c09): it returns `Ok` or a
  `ParseError` and no longer PANICS on a multi-byte character.
  `Parser::advance(n)` sliced `input[pos..pos + n]` as BYTES while
  `skip_line` (every `;` comment, unknown `; #` directive, unknown node
  comment and unknown top-level line) and `read_ident` stepped one byte per
  CHARACTER, so `; é` alone died with `byte index N is not a char boundary`
  (exit 101 from `trust-ir validate --format text`, instead of 0 or the
  parse-error exit 2). The cursor now has two moves: `bump()` consumes one
  character (`ch.len_utf8()` bytes) and serves every single-character step;
  `advance(n)` is FALLIBLE and refuses a non-boundary `pos + n` with
  `ParseError("internal: cursor split a UTF-8 scalar at byte {pos}")` in
  every build profile — no `debug_assert!`, so the tested program is the
  shipped one. **Behaviour change:** the bare-identifier alphabet is now
  ASCII `[A-Za-z0-9_.$]`. A non-ASCII symbol such as `café` or `List.mapα`
  (which used to PANIC) is a located `ParseError` at the offending character
  until the quoted-name grammar (WS4.3) prints it quoted; binary, JSON and
  MessagePack carry such names losslessly. Two more sites of the class were
  closed: `bytes:<len>:<hex>` dialect attrs sliced the input by a declared
  byte count (a multi-byte character in the span panicked, and `len * 2`
  could overflow) and decoded pairs with `u8::from_str_radix`, which also
  accepted `+e` as a second spelling of `0e` — the payload is now exactly
  `2 * len` ASCII hex digits read one at a time; and the `true` / `false` /
  `phantomdata` boundary peeks used a one-byte window, so `trueα` read as
  the keyword `true` — they now read the next character and refuse it like
  ASCII `truex`. No wire or golden change. Tests (gate 8,
  `wire-format-goldens`): the `parse_never_panics` leg of
  `crates/trust-ir-conformance/tests/module_roundtrip_fuzz.rs` inserts `é`,
  `→`, `𝕏` and U+0301 at every line start, before every newline and after
  every `;` of every corpus fixture and every fuzzer seed, asserts no panic
  and no `internal: cursor split`, and requires an insertion inside a `;`
  comment to parse to the baseline module (reverting the `skip_line` or
  `read_ident` step to a byte step trips it); a companion sweep inserts a 2-
  and 4-byte character at every character boundary of the corpus; the
  positive / negative-twin / per-site tests and the ported
  `a.format.text_parser_utf8` row live in the same target
  (`tests/text_parser_utf8/`). Gate 3 (`cli-gate-tests`): `trust-ir
  validate` on a `; é` file exits 0, not 101
  (`crates/trust-ir-cli/tests/cli_validate.rs`).
- WS2.8 (F-038): the reference interpreter executes `Inst::BindSlot` as the
  functional update every other party already specified (`inst.rs`, Lean
  `semBindSlot`, the validator's one-`Ptr`-result table,
  `FunctionBuilder::bind_slot`). It used to write in place and produce no
  result, so every builder-emitted `bind_slot` — a module that validated and
  sat inside the proven subset — failed with `MalformedInstruction` ("node
  declares 1, interpreter produced 0"; completeness-critic probe
  `c2_format_probes.rs::binding_frames`, row `crit.unex08`).
  `InterpretValueKind::Frame(u64)` is now `Frame { lineage, slots }` (a
  public API change of the interpreter value model): a handle carries its own
  immutable slot snapshot plus the `OpenFrame` lineage it descends from, and
  the interpreter tracks only which lineages are open. `BindSlot` checks the
  lineage is open and yields ONE new handle with the slot replaced;
  `LoadSlot` reads the handle's own snapshot, so an older handle keeps its
  prior slots; `CloseFrame` through any handle closes the whole lineage (a
  second close, or a use through any of its handles afterwards, is UB).
  Frame handles are typed `Ptr`, not `Unit`, matching the validator, so a
  handle crosses a `Ptr` block parameter — the documented loop-carried
  quantifier lowering — instead of failing there with `TypeError`. The
  `interpret_differential` generator (gate 8) now emits binding frames —
  chains, siblings, and a handle carried across a diamond — so its "no
  structural error on validated IR" property covers them, and the gate gains
  the WS2.8 positive / negative-twin / mutation-control tests. No validator,
  wire or golden change: `InstrResultArityMismatch` already refused a void or
  two-result `bind_slot`. Reading a slot never bound on the handle read is
  still UB here where Lean yields `undef`; WS2.10 decides that.
- WS2.8 remainder (F-038): ratchet row `crit.unex08` is ported and PASS.
  The critic probe `c2_format_probes.rs::binding_frames` measured one vector
  for a builder-emitted binding frame: validator, interpreter run, binary /
  text / JSON round-trips, proven subset and codegen validator. The GAP it
  recorded was a module that validated, round-tripped and sat in the subset,
  yet failed in the interpreter with "node declares 1, interpreter produced
  0". Three gate-8 tests in `interpret_differential` now pin the PASS. They
  run the built module and its binary, canonical-text, JSON and MessagePack
  images:
  - `crit_unex08_builder_binding_frames_agree_in_every_format` (positive).
    `bind_slot` has one `Ptr` result. Each image validates and is inside the
    subset. Unlicensed, the codegen validator's only refusal is
    `UnlicensedBodyForCodegen`; once licensed it has none. Each image
    executes to 42.
  - `crit_unex08_literal_probe_is_refused_by_poison_inspection_not_arity`
    (negative twin). This is the critic's literal shape: it reads the
    pre-bind handle and discards the one `bind_slot` returned. It holds the
    same static agreement, but execution refuses it with the named UB
    "integer use: use of an uninitialized value". That handle's slot is
    unbound, which is scalar poison. The `LoadSlot` only transports it and
    the `add` inspects it. The refusal is never `MalformedInstruction`.
  - `crit_unex08_zero_result_bind_slot_is_refused_in_every_format`
    (mutation control). The zero-result node the retired interpreter
    executed survives every transport. Each image is then refused by
    `InstrResultArityMismatch` in the validator and `MalformedInstruction`
    in the interpreter.

  The entry above ends by saying an unbound slot read "is still UB here".
  That sentence is superseded. WS2.10 (`90266919`) made the read scalar
  poison in both engines, matching Lean's `initFrame` `.undef`, and made
  inspecting it UB. No interpreter, validator, wire or golden change.
- WS2.8 remainder, review: four claims of the `crit.unex08` port were
  broader than what the tests checked, and each is now pinned.
  - "One `Ptr` result" was checked only through `result_tys`, which reads
    the op's result table and never the node. The static helper now also
    asserts that the node declares one result.
  - "Every format" covered only the canonical text spelling. Every image set
    now includes the exact transport spelling too (`text_checked`, what
    `trust-ir convert --to text` writes). It must parse back to the module
    itself, sparse value ids included.
  - "No transport launders the arity" was checked only for zero results.
    `crit_unex08_review_two_result_bind_slot_is_refused_in_every_format`
    adds the two-result node. It survives all five transports and both
    engines still refuse it by name.
  - "Refused at the `add`, never at `LoadSlot`" was checked only by message
    text.
    `crit_unex08_review_uninspected_pre_bind_read_executes_in_every_format`
    removes the one inspection. The literal shape still loads the unbound
    slot and still closes the frame through the pre-bind handle, and it
    executes to 42 in every image.

  The `Ptr` typing also had no executing-side negative.
  `crit_unex08_review_bound_handle_is_ptr_typed_across_an_edge` carries the
  bound handle across one block edge. Through a `Ptr` parameter it runs to
  42. Through a `Unit` parameter, the type the interpreter once gave frame
  handles, every image is refused. The validator reports
  `BranchArgTypeMismatch` and the interpreter reports `TypeError` at the
  edge. Test-only: no interpreter, validator, wire or golden change.
- WS2.5 — the unwind surface is validated, fails closed in the interpreter,
  and is ratified as the panic=abort projection (F-032, F-041; audit c15
  item 1). The format text (`inst.rs`) defines an `Invoke`'s unwind edge as
  entering "a block that BEGINS with an `Inst::LandingPad`", and a pad as the
  first instruction of a block an `unwind_dest` names; the validator checked
  only that the unwind block was parameter-free. Measured on the pre-fix
  tree: an `unwind_dest` that was `unreachable` or `resume null`, a pad in the
  entry block, a pad mid-block, an orphan pad, a pad block also entered by a
  `Br`, and `normal_dest == unwind_dest` all validated under every door. New
  per-function pass `validate_unwind_structure`:
  `UnwindDestWithoutLandingPad { block, target }` when an `unwind_dest` does
  not begin with a pad or equals the invoke's `normal_dest`;
  `MisplacedLandingPad { block, reason }` when a pad is not first, is in the
  entry block, is named by no invoke, or heads a block some `Br` / `CondBr` /
  `Switch` / normal edge also enters, and when a `Resume` re-raises "a value
  no landing pad produced" (no pad in the function, the pad's selector, or a
  literal). A pad shared by several invokes stays legal. The Resume rule is
  deliberately narrower than "the operand is a pad's first result": the
  in-repo producer's shared-cleanup lowering re-raises `load exn_slot`, and
  under SSA dominance no pad result is available in a cleanup block several
  pads branch into. The reference interpreter's `LandingPad` arm now returns
  `UnsupportedInstruction` ("landingpad entered without an unwind edge")
  instead of fabricating `(null, 0)`; `Invoke` keeps taking the normal edge,
  now documented as the ratified panic=abort semantics. New
  `ModuleValidationReport::unwind_surface()` lists the functions carrying
  `Invoke` / `LandingPad` / `Resume`, against which the new
  ub-numerics-policy §4 paragraph "Unwind surface under panic=abort" (mirrored
  in `LIMITATIONS.md`) states that a verdict covers the panic=abort
  projection only and a panic=unwind consumer must not rely on it.
- A B4 obligation scope (`ProofObligation.function`) must resolve to exactly
  one function (`ObligationFunctionScopeUnresolved`, audit c15 item 5; the
  WS1.8 scope-consistency item, landed early). Only
  `site` was resolved, so `function = Some(f77)` with no site validated in a
  two-function module.
- `Inst::CoroSuspend` is held to the function signature like the `Return` it
  macro-expands to (`GEP` + `Store` + `Return(value)`) — WS2.1, closes F-028.
  Only `Inst::Return` operands were compared with `FuncTy::returns`, and
  `frame` was never typed, so a `-> u64` generator could yield a `bool`, a
  `-> ()` or `-> (u64, u64)` function could yield one value, `frame` could be
  a `u64` — each caught only dynamically, by the interpreter or trust-cg's own
  return check — and, the v43 consequence, a `-> handle<Nat>` function could
  yield a `Ptr`: a forged handle the transport rule never saw, because nothing
  ON the node was handle-typed (audit row c03; measured: every library entry
  point and the CLI returned clean). The `Return` body is factored into
  `check_return_values`, which both terminators call (a suspend as the
  one-operand `Return` of `value`), so a suspend now reports the existing
  `ReturnArityMismatch { actual: 1 }` / `ReturnTypeMismatch`, with `Return`'s
  refinement handling: a `Refine` pair is exempt from raw equality and is
  decided by implication in the refinement layer, where `consumption_role`
  now files `CoroSuspend` under the `ReturnValues` site (it was
  `NoDeclaredRequirement`) — so a `Refine(u64, p)` yield into `-> u64`
  validates and an unrefined yield out of a refined signature is
  `RefinementNotImplied`. `frame` must be pointer-like (`OperandNotPointer`,
  op `coro_suspend`, the GEP-base rule). `CoroSuspend` stays outside the v43
  handle transport set (DG-36): an honest handle-yielding coroutine is still
  `InvalidHandleUse`. Gate 9 (`validator-fail-closed`) now also runs
  `handle_types` and `coro_suspend_signature` (two lines in
  `scripts/gates/validator-fail-closed.trust-ir-build.tests`). No wire or golden
  change. Producer note: a `~/trust` coroutine body whose yield type differs
  from its return type now fails validation, as the interpreter and trust-cg
  already refused it dynamically.
- `ExtractField` / `InsertField` over an ENUM is checked (audit c06, the
  static half). `validate_field_access` returned early on `Ty::Enum(_)` ("left
  to dedicated enum lowering", which never existed) and skipped every check —
  lane range, declared lane type, inserted value type, even `InsertField`'s
  result type — so `insert_field i64 <enum>` validated and recorded an `i64`
  for an enum value. Measured on 4efb21bc: an out-of-range lane, a lane read at
  a type no variant has, and a tag read at `u64` all validated (also for
  codegen) and failed only in the interpreter. The rule follows the
  `[tag, fields..]` value model the interpreter and the `~/trust` producer
  share: lane 0 is the tag at `EnumDef::canonical_tag_repr().ty()`, lane
  `i >= 1` is field `i - 1` of the active variant. A lane beyond every
  variant's arity, a tag lane at any other type, and a payload lane at a type
  that is the lane type of NO variant are refused as the new
  `EnumLaneAccessInvalid`, as is ANY `insert_field` on lane 0: a re-tag keeps
  the old variant's payload under the new tag, and with equal arity the
  interpreter runs it to `Ok` (c06 `p1_insert_tag_overwrite`) — a variant is
  constructed whole with `Const`, which is all the `~/trust` producer emits
  (Clean emits no `Ty::Enum`); a wrong `InsertField` result type is
  `OperandTypeMismatch { role: "result" }`, as for every other aggregate. The
  refinement consumption rule now covers enum lanes existentially (some
  variant's lane must admit the value / establish the read), reporting each
  candidate variant's own `RefinementNotImplied` / `RefinementTypeInvalid`.
  Still accepted, deliberately: a lane that is right for SOME variant used on
  a value whose active variant is another — which variant is active is not a
  static fact of the type; closing it needs a variant-indexed projection.
  Tests: `crates/trust-ir-build/tests/enum_lane_access.rs`, including the
  ported `b6.enum.payload_projection_unchecked` ratchet, now asserting the hole
  is closed.
- `ExtractField` / `InsertField` over an ENUM is checked (roadmap WS2.2,
  F-029 static half; audit c06). `validate_field_access` returned early on
  `Ty::Enum(_)` ("left to dedicated enum lowering", which never existed) and
  skipped every check — lane range, declared lane type, inserted value type,
  even `InsertField`'s result type — so `insert_field i64 <enum>` validated and
  recorded an `i64` for an enum value. Measured on 4efb21bc: an out-of-range
  lane, a lane read at a type no variant has, and a tag read at `u64` all
  validated (also for codegen) and failed only in the interpreter. The rule
  follows the `[tag, fields..]` value model the interpreter and the `~/trust`
  producer share: lane 0 is the tag at `EnumDef::canonical_tag_repr().ty()`,
  lane `i >= 1` is field `i - 1` of the active variant. Each refusal uses the
  error the rest of the aggregate family uses (no new `ValidationError`
  variant): the `InsertField` result-type rule is now checked FIRST and for
  EVERY aggregate kind (`OperandTypeMismatch { role: "result" }` — a struct
  insert with a wrong result type AND a bad field now reports both); an enum
  with no canonical tag repr refuses every projection, a lane beyond every
  variant's arity is `FieldAccessInvalid` "field {i} is out of range for every
  variant of {ty}", ANY `insert_field` on lane 0 is `FieldAccessInvalid`
  "insert_field cannot rewrite an enum discriminant; construct the variant
  with Const" (a re-tag keeps the old variant's payload under the new tag; the
  `~/trust` producer builds variants with `Const`, Clean emits no `Ty::Enum`),
  and a tag read at a non-canonical type or a payload lane read/written at a
  type NO variant has there is `OperandTypeMismatch` (role `field` / `value`,
  `expected: "one of {variant: ty, ..}"` for a payload lane). The refinement
  consumption rule covers enum lanes existentially (some variant's lane must
  admit the value / establish the read), reporting each candidate variant's
  own `RefinementNotImplied` / `RefinementTypeInvalid`.
  Wrong-variant-but-valid-lane is ratified as undefined behaviour
  (`docs/ub-numerics-policy.md` §4) and is now refused DYNAMICALLY: the
  reference interpreter's `ExtractField` / `InsertField` decode the active
  variant from lane 0 (`EnumDef::effective_discriminants`) and answer
  `UndefinedBehavior` "enum {ty}: lane {i} belongs to no field of active
  variant {name}" when the lane is beyond it or of another type, and refuse a
  lane-0 `insert_field` as UB (it used to re-tag silently: c06
  `p1_insert_tag_overwrite` ran to `Ok 7`). Lean `semInsertField` throws UB on
  `.Enum _` lane 0 (`ExecutableFixtures.lean`); Lean's missing lane-TYPE check
  (all aggregate kinds) is recorded on the B3 depth ledger. Honest limit, pinned
  by a test: a wrong-variant lane of the SAME type in both variants is
  invisible to both engines until the variant-indexed projection (WS2.2
  DECIDE (a), `variant: Option<u32>`, a reserved wire version) lands.
  Tests: `crates/trust-ir-build/tests/enum_lane_access.rs` (gate 9), including
  the roadmap fixture `enum AB { A(i64), B(ptr) }` with one named-reason twin
  per rule, the static/dynamic mutation control, a struct control, and the
  ported `b6.enum.payload_projection_unchecked` ratchet, now asserting the
  hole is closed; `crates/trust-ir-conformance/tests/interpret_differential.rs`
  (gate 8), whose generator now constructs and projects enum variants —
  honest lanes run to `Ok`, wrong-variant lanes reach the named UB, never a
  structural code — plus a tag-rewrite conformance fixture refused by both
  engines. WS3.14's `interpreter_store_refuses_a_forged_uninhabited_variant_value`
  forged its value by exactly that re-tag, which the interpreter now refuses
  before `Store`; it asserts that refusal and reaches `Store` through a forged
  entry argument instead (with an honest-`A` control), so the encode-direction
  refusal stays pinned.
- The pinned handle-runtime symbol namespace is guarded in its third spelling.
  `validate_handle_entry_points` keyed on `Function.name` / `Global.name`
  only; `Constant::SymbolAddr { symbol }` (admitted for `Ty::Ptr` and any
  `Ty::Func(_)`, with no `FnDef` provenance for the call-edge checks) let a
  `CallIndirect` reach `trust_bignum_nat_is_zero` as `fn(Ptr) -> Bool`, and a
  handle-free module could drive the whole runtime through relocatable
  constants — measured: both validators returned `[]`. Every constant tree
  (global initializers, function-body `Const`s, nested aggregates) is now
  walked and a pinned symbol is refused as `HandleEntryPointAddressTaken`.
- `Inst::Invoke`'s normal edge is arity- and type-checked against the
  continuation's block parameters (`validate_block_param_arity` handled
  `Br`/`CondBr`/`Switch` and dropped `Invoke` into `_ => {}`; the only other
  edge walk returned early unless a side was `Refine`), and its unwind edge
  must enter a parameter-free block. Measured: `bb0(%p: Ptr): invoke noop()
  to bb1(%p)` with `bb1(%h: handle<..>)` validated clean while the same edge
  through `Br` was `BranchArgTypeMismatch`. Pre-dates v43, but the v43
  transport rule admits `Invoke` on the premise that edge types are checked.
- `Module::resolve_extern_ref` (R4) refuses a BARE far re-declaration
  (`ImportVerificationError::FarSiteIsUnbackedDeclaration`). R3 picks the
  unique far function carrying the symbol, which may be body-less, and R4
  only refused `Internal`/`Private` linkage — so a dependency that merely
  RE-DECLARED the symbol satisfied every check at layer 1 while proving
  nothing, there being no body for the cited obligation to be about and no
  further module named that has one. Measured on the pre-fix tree: a
  dependency whose `f` was stripped to a bodyless `External` row, keeping its
  `Certified` Postcondition, resolved `Ok(())` at BOTH sites. The rule is
  deliberately narrow — a declaration that RECORDS a cross-crate backing
  (`summary.backed_by`, or an `InheritedFromCallee { external: Some }`
  certificate naming it as callee) is still admitted, because that is the
  ratified transitive chain and the closure walk follows the citation it
  names; `backed_by: None` with no such certificate is NOT RECORDED, and
  refused. Layer 2 already refused the shape through recursive validation, so
  this closes the hole for a consumer calling layer 1 on its own.
- A body-less declaration's `proved` summary is authenticated only by
  `backed_by` — on the INHERITED path as well, now pinned by a regression
  test rather than left to be re-derived. An `InheritedFromCallee`
  restatement is scoped to the callee and `R2` binds the local side of a
  citation to a declaration, so every restatement lands on a declaration and
  counts zero; an authenticated inheritance grounds the obligation it restates
  and never a summary's clause text. The counting rule counted Discharged/Certified contract rows
  scoped to a declaration, so a kernel-certified `(= 1 1)` beside a body-less
  `f` earned `proved` for any clause text (locally, and — through an
  `InheritedFromCallee` restatement — inside `validate_linked_module`, where
  the same clause via `backed_by` was refused as differing from the far
  summary), and a dependency that merely DECLARED a symbol authenticated an
  importer's `backed_by`. Declarations now count zero local rows (a `Failed`
  row still refutes); the refusal names the rule. Definitions are unchanged,
  and the `backed_by` + inherited-obligation chain through a declaration
  still re-earns.
- `Module::verify_import_with_digest` is renamed
  `verify_import_with_computed_digest` and documented as fail-closed: it is
  the hash-once hook for a walk that computed the candidate's digest, and
  passing the recorded `import.digest` compares the record with itself. The
  linked validator's memo path now passes the digest it computed.
  `NATIVE_BUNDLE_IDENTITY_CONTRACT_DIGEST_CONTEXTS`, the `stable_digest`
  rustdoc and the conformance determinism test read `MODULE_IDENTITY_DOMAIN`
  instead of re-spelling `"trust_ir.module.v2"`.
- Docs: `TRUST.md` gains item 9 (the pinned handle runtimes and their shims
  are trusted, not re-checkable), the §6 bump path no longer names v43 for the
  `ModuleImport.scheme` discriminator (v42 shipped declared tuple layouts and
  v43 shipped `Ty::Handle`; neither carries one), `README.md` and the
  `binary-format.md` error table state the v43 read set, the `Ty` variant count is 40 (39 encodable + `Error`), the
  authority-tier entry points document their `UnauthenticatedImport` refusal,
  and the runtime crate that defines the pinned symbols is documented as
  trusted base outside the validated lane.
- `Module::executable_content_digest_v1` no longer observes
  `Function.body_gate` or `Function.display_path` (v41 had folded them into
  the projected image, so licensing a verified module changed the identity the
  license named). The identity projection now writes gate tag 0 and an absent
  path, and neither field raises the projected wire version, so a module whose
  only v41 feature is the license projects to its exact pre-v41 bytes. The v41
  ABI/linkage residue (`Linkage` tags 5–8, `FuncAttrs.{naked,
  target_features}`, `Global.{section, visibility, retained}`,
  `Module.global_asm`, `Module.imports`) stays identity-bearing, and
  `Module::stable_digest` and every faithful `ModuleBinaryOptions` projection
  still observe the license (`RawV38`/`CanonicalV38` keep refusing it with
  `ContractSurfaceRequiresV41`). No wire change; the domain stays `.v1`
  because the recipe never shipped (`v0.13.0` predates it) and every
  unlicensed module's digest is unchanged.
- Function-item constants must name a unique module function with the exact
  declared signature, including nested/captured items never used by an indirect
  call. Shared constant and typed-container walks are iterative, use depth-sized
  iterator scratch, and avoid repeated diagnostic-prefix copies. Vector failures
  now identify the failing lane and element type.
- Native compiler-request identity v7 closes a real collision between distinct,
  valid generic type arguments: request type tag33 previously encoded both
  `Refine` and `Isize`. `Refine` now uses its own tag37, compiler-facts digests
  advance to v5, bundle digests/schema to v7, and the identity contract to v2.
  Older bundles are rejected; producers must regenerate requests and evidence,
  with no authority-compatible legacy digest fallback. Module binary tags and
  legacy-only module identities are unchanged by this repair. The migration and
  regression evidence are in the internal doc
  `docs/native-request-identity-v7.md` (not in the public snapshot).
- Dialect lowering drops source provenance from each rewritten function before
  applying a replacement or deletion, including when later lowering fails or
  exhausts its iteration limit. Untouched functions retain their carriers.
- `CleanCic` lineage and persisted obligation-cache identities now bind an
  obligation's exact optional IR site. Site-only obligations also bind the
  resolved owning function body; mismatched or dangling coordinates fail
  closed. The public domains advance from
  `trust_ir.proof.clean_cic.lineage.v4` and `trust_ir.obligation.digest.v4` to
  v5, deliberately invalidating prior `CleanCic` certificates and obligation-
  cache entries.

**Note on 0.7.0.** The workspace version passed through 0.7.0 (release commit
`chore(release): 0.6.0 -> 0.7.0`, 2026-08-20), but **no `v0.7.0` tag was ever
pushed** — the next cut went straight to 0.8.0 the same day. The 0.7.0 section
below records that window; do not cite a `v0.7.0` tag. Re-measured 2026-08-30:
still absent from the release remote. `v0.2.0-windows` is likewise **not** a
release tag — it exists only in the development repository.

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
