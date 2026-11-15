# Scope and limitations

TrustIr's 0.x line is a preview of a shared proof-carrying compiler IR. Representing a
program or proof claim is not the same as proving it, and each guarantee is
limited to the checker and semantic fragment that establishes it.

- The Rust API and schema are evolving under 0.x versioning. No minimum
  supported Rust version is promised yet.
- `ModuleBuilder` and `FunctionBuilder` construct data; they do not make it
  valid. Callers must run validation explicitly.
- Structural `trust-ir validate` checks IR well-formedness and evidence
  invariants. It does not prove every carried claim. `Trusted` remains a
  faith-based status, and rejection of `Trusted`/`Failed` states plus lineage
  checking are explicit CLI gates.
- Binding-frame validation joins handle generation liveness, possible aliases,
  and slot-signature origins across normal and unwind control-flow edges. A
  possibly closed or non-frame handle is refused; reopening a declaration
  does not revive an older handle. The join loses path correlations and may
  conservatively refuse a safe program. Unreachable blocks receive only a
  conservative structural check, not a proof of reachability. Closing a frame
  somewhere still does not establish closure on every exit or LIFO discipline.
  A close with multiple possible declaration origins cannot credit any one of
  them for this syntactic check; branch-correlated opens may therefore be refused.
  Rust and Lean both close a dynamic lineage shared by functional snapshots.
  Lean checks liveness before slot bounds or the bind-value lookup, rejects
  double close, and keeps its monotone lineage counter across call restoration.
  Recursive frame-identity validity now covers every runtime value carrier;
  successful frame operations preserve it, including loading nested handles.
  Bodies combining frame operations, Copy, complete scalar/vector Select,
  all original scalar/vector unary and binary operations (including explicit-choice
  min/max), Undef and NullPtr,
  and CFGs combining those bodies with ordinary branch/switch/return controls,
  preserve recursive identity validity on successful fuel-bounded execution.
  This includes scalar selected-arm laziness, vector lane transport, parameter publication
  and temporary retirement. Incoming arguments must themselves be recursively
  valid; checked parameter binding cannot establish this external-input premise.
  Caller restoration requires valid saved locals and return values. This does
  not establish recursive validity of arbitrary inputs or its correspondence
  with structural validation. Slot-type agreement remains a validation premise
  in Lean. Parameterized snapshot-typing laws preserve exact declared signatures
  through successful frame operations, given a value-typing relation and typed
  writes; they do not prove that validation establishes those premises or its
  refinement bridges. The lifetime laws
  and kernel traces are not a general proof of equivalence between the
  interpreters or of source-language binding lifetimes.
- There is no general proof from arbitrary Trust, Clean, or Rust source to
  machine code. Certificate authority is checker-specific and currently
  restricted to documented fragments. See [`TRUST.md`](TRUST.md) and
  [`lowering-target-subset.md`](lowering-target-subset.md).
- The tensor region is integer-only. `Ty::Tensor` admits only integer
  elements, and its operations are `TensorContract`, `TensorMap`,
  `TensorReduce`, `TensorView`, `TensorGather` and `TensorScatter`. A tensor
  has no memory layout, so it cannot be loaded, stored or allocated, and no
  backend lowers any of the six: the codegen gate refuses each. The
  kernel-checked theorem covers the integer matrix multiply of SemR's model,
  not machine code; the map, the reduction, the view, the gather and the
  scatter are tested against SemR, not proved. A `BoundsCheck` obligation
  sited on a gather or scatter is admitted, but no trust-ir component
  generates or discharges one: its status and evidence are checked as every
  other obligation's are. Float elements are not carried yet. Weight blobs
  (`Constant::TensorBlob`) name integer tensors by the SHA-256 of their
  bytes; nothing checks that a blob's bytes are the weights a source program
  meant, a global may not hold one, and no backend lowers one. Both
  executable models charge each tensor instruction one fuel unit, like any
  node, and materialize its whole result, so fuel does not bound its time or
  memory: an outer product of two large vectors, or a broadcast to a large
  shape, can exhaust the host.
- The reference interpreter is bounded and deliberately partial. It is a
  conformance and diagnostic path, not a production runtime or code generator.
  A call to a bodyless declaration (an external symbol, a runtime handle entry
  point) is refused as unsupported unless the embedder installs a host model
  of that symbol; a run a host model served is host-assisted, reports it
  (`host_calls`), and rests on that model, not on the module.
- Variadic functions are half-carried, by design. A call to a variadic
  DECLARATION (a `printf`-shaped C symbol) is a host call carrying the full
  argument list — the fixed prefix is checked against the signature, the
  variadic tail only for being whole values (a runtime handle is refused
  there: a variadic slot has no exact type to transport one at). A variadic
  DEFINITION is out of scope: the format has no instruction that reads a
  variadic argument (`va_list` / `va_arg` have no spelling — `c_variadic`
  bodies are unstable Rust), so a body could not observe the tail it was
  passed, and the reference interpreter refuses to execute one
  (`SignatureMismatch`, "non-executable vararg signature"). Carrying a
  variadic body is a format decision, not an interpreter gap.
- Reference-interpreter `Ty::Func` storage occupies one target pointer word
  with pointer alignment on the supported 32/64-bit little-endian layouts.
  Its bytes encode a module-local symbolic code address, not a host or native
  executable address. Zero is null; nonzero addresses must name a registered
  module function. Data allocations reserve a disjoint address range. Byte
  copying preserves the code word; indirect calls still check the declared
  value/call/callee signatures and calling convention. This does not supply
  closure-by-value memory layout or native ABI/proof authority.
- Float widths are binary16, binary32 and binary64 (`F16`, `F32`, `F64`).
  There is no `f128` type, and `f128` is out of scope: the WS8 F-127
  decision gate on semantics authority and float widths ruled it so on
  2026-10-02 (DG-08), because it is unstable Rust and no shipping producer
  emits it. Admitting it later is a new `Ty` variant landed together with its
  Lean semantics and a wire version, reopened only by a stable `f128` that a
  producer emits. `F16` executes in the reference interpreter (computed at a
  wider precision and rounded once, bit-exact) but stays OUTSIDE the proven subset:
  both engines now execute binary16, but versioned subset admission and
  consumer/native lowering remain open. Observable NaN payloads still refuse
  in Lean at every width. See the qualification, `reports/2026-11-06-binary16-execution.md` in the
  development tree.
- Wire v65's `SingleInhabited { variant }` describes a tag-free enum image
  with multiple declared variants, retaining nominal inactive types such as
  `Infallible`. It requires the selected variant to be inhabited and every
  inactive variant to be structurally uninhabited; legacy `Untagged` still
  requires one declared variant. Empty nominal declarations have no physical
  layout or constructible values. Format/interpreter tests do not establish
  agreement with a rebuilt Rust producer, native consumers or a platform ABI;
  those require their actual producer/consumer checks. A consumer must refuse
  an unsupported encoding instead of inventing a canonical tag.
- Drops execute only through a stated destructor. `Inst::Drop` and its
  unwinding twin `Inst::DropInvoke` (wire v55) run, in both engines, as a call
  of the glue the module's drop-glue table names for the dropped type; that
  the glue IS the source language's destructor is the producer's claim, which
  the format cannot check. A drop at a type with no row is refused by both
  engines and by the default codegen gate, never treated as a no-op. No
  backend lowers a drop yet, so drops stay outside the lowering-target subset.
- Unwinding executes only under a named strategy, and only partially.
  `Invoke` / `InvokeIndirect` / `AssertInvoke` / `DropInvoke` / `LandingPad`
  / `Resume` are structurally validated and carried faithfully for backends.
  Both engines run under a `PanicStrategy` (the ratified unwinding rule,
  §21 of the internal spec ratifications): the default `Abort` is the `panic = abort` projection (the unwind
  edge is never taken, a landing pad fails closed, `Resume` is unsupported);
  `Unwind` raises, catches, binds pads and resumes. Not modelled under
  either: typed catch clauses and filters (refused), phase-one search (the
  entry's caller is assumed to catch), foreign exceptions, `catch_unwind`
  payload extraction, and the `CallCannotUnwind` boundaries (below). A
  verdict computed under `Abort` about a function with an unwind surface
  (`ModuleValidationReport::unwind_surface()`) covers panic=abort only; a
  consumer that compiles the module with `panic = unwind` must use one
  computed under `Unwind`. No backend lowers a panic=unwind build yet, so
  `InvokeIndirect`, `LandingPad` and `Resume` stay outside the lowering-target
  subset.
- Typed `CallCannotUnwind` / `CallIndirectCannotUnwind` boundaries are carried
  faithfully and typechecked like ordinary calls. They state a normative
  no-crossing host-unwind boundary, not NoPanic evidence. Reference execution,
  Lean execution, Core reflection and the proven lowering subset refuse them
  until that boundary is modeled; a native consumer must enforce it or refuse,
  even in a function without other EH information. Authentic Rust FnAbi
  provenance and actual final target call-range enforcement are separate
  source/backend obligations, not inferred from the instruction alone.
- Borrow discipline is checked only structurally: a `BorrowMut` through a
  shared reference and an `EndBorrow` of a non-borrow are refused, but borrow
  LIVENESS (one `EndBorrow` per path, no two live `BorrowMut`, no use after
  `EndBorrow`) is a producer obligation, unchecked for Clean and hand-built
  producers (`TRUST.md` item 12). These instructions are an allocation-keyed
  permission machine, not Rust's reference semantics: a Rust producer emits
  none of them and spells every reference as the place's address (adopted
  2026-10-08, "A Rust reference carries no permission instruction"; the Trust
  MIR bridge still emits `Borrow` / `BorrowMut` until its respelling lands), so
  Rust's own reference rules (validity at creation, aliasing) are not stated
  in the format. For safe code rustc's borrow checker discharges them; for
  `unsafe` code nothing here decides them, and a reference to a null or
  dangling place that is never dereferenced is not flagged.
  `readnone` / `readonly` are checked against a defined body; on a bodyless
  declaration they remain a claim. So is a v59 typed effect summary
  (`FunctionSummary.effects`): checked against a defined body, and on a
  bodyless declaration admissible at a call only once `validate_linked_module`
  authenticated its `backed_by` — otherwise the caller havocs.
- `Switch.exhaustive_enum_unreachable` is a zero-authority producer hint.
  The validator checks that the `default` edge passes no arguments to a
  parameter-free block that is exactly `[Unreachable]`, that the case values
  are distinct as selector values, and — only when the
  selector resolves to an enum's tag lane — that the cases cover every
  variant not provably uninhabited. Over any other selector (a block
  parameter, a call result, a plain integer) a validated flag does NOT
  establish that the cases are exhaustive, and a verifier must not use it as
  a fact without re-deriving the case set.
- The codegen license (`Function::body_gate`) is the only checked license.
  `validate_module_for_codegen` binds the `clean-kernel-tv` authority to an
  in-module, kernel-rechecked translation-validation certificate, and that
  certificate proves the emitted body equal to its recorded comparand, not to
  the Clean source. Other gate authorities carry no evidence the format
  checks; recognizing one is the consumer's decision. The
  `@trust-internal::clean-origin-disclosure-v1` rows are unauthenticated
  producer claims: the validator binds a `fn:N` row's key to a bodied function
  of the module, but never parses or checks a row's content (its tier or
  `body_gate` text).
- The v41 producer rule — a bodied function in a v41-or-later blob carries a
  `body_gate` claim — is checked only for a module DECODED FROM BINARY:
  `validate_module_as_decoded` reads it against the header version the
  decoder returns beside the module (`deserialize_module_with_wire_version`),
  and `trust-ir validate` applies it to binary input. A `Module` carries no
  wire version, so a hand-built module, a text / JSON / MessagePack parse, or
  a plain `deserialize_module` result is not held to it: `validate_module`
  accepts a bodied `None` there, and the CLI states for such input that the
  rule is unchecked rather than passed. The check reads the header, which is
  the writer's declared version: a v41-or-later blob with a bodied `None` is
  refused whatever its content's history, and the writer keeps a faithful
  re-emission of pre-v41 content at its pre-v41 version, so that case never
  reaches the refusal.
- The Lean package does not yet model the entire TrustIr instruction set. Its
  axiom audit retains the explicit first-party `ay_sound_unsat` axiom, and
  Rust-to-Lean correspondence remains part of the trusted boundary.
- Canonical text is human-oriented and does not yet carry every field. Text
  refuses what it cannot carry (`format::text_losses`): a module with such a
  field prints with a `; #lossy:` marker that the parser refuses,
  `format::canonical_checked` (and `trust-ir convert --to text`,
  `trust-ir-fmt`) refuse it with the full loss list, and the parser refuses
  any directive or top-level line it does not know rather than dropping it.
  The layout and linkage surface is carried (struct field names and offsets,
  enum layout descriptors and variant field names, global section /
  visibility / retained, `global_asm` blocks, the `switch` exhaustiveness
  hint; WS4.5), and the proof surface — function summaries (`proved`,
  `backed_by`), typed clause bindings, certificate assurance, `clean_cic`
  kernel re-check directives, the v41 obligation kinds and the v46 typed spec
  carrier — is carried (WS4.4), except a clause sort nested deeper than 64
  levels, which is refused.
  Symbols outside ASCII `[A-Za-z0-9_.$]` (for example `m::f`, `café` or
  `Nat.add✝`) are among the refused fields. The marker is a tripwire, not
  integrity: text is unauthenticated. Two text spellings exist and only one
  is a transport: `trust-ir convert --to text` (`format::text_checked`)
  prints the module's own value ids and block order, so a loss-free module
  parses back EQUAL, with the same `stable_digest`; the canonical spelling
  (`trust-ir-fmt`, `format::canonical_checked`) renumbers values densely and
  reorders blocks first, so what parses back is the canonicalized module,
  whose `stable_digest` differs from the original's whenever the producer's
  numbering was not already canonical. Do not record an import digest of a
  module that went through canonical text. Binary, JSON, and MessagePack are the
  lossless module paths. Proof lineage is a separately versioned sidecar.
- `trust-ir-diff` reads all four formats, but compares the debug file
  table by its length only and never reports a module rename, value names,
  spans, obligation diagnostics or scope trees (the scope tree is opt-in,
  `--include-debug`); a text
  input carries only what text carries (see above). Unknown dialect
  payloads round-trip, but their semantics and lowering legality remain owned
  by the implementing backend: `validate_module` accepts them structurally,
  while `validate_module_for_codegen` refuses a `DialectOp` outside the in-tree
  namespaces (`vector`, `gpu`, `avx512`, `ane`, `trust_rust`) as
  `UnlowerableForCodegen`. A pointer-like indirect callee may carry a nominal
  dialect argument but cannot return one; only an exact `Ty::Func` callee can.
- The opt-in dialect schema registry checks exact fixed operand prefixes and
  an optional homogeneous, zero-minimum `OperandType::VariadicExact` tail.
  Every tail operand is checked against its actual SSA type. This is structural
  validation, not semantics, callback behavior, aggregate lifetime, or proof
  admission. Variadic operation operands do not enable variadic function
  signatures, and schema declarations do not alter the module wire format.
- Module identity is portable across checkouts; module BYTES are not yet.
  `Module::stable_digest`, the identity an import row records, leaves the
  debug source paths (`Module.files`) out, so a dependency built in one
  directory authenticates in another. The binary encoding and
  `executable_content_digest_v1` keep those paths, so two builds of one
  source at two checkout paths are different files and different codegen
  cache entries. Byte reproducibility across machines therefore needs a
  producer that writes portable (root-relative or remapped) source names, and
  neither shipping producer guarantees that yet: the rustc-based producer was measured
  (2026-09-17) recording the absolute checkout path and ignoring
  `--remap-path-prefix`, and the Clean backend records its source file path
  exactly as given on its command line, so an absolute invocation lands in
  the bytes.
- Give-back certification, the AY adapter, and the workspace-excluded
  `rustc_private` frontend are experimental or fragment-specific. Optional
  Clean-backed anchors require their exact mapped dependency revisions.
- Synthetic benchmark fixtures exercise construction, validation, and
  serialization. They do not establish an aggregate performance or scalability
  claim.
- The shared Core execution assembler builds candidate proofs, not checked
  executions. Its direct-function congruence and partial run function avoid
  introducing a fresh binder for each composition, but do not establish that a
  supplied function, equality, provider or execution summary is correct. The
  consumer must close and kernel-check the whole term against its own claim;
  construction limits and proof-replay limits remain separate.
- The `trust_ir_contract::formula_dag` sharing printers are tested, not
  proved: their texts are checked to expand to the tree text (and, for the
  test corpora, proved equal to it by ay), not verified in general. Under a
  binder, a symbol spelled like a name it binds is the bound variable, so a
  subterm that mentions a binder's variable means something different in
  every printed body of that binder and is spelled once in each: no `let`
  text can do better, because a `let` outside a binder's body cannot denote
  that body's variable. A DAG that nests such binders inside one another
  (`G_{i+1} = (and (forall ((k Int)) G_i) G_i)` over `G_0 = (> k 0)`) can
  therefore print larger than linear in the DAG (here n(n+3)/2 spellings for
  2n+3 nodes) — never larger than its tree text, and exactly one spelling per
  (node, region). The binder analysis is exact for a subterm that mentions at
  most one bound name; one that mentions two or more stays in the innermost
  region at each use, even where an outer one would do. Only a
  parameterised `define-fun` (lambda-lifting) can write such DAGs in linear
  size; it is not implemented, and `define-fun` is outside ay's strict
  certification anyway. Node ids, shell ids and per-node child counts are
  `u32`: a DAG of 2^32 nodes, shells or children per node panics, naming
  the width, rather than truncate.

Unsupported evidence and out-of-fragment operations should be rejected or
reported as unsupported. Treat every claim at the granularity of its named
artifact, checker, revision, and negative tests.

## Logical replay and optimized runtime implementations

The compact-DAG runtime implementations use retained object identities for memoization.
Their separate `TrustIrRuntime` library is attached to 15 safe structural interfaces
through explicit native symbols. Kernel replay of the structural definitions and their
theorems does not verify those compiled implementations. The boundary ledger
`lean/trust_ir-semantics/runtime-boundary.json` retains all 41 original runtime
obligations as **UNPROVED**, alongside the baseline's 7,084 safe logical obligations;
the combined imported/restored baseline remains 7,125. Skipped and undecoded
loader-extension findings remain in its complete inventory; these counts do not
establish full Lean metadata fidelity. New logical work adds obligations to that baseline.
Physical-sharing counters are operational diagnostics, not proofs.

`scripts/check_lean_runtime_boundary.py` inventories the source, import and symbol
boundary and hashes runtime inputs even when they are outside the logical import
closure. Its success cannot certify runtime correspondence or a complete program.

Schema 2 additionally retains three **UNPROVED** support obligations for native
initialization, Lake linking, and semantic fixture execution. The declaration-free
`TrustIrNativeLink` module imports only safe semantics; its native facet links the
separate runtime provider and invokes its initializer. Its C implementation, ABI,
initialization/error behavior and native linkage are additional unchecked runtime
work. Existing `native_decide` fixtures remain compiler/runtime-dependent evaluations.
Native controls establish their named observed behavior, not formal correspondence.
