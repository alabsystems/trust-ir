<div align="center">
  <h1>TrustIr</h1>
  <p><strong>Represent programs. Carry proofs. Make handoffs checkable.</strong></p>
  <p>A typed, proof-carrying mid-level IR in Rust for verifiable compiler and
  tool handoffs, developed as the t* stack's shared program format.</p>
  <p>
    <a href="#getting-started">Getting started</a> ·
    <a href="#tutorial-build-validate-and-run-a-module">Tutorial</a> ·
    <a href="#check-proof-claims">Check proof claims</a> ·
    <a href="#use-trustir">Use TrustIr</a> ·
    <a href="#capability-grid">Capabilities</a> ·
    <a href="TRUST.md">Trust model</a> ·
    <a href="LIMITATIONS.md">Limitations</a> ·
    <a href="#similar-projects">Similar projects</a> ·
    <a href="#roadmap">Roadmap</a> ·
    <a href="https://github.com/alabsystems/trust-ir/issues">Issues</a>
  </p>
</div>

## What is TrustIr?

TrustIr is the shared program representation between source-language
frontends, verification tools, and code generation in the t* toolchain. It
represents typed control flow and memory operations together with the proof
obligations, certificates, diagnostics, provenance, and lineage needed to
check what happened to a program between stages.

The repository provides three related artifact layers:

| Artifact | What it contains | What it is for |
| --- | --- | --- |
| TrustIr module | Functions, blocks, typed instructions, globals, target metadata, proof annotations, obligations, certificates, and diagnostics | The program handoff between producers, verifiers, interpreters, and code generators |
| Verification bundle | A module plus typed verification requests, producer facts, evidence bundles, and module identity | An in-process handoff to verification and orchestration tools |
| Proof-lineage manifest | A sidecar chain of transforms, module digests, obligations, certificates, replay records, and dependencies | Checking that evidence remains connected to the exact artifact it is claimed to justify |

In the intended stack, Trust and Clean produce TrustIr; AY and Ty consume its
verification requests; and TrustCg consumes validated modules for code
generation. Each integration can adopt the common data model without putting
its solver or backend inside the core IR crate.

```text
Trust / Clean
      │
      ▼
TrustIr module + proof lineage
      ├──► validator and replay gates
      ├──► AY / Ty verification adapters
      ├──► bounded reference interpreter
      └──► TrustCg on supported code-generation paths
```

> **Status:** TrustIr 0.3 is a preview under active development. The IR,
> builders, validator, four module codecs, reference interpreter, lineage
> carriers, command-line tools, conformance corpus, and Lean semantics package
> are implemented. The schema and APIs are still evolving, and the project
> does not yet establish a general end-to-end proof from arbitrary Trust or
> Clean source to machine code. The exact trusted base, covered fragments, and
> remaining correspondence boundaries are stated in [`TRUST.md`](TRUST.md).
> The concise user-facing boundary is also collected in
> [`LIMITATIONS.md`](LIMITATIONS.md).

## Getting started

The commands below were verified locally with Rust 1.97.1. TrustIr 0.3 does
not yet promise a minimum supported Rust version.

```bash
git clone https://github.com/alabsystems/trust-ir.git
cd trust-ir

cargo build --release --locked \
  -p trust-ir-cli -p trust-ir-fmt -p trust-ir-diff
export PATH="$PWD/target/release:$PATH"
```

Validate and inspect artifacts from the checked-in conformance corpus:

```bash
FIXTURES=crates/trust-ir-conformance/tests/fixtures

trust-ir validate "$FIXTURES/chc_batch.tmbc" --no-giveback
trust-ir dump "$FIXTURES/b1_scalars.tmbc" | sed -n '1,24p'
trust-ir-fmt "$FIXTURES/b1_scalars.trust_ir" | sed -n '1,24p'
```

The first command reports that the module is well formed. `dump` accepts any
supported module format and writes readable TrustIr text; `trust-ir-fmt`
canonicalizes text to standard output rather than editing the input file.
`--no-giveback` keeps these introductory validations focused on the core IR;
without it, validation runs the experimental `&mut` give-back elaboration pass
by default.

The public source snapshot must resolve its exact dependencies through Cargo
without sibling checkouts. The private combined t* workspace may redirect
those same revisions to adjacent sources for development, but that layout is
not part of the public getting-started contract.

Lean 4 is optional for normal Rust development. To build the formal semantics,
install `elan`; the package selects its pinned toolchain through
[`lean-toolchain`](lean/trust_ir-semantics/lean-toolchain).

## Tutorial: build, validate, and run a module

This short tutorial constructs a nullary function that returns `42`, validates
the resulting module, writes readable TrustIr text, and runs it with the
bounded reference interpreter. The complete example is
[`getting_started.rs`](crates/trust-ir-build/examples/getting_started.rs).

The central builder code is deliberately small:

```rust
use trust_ir::Ty;
use trust_ir_build::{ModuleBuilder, validate_module};

let mut module = ModuleBuilder::new("answer");
let signature = module.add_func_type(vec![], vec![Ty::I64]);

let mut program = module.function("program", signature);
let entry = program.create_block();
program.switch_to_block(entry);
let twenty = program.iconst(Ty::I64, 20);
let twenty_two = program.iconst(Ty::I64, 22);
let answer = program.add(Ty::I64, twenty, twenty_two);
program.ret(vec![answer]);
program.build();

let module = module.build();
let errors = validate_module(&module);
assert!(errors.is_empty(), "{errors:#?}");
print!("{module}");
```

`ModuleBuilder` and `FunctionBuilder` emit structure; they intentionally do
not perform type, SSA, dominance, or terminator checks while emitting. Always
run `validate_module` before a consumer accepts builder output.

Run the example and save its text output:

```bash
mkdir -p target
cargo run --quiet --locked -p trust-ir-build \
  --example getting_started > target/answer.trust_ir
```

Now validate and execute it:

```bash
trust-ir validate target/answer.trust_ir --no-giveback
trust-ir run target/answer.trust_ir --entry program --validate
```

The interpreter prints `42`. It also reports linking, validation, and executed
step counts on standard error so scripts can keep the return value on standard
output.

Finally, convert the module to JSON and produce a canonical text copy:

```bash
trust-ir convert --from text --to json \
  target/answer.trust_ir target/answer.json
trust-ir-fmt target/answer.trust_ir \
  > target/answer.canonical.trust_ir
trust-ir-diff target/answer.json target/answer.json
```

`trust-ir-diff` exits `0` and stays silent for isomorphic modules. It currently
accepts serde JSON modules; use `trust-ir convert` before comparing another
module format.

### Tutorial: reject faith-stamped proof state

The same example can attach a structurally valid `Trusted` proof obligation.
That status means "accepted on faith," not "checked." Generate the variant:

```bash
cargo run --quiet --locked -p trust-ir-build \
  --example getting_started -- --trusted \
  > target/answer-trusted.trust_ir
```

Plain structural validation accepts the representation. The stricter consumer
gate rejects it and names the faith-stamped obligation:

```bash
trust-ir validate target/answer-trusted.trust_ir --no-giveback

if trust-ir validate target/answer-trusted.trust_ir \
  --no-giveback --forbid-trusted; then
  echo "unexpected: Trusted proof state was accepted" >&2
  exit 1
else
  echo "expected: Trusted proof state was rejected"
fi
```

The CLI integration suites exercise the stronger closed-lineage path as well
as trusted, opaque, and mis-threaded negative cases:

```bash
cargo test --locked -p trust-ir-cli --test cli_forbid_trusted
cargo test --locked -p trust-ir-cli --test cli_lineage
```

## Check proof claims

A TrustIr artifact can carry a proof claim without making that claim true.
Parsing, round-tripping, or constructing a module is not proof checking. The
consumer chooses the gate that matches the claim it intends to rely on:

| Claim | Gate | Scope |
| --- | --- | --- |
| The module is structurally well formed | `trust-ir validate MODULE` | Types, SSA and dominance, CFG and terminators, ABI consistency, proof references, and other validator invariants |
| No obligation is already marked refuted | `trust-ir validate MODULE --forbid-failed` | Fails if any obligation has `ProofStatus::Failed`; it does not prove pending obligations |
| No faith-stamped evidence is present | `trust-ir validate MODULE --forbid-trusted` | Fails on every `Trusted` status or `ProofEvidence::Trusted` payload |
| The transform chain is connected and replay-authoritative | `trust-ir validate MODULE --lineage MANIFEST` | Checks the `.tmpl` or JSON sidecar against the module and requires every reachable rung to close under the validator's authority rules |
| A state-machine specification is linked to source objects and proof harnesses | `trust-ir spec-link MODULE --harness-manifest MANIFEST` | Checks typed anchors, coverage, ownership, and proof-name resolution; exits successfully only for a certifying linked result |
| A source-to-machine claim is closed | The applicable validator/kernel re-checks plus a complete lineage | Only the transformations and instruction families covered by those exact checks; there is no general whole-toolchain certificate yet |

Proof status is explicit. `Pending` is not proved, `Failed` is refuted,
`Trusted` is taken on faith, `Discharged` records solver or verifier evidence,
and `Certified` requires the applicable kernel-checkable evidence path. A
certificate's bytes, label, or digest are never sufficient by themselves;
the consumer must rederive the claim and run the checker appropriate to its
evidence kind.

The Lean package is free of `sorry` placeholders. Its axiom audit permits one
first-party axiom, `ay_sound_unsat`, which makes AY's UNSAT soundness an
explicit boundary. Rust-to-Lean semantic correspondence and the remaining
source/lowering encoding assumptions are also part of the trusted base; see
[`TRUST.md`](TRUST.md) rather than inferring a stronger guarantee from a green
validator result.

## Use TrustIr

### Command line

The workspace builds three user-facing binaries:

| Command | Purpose |
| --- | --- |
| `trust-ir validate MODULE` | Validate a module, run give-back by default, and optionally check lineage or reject `Trusted` and `Failed` proof states |
| `trust-ir dump MODULE` | Read any supported module format and print TrustIr text |
| `trust-ir convert --from F --to F IN [OUT]` | Convert between text, binary, JSON, and MessagePack |
| `trust-ir run MODULE… --entry NAME` | Link modules and execute a nullary entry point with the bounded reference interpreter |
| `trust-ir show-gpu-eligibility MODULE` | Report the safety, eligibility, divergence, and proof metadata used by the GPU gate |
| `trust-ir spec-link MODULE` | Check state-machine/source anchors and proof-harness bindings |
| `trust-ir-fmt FILE` | Parse TrustIr text and write its idempotent canonical form to standard output |
| `trust-ir-diff A.json B.json` | Compare serde JSON modules semantically while ignoring ID renumbering and declaration order |

Run `trust-ir <command> --help`, `trust-ir-fmt --help`, or
`trust-ir-diff --help` for the available options and usage contracts.

The `run` command is a diagnostic and conformance tool, not a production
runtime. It has explicit fuel, call-depth, and memory budgets; unsupported
operations, layouts, casts, or dialect operations return structured errors or
trap stubs rather than silently changing semantics.

### Embed in Rust

Use `trust-ir` for the core data model and `trust-ir-build` for construction and
validation. A sibling consumer can use the checked-out sources directly:

```toml
[dependencies]
trust-ir = { path = "../trust-ir/crates/trust-ir", features = ["parser", "binary", "serde", "fmt"] }
trust-ir-build = { path = "../trust-ir/crates/trust-ir-build", features = ["serde"] }
```

The core crate keeps optional surfaces behind features:

| Feature | Public surface |
| --- | --- |
| default: `request-reexports` | Re-export the verification request/bundle schema at the crate root; it is always available under `trust_ir::request` |
| `parser` | TrustIr text parser |
| `binary` | Canonical binary module and lineage codecs |
| `serde` | JSON/MessagePack-compatible serde types |
| `fmt` | Canonical text formatter |
| `diff` | Semantic module comparison |
| `dialect-verif-example` | Opt-in example helpers for the `verif` dialect |
| `clean-expr` | Clean kernel expression obligations and their bounded codec |

For Git dependencies, pin both packages to the same public release tag or full
public commit rather than a moving branch. Keep producer and TrustIr revisions
atomic, then validate every emitted module.

## Why TrustIr?

Most compiler IRs are designed to preserve executable meaning while enabling
analysis and transformation. A verified compilation stack must also preserve
what was proved, which assumptions were used, which artifact the evidence was
about, and whether every transform in between was checked.

| Design choice | What it gives the toolchain |
| --- | --- |
| One typed handoff | Trust and Clean can target the same validator, formats, verification requests, interpreter, and code-generation contract |
| Proof state in the schema | Instructions and functions can carry annotations while modules carry scoped obligations, certificates, diagnostics, and summaries |
| Content-bound evidence | SHA-256 identities and lineage manifests bind claims to exact modules and transformation stages |
| Fail-closed consumer gates | Consumers can reject failed, trusted, dangling, unreplayable, or unsupported evidence instead of treating metadata as proof |
| Multiple representations | Human-readable text, compact binary, JSON, and MessagePack cover source control, pipeline transport, and tool interoperability |
| Executable and formal semantics | A bounded Rust interpreter supports differential checks while Lean states and proves selected operational properties |
| Extensible operations | Namespaced dialect payloads survive unknown consumers and can lower progressively into core TrustIr |

The result is a shared contract rather than a monolithic compiler: producers,
solvers, model checkers, proof kernels, and backends remain separate systems,
but exchange typed artifacts whose claims can be checked at each boundary.

## Capability grid

The table distinguishes implemented transport or checking surfaces from the
stronger guarantees that remain limited to particular fragments.

| Surface | Implemented today | Important limit |
| --- | --- | --- |
| Core IR | Typed SSA modules, functions, blocks, scalars, aggregates, vectors, memory, borrowing/ARC, atomics, calls, control flow, ABI/target data, debug spans, producer metadata, and refinement predicates | The 0.3 schema and Rust API are still evolving |
| Proof transport | Function/instruction annotations, scoped obligations, certificates, diagnostics, function summaries, SHA-256 identities, lineage manifests, and native verification bundles | Carrying or structurally validating evidence is not itself an end-to-end proof; `Trusted` evidence remains faith-based |
| Construction and validation | `ModuleBuilder`, `FunctionBuilder`, `validate_function`, `validate_module`, validation reports, and focused consumption/source-to-silicon gates | Builders are unchecked emitters; callers must run validation explicitly |
| Module formats | Canonical text, canonical binary, serde JSON, and MessagePack, guarded by a byte-golden conformance corpus | Canonical text omits concrete layout facts and function summaries; binary, JSON, and MessagePack are the lossless paths for those fields; lineage travels as a separate sidecar |
| Execution | A bounded `Interpreter`; `trust-ir run` links modules, synthesizes supported builtins, and executes a core slice | Deliberately partial; it is a reference path, not TrustCg or a complete Rust runtime |
| Dialects | Opaque round-trip payloads, a registry, fixpoint lowering, vector helpers/lowering, and GPU, AVX-512, ANE, and Trust-Rust payload schemas | Backend-oriented payload schemas still require their backend-owned lowering and legality checks |
| Command-line tools | Validation, inspection, conversion, reference execution, GPU reporting, spec linking, canonical formatting, and semantic JSON diffing | `trust-ir-diff` currently reads JSON only; formatter output is stdout-only |
| Formal model | Lean operational semantics, executable fixtures, safety/transform theorems, Rust/Lean name-parity tests, and an axiom-audit gate | Coverage is not yet the whole TrustIr instruction set implemented by the Rust reference interpreter; one explicit first-party axiom and correspondence assumptions remain |
| Integrations | Shared contract vocabulary, non-default AY adapter, experimental give-back elaborator, and a Rust `rustc_private` frontend | AY support is fragment-specific; give-back has documented certification gaps; the frontend needs a custom compiler toolchain |

### Formats and extensions

| Extension | Artifact | Reader/writer |
| --- | --- | --- |
| `.trust_ir` | Human-readable module text | `trust-ir dump`, `trust-ir convert`, `trust-ir-fmt`, `trust_ir::parser` |
| `.tmbc` | Canonical binary module | `trust-ir dump`, `trust-ir convert`, `trust_ir::binary` |
| `.json` | Serde JSON module | `trust-ir convert`, `trust-ir-diff`, serde consumers |
| `.msgpack` | Serde MessagePack module | `trust-ir convert`, serde consumers |
| `.tmpl` | Canonical binary proof-lineage sidecar | `trust-ir validate --lineage`, `trust_ir::binary` |

Extensions drive CLI auto-detection. An explicit `--format` overrides module
auto-detection where the command exposes it.

The module binary writer emits v36. Readers accept v23–v25 and v29–v36; v26–v28
are rejected because those version numbers were used by byte-incompatible
development lines. Proof-lineage `.tmpl` sidecars use their own v2 format.

## Implementation highlights

TrustIr builds on established SSA, operational-semantics, proof-carrying-code,
and translation-validation ideas. Its distinctive work is in making those
ideas one practical cross-tool artifact contract:

- **Canonical identity across representations.** The module's stable digest
  is recomputed from one canonical encoder, and security-sensitive proof
  identities use domain-separated SHA-256. Golden fixtures and cross-process
  determinism tests make format drift visible.
- **Proof authority is separate from proof metadata.** Obligations,
  certificates, evidence payloads, and lineage records are representable in
  the IR, but validator authority requires exact identity, applicable replay,
  and the right checker. Unknown or unsupported certificate anchors fail
  closed.
- **Semantic comparison ignores incidental IDs.** `trust-ir-diff` aligns
  declarations and CFG structure rather than equating allocator-assigned IDs,
  making producer changes reviewable without hiding real semantic or proof
  differences.
- **Unknown dialects remain portable.** A consumer can deserialize and
  reserialize a namespaced dialect operation it does not implement. Registered
  lowering passes then rewrite supported operations to a fixpoint without
  changing the core instruction enum for every experiment.
- **Executable and theorem-level models are checked together.** Rust tests
  exercise the reference interpreter and format corpus; Lean executable
  fixtures and schema-parity gates expose drift instead of assuming the formal
  model follows the implementation automatically.

## TrustIr in ALab Systems

TrustIr is the compiler-artifact spine used by the surrounding ALab Systems
projects:

| Project | Relationship to TrustIr |
| --- | --- |
| Trust *(development integration; public repository pending)* | Rust-oriented producer and compiler integration |
| Clean *(development integration; public repository pending)* | Fused program/proof language with an experimental TrustIr emission path and kernel-backed certificate checks |
| [AY](https://github.com/alabsystems/ay) | Solver backend used through the non-default `trust-ir-ay` adapter and typed verification requests |
| [Ty](https://github.com/alabsystems/ty) | Temporal and whole-program verification consumer |
| TrustCg *(development integration; public repository pending)* | Code-generation consumer for supported TrustIr lowering paths |

These projects are versioned separately. A shared schema makes composition
possible, but a cross-project correctness claim still requires compatible
revisions and the exact evidence/replay chain for that artifact.

## Similar projects

TrustIr occupies a different point in the design space from several widely
used compiler and verification representations:

| Project | Primary focus | TrustIr's focus |
| --- | --- | --- |
| [LLVM IR](https://llvm.org/docs/LangRef.html) | Portable optimizer and code-generator IR | A smaller proof-carrying handoff with explicit obligations, certificates, lineage, and a separate verified-backend goal |
| [MLIR](https://mlir.llvm.org/) | Multi-level compiler infrastructure built around extensible dialects | One typed mid-level contract whose dialect payloads can remain opaque across proof and tool boundaries |
| [Cranelift IR](https://docs.rs/cranelift-codegen/latest/cranelift_codegen/ir/) | SSA representation for fast machine-code generation | Verification evidence, deterministic interchange, and formal/reference semantics rather than a standalone production backend |
| [Boogie](https://github.com/boogie-org/boogie) | Intermediate verification language and verification-condition generation | An executable compiler IR that carries proof state alongside operational program structure |

They are complementary reference points, not drop-in replacements. TrustIr is
most useful when several producers and verification/code-generation consumers
need one content-addressed program-and-evidence handoff.

## Conformance and benchmarks

The conformance crate locks the four module representations together with
byte-golden fixtures, round-trip tests, compatibility fixtures, property tests,
and a machine-readable lowering subset. Run it directly:

```bash
cargo test --locked -p trust-ir-conformance --test conformance
cargo test --locked -p trust-ir-conformance --test lowering_subset
```

The workspace also includes two synthetic generators for stressing module
construction, validation, and serialization:

```bash
# Large CHC-shaped block chain; defaults to 10,000 states.
cargo run --release --locked -p supremacy-fixture -- \
  --states 10000 --output target/supremacy.tmbc

# Raft-shaped grid-parallel synthesis fixture.
cargo run --release --locked -p raft-fixture -- \
  --output target/raft.tmbc

trust-ir validate target/supremacy.tmbc --no-giveback
trust-ir validate target/raft.tmbc --no-giveback
```

These are pipeline stress fixtures, not realistic application workloads and
not performance comparisons with another IR. See
[`benchmarks/README.md`](benchmarks/README.md) for their generated shapes and
usage. TrustIr currently makes no aggregate speed claim; a publishable
performance result should preserve the commit, host, toolchain, exact command,
input, resource limits, and failures as well as elapsed time.

## Roadmap

TrustIr's roadmap is ordered by the evidence needed for progressively stronger
claims:

1. **Publish a dependable 0.x source distribution.** Make a fresh public clone
   build without private checkout assumptions, run public-clone checks, publish
   coherent dependency pins and release notes, and establish multi-platform
   CI.
2. **Stabilize the interchange contract.** Specify compatibility policy for
   text, binary, JSON, MessagePack, native bundles, and lineage; keep golden
   migrations and downstream producer/consumer tests for every schema change.
3. **Close Rust-to-Lean semantic gaps.** Expand operational coverage, replace
   correspondence assumptions with executable or proved refinements, and keep
   the axiom audit explicit as the model grows.
4. **Expand checked source-to-machine fragments.** Add translation-validation
   and lowering certificates instruction family by instruction family, compose
   them through lineage, and report unsupported rungs instead of generalizing
   from the covered subset.
5. **Deepen whole-program specifications.** Grow the current spec-link and
   out-of-band temporal handoffs into checked safety and liveness workflows
   without pretending aspirational state-machine fields already exist in the
   core module.
6. **Improve producer and consumer ergonomics.** Stabilize the builder API,
   make diagnostics source-oriented, broaden frontend emission, and make
   artifact inspection and replay straightforward outside the combined t*
   workspace.

The 1.0 bar is a stable, independently buildable IR distribution whose format,
validation, semantic, and proof-authority claims are public, reproducible, and
matched by downstream producer and consumer gates. It is not a declaration
that every source program has an end-to-end machine proof.

<details>
<summary><strong>Repository layout and crate map</strong></summary>

## Repository layout

TrustIr is a Cargo workspace plus a separate Lean package and an experimental
compiler frontend:

| Path | Purpose |
| --- | --- |
| `crates/trust-ir` | Core IR, types, instructions, proof/evidence model, predicates, request bundles, codecs, formatter, diff engine, and reference interpreter |
| `crates/trust-ir-build` | Builders, validator, certificate re-checks, give-back integration, and source-to-silicon composition gates |
| `crates/trust-ir-contract` | Small shared SMT, translation-validation, and assurance vocabulary used across repositories |
| `crates/trust-ir-conformance` | Golden fixture corpus, compatibility tests, property tests, and lowering-subset checker |
| `crates/trust-ir-cli` | `trust-ir` validation, dump, conversion, execution, GPU-reporting, and spec-link command line |
| `crates/trust-ir-fmt` | Canonical text formatter shell |
| `crates/trust-ir-diff` | Semantic JSON-module diff shell |
| `crates/trust-ir-ay` | Non-default, exact-revision AY adapter for proof obligations and certificates |
| `crates/trust-ir-giveback` | Experimental Aeneas-style single-region `&mut` give-back elaborator; an untrusted producer with explicit certification limits |
| `frontend` | Workspace-excluded Rust MIR/THIR frontend requiring `rustc_private` and the Trust toolchain |
| `lean/trust_ir-semantics` | Lean operational semantics, executable fixtures, proofs, and axiom audit |
| `benchmarks` | Synthetic Supremacy and Raft fixture generators plus checked-in sample modules |
| `scripts` | Repository-owned standing gates and comprehensive self-verification runner |

The normative public lowering subset is
[`lowering-target-subset.md`](lowering-target-subset.md). The long-term design
direction is separated from current claims in [`VISION.md`](VISION.md); the
trusted-base statement is [`TRUST.md`](TRUST.md).

</details>

## Development

See [`CONTRIBUTING.md`](CONTRIBUTING.md) for the contribution workflow,
licensing terms, and review expectations. Start with the narrowest check that
covers a change, then broaden it:

```bash
cargo test --locked -p trust-ir
cargo test --locked -p trust-ir-build
cargo test --locked -p trust-ir-cli
cargo test --locked -p trust-ir-conformance --test conformance
cargo test --locked --all-features
```

The AY adapter is a workspace member but not a default member, so test it
explicitly. Lean is a separate build:

```bash
cargo test --locked -p trust-ir-ay
(cd lean/trust_ir-semantics && lake build)
```

Changes to the IR schema should update every affected codec, golden fixture,
validator rule, formatter/parser path, interpreter path, Lean parity surface,
and downstream contract in one reviewable change. Changes to a proof claim
should include the negative test: unsupported, stale, forged, dangling, or
faith-stamped evidence must be rejected for the claimed authority level.

Use the [issue tracker](https://github.com/alabsystems/trust-ir/issues) for
bugs and proposals. Participation is governed by the
[`CODE_OF_CONDUCT.md`](CODE_OF_CONDUCT.md). Usage and packaging help is
described in [`SUPPORT.md`](SUPPORT.md); report suspected vulnerabilities
privately as directed by [`SECURITY.md`](SECURITY.md).

## Maintainer commands

The checked-in scripts compose the repository's broader local gates:

| Command | What it checks |
| --- | --- |
| `./scripts/ci_gates.sh` | Lean/Rust schema parity, workspace build, CLI proof gates, zero-`Trusted` and zero-`Failed` censuses, and lineage closure fixtures |
| `./scripts/ci-self-verify.sh` | Rev-pinned Git dependencies, Lean placeholder/axiom policy, locked default and all-feature tests, conformance, the non-default AY adapter, and the Lean build when available |

Set `TRUST_IR_REQUIRE_LEAN=1` to make a missing Lean toolchain fail the
self-verify gate. `TRUST_IR_SKIP_AY=1` or `TRUST_IR_SKIP_LEAN=1` are explicit
diagnostic skips; do not use a skipped run as release evidence for that
surface.

## License

Apache License 2.0. See [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE). Dependency
and influence notes are collected in [`THIRD_PARTY.md`](THIRD_PARTY.md).
TrustIr was created by Andrew Yates.
