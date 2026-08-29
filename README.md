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

| Artifact | What it contains | What it is for |
| --- | --- | --- |
| TrustIr module | Functions, blocks, typed instructions, globals, target metadata, proof annotations, obligations, certificates, and diagnostics | The handoff between producers, verifiers, interpreters, and code generators |
| Verification bundle | A module plus typed verification requests, producer facts, evidence bundles, and module identity | An in-process handoff to verification and orchestration tools |
| Proof-lineage manifest | A sidecar chain of transforms, module digests, obligations, certificates, replay records, and dependencies | Checking that evidence stays connected to the exact artifact it claims to justify |

In the intended stack, Trust and Clean produce TrustIr; the validator, replay
gates, and bounded interpreter check it; AY and Ty consume its verification
requests; and TrustCg consumes validated modules on supported code-generation
paths. Each integration adopts the common data model without putting its solver
or backend inside the core IR crate.

> **Status:** TrustIr's 0.x line is a preview under active development. The IR,
> builders, validator, four module codecs, reference interpreter, lineage
> carriers, command-line tools, conformance corpus, and Lean semantics package
> are implemented; the schema and Rust API are still evolving under 0.x. There
> is no general end-to-end proof from arbitrary Trust or Clean source to machine
> code. The trusted base, covered fragments, and remaining correspondence
> boundaries are stated in [`TRUST.md`](TRUST.md); the concise user-facing
> boundary is [`LIMITATIONS.md`](LIMITATIONS.md).

## Getting started

```bash
git clone https://github.com/alabsystems/trust-ir.git
cd trust-ir

cargo build --release --locked \
  -p trust-ir-cli -p trust-ir-fmt -p trust-ir-diff
export PATH="$PWD/target/release:$PATH"
```

Development builds use Rust 1.97.1; TrustIr does not yet promise a minimum
supported Rust version. A clone resolves its exact dependency revisions through
Cargo — no sibling checkout or path patch is part of the build contract.

Validate and inspect artifacts from the checked-in conformance corpus:

```bash
FIXTURES=crates/trust-ir-conformance/tests/fixtures

trust-ir validate "$FIXTURES/chc_batch.tmbc" --no-giveback
trust-ir dump "$FIXTURES/b1_scalars.tmbc" | sed -n '1,24p'
trust-ir-fmt "$FIXTURES/b1_scalars.trust_ir" | sed -n '1,24p'
```

`dump` reads any supported module format and writes readable TrustIr text;
`trust-ir-fmt` canonicalizes text to standard output instead of editing the
input. `--no-giveback` skips the experimental `&mut` give-back elaboration pass
that validation otherwise runs by default.

Lean 4 is optional for normal Rust development. To build the formal semantics,
install `elan`; the package selects its pinned toolchain through
[`lean-toolchain`](lean/trust_ir-semantics/lean-toolchain).

## Tutorial: build, validate, and run a module

This tutorial builds a nullary function that returns `42`, validates it, writes
readable TrustIr text, and runs it with the bounded reference interpreter. The
complete example is
[`getting_started.rs`](crates/trust-ir-build/examples/getting_started.rs); its
central builder code is deliberately small:

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

`ModuleBuilder` and `FunctionBuilder` emit structure; they intentionally do not
check types, SSA, dominance, or terminators while emitting. Always run
`validate_module` before a consumer accepts builder output.

Run the example, then validate and execute its output:

```bash
mkdir -p target
cargo run --quiet --locked -p trust-ir-build \
  --example getting_started > target/answer.trust_ir

trust-ir validate target/answer.trust_ir --no-giveback
trust-ir run target/answer.trust_ir --entry program --validate
```

The interpreter prints `42`, and reports linking, validation, and executed step
counts on standard error so scripts can keep the return value on standard
output. Finally, convert the module and compare it semantically:

```bash
trust-ir convert --from text --to json \
  target/answer.trust_ir target/answer.json
trust-ir-fmt target/answer.trust_ir \
  > target/answer.canonical.trust_ir
trust-ir-diff target/answer.json target/answer.json
```

`trust-ir-diff` exits `0` and stays silent for isomorphic modules. It accepts
serde JSON modules only; use `trust-ir convert` before comparing another format.

### Tutorial: reject faith-stamped proof state

The same example can attach a structurally valid `Trusted` proof obligation.
That status means "accepted on faith," not "checked." Plain structural
validation accepts the representation; the stricter consumer gate rejects it
and names the faith-stamped obligation:

```bash
cargo run --quiet --locked -p trust-ir-build \
  --example getting_started -- --trusted \
  > target/answer-trusted.trust_ir

trust-ir validate target/answer-trusted.trust_ir --no-giveback

if trust-ir validate target/answer-trusted.trust_ir \
  --no-giveback --forbid-trusted; then
  echo "unexpected: Trusted proof state was accepted" >&2
  exit 1
fi
echo "expected: Trusted proof state was rejected"
```

The CLI integration suites also exercise the closed-lineage path and the
trusted, opaque, and mis-threaded negative cases:

```bash
cargo test --locked -p trust-ir-cli --test cli_forbid_trusted
cargo test --locked -p trust-ir-cli --test cli_lineage
```

## Check proof claims

A TrustIr artifact can carry a proof claim without making it true. Parsing,
round-tripping, or constructing a module is not proof checking; the consumer
chooses the gate that matches the claim it intends to rely on:

| Claim | Gate | Scope |
| --- | --- | --- |
| The module is structurally well formed | `trust-ir validate MODULE` | Types, SSA and dominance, CFG and terminators, ABI consistency, proof references, and other validator invariants |
| No obligation is already marked refuted | `trust-ir validate MODULE --forbid-failed` | Fails if any obligation has `ProofStatus::Failed`; it does not prove pending obligations |
| No faith-stamped evidence is present | `trust-ir validate MODULE --forbid-trusted` | Fails on every `Trusted` status or `ProofEvidence::Trusted` payload |
| The transform chain is connected and replay-authoritative | `trust-ir validate MODULE --lineage MANIFEST` | Checks the `.tmpl` or JSON sidecar against the module and requires every reachable rung to close under the validator's authority rules |
| A state-machine specification is linked to source objects and proof harnesses | `trust-ir spec-link MODULE --harness-manifest MANIFEST` | Checks typed anchors, coverage, ownership, and proof-name resolution; exits successfully only for a certifying linked result |
| A source-to-machine claim is closed | The applicable validator/kernel re-checks plus a complete lineage | Only the transformations and instruction families covered by those exact checks; there is no general whole-toolchain certificate yet |

Proof status is explicit: `Pending` is not proved, `Failed` is refuted,
`Trusted` is taken on faith, `Discharged` records solver or verifier evidence,
and `Certified` requires the applicable kernel-checkable evidence path. A
certificate's bytes, label, or digest are never sufficient by themselves: the
consumer must rederive the claim and run the checker for its evidence kind.

The Lean package is free of `sorry` placeholders, and its axiom audit permits
one first-party axiom, `ay_sound_unsat`, which makes AY's UNSAT soundness an
explicit boundary. Rust-to-Lean correspondence and the remaining source/lowering
encoding assumptions are also part of the trusted base; read
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

Run any of them with `--help` for the available options. `run` is a diagnostic
and conformance tool, not a production runtime: it has explicit fuel,
call-depth, and memory budgets, and unsupported operations, layouts, casts, or
dialect operations return structured errors or trap stubs rather than silently
changing semantics.

### Embed in Rust

Use `trust-ir` for the core data model and `trust-ir-build` for construction and
validation; a sibling consumer can use the checked-out sources directly:

```toml
[dependencies]
trust-ir = { path = "../trust-ir/crates/trust-ir", features = ["parser", "binary", "serde", "fmt"] }
trust-ir-build = { path = "../trust-ir/crates/trust-ir-build", features = ["serde"] }
```

The core crate keeps optional surfaces behind features:

| Feature | Public surface |
| --- | --- |
| default: `request-reexports` | Re-export the verification request/bundle schema at the crate root; it is always reachable as `trust_ir::request` |
| `parser` | TrustIr text parser |
| `binary` | Canonical binary module and lineage codecs |
| `serde` | JSON/MessagePack-compatible serde types |
| `fmt` | Canonical text formatter |
| `diff` | Semantic module comparison |
| `dialect-verif-example` | Opt-in example helpers for the `verif` dialect |
| `clean-expr` | Clean kernel expression obligations and their bounded codec |

For Git dependencies, pin both packages to the same public release tag or full
commit rather than a moving branch, keep producer and TrustIr revisions atomic,
and validate every emitted module.

## Why TrustIr?

Most compiler IRs preserve executable meaning. A verified stack must also
preserve what was proved, which assumptions were used, which artifact the
evidence was about, and whether every transform in between was checked. TrustIr
makes that one typed handoff — Trust and Clean target the same validator,
formats, verification requests, interpreter, and code-generation contract — and
keeps proof state in the schema rather than beside it. Four consequences:

- **Content-bound identity.** Module identity is recomputed from one canonical
  encoder, security-sensitive proof identities use domain-separated SHA-256, and
  lineage manifests bind claims to exact modules and transformation stages.
- **Authority is separate from metadata.** Obligations, certificates, and
  lineage records are representable, but validator authority requires exact
  identity, applicable replay, and the right checker; failed, trusted, dangling,
  unreplayable, or unknown-anchor evidence fails closed.
- **Comparison ignores incidental IDs.** `trust-ir-diff` aligns declarations and
  CFG structure instead of equating allocator-assigned IDs, so producer changes
  stay reviewable without hiding real semantic or proof differences.
- **Unknown dialects stay portable.** A consumer can round-trip a namespaced
  dialect payload it does not implement; registered lowering passes rewrite
  supported operations to a fixpoint without growing the core instruction enum.

Producers, solvers, model checkers, proof kernels, and backends stay separate
systems that exchange typed artifacts whose claims are checkable at each
boundary.

## Capability grid

Implemented transport or checking surfaces, against the stronger guarantees
that remain limited to particular fragments:

| Surface | Implemented today | Important limit |
| --- | --- | --- |
| Core IR | Typed SSA modules, functions, blocks, scalars, aggregates, vectors, memory, borrowing/ARC, atomics, calls, control flow, ABI/target data, debug spans, producer metadata, and refinement predicates | The 0.x schema and Rust API are still evolving |
| Proof transport | Function/instruction annotations, scoped obligations, certificates, diagnostics, function summaries, SHA-256 identities, lineage manifests, and native verification bundles | Carrying or structurally validating evidence is not an end-to-end proof; `Trusted` evidence stays faith-based |
| Construction and validation | `ModuleBuilder`, `FunctionBuilder`, `validate_function`, `validate_module`, validation reports, and focused consumption/source-to-silicon gates | Builders are unchecked emitters; callers must run validation explicitly |
| Module formats | Canonical text, canonical binary, serde JSON, and MessagePack, guarded by a byte-golden conformance corpus | Canonical text omits concrete layout facts and function summaries, for which binary, JSON, and MessagePack are the lossless paths; lineage travels as a separate sidecar |
| Execution | A bounded `Interpreter`; `trust-ir run` links modules, synthesizes supported builtins, and executes a core slice | Deliberately partial: a reference path, not TrustCg or a complete Rust runtime |
| Dialects | Opaque round-trip payloads, a registry, fixpoint lowering, vector helpers/lowering, and GPU, AVX-512, ANE, and Trust-Rust payload schemas | Backend-oriented schemas still require their backend-owned lowering and legality checks |
| Formal model | Lean operational semantics, executable fixtures, safety/transform theorems, Rust/Lean name-parity tests, and an axiom-audit gate | Coverage lags the instruction set the Rust interpreter implements; one first-party axiom and correspondence assumptions remain |
| Integrations | Shared contract vocabulary, non-default AY adapter, experimental give-back elaborator, and a Rust `rustc_private` frontend | AY support is fragment-specific, give-back has documented certification gaps, and the frontend needs a custom compiler toolchain |

### Formats and extensions

| Extension | Artifact | Reader/writer |
| --- | --- | --- |
| `.trust_ir` | Human-readable module text | `trust-ir dump`, `trust-ir convert`, `trust-ir-fmt`, `trust_ir::parser` |
| `.tmbc` | Canonical binary module | `trust-ir dump`, `trust-ir convert`, `trust_ir::binary` |
| `.json` | Serde JSON module | `trust-ir convert`, `trust-ir-diff`, serde consumers |
| `.msgpack` | Serde MessagePack module | `trust-ir convert`, serde consumers |
| `.tmpl` | Canonical binary proof-lineage sidecar | `trust-ir validate --lineage`, `trust_ir::binary` |

Extensions drive CLI auto-detection; an explicit `--format` overrides module
auto-detection where the command exposes it. The module binary writer emits
v38. Readers accept v23–v25 and v29–v38; v26–v28 are rejected because those
version numbers were used by byte-incompatible development lines. Proof-lineage
`.tmpl` sidecars use their own v2 format.

## TrustIr in ALab Systems

TrustIr is the compiler-artifact spine of the surrounding ALab Systems
projects:

| Project | Relationship to TrustIr |
| --- | --- |
| [Trust](https://github.com/alabsystems/trust) | Rust-oriented producer and compiler integration (in development) |
| [Clean](https://github.com/alabsystems/clean) | Fused program/proof language with an experimental TrustIr emission path and kernel-backed certificate checks |
| [AY](https://github.com/alabsystems/ay) | Solver backend used through the non-default `trust-ir-ay` adapter and typed verification requests |
| [Ty](https://github.com/alabsystems/ty) | Temporal and whole-program verification consumer |
| [TrustCg](https://github.com/alabsystems/trust-cg) | Code-generation consumer for supported TrustIr lowering paths (in development) |

These projects are versioned separately: a shared schema makes composition
possible, but a cross-project correctness claim still requires compatible
revisions and the exact evidence/replay chain for that artifact.

## Similar projects

TrustIr occupies a different point in the design space from widely used
compiler and verification representations. [LLVM IR](https://llvm.org/docs/LangRef.html)
and [MLIR](https://mlir.llvm.org/) are a portable optimizer/code-generator IR
and an extensible multi-level infrastructure; TrustIr is a smaller typed
mid-level contract with explicit obligations, certificates, and lineage, whose
dialect payloads can stay opaque across proof and tool boundaries.
[Cranelift IR](https://docs.rs/cranelift-codegen/latest/cranelift_codegen/ir/)
targets fast machine-code generation, where TrustIr targets verification
evidence, deterministic interchange, and formal/reference semantics rather than
a production backend. [Boogie](https://github.com/boogie-org/boogie) is an
intermediate verification language; TrustIr is an executable compiler IR that
carries proof state alongside operational program structure. They are
complementary reference points, not drop-in replacements.

## Conformance and benchmarks

The conformance crate locks the four module representations together with
byte-golden fixtures, round-trip and compatibility tests, property tests, and a
machine-readable lowering subset:

```bash
cargo test --locked -p trust-ir-conformance --test conformance
cargo test --locked -p trust-ir-conformance --test lowering_subset
```

Two synthetic generators stress module construction, validation, and
serialization:

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

These are pipeline stress fixtures, not application workloads or comparisons
with another IR; [`benchmarks/README.md`](benchmarks/README.md) documents their
shapes. TrustIr makes no aggregate speed claim: a publishable performance result
should preserve the commit, host, toolchain, exact command, input, resource
limits, and failures as well as elapsed time.

## Roadmap

Ordered by the evidence needed for progressively stronger claims:

1. **Stabilize the public source distribution.** Keep a fresh public clone
   building without private checkout assumptions, publish coherent dependency
   pins and release notes, and establish multi-platform CI.
2. **Stabilize the interchange contract.** Specify a compatibility policy for
   every format, bundle, and lineage sidecar, with golden migrations and
   downstream producer/consumer tests for each schema change.
3. **Close Rust-to-Lean semantic gaps.** Expand operational coverage, replace
   correspondence assumptions with executable or proved refinements, and keep
   the axiom audit explicit as the model grows.
4. **Expand checked source-to-machine fragments.** Add translation-validation
   and lowering certificates instruction family by instruction family, compose
   them through lineage, and report unsupported rungs rather than generalizing
   from the covered subset.
5. **Deepen specifications and producer ergonomics.** Grow spec-link and the
   out-of-band temporal handoffs into checked safety and liveness workflows,
   stabilize the builder API, make diagnostics source-oriented, and broaden
   frontend emission.

The 1.0 bar is a stable, independently buildable IR distribution whose format,
validation, semantic, and proof-authority claims are public, reproducible, and
matched by downstream producer and consumer gates — not a declaration that every
source program has an end-to-end machine proof.

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
| `crates/trust-ir-cli` | The `trust-ir` command line |
| `crates/trust-ir-fmt` | Canonical text formatter shell |
| `crates/trust-ir-diff` | Semantic JSON-module diff shell |
| `crates/trust-ir-ay` | Non-default, exact-revision AY adapter for proof obligations and certificates |
| `crates/trust-ir-giveback` | Experimental Aeneas-style single-region `&mut` give-back elaborator: an untrusted producer with explicit certification limits |
| `frontend` | Workspace-excluded Rust MIR/THIR frontend requiring `rustc_private` and the Trust toolchain |
| `lean/trust_ir-semantics` | Lean operational semantics, executable fixtures, proofs, and axiom audit |
| `benchmarks` | Synthetic Supremacy and Raft fixture generators and sample modules |
| `scripts` | Standing repository gates and the self-verification runner |

The normative public lowering subset is
[`lowering-target-subset.md`](lowering-target-subset.md); the long-term design
direction is separated from current claims in [`VISION.md`](VISION.md), and the
trusted-base statement is [`TRUST.md`](TRUST.md).

</details>

## Development

See [`CONTRIBUTING.md`](CONTRIBUTING.md) for the workflow, licensing terms, and
review expectations. Start with the narrowest check that covers a change:

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

A schema change should update every affected codec, golden fixture, validator
rule, formatter/parser path, interpreter path, Lean parity surface, and
downstream contract in one reviewable change. A change to a proof claim should
carry its negative test: unsupported, stale, forged, dangling, or faith-stamped
evidence must be rejected for the claimed authority level.

Use the [issue tracker](https://github.com/alabsystems/trust-ir/issues) for bugs
and proposals; participation is governed by
[`CODE_OF_CONDUCT.md`](CODE_OF_CONDUCT.md). Usage and packaging help is in
[`SUPPORT.md`](SUPPORT.md); report suspected vulnerabilities privately as
directed by [`SECURITY.md`](SECURITY.md).

## Maintainer commands

The checked-in scripts compose the repository's local gates:

| Command | What it checks |
| --- | --- |
| `./scripts/ci_gates.sh` | Repository policy (no ignored Rust tests, dependency-pin census, toolchain default-authority preflight), formatting and lints, Lean/Rust schema parity, the workspace build, CLI proof gates, zero-`Trusted` and zero-`Failed` censuses, lineage closure, pin coherence, wire-format goldens, validator fail-closed arms, and the untrusted give-back elaborator |
| `./scripts/ci-self-verify.sh` | Rev-pinned Git dependencies, no ignored tests or non-executing doc examples, Lean placeholder/axiom policy, locked default and all-feature tests, conformance, the non-default AY adapter, and the Lean build when available |

Both scripts run their Rust steps through `scripts/run-targo.sh`, the
Trust-owned Targo frontend; it fails closed when Targo is unavailable and never
falls back to upstream Cargo. Set `TRUST_IR_REQUIRE_LEAN=1` to make a missing
Lean toolchain fail the self-verify gate. `TRUST_IR_SKIP_AY=1` or
`TRUST_IR_SKIP_LEAN=1` are explicit diagnostic skips; do not use a skipped run
as release evidence for that surface.

## License

Apache License 2.0. See [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE). Dependency
and influence notes are collected in [`THIRD_PARTY.md`](THIRD_PARTY.md).
TrustIr was created by Andrew Yates.
