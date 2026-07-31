# The Trust Toolchain Trusted Base

**Status:** Ratified (2026-06-13). This document is canonical. It states what
the correctness of a Trust-produced artifact rests on, and — equally important —
what it does **not**. Other repo documents link here instead of restating
folklore.

The active program driving boundary closures is **Program CK1**
(`designs/2026-07-07-program-ck1-confluent-kernel.md`, with an internal
program ledger). Closure claims land as reviewed edits to *this*
document, adversarially checked against the mechanization; boundaries are
restated or deleted here, never silently dropped elsewhere.

## Trusted base

The Trust toolchain's correctness rests on exactly this trusted base:

1. **The Lean 4 kernel.**
2. **`ay_sound_unsat`** (`lean/trust_ir-semantics/TrustIr/Proofs/AYBridge.lean`):
   every `ay` UNSAT verdict is sound. This is the one first-party axiom; it is
   the documented SMT-solver soundness boundary.
3. **The trust-ir → Lean semantics correspondence**: the Lean operational
   semantics faithfully models the TrustIr that TrustCg consumes. This is a
   *known gap* wherever the Lean model lags the Rust reference interpreter — see
   the ratified UB/numerics policy §7 (numerics) and the B3 schema-parity gate. The
   gap is tracked, not hidden: the Rust reference interpreter is locked by tests
   (`crates/trust-ir-build/tests/numerics_policy.rs`), and the Lean side is
   specified pending reconciliation.
4. **The `trust-ir` validator** (`trust-ir-build::validate_module`): a module
   admitted by the validator is well-formed in the senses the validator checks
   (type-correctness of every instruction, SSA + dominance, CFG/terminator
   structure, ABI/entry-signature agreement, proof-obligation integrity).
5. **For self-hosted binaries only**: the bootstrap argument (diverse
   double-compilation and/or independent re-check) and the closure of the
   `ProofLineageNode` chain with zero `Trusted(...)` rungs.

Everything **outside** this list — including the `rustc`/LLVM that built the
first checker — is **not** trusted: its output is independently re-checkable
from the proof certificates.

### Backend certificate boundaries (Clean producer, t-silicon route 1)

The Clean producer carries two kinds of `ck0`-kernel-rechecked certificate.
Both re-run `clean_kernel::check_type` with `axiom_deps ⊆ FOUNDATIONAL_AXIOMS`
(the `KERNEL_ANCHOR_CLEAN_BACKEND_TV` and `KERNEL_ANCHOR_TRUSTCG_LOWERING_RESOLUTION`
anchors in `crates/trust-ir-build/src/validate.rs`), so what the *kernel*
decides adds nothing to the trusted base above. Each carries **one** named
residual assumption, stated here so it is tracked, not hidden:

6. **Backend translation-validation denotation maps** (source → trust-ir): the
   `clean-reflect` maps that reflect an emitted trust-ir function and the source
   Clean `Expr` into one shared `Nat`-mod-`2^w` vocabulary are *checker spec*
   (the Fragment-1 discipline). The kernel decides the resulting equation
   `reflected ≐ original`; that the two maps compute the source/emitted meanings
   is the assumption. A miscompile within the covered fragment IS caught (the
   kernel refuses the equation) — the maps' own in-kernel mechanization is the
   open deepening.
7. **Lowering-miter encoding fidelity** (trust-ir → machine): the kernel
   certifies UNSAT of the bit-blast clause list, and the untrusted producer's
   gate-level provenance (`trust_ir::proof::satprov`) is *checked* — the clause
   list is confirmed to be exactly the Tseitin miter of the recorded gate DAG,
   sides compared bit-for-bit. The single residual assumption is
   **gate-DAG ⇔ `SmtExpr`**: that `blast(ir_expr)` / `blast(machine_expr)`
   compute the rule's actual source/machine semantics. Closing it is t-silicon
   route (b) (route ay's own audited bit-blaster through the same cert), scoped
   in `designs/2026-07-01-t-silicon-one-tcb-scoping.md`.
   *Composed-claim scope note:* `verify_source_to_silicon` requires a P3 miter
   cert for every ALU node in `f`'s body (unrecognized nodes fail closed), but
   the two trivially-lowered node kinds — `Const{i8}` → immediate
   materialization and single-value `Return` → calling-convention — carry no
   miter cert by construction. So the composed "source ≐ machine" claim
   additionally trusts those two lowerings (same trust class as the fidelity
   assumption above, for two non-ALU node kinds). A soundness review
   (2026-07-05) found no code hole in the composition beyond this.

### Two interpretations of "proven"

- **(A) Per-module admissibility** — each emitted module carries proofs the
  validator + Lean semantics admit. The current artifacts satisfy A per-module.
- **(B) Whole-pipeline correctness** — the *transformation* from source to
  emitted code is proven correct end to end. The current artifacts satisfy B
  for the vector dialect and the proven dialect lowerings, and — for the Clean
  producer — over a growing *fragment*: the source → trust-ir step is
  kernel-checked by the backend TV certificate (boundary 6) and the
  trust-ir → machine step is kernel-checked by the lowering-resolution
  certificate for the i8 ALU lowering family (`iadd`/`isub`/`neg`/`band`/`bor`/
  `bxor`, boundary 7). Composing the two on one artifact (the transitive
  source → machine claim under the single `ck0` kernel) is the t-silicon
  milestone-2 target. B remains **honestly known-not-closed** *in general*:
  `TransformCorrectness.lean` inlining-correctness is still prose, and the
  fragment excludes memory, loops, recursion, and lowering rules past the i8
  tier — each an open rung that would otherwise force a `Trusted(...)` gap.

### Lineage closure

A module's `ProofLineageNode` chain is **closed** iff every rung from the source
digest to the emitted-code digest is present, `depends_on`-connected, and **none
uses `ProofEvidence::Trusted(...)`**. Only a closed chain backs interpretation
B for that module. (Helper tracked on the internal roadmap,
proofchain-lineage-append.)

## Build determinism

For an artifact to be *independently re-checkable* — and for diverse
double-compilation to mean anything — the same source must produce
**bit-identical** TrustIr and **identical** proof digests on any machine.

**Guarantee (ratified):** for a *fixed* producer version, Trust IR emission and
proof-digest computation are deterministic. This rests on:

- `ProofDigest::TrustIrStableV1` digests via explicit `write_*_stable` helpers,
  never `derive`d/`HashMap`-order output (verified by the SHA-256 known-answer
  tests and the stable-digest paths).
- A byte-golden conformance corpus pins every wire format
  (`crates/trust-ir-conformance`, backed by the internal binary-format and
  serialization-formats specs).
- `Module` stores all tables as order-stable `Vec`s; the semantic diff
  (`trust-ir-diff`) is the tool that makes ID-renumbering/reorder *observable*
  rather than silent.

**Audit obligation (discharged in-repo; one cross-repo hazard open):** every
`HashMap`/`HashSet` whose iteration feeds serialized output or a digest input,
and every interning/dedup step, is confirmed insertion-ordered / `BTreeMap` /
`Vec`-order — the per-item checklist (file:line verdicts),
`Module::stable_digest`, the cross-process determinism test, and the DDC
procedure live on the internal build-determinism roadmap. The one open hazard is
cross-repo: canonical ay SMT proof transcripts (`ProofEvidence::SmtProof` bytes
are hashed as-is; dormant today because ay exports no proof payloads). Until it
closes, the guarantee does not yet cover future non-empty `SmtProof` evidence
digests.

## Frontend emission handshake

Producers (tRust, Clean) emit TrustIr through the `trust-ir-build` builder
API and may carry source provenance via the debug-info source-file table
(`Module::intern_file` + `SourceSpan::file`, since binary VERSION 9). The pinned
conformance subset a producer must round-trip is the `trust-ir-conformance`
corpus. A typed in-process handoff for verification requests already exists
(`trust_ir::request::NativeVerificationBundle`). What remains roadmap is a
first-class span-threaded emission bridge from native MIR, tracked on the
internal frontend-emission integration roadmap.
