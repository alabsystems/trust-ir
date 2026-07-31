# Scope and limitations

TrustIr 0.2 is a preview of a shared proof-carrying compiler IR. Representing a
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
- There is no general proof from arbitrary Trust, Clean, or Rust source to
  machine code. Certificate authority is checker-specific and currently
  restricted to documented fragments. See [`TRUST.md`](TRUST.md) and
  [`lowering-target-subset.md`](lowering-target-subset.md).
- The reference interpreter is bounded and deliberately partial. It is a
  conformance and diagnostic path, not a production runtime or code generator.
- The Lean package does not yet model the entire TrustIr instruction set. Its
  axiom audit retains the explicit first-party `ay_sound_unsat` axiom, and
  Rust-to-Lean correspondence remains part of the trusted boundary.
- Canonical text is human-oriented and currently omits struct field names and
  offsets and `FunctionSummary`. Binary, JSON, and MessagePack are the lossless
  module paths. Proof lineage is a separately versioned sidecar.
- `trust-ir-diff` currently accepts serde JSON modules only. Unknown dialect
  payloads round-trip, but their semantics and lowering legality remain owned
  by the implementing backend.
- Give-back certification, the AY adapter, and the workspace-excluded
  `rustc_private` frontend are experimental or fragment-specific. Optional
  Clean-backed anchors require their exact mapped dependency revisions.
- Synthetic benchmark fixtures exercise construction, validation, and
  serialization. They do not establish an aggregate performance or scalability
  claim.

Unsupported evidence and out-of-fragment operations should be rejected or
reported as unsupported. Treat every claim at the granularity of its named
artifact, checker, revision, and negative tests.
