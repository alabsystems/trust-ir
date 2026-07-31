// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared helpers for trust_ir-cli integration tests.

#![allow(dead_code)]

use std::path::PathBuf;
use std::process::Command;

use trust_ir::proof::{
    DiagnosticSeverity, Divergence, ObligationDiagnostic, ObligationKind, ProofAnnotation,
    ProofCertificate, ProofCertificateRef, ProofDigest, ProofEvidence, ProofLineageId,
    ProofLineageManifest, ProofLineageNode, ProofObligation, ProofStatus, ProofTransform,
    ProofTransformStage,
};
use trust_ir::spec::{
    ProofKind, SpecAnchor, SpecEnforcementMode, SpecInvariant, SpecOrigin, SpecProjectionTarget,
    SpecProof, SpecVar, SpecWaiver, TEMPORAL_FIELD_PATH_PROJECTION_V1,
};
use trust_ir::ty::Ty;
use trust_ir::value::{ProofId, SourceSpan};
use trust_ir::{BlockId, FuncId, FuncTy, Function, Module, SpecModule};
use trust_ir_build::ModuleBuilder;

/// Return the compiled `trust-ir` binary path. Cargo sets `CARGO_BIN_EXE_trust_ir`
/// for integration tests of the package that defines the `trust-ir` bin.
pub fn trust_ir_bin() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_trust-ir"))
}

/// Start a fresh `Command` pointing at the `trust-ir` binary.
pub fn trust_ir_cmd() -> Command {
    Command::new(trust_ir_bin())
}

/// Build a minimal well-formed module with a single `add(i64, i64) -> i64`
/// function carrying `Pure + NoPanic + Deterministic` annotations.
pub fn build_valid_module() -> Module {
    let mut mb = ModuleBuilder::new("test_valid");
    let ft = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function("add", ft);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::I64);
    let b = fb.add_block_param(entry, Ty::I64);
    fb.switch_to_block(entry);
    let sum = fb.add(Ty::I64, a, b);
    fb.ret(vec![sum]);
    fb.add_proof(ProofAnnotation::Pure);
    fb.add_proof(ProofAnnotation::NoPanic);
    fb.add_proof(ProofAnnotation::Deterministic);
    fb.build();
    mb.build()
}

/// A backend-TV-fragment sibling used by kernel-backed lineage fixtures. The
/// TV rechecker intentionally accepts uniform unsigned integer functions;
/// ordinary CLI validation controls keep using the signed-i64 module above.
fn build_lineage_module() -> Module {
    let mut mb = ModuleBuilder::new("test_lineage");
    let ft = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function("identity", ft);
    let entry = fb.create_block();
    let value = fb.add_block_param(entry, Ty::U64);
    fb.switch_to_block(entry);
    fb.ret(vec![value]);
    fb.build();
    mb.build()
}

/// Build a well-formed module carrying the diagnostics-reporting surface: a
/// populated file table, a spanned instruction, and two obligation
/// diagnostics — a located error with a machine-readable detail, and a
/// location-less note. Still validates cleanly (diagnostics are module data,
/// not a validation verdict).
pub fn build_diagnostics_module() -> Module {
    let mut m = build_valid_module();
    let f = m.intern_file("src/main.rs");
    m.functions[0].blocks[0].body[0].span = Some(SourceSpan {
        file: f,
        line: 12,
        col: 5,
    });
    // Number the obligation past any claim-synthesized rows so ids stay unique.
    let oid = ProofId::new(
        m.proof_obligations
            .iter()
            .map(|o| o.id.index() + 1)
            .max()
            .unwrap_or(0),
    );
    m.proof_obligations.push(ProofObligation::new(
        oid,
        ObligationKind::PanicFreedom,
        ProofStatus::Failed,
        "add must not overflow",
    ));
    m.obligation_diagnostics.push(
        ObligationDiagnostic::error(oid, "could not prove a + b stays in range")
            .with_location(SourceSpan {
                file: f,
                line: 12,
                col: 5,
            })
            .with_detail("counterexample: a=i64::MAX, b=1"),
    );
    m.obligation_diagnostics.push(ObligationDiagnostic {
        obligation: oid,
        severity: DiagnosticSeverity::Note,
        message: "see verifier transcript".into(),
        location: None,
        detail: None,
    });
    m
}

/// Build a minimal module with a function that has ParallelMap +
/// DivergenceClass(Uniform) on top of the base Pure/NoPanic/Deterministic
/// contract — this function is fully GPU-eligible.
pub fn build_gpu_eligible_module() -> Module {
    let mut mb = ModuleBuilder::new("gpu_eligible");
    let ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function("kernel", ft);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::I64);
    fb.switch_to_block(entry);
    fb.ret(vec![x]);
    fb.add_proof(ProofAnnotation::Pure);
    fb.add_proof(ProofAnnotation::NoPanic);
    fb.add_proof(ProofAnnotation::Deterministic);
    fb.add_proof(ProofAnnotation::ParallelMap);
    fb.add_proof(ProofAnnotation::DivergenceClass(Divergence::Uniform));
    fb.build();
    mb.build()
}

/// Build a module whose single function has the base GPU contract but
/// `DivergenceClass(High)` — safe-for-gpu = true, gpu-eligible = false.
pub fn build_gpu_high_divergence_module() -> Module {
    let mut mb = ModuleBuilder::new("high_divergence");
    let ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function("hot_path", ft);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::I64);
    fb.switch_to_block(entry);
    fb.ret(vec![x]);
    fb.add_proof(ProofAnnotation::Pure);
    fb.add_proof(ProofAnnotation::NoPanic);
    fb.add_proof(ProofAnnotation::Deterministic);
    fb.add_proof(ProofAnnotation::ParallelMap);
    fb.add_proof(ProofAnnotation::DivergenceClass(Divergence::High));
    fb.build();
    mb.build()
}

/// Build a fully-conforming `ring` SpecModule: `Push` anchored, `Pop` waived,
/// every action covered, the machine name resolves. Passes all obligations.
pub fn ring_spec_pass() -> SpecModule {
    SpecModule {
        name: "ring".to_string(),
        vars: vec![SpecVar::new("seq", "0..7")],
        actions: vec!["Push".to_string(), "Pop".to_string()],
        invariants: vec![SpecInvariant::new("BoundedSeq", "seq <= 7")],
        anchors: vec![SpecAnchor {
            machine: "ring".to_string(),
            action: "Push".to_string(),
            function: Some(FuncId::new(0)),
            rust_symbol: "add".to_string(),
            span: "crates/aterm-buffer/src/ring.rs:120:4".to_string(),
            project: Some(TEMPORAL_FIELD_PATH_PROJECTION_V1.to_string()),
            projection_target: Some(SpecProjectionTarget::TemporalFieldPathsV1),
        }],
        waivers: vec![SpecWaiver {
            machine: "ring".to_string(),
            action: "Pop".to_string(),
            reason: "pop has no shipping handler yet".to_string(),
        }],
        proofs: vec![],
        origin: SpecOrigin::External("fixtures/Ring.tla".to_string()),
        enforcement: SpecEnforcementMode::Linked,
    }
}

fn module_with_spec(name: &str, spec: SpecModule) -> Module {
    let mut module = build_valid_module();
    module.name = name.to_string();
    module.spec_modules.push(spec);
    module
}

/// A module carrying the passing `ring` spec and nothing else.
pub fn build_spec_pass_module() -> Module {
    module_with_spec("spec_pass", ring_spec_pass())
}

/// A fully linked typed anchor. The enclosing `Module.name` plus FuncId(0)
/// identifies the exact body; `rust_symbol` mirrors its module-local name.
pub fn build_spec_pass_typed_anchor_module() -> Module {
    let mut m = build_spec_pass_module();
    m.name = "typed_anchor".to_string();
    m
}

/// A typed anchor whose module-local FuncId has no target.
pub fn build_spec_fail_typed_anchor_missing_function() -> Module {
    let mut m = build_spec_pass_typed_anchor_module();
    m.spec_modules[0].anchors[0].function = Some(FuncId::new(99));
    m
}

/// A typed anchor whose diagnostic source name disagrees with its exact target.
pub fn build_spec_fail_typed_anchor_mismatched_symbol() -> Module {
    let mut m = build_spec_pass_typed_anchor_module();
    m.spec_modules[0].anchors[0].rust_symbol = "other::add".to_string();
    m
}

/// A linked embedded anchor whose projection resolves to a real body and exact
/// name but has the forbidden `(T) -> R` shape instead of `(&T) -> R`.
pub fn build_spec_fail_typed_projection_signature() -> Module {
    let mut mb = ModuleBuilder::new("typed_projection_signature");
    let action_ty = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let mut action = mb.function("action", action_ty);
    let action_entry = action.create_block();
    let value = action.add_block_param(action_entry, Ty::I64);
    action.switch_to_block(action_entry);
    action.ret(vec![value]);
    action.build();

    let projection_ty = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let mut projection = mb.function("project", projection_ty);
    let projection_entry = projection.create_block();
    let value = projection.add_block_param(projection_entry, Ty::I64);
    projection.switch_to_block(projection_entry);
    projection.ret(vec![value]);
    projection.build();

    let mut module = mb.build();
    let mut spec = SpecModule::linked("Machine");
    spec.actions.push("Step".to_string());
    spec.anchors.push(SpecAnchor {
        machine: "Machine".to_string(),
        action: "Step".to_string(),
        rust_symbol: "action".to_string(),
        span: "fixture.rs:1:1".to_string(),
        project: Some("project".to_string()),
        function: Some(FuncId::new(0)),
        projection_target: Some(SpecProjectionTarget::Function(FuncId::new(1))),
    });
    module.spec_modules.push(spec);
    module
}

// ---------------------------------------------------------------------------
// L1 / L2 / L3 fixtures (the spec-link integrity teeth — §1.C / §3.1)
// ---------------------------------------------------------------------------

/// L1 RED fixture — a `SpecProof` whose `proof_name` does not exist. Paired with
/// a manifest lacking it (`harness_manifest_without_proof`), spec-link must flag
/// `L1 ProofUnresolved` (exit 1).
pub fn build_spec_fail_l1_module() -> Module {
    let mut ring = ring_spec_pass();
    ring.proofs.push(SpecProof {
        machine: "ring".to_string(),
        action: "Push".to_string(),
        proof_name: "does_not_exist".to_string(),
        kind: ProofKind::Kani,
    });
    module_with_spec("spec_fail_l1", ring)
}

/// L1 CONTROL fixture — the same `SpecProof`, but with a real `proof_name`
/// (`ring_push_refines`). Paired with `harness_manifest_with_proof`, spec-link
/// passes (exit 0).
pub fn build_spec_pass_l1_module() -> Module {
    let mut ring = ring_spec_pass();
    ring.proofs.push(SpecProof {
        machine: "ring".to_string(),
        action: "Push".to_string(),
        proof_name: "ring_push_refines".to_string(),
        kind: ProofKind::Kani,
    });
    module_with_spec("spec_pass_l1", ring)
}

/// A harness manifest (JSON text) that DOES list `ring_push_refines` — the L1
/// control manifest.
pub fn harness_manifest_with_proof() -> String {
    r#"{
  "harnesses": [
    { "name": "ring_push_refines", "span": "crates/aterm-buffer/src/ring.rs:300:1" },
    { "name": "ring_pop_refines",  "span": "crates/aterm-buffer/src/ring.rs:340:1" }
  ]
}"#
    .to_string()
}

/// A harness manifest (JSON text) that does NOT list the proof — the L1 red
/// manifest. (`ring_push_refines` is present so the control passes, but
/// `does_not_exist` never is.)
pub fn harness_manifest_without_proof() -> String {
    r#"{
  "harnesses": [
    { "name": "ring_push_refines", "span": "crates/aterm-buffer/src/ring.rs:300:1" }
  ]
}"#
    .to_string()
}

/// L2 RED fixture — a present owned anchor whose `project` is `None`.
/// spec-link must flag `L2 ProjectionMissing` (exit 1). We add a new
/// anchor for the `Pop` action (un-waiving it) so the missing-projection anchor
/// is the sole new violation.
pub fn build_spec_fail_l2_module() -> Module {
    let mut ring = ring_spec_pass();
    ring.waivers.clear(); // un-waive Pop so we can anchor it
    ring.anchors.push(SpecAnchor {
        machine: "ring".to_string(),
        action: "Pop".to_string(),
        function: Some(FuncId::new(0)),
        rust_symbol: "add".to_string(),
        span: "crates/aterm-buffer/src/ring.rs:140:4".to_string(),
        project: None, // <-- the inert project the audit found
        projection_target: Some(SpecProjectionTarget::ExternalUnresolved),
    });
    module_with_spec("spec_fail_l2", ring)
}

/// L2 CONTROL fixture — same shape, but the `Pop` anchor carries a real
/// projection name. spec-link passes (exit 0).
pub fn build_spec_pass_l2_module() -> Module {
    let mut ring = ring_spec_pass();
    ring.waivers.clear();
    ring.anchors.push(SpecAnchor {
        machine: "ring".to_string(),
        action: "Pop".to_string(),
        function: Some(FuncId::new(0)),
        rust_symbol: "add".to_string(),
        span: "crates/aterm-buffer/src/ring.rs:140:4".to_string(),
        project: Some(TEMPORAL_FIELD_PATH_PROJECTION_V1.to_string()),
        projection_target: Some(SpecProjectionTarget::TemporalFieldPathsV1),
    });
    module_with_spec("spec_pass_l2", ring)
}

/// L3 RED fixture — an **external** (Next-only) `SpecModule` whose `actions`
/// list only the Next-disjunct `Step`, plus an anchor naming the non-Next def
/// `TypeOK`. Because the external artifact carries only Next-disjunct actions,
/// Ob.1 must reject the `TypeOK` anchor (exit 1) — locking the stricter
/// external behavior so a future change cannot re-widen `actions` to all defs.
pub fn build_spec_fail_l3_module() -> Module {
    let external = SpecModule {
        name: "isolation".to_string(),
        vars: vec![SpecVar::new("entered", "Bool")],
        // Next-only: the lowering emits ONLY coverage_actions() (Next disjuncts).
        // `TypeOK`/`Init` are NOT here — they are invariants/initial-state defs.
        actions: vec!["Step".to_string()],
        invariants: vec![SpecInvariant::new("TypeOK", "entered \\in BOOLEAN")],
        anchors: vec![SpecAnchor {
            machine: "isolation".to_string(),
            // Names a non-Next def — must be rejected by Ob.1.
            action: "TypeOK".to_string(),
            function: Some(FuncId::new(0)),
            rust_symbol: "add".to_string(),
            span: "crates/aterm-isolation/src/lib.rs:10:4".to_string(),
            project: Some(TEMPORAL_FIELD_PATH_PROJECTION_V1.to_string()),
            projection_target: Some(SpecProjectionTarget::TemporalFieldPathsV1),
        }],
        waivers: vec![],
        proofs: vec![],
        origin: SpecOrigin::External("crates/aterm-spec-models/specs/Isolation.tla".to_string()),
        enforcement: SpecEnforcementMode::Linked,
    };
    module_with_spec("spec_fail_l3", external)
}

/// Negative fixture #1 — violates **Ob.1** (action exists): adds an anchor for
/// an action `"SetOriginMode"` that the `ring` machine does not declare.
pub fn build_spec_fail_ob1_module() -> Module {
    let mut ring = ring_spec_pass();
    ring.anchors.push(SpecAnchor {
        machine: "ring".to_string(),
        action: "SetOriginMode".to_string(),
        function: Some(FuncId::new(0)),
        rust_symbol: "add".to_string(),
        span: "crates/aterm-buffer/src/ring.rs:200:4".to_string(),
        project: Some(TEMPORAL_FIELD_PATH_PROJECTION_V1.to_string()),
        projection_target: Some(SpecProjectionTarget::TemporalFieldPathsV1),
    });
    module_with_spec("spec_fail_ob1", ring)
}

/// Negative fixture #2 — violates **Ob.3** (coverage): the `Pop` action is
/// neither anchored nor waived. The machine is explicitly `Linked`, so
/// coverage remains a hard gate.
pub fn build_spec_fail_ob3_module() -> Module {
    let mut ring = ring_spec_pass();
    ring.waivers.clear(); // drop the waiver covering `Pop`
    module_with_spec("spec_fail_ob3", ring)
}

/// Negative fixture #3 — violates **Ob.4** (machine resolves): an anchor names
/// machine `"terminal_modes"` for which no SpecModule exists in the input
/// (the dead-`TerminalModes.tla` situation from the design).
pub fn build_spec_fail_ob4_module() -> Module {
    let mut ring = ring_spec_pass();
    ring.anchors.push(SpecAnchor {
        machine: "terminal_modes".to_string(),
        action: "SetOriginMode".to_string(),
        function: Some(FuncId::new(0)),
        rust_symbol: "add".to_string(),
        span: "crates/aterm-terminal/src/modes.rs:42:4".to_string(),
        project: Some(TEMPORAL_FIELD_PATH_PROJECTION_V1.to_string()),
        projection_target: Some(SpecProjectionTarget::TemporalFieldPathsV1),
    });
    module_with_spec("spec_fail_ob4", ring)
}

// ---------------------------------------------------------------------------
// Lineage-closure / zero-Trusted census fixtures (`validate --lineage`,
// `validate --forbid-trusted` — bootstrap-trust-model.md sketch item 2)
// ---------------------------------------------------------------------------

/// Allocate the next free obligation id (past any claim-synthesized rows).
fn next_obligation_id(m: &Module) -> ProofId {
    ProofId::new(
        m.proof_obligations
            .iter()
            .map(|o| o.id.index() + 1)
            .max()
            .unwrap_or(0),
    )
}

/// Push one obligation (with `status`) plus a certificate carrying `evidence`
/// onto `m`'s proof tables; returns the obligation id and the certificate's
/// lineage reference for threading into a manifest rung.
fn push_backed_obligation(
    m: &mut Module,
    status: ProofStatus,
    evidence: ProofEvidence,
    description: &str,
) -> (ProofId, ProofCertificateRef) {
    let id = next_obligation_id(m);
    m.proof_obligations.push(ProofObligation::new(
        id,
        ObligationKind::TranslationValidation,
        status,
        description,
    ));
    let cert = ProofCertificate {
        obligation: id,
        prover: "ay".to_string(),
        evidence,
    };
    let cert_ref = cert.lineage_ref();
    m.proof_certificates.push(cert);
    (id, cert_ref)
}

fn lineage_digest(tag: &str) -> ProofDigest {
    ProofDigest::sha256_domain("trust_ir-cli.test.lineage.v2", tag.as_bytes())
}

fn build_non_authoritative_lineage_fixture(
    status: ProofStatus,
    evidence: ProofEvidence,
) -> (Module, ProofLineageManifest) {
    let mut m = build_valid_module();
    let id = next_obligation_id(&m);
    let mut node = ProofLineageNode::new(
        ProofLineageId::new(0),
        ProofTransform::new(
            ProofTransformStage::Frontend,
            "frontend",
            "trust-ir-cli-test",
            "1.0.0",
        ),
        lineage_digest("source"),
        lineage_digest("target"),
    );
    let obligation = ProofObligation::new(
        id,
        ObligationKind::TranslationValidation,
        status,
        "pass preserved semantics",
    )
    .with_formula(node.transform_binding_formula());
    let certificate = ProofCertificate {
        obligation: id,
        prover: "trust-ir-cli-test".to_string(),
        evidence,
    };
    node.obligations.push(id);
    node.certificates.push(certificate.lineage_ref());
    m.proof_obligations.push(obligation);
    m.proof_certificates.push(certificate);
    let mut manifest = ProofLineageManifest::new();
    manifest.nodes.push(node);
    manifest.roots.push(ProofLineageId::new(0));
    (m, manifest)
}

/// A CLOSED identity lineage whose exact source/target semantics, transform
/// identity, obligation, and CleanCic proof are all re-derived and
/// kernel-replayed by the validator.
pub fn build_lineage_closed_fixture() -> (Module, ProofLineageManifest) {
    let mut module = build_lineage_module();
    let id = next_obligation_id(&module);
    let (node, obligation, certificate) = trust_ir_build::certify_identity_lineage_rung(
        &module,
        ProofLineageId::new(0),
        id,
        ProofTransform::new(
            ProofTransformStage::Frontend,
            "identity-frontend",
            "trust-ir-cli-test",
            "1.0.0",
        ),
        module.functions[0].id,
    )
    .expect("identity lineage fixture must be kernel-certifiable");
    module.proof_obligations.push(obligation);
    module.proof_certificates.push(certificate);
    let mut manifest = ProofLineageManifest::new();
    manifest.roots.push(node.id);
    manifest.nodes.push(node);
    (module, manifest)
}

/// A structurally complete but OPEN lineage: every rung carries only opaque
/// SMT bytes. No validator replay capability recognizes those bytes.
pub fn build_lineage_opaque_smt_fixture() -> (Module, ProofLineageManifest) {
    build_non_authoritative_lineage_fixture(
        ProofStatus::Discharged,
        ProofEvidence::SmtProof(vec![0xDE, 0xAD, 0xBE, 0xEF]),
    )
}

/// An OPEN lineage: its rung is faith-stamped (`Trusted` evidence and
/// the internally-consistent `Trusted` status). `lineage_is_closed` must
/// report a `TrustedRung` gap.
pub fn build_lineage_trusted_rung_fixture() -> (Module, ProofLineageManifest) {
    build_non_authoritative_lineage_fixture(
        ProofStatus::Trusted,
        ProofEvidence::Trusted("hand-checked by reviewer".to_string()),
    )
}

/// A MIS-THREADED chain: two kernel-backed identity rungs whose second source
/// digest is tampered so it no longer matches rung 0's target.
/// `lineage_is_closed` alone does not inspect digest threading — this is
/// exactly what `validate_against` catches, and why `--lineage` runs both.
pub fn build_lineage_misthreaded_fixture() -> (Module, ProofLineageManifest) {
    let (mut m, mut manifest) = build_lineage_closed_fixture();
    let id = next_obligation_id(&m);
    let (mut node, obligation, certificate) = trust_ir_build::certify_identity_lineage_rung(
        &m,
        ProofLineageId::new(1),
        id,
        ProofTransform::new(
            ProofTransformStage::Backend,
            "identity-backend",
            "trust-ir-cli-test",
            "1.0.0",
        ),
        m.functions[0].id,
    )
    .expect("second identity lineage rung must be kernel-certifiable");
    node.depends_on.push(ProofLineageId::new(0));
    m.proof_obligations.push(obligation);
    m.proof_certificates.push(certificate);
    manifest.roots.clear();
    manifest.roots.push(node.id);
    manifest.nodes.push(node);
    manifest.nodes[1].source_module = lineage_digest("not-the-predecessor-target");
    (m, manifest)
}

/// Module with a faith-stamped obligation STATUS: `Trusted`, scoped to the
/// `add` function, no certificate. `--forbid-trusted` must list it (id, kind,
/// function scope, description) and exit 1.
pub fn build_trusted_status_module() -> Module {
    let mut m = build_valid_module();
    let id = next_obligation_id(&m);
    let mut obligation = ProofObligation::new(
        id,
        ObligationKind::PanicFreedom,
        ProofStatus::Trusted,
        "believed panic-free (manual audit)",
    );
    obligation.function = Some(m.functions[0].id);
    m.proof_obligations.push(obligation);
    m
}

/// Module with faith-stamped EVIDENCE: a certificate whose evidence is
/// `ProofEvidence::Trusted` with the internally consistent `Trusted` status.
/// `--forbid-trusted` must list the certificate's justification string as well
/// as refusing the faith-stamped status.
pub fn build_trusted_evidence_module() -> Module {
    let mut m = build_valid_module();
    push_backed_obligation(
        &mut m,
        ProofStatus::Trusted,
        ProofEvidence::Trusted("hand-checked 2026-07-10".to_string()),
        "audited translation step",
    );
    m
}

/// Module with a refuted obligation STATUS: `Failed`, scoped to the `add`
/// function, no certificate — the shape `trust_ir_ay::apply_vc_outcomes`
/// leaves behind when ay refutes a contract's ensures (WS3-M1).
/// `--forbid-failed` must list it (id, kind, function scope, description)
/// and exit 1.
pub fn build_failed_status_module() -> Module {
    let mut m = build_valid_module();
    let id = next_obligation_id(&m);
    let mut obligation = ProofObligation::new(
        id,
        ObligationKind::Postcondition,
        ProofStatus::Failed,
        "ensures clause 0 of 'add': (= result (+ a b 1))",
    );
    obligation.function = Some(m.functions[0].id);
    m.proof_obligations.push(obligation);
    m
}

/// Build a deliberately invalid module: a function whose single block has no
/// terminator. `trust-ir_build::validate_module` should report this.
pub fn build_invalid_module() -> Module {
    // Manually construct — the builder enforces invariants we want to
    // deliberately violate. We use the raw `trust-ir::Module` API instead.
    let mut module = Module::new("test_invalid");
    let ft = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![],
        is_vararg: false,
    });
    let entry = BlockId::new(0);
    let mut func = Function::new(trust_ir::FuncId::new(0), "no_terminator", ft, entry);
    func.blocks.push(trust_ir::Block::new(entry));
    module.add_function(func);
    module
}
