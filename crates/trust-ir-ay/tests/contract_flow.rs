// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// WS3-M1 contracts-flow seed, NEGATIVE-TEST-FIRST: a function whose body
// VIOLATES its `ensures` must end with a `Failed` obligation carrying the
// ay counterexample — before any passing demo. These run the pinned ay
// solver in-process (real verdicts, like vc_integration.rs). The flow:
//
//   FunctionSummary (ensures)  --mint_summary_obligations-->  Pending
//   Postcondition obligation (B4-scoped)  --verify_function--> whole-function
//   VC over the body's lowered ensures-check (`Assert`)  --apply_vc_outcomes-->
//   Failed (+ ObligationDiagnostic counterexample) | Pending (proved by ay,
//   but awaiting a replayable certificate).
//
// The build-abort half of the seed lives in trust-ir-cli:
// `validate --forbid-failed` (see cli_forbid_failed.rs and scripts/ci_gates.sh).
//
// WS1.3: `mint_summary_obligations` now attaches each clause as the row's
// `formula` (that is what lets a row back exactly one clause of a `proved`
// summary), and this adapter reports a formula-carrying obligation
// `Unsupported` — it has no SMT-LIB bridge over bound places yet (WS5 /
// F-091). So a MINTED row is never ay-discharged or ay-refuted
// (`a_minted_contract_row_is_unsupported_fail_closed`). The refutation flow
// below still runs, on a hand-built formula-less row (`mint_unstated`): such a
// row can be refuted, and — WS1.3 — can never back `proved`.

#![allow(clippy::disallowed_methods)] // a test drives ay directly; a panic here is a test failure (r11 item 5, crates/trust-ir-ay/clippy.toml)

use trust_ir::inst::ICmpOp;
use trust_ir::proof::{DiagnosticSeverity, ObligationKind, ProofFormula, ProofStatus};
use trust_ir::ty::Ty;
use trust_ir::value::{FuncId, ProofId, ValueId};
use trust_ir::{FunctionSummary, Module};
use trust_ir_ay::{
    Counterexample, VcApplyError, VcObligationOutcome, VcSource, VcVerdict, apply_vc_outcomes,
    verify_function,
};
use trust_ir_build::{ModuleBuilder, mint_summary_obligations, validate_module};

/// `fn bump(x: i64) -> i64 { x + addend }` with the contract
/// `ensures (= result (+ x 1))`, and the checked-contract lowering of that
/// ensures in the body: `assert(result == x + 1)` before the return.
/// `addend == 1` satisfies the contract; any other addend violates it.
fn build_bump_module(addend: i128) -> (Module, ValueId) {
    let mut mb = ModuleBuilder::new("contract_bump");
    let ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function("bump", ft);

    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::I64);
    fb.switch_to_block(entry);

    let k = fb.iconst(Ty::I64, addend);
    let result = fb.add(Ty::I64, x, k);
    // Lowered ensures check: result == x + 1.
    let one = fb.iconst(Ty::I64, 1);
    let expected = fb.add(Ty::I64, x, one);
    let ok = fb.icmp(ICmpOp::Eq, Ty::I64, result, expected);
    fb.assert(ok);
    fb.ret(vec![result]);
    fb.build();

    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    module.functions[0].summary = Some(
        FunctionSummary::new()
            .with_params(vec!["x".to_string()])
            .ensuring(ProofFormula::smtlib2("(= result (+ x 1))", "Bool")),
    );
    (module, x)
}

/// Mint the contract rows, then strip each row's `formula`: the pre-WS1.3
/// shape, which this adapter can still bind a function-wide refutation to.
/// A formula-less row states no clause, so it can be REFUTED here but can
/// never back a `proved` summary.
fn mint_unstated(module: &mut Module, func: FuncId) -> Vec<ProofId> {
    let ids = mint_summary_obligations(module, func).expect("fresh obligation ids");
    for obligation in &mut module.proof_obligations {
        if ids.contains(&obligation.id) {
            obligation.formula = None;
        }
    }
    ids
}

// ============================================================================
// WS1.3: a minted row states its clause, and the adapter fails closed on it
// ============================================================================

/// The minted Postcondition carries `ensures (= result (+ x 1))` as its
/// formula; the adapter has no bridge for a formula-carrying row, so the
/// outcome is `Unsupported` whether the body satisfies or violates the
/// clause, nothing transitions, and a `proved` summary over the still-Pending
/// row is refused by the validator. ay-earned `proved` is unavailable until
/// the adapter can discharge such a row — fail closed, never a false verdict.
#[test]
fn a_minted_contract_row_is_unsupported_fail_closed() {
    for addend in [1, 2] {
        let (mut module, _) = build_bump_module(addend);
        let func = module.functions[0].id;
        let ids = mint_summary_obligations(&mut module, func).expect("fresh obligation ids");
        assert_eq!(ids.len(), 1);
        assert_eq!(
            module.proof_obligations[0].formula.as_ref(),
            Some(&module.functions[0].summary.as_ref().unwrap().ensures[0]),
            "the minted row states its clause exactly"
        );

        let vc = verify_function(&module, func).unwrap();
        let outcome = vc
            .obligations
            .iter()
            .find(|(id, _)| *id == ids[0])
            .map(|(_, outcome)| outcome.clone())
            .expect("the minted row is reported");
        assert!(
            matches!(&outcome, VcObligationOutcome::Unsupported { reason } if reason.contains("formula payload")),
            "addend {addend}: {outcome:?}"
        );
        let transitions = apply_vc_outcomes(&mut module, &vc).unwrap();
        assert!(transitions.is_empty(), "addend {addend}: {transitions:?}");
        assert_eq!(module.proof_obligations[0].status, ProofStatus::Pending);

        let summary = module.functions[0].summary.take().unwrap();
        module.functions[0].summary = Some(summary.proved());
        assert!(
            validate_module(&module).iter().any(|error| error
                .to_string()
                .contains("ensures clause 0 `(= result (+ x 1))` has no Discharged/Certified")),
            "addend {addend}: a Pending minted row backs nothing"
        );
    }
}

// ============================================================================
// NEGATIVE FIRST: violated ensures -> ay refutes -> Failed + counterexample
// ============================================================================

/// `ensures result == x + 1`, body returns `x + 2`: the VC's lowered ensures
/// assert refutes, and the minted Postcondition obligation transitions to
/// `Failed` with the counterexample attached as an ObligationDiagnostic.
#[test]
fn violated_ensures_fails_obligation_with_counterexample() {
    let (mut module, x) = build_bump_module(2);
    let func = module.functions[0].id;

    let ids = mint_unstated(&mut module, func);
    assert_eq!(ids.len(), 1, "one ensures clause -> one obligation");
    let oid = ids[0];
    assert_eq!(
        module.proof_obligations[0].kind,
        ObligationKind::Postcondition
    );
    assert_eq!(module.proof_obligations[0].status, ProofStatus::Pending);
    assert_eq!(module.proof_obligations[0].function, Some(func));
    assert!(
        validate_module(&module).is_empty(),
        "the minted module must be well-formed"
    );

    // Real solver: the lowered ensures assert refutes for every x.
    let vc = verify_function(&module, func).unwrap();
    assert_eq!(vc.conditions.len(), 1);
    assert_eq!(vc.conditions[0].source, VcSource::Assert);
    let VcVerdict::Refuted {
        counterexample: Counterexample::Model(counterexample),
    } = &vc.conditions[0].verdict
    else {
        panic!(
            "expected Refuted with a consumer-accepted model, got {:?}",
            vc.conditions[0].verdict
        );
    };
    assert!(
        counterexample.iter().any(|(v, _)| *v == x),
        "counterexample must name the input parameter: {counterexample:?}"
    );

    // Apply: Pending -> Failed, diagnostic attached.
    let transitions = apply_vc_outcomes(&mut module, &vc).unwrap();
    assert_eq!(transitions, vec![(oid, ProofStatus::Failed)]);
    assert_eq!(module.proof_obligations[0].status, ProofStatus::Failed);

    let diagnostic = module
        .obligation_diagnostics
        .iter()
        .find(|d| d.obligation == oid)
        .expect("a Failed transition must attach a diagnostic");
    assert_eq!(diagnostic.severity, DiagnosticSeverity::Error);
    assert!(
        diagnostic.message.contains("refuted"),
        "message should say the VC refuted: {}",
        diagnostic.message
    );
    let detail = diagnostic
        .detail
        .as_deref()
        .expect("the diagnostic must carry the counterexample detail");
    assert!(
        detail.contains("counterexample") && detail.contains(&format!("v{}", x.index())),
        "detail should carry the named counterexample assignment, got: {detail}"
    );

    // The module still round-trips validation (Failed is recorded, not
    // rejected — the build abort is the CLI's --forbid-failed gate).
    assert!(validate_module(&module).is_empty());
}

/// WS1.8 rule (a) companion: a Pending row may carry an evidence-awaiting-
/// replay certificate an earlier pass attached. When THIS pass refutes the
/// row, the stale certificate is dropped with the flip, so the module the
/// validator sees is not a Failed row beside a discharging certificate
/// (`GroundCertificateStatusInconsistent`). An `InheritedFromCallee`
/// certificate is a composition edge, not a discharge claim, and is kept.
#[test]
fn refuting_a_row_drops_its_stale_discharging_certificate() {
    use trust_ir::proof::{ProofCertificate, ProofEvidence};
    let (mut module, _) = build_bump_module(2);
    let func = module.functions[0].id;
    let ids = mint_unstated(&mut module, func);
    let oid = ids[0];
    // An earlier pass left a replayable-later SMT payload on the Pending row
    // (legal: Pending + certificate is the honest awaiting-replay carrier).
    module.proof_certificates.push(ProofCertificate {
        obligation: oid,
        prover: "ay".to_string(),
        evidence: ProofEvidence::SmtProof(b"(stale proof)".to_vec()),
        assurance: None,
    });
    assert!(
        validate_module(&module).is_empty(),
        "Pending + certificate validates"
    );

    let vc = verify_function(&module, func).unwrap();
    let transitions = apply_vc_outcomes(&mut module, &vc).unwrap();
    assert_eq!(transitions, vec![(oid, ProofStatus::Failed)]);
    assert!(
        module
            .proof_certificates
            .iter()
            .all(|c| c.obligation != oid),
        "the refuted row's stale discharging certificate is dropped: {:?}",
        module.proof_certificates
    );
    // The flipped module is valid: no Failed row carries a discharging
    // certificate.
    let errors = validate_module(&module);
    assert!(errors.is_empty(), "{errors:?}");
}

// ============================================================================
// GREEN TWIN: satisfied ensures -> ay proves, authority remains pending
// ============================================================================

/// Same shape, body returns `x + 1`: the ensures assert proves for all x, but
/// the obligation remains `Pending` because ay cannot export a replayable
/// UNSAT proof. A solver verdict alone must not mint authority.
#[test]
fn satisfied_ensures_remains_pending_without_replayable_certificate() {
    let (mut module, _) = build_bump_module(1);
    let func = module.functions[0].id;

    let ids = mint_unstated(&mut module, func);
    assert_eq!(ids.len(), 1);
    let oid = ids[0];
    assert_eq!(module.proof_obligations[0].id, oid);

    let vc = verify_function(&module, func).unwrap();
    assert_eq!(vc.conditions.len(), 1);
    assert_eq!(vc.conditions[0].verdict, VcVerdict::Proved);
    assert!(vc.all_proved());

    let transitions = apply_vc_outcomes(&mut module, &vc).unwrap();
    assert!(transitions.is_empty());
    assert_eq!(module.proof_obligations[0].status, ProofStatus::Pending);
    assert!(
        module.obligation_diagnostics.is_empty(),
        "a proved obligation awaiting replay attaches no failure diagnostic"
    );
    assert!(validate_module(&module).is_empty());
}

// ============================================================================
// Fail-closed edges of the application step
// ============================================================================

/// A recorded `Failed` verdict is never laundered back: re-running the VC on
/// a fixed (proving) body must NOT flip a non-`Pending` obligation.
#[test]
fn recorded_failed_verdict_is_not_overwritten() {
    let (mut module, _) = build_bump_module(1);
    let func = module.functions[0].id;
    let ids = mint_unstated(&mut module, func);
    module.proof_obligations[0].status = ProofStatus::Failed;

    let vc = verify_function(&module, func).unwrap();
    assert!(vc.all_proved());
    let transitions = apply_vc_outcomes(&mut module, &vc).unwrap();
    assert!(
        transitions.is_empty(),
        "only Pending obligations may transition, got: {transitions:?}"
    );
    assert_eq!(module.proof_obligations[0].status, ProofStatus::Failed);
    let _ = ids;
}

/// A `requires` clause mints a Precondition obligation, but a body VC can
/// neither discharge nor refute it (callers establish preconditions — the B5
/// call-site flow): it stays `Pending` even when the body proves.
#[test]
fn precondition_obligation_stays_pending_under_body_vc() {
    let (mut module, _) = build_bump_module(1);
    module.functions[0].summary = Some(
        module.functions[0]
            .summary
            .take()
            .unwrap()
            .requiring(ProofFormula::smtlib2("(>= x 0)", "Bool")),
    );
    let func = module.functions[0].id;
    let ids = mint_unstated(&mut module, func);
    assert_eq!(ids.len(), 2, "requires + ensures");

    let vc = verify_function(&module, func).unwrap();
    assert!(vc.all_proved());
    let transitions = apply_vc_outcomes(&mut module, &vc).unwrap();

    let pre = module
        .proof_obligations
        .iter()
        .find(|o| o.kind == ObligationKind::Precondition)
        .unwrap();
    let post = module
        .proof_obligations
        .iter()
        .find(|o| o.kind == ObligationKind::Postcondition)
        .unwrap();
    assert_eq!(
        pre.status,
        ProofStatus::Pending,
        "a body VC must not claim a caller-side precondition"
    );
    assert_eq!(
        post.status,
        ProofStatus::Pending,
        "a solver verdict without replayable evidence cannot mint discharge authority"
    );
    assert!(transitions.is_empty());
}

/// A VC is a result for one exact module snapshot. Reusing a refutation from a
/// different body with the same function/obligation ids must not fail the
/// target obligation or attach a foreign counterexample.
#[test]
fn vc_apply_rejects_cross_module_identity_mismatch() {
    let (mut refuted_module, _) = build_bump_module(2);
    let refuted_func = refuted_module.functions[0].id;
    mint_unstated(&mut refuted_module, refuted_func);
    let vc = verify_function(&refuted_module, refuted_func).unwrap();

    let (mut proved_module, _) = build_bump_module(1);
    let proved_func = proved_module.functions[0].id;
    mint_unstated(&mut proved_module, proved_func);
    let target_digest = proved_module.stable_digest();

    let error = apply_vc_outcomes(&mut proved_module, &vc)
        .expect_err("a VC from a different module body must be rejected");
    assert_eq!(
        error,
        VcApplyError::ModuleDigestMismatch {
            expected: vc.source_module_digest(),
            actual: target_digest,
        }
    );
    assert_eq!(
        proved_module.proof_obligations[0].status,
        ProofStatus::Pending
    );
    assert!(proved_module.obligation_diagnostics.is_empty());
}

/// Public VC fields are a reporting projection. Mutating that projection must
/// not redirect or suppress the sealed outcome that `apply_vc_outcomes` uses.
#[test]
fn vc_apply_uses_sealed_outcomes_not_mutable_report_projection() {
    let (mut module, _) = build_bump_module(2);
    let func = module.functions[0].id;
    let ids = mint_unstated(&mut module, func);
    let oid = ids[0];
    let mut vc = verify_function(&module, func).unwrap();

    vc.conditions.clear();
    vc.obligations[0].1 = VcObligationOutcome::ProvedByVc;

    let transitions = apply_vc_outcomes(&mut module, &vc).unwrap();
    assert_eq!(transitions, vec![(oid, ProofStatus::Failed)]);
    assert_eq!(module.proof_obligations[0].status, ProofStatus::Failed);
    assert_eq!(module.obligation_diagnostics.len(), 1);
}
