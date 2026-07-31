// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Validator coverage for the obligation-diagnostics sidecar: every diagnostic
// must reference an obligation present in the module.

use trust_ir::value::ProofId;
use trust_ir::{Module, ObligationDiagnostic, ObligationKind, ProofObligation, ProofStatus};
use trust_ir_build::{ValidationError, validate_module};

#[test]
fn diagnostic_referencing_present_obligation_ok() {
    let mut m = Module::new("d");
    m.proof_obligations.push(ProofObligation::new(
        ProofId::new(3),
        ObligationKind::Precondition,
        ProofStatus::Failed,
        "p",
    ));
    m.obligation_diagnostics
        .push(ObligationDiagnostic::error(ProofId::new(3), "msg"));
    assert!(
        !validate_module(&m)
            .iter()
            .any(|e| matches!(e, ValidationError::DanglingDiagnosticObligation { .. }))
    );
}

#[test]
fn diagnostic_referencing_absent_obligation_rejected() {
    let mut m = Module::new("d");
    // No obligation #9 in the module.
    m.obligation_diagnostics
        .push(ObligationDiagnostic::error(ProofId::new(9), "dangling"));
    assert!(validate_module(&m).iter().any(|e| matches!(
        e,
        ValidationError::DanglingDiagnosticObligation { obligation: 9 }
    )));
}
