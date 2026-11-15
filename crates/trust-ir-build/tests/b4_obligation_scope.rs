// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// B4: ProofObligation function-scope + inheritance scope check.
//
// `ProofObligation::function` records which function an obligation is a
// pre/postcondition OF. `validate_inherited_proofs` now uses it to turn
// `InheritedFromCallee` from "discharged somewhere in the module" into "this
// exact callee discharged this exact obligation": inheriting an obligation
// owned by a DIFFERENT function is rejected.
//
// See docs/roadmap/B4-obligation-scope.md.

use trust_ir::Module;
use trust_ir::proof::{
    ObligationKind, ProofCertificate, ProofEvidence, ProofObligation, ProofStatus,
};
use trust_ir::ty::Ty;
use trust_ir::value::{FuncId, ProofId};
use trust_ir_build::{ModuleBuilder, validate_module};

/// Build a module with two trivial valid functions (fn#0, fn#1).
fn two_fn_module() -> Module {
    let mut mb = ModuleBuilder::new("b4");
    for name in ["caller", "callee"] {
        let ft = mb.add_func_type(vec![], vec![Ty::I32]);
        let mut fb = mb.function(name, ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let z = fb.iconst(Ty::I32, 0);
        fb.ret(vec![z]);
        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// O0 is owned by fn#1 and grounded; the caller inherits it naming the WRONG
/// callee (fn#0) -> InheritedProofCalleeScopeMismatch.
#[test]
fn inheriting_from_wrong_callee_is_rejected() {
    let mut m = two_fn_module();
    // O0: owned by fn#1, discharged by ground (Trusted) evidence.
    m.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Discharged,
            "callee post",
        )
        .with_function(FuncId::new(1)),
    );
    // O1: the caller's obligation, discharged by inheriting O0.
    m.proof_obligations.push(ProofObligation::new(
        ProofId::new(1),
        ObligationKind::Precondition,
        ProofStatus::Discharged,
        "caller pre",
    ));
    m.proof_certificates.push(ProofCertificate {
        obligation: ProofId::new(0),
        prover: "audit".into(),
        evidence: ProofEvidence::Trusted("ground".into()),
        assurance: None,
    });
    m.proof_certificates.push(ProofCertificate {
        obligation: ProofId::new(1),
        prover: "compose".into(),
        evidence: ProofEvidence::InheritedFromCallee {
            callee: FuncId::new(0), // WRONG: O0 is owned by fn#1
            obligation: ProofId::new(0),
            external: None,
        },
        assurance: None,
    });

    let errs = validate_module(&m);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            trust_ir_build::validate::ValidationError::InheritedProofCalleeScopeMismatch { .. }
        )),
        "inheriting an obligation owned by a different function must be rejected; got: {errs:?}"
    );
}

/// Naming the correct owning callee (fn#1) is accepted.
#[test]
fn inheriting_from_correct_callee_is_accepted() {
    let mut m = two_fn_module();
    m.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Discharged,
            "callee post",
        )
        .with_function(FuncId::new(1)),
    );
    m.proof_obligations.push(ProofObligation::new(
        ProofId::new(1),
        ObligationKind::Precondition,
        ProofStatus::Discharged,
        "caller pre",
    ));
    m.proof_certificates.push(ProofCertificate {
        obligation: ProofId::new(0),
        prover: "audit".into(),
        evidence: ProofEvidence::Trusted("ground".into()),
        assurance: None,
    });
    m.proof_certificates.push(ProofCertificate {
        obligation: ProofId::new(1),
        prover: "compose".into(),
        evidence: ProofEvidence::InheritedFromCallee {
            callee: FuncId::new(1), // correct owner
            obligation: ProofId::new(0),
            external: None,
        },
        assurance: None,
    });

    let errs = validate_module(&m);
    assert!(
        !errs.iter().any(|e| matches!(
            e,
            trust_ir_build::validate::ValidationError::InheritedProofCalleeScopeMismatch { .. }
        )),
        "inheriting from the correct owning callee must NOT trip the scope check; got: {errs:?}"
    );
}
