// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! UNRUN full ordinary inherited-diagnostic contracts, not replay/authentication.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::linked::{AuthenticatedImports, SiteOutcome};
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::proof::{
    CoverageAssurance, CoverageBound, ObligationKind, ProofDigest, ProofFormula,
};
use trust_ir::value::{FuncTyId, ImportId};
mod custody;
mod parity;
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    calls: Rc<Cell<usize>>,
    stop: Option<usize>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("inherit stop");
        }
        self.work = self.work.checked_add(e.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(e.copy_bytes).ok_or("overflow")?;
        if self.work_cap.is_some_and(|n| self.work > n) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|n| self.bytes > n) {
            return Err("copy");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(620))
}
fn row(id: u32, status: ProofStatus) -> ProofObligation {
    let mut r = ProofObligation::new(
        ProofId::new(id),
        ObligationKind::Postcondition,
        status,
        "row",
    );
    r.function = Some(FuncId::new(7));
    r.formula = Some(ProofFormula::new("raw", "claim"));
    r
}
fn fixture() -> Module {
    let mut m = Module::new("inheritance");
    m.functions = vec![Function::new(
        FuncId::new(7),
        "callee",
        FuncTyId::new(0),
        BlockId::new(0),
    )];
    m.imports = vec![trust_ir::ModuleImport::new(
        "dep",
        ProofDigest::sha256([7; 32]),
    )];
    m.proof_obligations = vec![
        row(1, ProofStatus::Certified),
        row(2, ProofStatus::Discharged),
        row(3, ProofStatus::Discharged),
    ];
    m.proof_certificates = vec![
        ProofCertificate {
            obligation: ProofId::new(1),
            prover: "kernel input onlyé🦀".into(),
            evidence: ProofEvidence::CleanCic {
                term: vec![1, 2, 3],
                context: vec![],
                lineage: ProofDigest::sha256([1; 32]),
                kernel_recheck: None,
            },
            assurance: None,
        },
        ProofCertificate {
            obligation: ProofId::new(2),
            prover: "local".into(),
            evidence: ProofEvidence::InheritedFromCallee {
                callee: FuncId::new(7),
                obligation: ProofId::new(1),
                external: None,
            },
            assurance: None,
        },
        ProofCertificate {
            obligation: ProofId::new(3),
            prover: "external".into(),
            evidence: ProofEvidence::InheritedFromCallee {
                callee: FuncId::new(99),
                obligation: ProofId::new(88),
                external: Some(
                    trust_ir::ExternRef::new(ImportId::new(0), "symbolé🦀'\"\\\n\0\u{1248}")
                        .relying_on(ProofId::new(44)),
                ),
            },
            assurance: None,
        },
    ];
    m
}
// cfg(test) currency inputs do NOT establish that the arbitrary Clean term replays.
fn input(m: &Module) -> Authority<'_> {
    Authority {
        module: m,
        kernel: vec![m.proof_certificates[0].lineage_ref()],
        discharged: vec![],
    }
}
fn authenticated(m: &Module, outcome: Option<SiteOutcome>) -> AuthenticatedImports {
    AuthenticatedImports::inherited_fixture_for_observed_tests(
        outcome
            .map(|v| (m.proof_certificates[2].clone(), v))
            .into_iter()
            .collect(),
    )
}
fn oracle(a: &Authority<'_>, policy: ImportPolicy<'_>) -> Vec<ValidationError> {
    let refs = a.kernel.iter().cloned().collect();
    validate_inherited_proofs_with_authority(a.module, &refs, policy)
}
fn call<O: ExecutionObserver>(
    a: &Authority<'_>,
    policy: ImportPolicy<'_>,
    s: &mut ObservedSession<'_, O>,
) -> R<Vec<ValidationError>> {
    a.inherited_errors(a.module, policy, s, site())
}
fn run(a: &Authority<'_>, policy: ImportPolicy<'_>) -> (Observer, usize) {
    let expected = oracle(a, policy);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = call(a, policy, &mut s).unwrap();
    let end = calls.get();
    assert_eq!(out, expected);
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    (o, end)
}
fn refused_local() -> Module {
    let mut m = fixture();
    m.proof_obligations[1].formula = None;
    m.proof_certificates.swap(1, 2);
    m
}
