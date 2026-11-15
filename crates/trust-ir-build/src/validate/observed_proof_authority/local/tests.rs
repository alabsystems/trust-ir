// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! UNRUN local data contracts. Private kernel fixtures are not replay evidence.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::proof::{
    ClauseBinding, ClausePlace, ClauseSort, CoverageAssurance, ProofDigest, ProofFormula,
};
use trust_ir::value::FuncTyId;
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
            return Err("local stop");
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
    ExecutionSite::Entry(FuncId::new(608))
}
fn row(id: u32, status: ProofStatus) -> ProofObligation {
    let mut r = ProofObligation::new(
        ProofId::new(id),
        ObligationKind::Postcondition,
        status,
        "local data",
    );
    r.function = Some(FuncId::new(7));
    let mut f = ProofFormula::new("raw", "formula");
    f.smtlib = Some("opaque".into());
    f.sort = Some("sort".into());
    f.bindings = vec![(
        "x".into(),
        ClauseBinding {
            sort: ClauseSort::Array(
                Box::new(ClauseSort::Bool),
                Box::new(ClauseSort::Datatype {
                    name: "D".into(),
                    constructors: vec![("C".into(), vec![("f".into(), ClauseSort::BitVec(0))])],
                }),
            ),
            place: ClausePlace::WorldPre,
        },
    )];
    r.formula = Some(f);
    r
}
fn fixture() -> Module {
    let mut m = Module::new("local inheritance");
    m.functions = vec![Function::new(
        FuncId::new(7),
        "callee",
        FuncTyId::new(0),
        BlockId::new(0),
    )];
    m.proof_obligations = vec![
        row(1, ProofStatus::Certified),
        row(2, ProofStatus::Discharged),
    ];
    m.proof_certificates = vec![
        ProofCertificate {
            obligation: ProofId::new(1),
            prover: "kernel-data-onlyé🦀".into(),
            evidence: ProofEvidence::CleanCic {
                term: vec![1, 2, 3],
                context: vec![],
                lineage: ProofDigest::sha256([9; 32]),
                kernel_recheck: None,
            },
            assurance: None,
        },
        ProofCertificate {
            obligation: ProofId::new(2),
            prover: "inheritance".into(),
            evidence: ProofEvidence::InheritedFromCallee {
                callee: FuncId::new(7),
                obligation: ProofId::new(1),
                external: None,
            },
            assurance: None,
        },
    ];
    m
}
// cfg(test) input construction only. Production has no currency constructor.
fn input(m: &Module) -> Authority<'_> {
    Authority {
        module: m,
        kernel: vec![m.proof_certificates[0].lineage_ref()],
        discharged: vec![],
    }
}
fn normalized(v: &LocalInheritance) -> (u8, Option<&str>) {
    match v {
        LocalInheritance::NotRouted => (0, None),
        LocalInheritance::Admitted => (1, None),
        LocalInheritance::RefusedNamedElsewhere => (2, None),
        LocalInheritance::Refused(s) => (3, Some(s)),
    }
}
fn oracle(a: &Authority<'_>, at: usize) -> LocalInheritance {
    let refs = a.kernel.iter().cloned().collect();
    let ground = kernel_ground_obligations(a.module, &refs);
    admit_local_inheritance(
        a.module,
        &ObligationRows::new(a.module),
        &a.module.proof_certificates[at],
        &ground,
    )
}
fn call<O: ExecutionObserver>(
    a: &Authority<'_>,
    at: usize,
    s: &mut ObservedSession<'_, O>,
) -> R<LocalInheritance> {
    a.local_inheritance(a.module, &a.module.proof_certificates[at], s, site())
}
fn run(a: &Authority<'_>, at: usize) -> (Observer, usize) {
    let expected = oracle(a, at);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = call(a, at, &mut s).unwrap();
    let end = calls.get();
    assert_eq!(normalized(&out), normalized(&expected));
    out.retire_observed(&mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    (o, end)
}
fn assurance(bound: CoverageBound) -> Option<CoverageAssurance> {
    Some(CoverageAssurance {
        bound,
        request_digest: ProofDigest::sha256([4; 32]),
    })
}
fn coverage_fixture() -> Module {
    let mut m = fixture();
    m.proof_certificates[0].assurance = assurance(CoverageBound::UnwindBounded {
        depth: u64::MAX - 1,
    });
    m.proof_certificates[1].assurance = assurance(CoverageBound::Unbounded);
    let mut extra = m.proof_certificates[0].clone();
    extra.prover = "decorative".into();
    extra.evidence = ProofEvidence::Trusted("no replay".into());
    extra.assurance = assurance(CoverageBound::ModelBounded { size: 0 });
    m.proof_certificates.push(extra);
    m
}
