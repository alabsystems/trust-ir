// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! UNRUN consumer-contract fixtures, NOT kernel replay or authority minting.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::proof::{ObligationKind, ProofCertificate, ProofContext, ProofDigest, ProofEvidence};
use trust_ir::value::FuncTyId;
use trust_ir::{Block, DropGlueEntry, InstrNode};
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
            return Err("consumer stop");
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
#[derive(Clone, Copy)]
enum Group {
    Contexts,
    References,
    Discharged,
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(302))
}
fn row(id: u32, kind: ObligationKind, status: ProofStatus, owner: Option<u32>) -> ProofObligation {
    let mut r = ProofObligation::new(ProofId::new(id), kind, status, "row");
    r.function = owner.map(FuncId::new);
    r
}
fn fixture() -> Module {
    let mut m = Module::new("consumers");
    m.proof_obligations = vec![
        row(
            0,
            ObligationKind::Postcondition,
            ProofStatus::Certified,
            Some(7),
        ),
        row(
            1,
            ObligationKind::ArithmeticSafety,
            ProofStatus::Certified,
            Some(3),
        ),
        row(
            2,
            ObligationKind::MemorySafety,
            ProofStatus::Discharged,
            Some(3),
        ),
    ];
    m.proof_obligations[1].site = Some(ObligationSite::new(FuncId::new(3), BlockId::new(8), 0));
    m.proof_certificates = m
        .proof_obligations
        .iter()
        .map(|r| ProofCertificate {
            obligation: r.id,
            prover: "consumer-input-onlyé🦀".repeat(70),
            evidence: ProofEvidence::CleanCic {
                term: vec![1, 2, 3],
                context: vec![],
                lineage: ProofDigest::sha256([9; 32]),
                kernel_recheck: None,
            },
            assurance: None,
        })
        .collect();
    let mut f = Function::new(FuncId::new(3), "caller", FuncTyId::new(0), BlockId::new(8));
    f.proofs = vec![
        ProofAnnotation::ProofRef(ProofId::new(99)),
        ProofAnnotation::Pure,
        ProofAnnotation::ProofRef(ProofId::new(0)),
    ];
    let mut b = Block::new(f.entry);
    let mut n = InstrNode::new(Inst::Call {
        callee: FuncId::new(7),
        args: vec![],
    });
    n.proofs = vec![
        ProofAnnotation::NoOverflow,
        ProofAnnotation::ProofRef(ProofId::new(1)),
    ];
    n.proof_context = Some(ProofContext {
        assumes: vec![ProofId::new(0), ProofId::new(99)],
        establishes: vec![ProofId::new(0), ProofId::new(88)],
    });
    b.body.push(n);
    f.blocks.push(b);
    m.functions.push(f);
    m
}
// Only cfg(test) can inject arbitrary consumer inputs. Production constructor
// of the private Authority is still the mandatory UNFINISHED replay builder.
fn input<'a>(m: &'a Module) -> Authority<'a> {
    Authority {
        module: m,
        kernel: m.proof_certificates[..2]
            .iter()
            .map(ProofCertificate::lineage_ref)
            .collect(),
        discharged: m
            .proof_certificates
            .iter()
            .map(ProofCertificate::lineage_ref)
            .collect(),
    }
}
fn oracle(a: &Authority<'_>, g: Group) -> Vec<ValidationError> {
    let kernel = a.kernel.iter().cloned().collect();
    let discharged = a.discharged.iter().cloned().collect();
    match g {
        Group::Contexts => super::super::validate_proof_contexts(a.module, &kernel),
        Group::References => super::super::validate_proof_refs_with_authority(a.module, &kernel),
        Group::Discharged => super::super::validate_discharged_authority(a.module, &discharged),
    }
}
fn call<O: ExecutionObserver>(
    a: &Authority<'_>,
    g: Group,
    s: &mut ObservedSession<'_, O>,
) -> R<Vec<ValidationError>> {
    match g {
        Group::Contexts => a.contexts(a.module, s, site()),
        Group::References => a.references(a.module, s, site()),
        Group::Discharged => a.discharged_errors(a.module, s, site()),
    }
}
fn run(a: &Authority<'_>, g: Group) -> (Observer, usize) {
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = call(a, g, &mut s).unwrap();
    let end = calls.get();
    assert_eq!(out, oracle(a, g));
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    (o, end)
}
