//! Complete ordinary config-leaf oracles; all new Rust controls UNRUN.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::{InstructionSite, InterpretOptions};
use trust_ir::proof::{
    CertificateBinding, ClauseBinding, ClausePlace, ClauseSort, CleanCicKernelRecheck,
    IslandEnvironment, ObligationKind, ProofDigest, ProofFormula, ProofStatus, SpecObligationRef,
    clean_cic_lineage_digest, clean_cic_lineage_digest_v8,
};
use trust_ir::value::{FuncTyId, ProofId};
use trust_ir::{BlockId, Function};
mod custody;
mod parity;
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    calls: Rc<Cell<usize>>,
    stop: Option<usize>,
    cleanup: Rc<Cell<bool>>,
    work: usize,
    copy: usize,
    work_cap: Option<usize>,
    copy_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, p: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(p);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("unbound stop");
        }
        if self.cleanup.get() && p.phase == ExecutionPhase::ScratchRetirement {
            return Err("unbound cleanup");
        }
        let w = self.work.checked_add(p.work).ok_or("overflow")?;
        let c = self.copy.checked_add(p.copy_bytes).ok_or("overflow")?;
        if self.work_cap.is_some_and(|n| w > n) {
            return Err("work");
        }
        if self.copy_cap.is_some_and(|n| c > n) {
            return Err("copy");
        }
        self.work = w;
        self.copy = c;
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Instruction(InstructionSite {
        function: FuncId::new(8107),
        block: BlockId::new(19),
        instruction_index: 27,
    })
}
fn row(id: u32) -> ProofObligation {
    ProofObligation::new(
        ProofId::new(id),
        ObligationKind::TranslationValidation,
        ProofStatus::Certified,
        "claim λ🙂",
    )
}
fn binding(environment: bool) -> Box<CertificateBinding> {
    let mut b = CertificateBinding::new(ProofDigest::sha256([3; 32]), ProofDigest::sha256([4; 32]));
    if environment {
        b.environment = Some(IslandEnvironment {
            declarations: vec![],
            digest: ProofDigest::sha256([5; 32]),
        });
    }
    Box::new(b)
}
fn directive(b: Option<Box<CertificateBinding>>) -> CleanCicKernelRecheck {
    CleanCicKernelRecheck {
        module: "malformed but not checked by this diagnostic".into(),
        theorems: vec![],
        anchor: KERNEL_ANCHOR_CLEAN_BACKEND_TV.into(),
        allowed_axioms: vec![],
        binding: b,
    }
}
fn cert(row: &ProofObligation, recheck: Option<CleanCicKernelRecheck>) -> ProofCertificate {
    ProofCertificate {
        obligation: row.id,
        prover: "untrusted malformed prover".into(),
        evidence: ProofEvidence::CleanCic {
            term: vec![0xff],
            context: vec![0xff],
            lineage: clean_cic_lineage_digest(row),
            kernel_recheck: recheck,
        },
        assurance: None,
    }
}
fn fixture() -> Module {
    let mut m = Module::new("unbound-data");
    let r = row(7);
    m.proof_certificates.push(cert(&r, Some(directive(None))));
    m.proof_obligations.push(r);
    m
}
fn v8(m: &Module, r: &ProofObligation, recheck: Option<CleanCicKernelRecheck>) -> ProofCertificate {
    let catalog = ModuleFunctionCatalog::new(m);
    let d = clean_cic_lineage_digest_v8(
        r,
        &|id| catalog.unique(id).map(|f| f.name.clone()),
        recheck.as_ref().and_then(|r| r.binding.as_deref()),
    )
    .unwrap();
    let mut c = cert(r, recheck);
    if let ProofEvidence::CleanCic { lineage, .. } = &mut c.evidence {
        *lineage = d;
    }
    c
}
fn oracle(m: &Module, mode: Mode) -> Vec<ValidationError> {
    match mode {
        Mode::Unbound => super::super::super::unbound_certificate_errors(m),
        Mode::Source => super::super::super::source_unbound_certificate_errors(m),
    }
}
fn call<O: ExecutionObserver>(
    m: &Module,
    c: &ModuleFunctionCatalog<'_>,
    mode: Mode,
    s: &mut ObservedSession<'_, O>,
) -> R<Vec<ValidationError>> {
    match mode {
        Mode::Unbound => unbound_certificate_errors_observed(m, c, s, site()),
        Mode::Source => source_unbound_certificate_errors_observed(m, c, s, site()),
    }
}
fn run(m: &Module, mode: Mode) -> (Observer, usize) {
    let c = ModuleFunctionCatalog::new(m);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = call(m, &c, mode, &mut s).unwrap();
    assert_eq!(out, oracle(m, mode));
    let end = calls.get();
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    drop(s);
    assert!(o.events.iter().all(|p| p.site == site()));
    (o, end)
}
