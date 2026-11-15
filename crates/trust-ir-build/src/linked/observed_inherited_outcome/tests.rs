// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! UNRUN exact sealed-record getter contracts, not linked authentication evidence.
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::proof::{ProofDigest, ProofDigestAlgorithm, ProofEvidence};
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
            return Err("sealed stop");
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
    ExecutionSite::Entry(FuncId::new(912))
}
fn key(n: u32) -> ProofCertificateRef {
    ProofCertificateRef {
        obligation: ProofId::new(n),
        prover: format!("prover{n}é🦀\0"),
        evidence_digest: ProofDigest::sha256([n as u8; 32]),
    }
}
fn fixture() -> AuthenticatedImports {
    let mut a = AuthenticatedImports::default();
    for n in 0..24 {
        a.inherited.insert(
            key(n),
            match n % 3 {
                0 => SiteOutcome::Authenticated,
                1 => SiteOutcome::Reported,
                _ => SiteOutcome::Refused("complete detailé🦀".repeat(80)),
            },
        );
        if n % 2 == 0 {
            a.admitted.insert(key(n));
        }
    }
    a
}
#[derive(Clone, Copy)]
enum Group {
    Outcome,
    Admission,
}
fn call<O: ExecutionObserver>(
    a: &AuthenticatedImports,
    key: &ProofCertificateRef,
    g: Group,
    s: &mut ObservedSession<'_, O>,
) -> R<bool> {
    match g {
        Group::Outcome => a.inherited_outcome_observed(key, s, site()).map(|out| {
            let expected = a.inherited_outcome(key);
            assert_eq!(out, expected);
            if let (Some(a), Some(b)) = (out, expected) {
                assert!(core::ptr::eq(a, b));
            }
            out.is_some()
        }),
        Group::Admission => a
            .inherited_admission_observed(key, s, site())
            .inspect(|&out| {
                assert_eq!(out, a.admitted.contains(key));
            }),
    }
}
fn run(a: &AuthenticatedImports, key: &ProofCertificateRef, g: Group) -> Observer {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    call(a, key, g, &mut s).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    o
}
#[test]
fn every_actual_full_key_outcome_and_missing_row_matches_original_borrowed_map_oracle() {
    let a = fixture();
    for n in 0..=24 {
        run(&a, &key(n), Group::Outcome);
        run(&a, &key(n), Group::Admission);
    }
}
#[test]
fn each_raw_key_field_and_digest_algorithm_matters_without_normalization() {
    let a = fixture();
    let base = key(2);
    let mut keys = vec![base.clone()];
    let mut k = base.clone();
    k.obligation = ProofId::new(99);
    keys.push(k);
    let mut k = base.clone();
    k.prover.push('x');
    keys.push(k);
    let mut k = base.clone();
    k.evidence_digest.algorithm = ProofDigestAlgorithm::TrustIrStableV1;
    keys.push(k);
    let mut k = base.clone();
    k.evidence_digest.bytes[31] ^= 1;
    keys.push(k);
    for key in keys {
        run(&a, &key, Group::Outcome);
        run(&a, &key, Group::Admission);
    }
}
#[test]
fn actual_record_inherited_can_retain_admitted_set_when_later_map_outcome_is_refused() {
    let mut a = AuthenticatedImports::default();
    let cert = ProofCertificate {
        obligation: ProofId::new(7),
        prover: "actual recorder".into(),
        evidence: ProofEvidence::Trusted("data only".into()),
        assurance: None,
    };
    a.record_inherited(&cert, SiteOutcome::Authenticated);
    a.record_inherited(&cert, SiteOutcome::Refused("later".into()));
    let key = cert.lineage_ref();
    assert!(a.admitted.contains(&key));
    assert!(matches!(a.inherited_outcome(&key),Some(SiteOutcome::Refused(t))if t=="later"));
    run(&a, &key, Group::Outcome);
    run(&a, &key, Group::Admission);
}
#[test]
fn other_record_tables_and_empty_default_never_supply_an_inheritance_outcome() {
    let mut a = AuthenticatedImports::default();
    a.backed_by.insert(7, SiteOutcome::Authenticated);
    a.handle_declarations.insert(7, SiteOutcome::Authenticated);
    a.admitted.insert(key(7));
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        a.inherited_outcome_observed(&key(7), &mut s, site())
            .unwrap(),
        None
    );
    assert!(
        a.inherited_admission_observed(&key(7), &mut s, site())
            .unwrap()
    );
    let empty = AuthenticatedImports::default();
    assert_eq!(
        empty
            .inherited_outcome_observed(&key(7), &mut s, site())
            .unwrap(),
        None
    );
    assert!(
        !empty
            .inherited_admission_observed(&key(7), &mut s, site())
            .unwrap()
    );
}
#[test]
fn every_actual_cursor_key_chunk_and_output_callback_refuses_without_publication_or_mutation() {
    let a = fixture();
    for g in [Group::Outcome, Group::Admission] {
        for key in [key(23), key(24)] {
            let base = run(&a, &key, g);
            let before = a.clone();
            for cut in 1..=base.events.len() {
                let mut o = Observer {
                    stop: Some(cut),
                    ..Observer::default()
                };
                let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
                assert_eq!(
                    call(&a, &key, g, &mut s),
                    Err(ObservedValueError::AdmissionRefused)
                );
                assert_eq!(s.first_refusal().unwrap().cause, "sealed stop");
                drop(s);
                assert_eq!(&o.events[..cut], &base.events[..cut]);
                assert_eq!(o.events.len(), cut);
                assert_eq!(a.inherited, before.inherited);
                assert_eq!(a.admitted, before.admitted);
            }
        }
    }
}
#[test]
fn cumulative_original_work_and_copy_caps_are_not_refreshed_between_actual_record_reads() {
    let a = fixture();
    for g in [Group::Outcome, Group::Admission] {
        let key = key(23);
        let base = run(&a, &key, g);
        for copy in [false, true] {
            let cap = base
                .events
                .iter()
                .map(|e| if copy { e.copy_bytes } else { e.work })
                .sum();
            let mut o = Observer {
                work_cap: (!copy).then_some(cap),
                byte_cap: copy.then_some(cap),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            call(&a, &key, g, &mut s).unwrap();
            assert_eq!(
                call(&a, &key, g, &mut s),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(
                s.first_refusal().unwrap().cause,
                if copy { "copy" } else { "work" }
            );
        }
    }
}
#[test]
fn prior_debit_zero_fuel_and_sticky_first_cause_preserve_original_owner_and_no_default() {
    let a = fixture();
    let key = key(23);
    for g in [Group::Outcome, Group::Admission] {
        let base = run(&a, &key, g);
        let cap = base.events.iter().map(|e| e.work).sum();
        let mut o = Observer {
            work_cap: Some(cap),
            ..Observer::default()
        };
        let mut opts = InterpretOptions::default();
        opts.fuel = 0;
        let mut s = ObservedSession::new(opts, &mut o);
        s.admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site: site(),
            work: 1,
            copy_bytes: 0,
        })
        .unwrap();
        assert_eq!(
            call(&a, &key, g, &mut s),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.remaining_fuel(), 0);
        assert_eq!(s.first_refusal().unwrap().cause, "work");
        assert_eq!(
            call(&a, &key, g, &mut s),
            Err(ObservedValueError::AdmissionRefused)
        );
    }
}
#[test]
fn whole_long_prover_is_compared_in_paid_chunks_and_return_is_exact_original_borrow() {
    let mut a = AuthenticatedImports::default();
    let mut k = key(4);
    k.prover = "é🦀\0".repeat(900);
    a.inherited
        .insert(k.clone(), SiteOutcome::Refused("retained source".into()));
    a.admitted.insert(k.clone());
    run(&a, &k, Group::Outcome);
    run(&a, &k, Group::Admission);
    let mut missing = k.clone();
    missing
        .prover
        .replace_range(missing.prover.len() - 1.., "x");
    run(&a, &missing, Group::Outcome);
    run(&a, &missing, Group::Admission);
}
