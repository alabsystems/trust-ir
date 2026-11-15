// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_lookup_shape_scan_and_output_callback_remains_refusable() {
    let m = fixture();
    let (_, baseline, bound) = run(&m);
    for cut in 1..=bound {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_module_certificate_integrity_tail_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(s.first_refusal().is_some());
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn empty_and_early_unique_ambiguous_paths_cannot_return_success_on_stop() {
    let mut duplicate = Module::new("");
    duplicate.proof_obligations = vec![
        row(7, ProofStatus::Failed, ObligationKind::BoundsCheck),
        row(7, ProofStatus::Pending, ObligationKind::Precondition),
    ];
    duplicate
        .proof_certificates
        .push(cert(7, ProofEvidence::Trusted("irrelevant".into())));
    for m in [Module::new(""), duplicate] {
        let (_, _, bound) = run(&m);
        for cut in 1..=bound {
            let mut o = Observer {
                stop: Some(cut),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                validate_module_certificate_integrity_tail_observed(&m, &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
        }
    }
}
#[test]
fn actual_unicode_justification_classification_stops_in_its_interior() {
    let mut m = Module::new("");
    m.proof_obligations
        .push(row(7, ProofStatus::Trusted, ObligationKind::Precondition));
    m.proof_certificates.push(cert(
        7,
        ProofEvidence::Trusted("\u{3000}".repeat(400) + "X"),
    ));
    let (_, baseline, _) = run(&m);
    let cut = baseline
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 8 * u32::BITS as usize
                && e.copy_bytes == size_of::<bool>()
        })
        .nth(100)
        .unwrap()
        .0
        + 1;
    let mut o = Observer {
        stop: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_module_certificate_integrity_tail_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    drop(s);
    assert_eq!(&o.events[..cut], &baseline.events[..cut]);
    assert!(
        o.events[cut..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn two_complete_tail_calls_and_explicit_caller_cleanup_share_cumulative_caps() {
    let m = fixture();
    let (_, baseline, _) = run(&m);
    for copy in [false, true] {
        let mut o = Observer::default();
        if copy {
            o.byte_cap = Some(baseline.bytes + 1)
        } else {
            o.work_cap = Some(baseline.work + 1)
        }
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let out = validate_module_certificate_integrity_tail_observed(&m, &mut s, site()).unwrap();
        retire_validation_errors_observed(out, &mut s, site()).unwrap();
        assert_eq!(
            validate_module_certificate_integrity_tail_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(s.first_refusal().is_some());
    }
}
#[test]
fn final_outer_publication_must_admit_the_whole_vector_before_transfer() {
    let m = fixture();
    let (_, baseline, bound) = run(&m);
    assert_eq!(
        baseline.events[bound - 1].phase,
        ExecutionPhase::Publication
    );
    assert_eq!(
        baseline.events[bound - 1].copy_bytes,
        size_of::<Vec<ValidationError>>()
    );
    let mut o = Observer {
        stop: Some(bound),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_module_certificate_integrity_tail_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    drop(s);
    assert!(o.events.len() > bound);
    assert!(
        o.events[bound..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn zero_fuel_original_site_and_preexisting_first_cause_are_preserved() {
    let m = fixture();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut o = Observer::default();
    let mut s = ObservedSession::new(options, &mut o);
    let out = validate_module_certificate_integrity_tail_observed(&m, &mut s, site()).unwrap();
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    let mut o = Observer {
        stop: Some(1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        s.admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site: site(),
            work: 1,
            copy_bytes: 0
        })
        .is_err()
    );
    assert_eq!(
        validate_module_certificate_integrity_tail_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original certificate stop"
    );
    drop(s);
    assert_eq!(o.events.len(), 1);
}
#[test]
fn repeated_cleanup_refusal_preserves_first_stop_and_still_consumes_all_errors() {
    let m = fixture();
    let (_, _, bound) = run(&m);
    let mut o = Observer {
        stop: Some(bound),
        cleanup_after: Some(0),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_module_certificate_integrity_tail_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original certificate stop"
    );
    drop(s);
    assert!(o.events[bound..].len() > 12);
    assert!(
        o.events[bound..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
