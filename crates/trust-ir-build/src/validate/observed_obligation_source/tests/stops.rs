// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_empty_absent_duplicate_and_multirefusal_callback_returns_no_partial_identity_result()
 {
    let mut absent = Module::new("");
    absent.proof_obligations.push(row(3, None));
    let mut bad = Module::new("");
    bad.proof_obligations.push(row(3, Some(bad_source())));
    for m in [Module::new(""), absent, fixture(), bad] {
        let (_, base, bound) = run(&m);
        for stop in 1..=bound {
            let mut o = Observer {
                stop: Some(stop),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                validate_module_obligation_source_observed(&m, &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(
                s.first_refusal().unwrap().cause,
                "original obligation-source stop"
            );
            assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
            drop(s);
            assert!(
                o.events[stop..]
                    .iter()
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn original_cumulative_work_and_copy_include_raw_duplicate_and_successful_caller_disposal() {
    let mut m = fixture();
    for p in &mut m.proof_obligations {
        p.source
            .as_mut()
            .unwrap()
            .public
            .as_mut()
            .unwrap()
            .obligation_id = "large invalid?".repeat(300);
    }
    let (_, base, _) = run(&m);
    for copy in [false, true] {
        let mut o = Observer {
            work_cap: (!copy).then_some(base.work),
            byte_cap: copy.then_some(base.bytes),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let out = validate_module_obligation_source_observed(&m, &mut s, site()).unwrap();
        retire_validation_errors_observed(out, &mut s, site()).unwrap();
        assert!(s.first_refusal().is_none());
        assert_eq!(
            validate_module_obligation_source_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = s.first_refusal().unwrap().progress;
        assert_eq!(
            validate_module_obligation_source_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, first);
        assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    }
}
#[test]
fn original_instruction_coordinates_and_zero_fuel_hold_through_ids_ranges_digest_and_cleanup() {
    let mut m = fixture();
    m.proof_obligations[0].source = Some(bad_source());
    let mut o = Observer::default();
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    let out = validate_module_obligation_source_observed(&m, &mut s, site()).unwrap();
    assert_eq!(
        out,
        super::super::super::validate_proof_obligation_integrity(&m)
    );
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
    assert!(s.first_refusal().is_none());
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
}
#[test]
fn outer_final_publication_refuses_empty_or_complete_owned_duplicate_diagnostics() {
    for m in [Module::new(""), fixture()] {
        let (_, base, bound) = run(&m);
        let mut o = Observer {
            stop: Some(bound),
            cleanup_after: Some(bound),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_module_obligation_source_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            "original obligation-source stop"
        );
        assert_eq!(s.first_refusal().unwrap().progress, base.events[bound - 1]);
        drop(s);
        assert!(
            o.events[bound..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn actual_source_unicode_control_scan_refuses_inside_the_original_predicate_before_boolean_publication()
 {
    let text = "λ".repeat(400);
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    assert!(w.source_id(&text).unwrap());
    drop(w);
    drop(s);
    let stop = base
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
        stop: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    assert_eq!(
        w.source_id(&text),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        w.session.first_refusal().unwrap().progress,
        base.events[stop - 1]
    );
    drop(w);
    drop(s);
    assert!(
        !o.events[..stop]
            .iter()
            .any(|e| e.phase == ExecutionPhase::Publication)
    );
}
#[test]
fn actual_raw_public_identity_match_can_refuse_interior_without_becoming_a_missing_key() {
    let mut m = fixture();
    let id = "λ".repeat(3000);
    for p in &mut m.proof_obligations {
        p.source
            .as_mut()
            .unwrap()
            .public
            .as_mut()
            .unwrap()
            .obligation_id = id.clone();
    }
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    assert_eq!(w.first_public(&m, 1, &id).unwrap(), Some(5));
    drop(w);
    drop(s);
    let stop = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation && e.work == 1024 && e.copy_bytes == 0
        })
        .nth(1)
        .unwrap()
        .0
        + 1;
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    assert_eq!(
        w.first_public(&m, 1, &id),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        w.session.first_refusal().unwrap().progress,
        base.events[stop - 1]
    );
    drop(w);
    drop(s);
    assert!(
        !o.events[..stop]
            .iter()
            .any(|e| e.phase == ExecutionPhase::Publication)
    );
}
#[test]
fn initial_copy_and_existing_sticky_refusal_never_enter_source_validation_or_id_copying() {
    let m = fixture();
    let mut o = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_module_obligation_source_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    let first = s.first_refusal().unwrap().progress;
    assert_eq!(
        validate_module_obligation_source_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().progress, first);
    drop(s);
    assert_eq!(o.events.len(), 1);
}
