// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_const_copy_map_round_and_whole_publication_callback_refuses() {
    let f = fixture();
    let (baseline, end) = run(&f);
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert!(matches!(
            ObservedLocalClosureTargets::new_observed(&f, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert_eq!(
            s.first_refusal().unwrap().cause,
            "original closure target stop"
        );
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
fn every_actual_query_callback_refuses_without_becoming_semantic_none() {
    let f = fixture();
    for key in [0, 10, 12] {
        let mut baseline = Observer::default();
        let calls = baseline.calls.clone();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
        let a = ObservedLocalClosureTargets::new_observed(&f, &mut s, site()).unwrap();
        let begin = calls.get();
        a.get_observed(v(key), &mut s, site()).unwrap();
        let end = calls.get();
        a.retire_observed(&mut s, site()).unwrap();
        drop(s);
        for cut in begin + 1..=end {
            let mut o = Observer {
                stop: Some(cut),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            let a = ObservedLocalClosureTargets::new_observed(&f, &mut s, site()).unwrap();
            assert_eq!(
                a.get_observed(v(key), &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            let _ = a.retire_observed(&mut s, site());
            drop(s);
            assert_eq!(&o.events[..cut], &baseline.events[..cut]);
            assert!(
                o.events[cut..]
                    .iter()
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn cumulative_work_and_copy_apply_to_repeated_construction_without_round_or_call_regrant() {
    let f = fixture();
    let (baseline, end) = run(&f);
    for copy in [false, true] {
        let cap = baseline.events[..end]
            .iter()
            .map(|e| if copy { e.copy_bytes } else { e.work })
            .sum();
        let mut o = Observer::default();
        if copy {
            o.byte_cap = Some(cap)
        } else {
            o.work_cap = Some(cap)
        }
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let first = ObservedLocalClosureTargets::new_observed(&f, &mut s, site()).unwrap();
        assert!(matches!(
            ObservedLocalClosureTargets::new_observed(&f, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        let _ = first.retire_observed(&mut s, site());
    }
}
#[test]
fn zero_fuel_and_preexisting_first_cause_stay_at_original_request_site() {
    let f = fixture();
    let mut o = Observer::default();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut s = ObservedSession::new(options, &mut o);
    let a = ObservedLocalClosureTargets::new_observed(&f, &mut s, site()).unwrap();
    a.retire_observed(&mut s, site()).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    let mut o = Observer {
        stop: Some(1),
        cleanup_after: Some(1),
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
    assert!(matches!(
        ObservedLocalClosureTargets::new_observed(&f, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    ));
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original closure target stop"
    );
}
