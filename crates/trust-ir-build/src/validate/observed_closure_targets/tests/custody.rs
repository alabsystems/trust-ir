// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_same_private_build_cut_keeps_partial_map_until_explicit_original_retirement() {
    let f = fixture();
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut state = State::default();
    state
        .build(
            &f,
            &mut Work {
                session: &mut s,
                site: site(),
            },
        )
        .unwrap();
    let end = calls.get();
    state.retire(&mut Work {
        session: &mut s,
        site: site(),
    });
    drop(s);
    let mut held = false;
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut state = State::default();
        assert_eq!(
            state.build(
                &f,
                &mut Work {
                    session: &mut s,
                    site: site()
                }
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        held |= !state.targets.is_empty();
        state.retire(&mut Work {
            session: &mut s,
            site: site(),
        });
        assert!(state.targets.is_empty());
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
    assert!(held);
}
#[test]
fn every_consuming_map_retirement_callback_refuses_after_all_rows_and_buffer_drop() {
    let f = fixture();
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let a = ObservedLocalClosureTargets::new_observed(&f, &mut s, site()).unwrap();
    let begin = calls.get();
    a.retire_observed(&mut s, site()).unwrap();
    let end = calls.get();
    drop(s);
    assert_eq!(
        baseline.events[end - 1],
        ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 0,
            copy_bytes: 0
        }
    );
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let a = ObservedLocalClosureTargets::new_observed(&f, &mut s, site()).unwrap();
        assert_eq!(
            a.retire_observed(&mut s, site()),
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
}
#[test]
fn final_whole_map_publication_stop_never_returns_a_smaller_success() {
    let f = fixture();
    let (baseline, end) = run(&f);
    let mut o = Observer {
        stop: Some(end),
        cleanup_after: Some(end),
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
    assert_eq!(&o.events[..end], &baseline.events[..end]);
    assert!(
        o.events[end..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn sticky_cleanup_consumes_all_rows_while_borrowed_function_and_first_cause_survive() {
    let f = fixture();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let a = ObservedLocalClosureTargets::new_observed(&f, &mut s, site()).unwrap();
    let end = calls.get();
    a.retire_observed(&mut s, site()).unwrap();
    drop(s);
    let mut o = Observer {
        stop: Some(end + 1),
        cleanup_after: Some(end + 1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let a = ObservedLocalClosureTargets::new_observed(&f, &mut s, site()).unwrap();
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
        a.retire_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original closure target stop"
    );
    assert_eq!(f.blocks[0].body.len(), 3);
}
