// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn same_private_entry_cuts_keep_owned_render_and_partial_lists_until_full_retirement() {
    let (m, f) = mismatch();
    let mut base = Observer::default();
    let calls = base.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut state = State::default();
    state
        .run(
            &m,
            &f,
            &mut Work {
                session: &mut s,
                site: site(),
            },
        )
        .unwrap();
    let end = calls.get();
    drain(
        &mut state,
        &mut Work {
            session: &mut s,
            site: site(),
        },
    );
    drop(s);
    let (mut render, mut lists) = (false, false);
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut state = State::default();
        assert_eq!(
            state.run(
                &m,
                &f,
                &mut Work {
                    session: &mut s,
                    site: site()
                }
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        render |= state.render.capacity() != 0;
        lists |= state.expected.capacity() != 0 || state.actual.capacity() != 0;
        drain(
            &mut state,
            &mut Work {
                session: &mut s,
                site: site(),
            },
        );
        assert!(empty(&state));
        drop(s);
        assert_eq!(&o.events[..cut], &base.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
    assert!(render && lists);
}
#[test]
fn complete_returned_display_string_is_held_before_parent_list_copy() {
    let (m, f) = mismatch();
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut state = State::default();
    state
        .run(
            &m,
            &f,
            &mut Work {
                session: &mut s,
                site: site(),
            },
        )
        .unwrap();
    let end = calls.get();
    drain(
        &mut state,
        &mut Work {
            session: &mut s,
            site: site(),
        },
    );
    drop(s);
    let mut saw = false;
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut state = State::default();
        assert_eq!(
            state.run(
                &m,
                &f,
                &mut Work {
                    session: &mut s,
                    site: site()
                }
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        if state.render.contains("rt::Name") {
            assert_eq!(state.render, f.blocks[0].params[1].1.to_string());
            saw = true;
        }
        drain(
            &mut state,
            &mut Work {
                session: &mut s,
                site: site(),
            },
        );
        assert!(empty(&state));
    }
    assert!(saw);
}
#[test]
fn prior_errors_and_partial_fields_are_all_consumed_under_sticky_original_refusal() {
    let mut state = State {
        render: "full render".repeat(1000),
        name: "raw λ".repeat(1000),
        expected: "(expected)".repeat(1000),
        actual: "(actual)".repeat(1000),
        errors: vec![ValidationError::EntryParamsMismatch {
            func_name: "prior".into(),
            expected: "prior expected".repeat(200),
            actual: "prior actual".repeat(200),
        }],
    };
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
    drain(
        &mut state,
        &mut Work {
            session: &mut s,
            site: site(),
        },
    );
    assert!(empty(&state));
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original entry parameter stop"
    );
    drop(s);
    assert!(
        o.events[1..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn final_error_publication_refusal_and_healthy_caller_retirement_use_real_terminal_receipt() {
    let (m, f) = mismatch();
    let (_, baseline, end) = run(&m, &f);
    let mut o = Observer {
        stop: Some(end),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_entry_params_observed(&m, &f, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    drop(s);
    assert_eq!(&o.events[..end], &baseline.events[..end]);
    assert!(
        o.events[end..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
    assert_eq!(
        *baseline.events.last().unwrap(),
        ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 0,
            copy_bytes: 0
        }
    );
}
