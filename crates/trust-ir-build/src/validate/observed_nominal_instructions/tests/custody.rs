// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_same_private_entry_cut_drains_partial_operand_and_full_diagnostic_state() {
    let (m, f) = fixture();
    let node = InstrNode::new(Inst::Load {
        ty: handle(),
        ptr: v(4),
        volatile: false,
        align: None,
    });
    let location = "λ raw\0".repeat(1000);
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let (table, nominal, values, guards, slots) = setup(&m, &f, false, false, &mut s);
    let begin = calls.get();
    let mut state = State::default();
    state
        .run(
            &m,
            &node,
            &values,
            &nominal,
            f.entry,
            3,
            None,
            None,
            &location,
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
    assert!(empty(&state));
    dispose(table, nominal, values, guards, slots, &mut s);
    drop(s);
    let (mut saw_operand, mut saw_string, mut saw_error) = (false, false, false);
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (table, nominal, values, guards, slots) = setup(&m, &f, false, false, &mut s);
        let mut state = State::default();
        assert_eq!(
            state.run(
                &m,
                &node,
                &values,
                &nominal,
                f.entry,
                3,
                None,
                None,
                &location,
                &mut Work {
                    session: &mut s,
                    site: site()
                }
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        saw_operand |= state.operands.capacity() != 0;
        saw_string |= state.location.capacity() != 0 || state.detail.capacity() != 0;
        saw_error |= !state.errors.is_empty();
        drain(
            &mut state,
            &mut Work {
                session: &mut s,
                site: site(),
            },
        );
        assert!(empty(&state));
        dispose(table, nominal, values, guards, slots, &mut s);
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
    // Private run has no callback after the error push; public publication covers
    // the complete error owner separately, so no guessed post-push cut is needed.
    assert!(saw_operand && saw_string);
    assert!(!saw_error);
}
#[test]
fn complete_returned_child_reason_is_held_before_parent_decision_and_location_fees() {
    let (m, f) = fixture();
    let node = InstrNode::new(Inst::Load {
        ty: handle(),
        ptr: v(4),
        volatile: false,
        align: None,
    });
    let (expected, _, _, _) = run(&m, &f, &node, (f.entry, 3), false, false, "L");
    let expected = match &expected[0] {
        ValidationError::InvalidHandleUse { detail, .. } => detail,
        _ => panic!("handle reason"),
    };
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let (table, nominal, values, guards, slots) = setup(&m, &f, false, false, &mut s);
    let begin = calls.get();
    let mut state = State::default();
    state
        .run(
            &m,
            &node,
            &values,
            &nominal,
            f.entry,
            3,
            None,
            None,
            "L",
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
    dispose(table, nominal, values, guards, slots, &mut s);
    drop(s);
    let mut saw_full = false;
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (table, nominal, values, guards, slots) = setup(&m, &f, false, false, &mut s);
        let mut state = State::default();
        assert_eq!(
            state.run(
                &m,
                &node,
                &values,
                &nominal,
                f.entry,
                3,
                None,
                None,
                "L",
                &mut Work {
                    session: &mut s,
                    site: site()
                }
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        if !state.detail.is_empty() {
            assert_eq!(&state.detail, expected);
            saw_full = true;
        }
        drain(
            &mut state,
            &mut Work {
                session: &mut s,
                site: site(),
            },
        );
        assert!(empty(&state));
        dispose(table, nominal, values, guards, slots, &mut s);
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
    }
    assert!(saw_full);
}
#[test]
fn prior_errors_and_all_partials_are_consumed_on_sticky_stop_without_shorter_output() {
    let mut state = State {
        operands: vec![v(1); 40],
        location: "partial λ".repeat(300),
        detail: "complete child".repeat(1000),
        errors: vec![
            ValidationError::InvalidHandleUse {
                location: "prior λ".repeat(200),
                detail: "prior full".repeat(500),
            },
            ValidationError::InvalidDialectType {
                location: "second".into(),
                detail: "second full".repeat(500),
            },
        ],
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
        "original nominal instruction stop"
    );
    drop(s);
    assert!(
        o.events[1..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn full_error_output_publication_and_healthy_consuming_retirement_keep_actual_terminal_contract() {
    let (m, f) = fixture();
    let node = InstrNode::new(Inst::Undef { ty: mixed() });
    let (_, baseline, _, end) = run(&m, &f, &node, (f.entry, 3), false, false, "L");
    let mut o = Observer {
        stop: Some(end),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (table, nominal, values, guards, slots) = setup(&m, &f, false, false, &mut s);
    assert_eq!(
        validate_nominal_instruction_types_observed(
            &m,
            &node,
            &values,
            &nominal,
            f.entry,
            3,
            None,
            None,
            "L",
            &mut s,
            site()
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    dispose(table, nominal, values, guards, slots, &mut s);
    drop(s);
    assert_eq!(&o.events[..end], &baseline.events[..end]);
    assert!(
        o.events[end..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (table, nominal, values, guards, slots) = setup(&m, &f, false, false, &mut s);
    let out = validate_nominal_instruction_types_observed(
        &m,
        &node,
        &values,
        &nominal,
        f.entry,
        3,
        None,
        None,
        "L",
        &mut s,
        site(),
    )
    .unwrap();
    assert!(matches!(
        &out[..],
        [ValidationError::InvalidHandleUse { .. }]
    ));
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    let retired = calls.get();
    dispose(table, nominal, values, guards, slots, &mut s);
    drop(s);
    assert_eq!(
        o.events[retired - 1],
        ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 0,
            copy_bytes: 0
        }
    );
}
