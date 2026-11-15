// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn selected_borrowed_rows_and_buffer_remain_held_until_complete_original_drain() {
    let m = long_enum();
    let inst = extract(4, 1, Ty::Ptr);
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let values = setup(&m, &mut s);
    let begin = calls.get();
    let mut state = State::default();
    state
        .run(
            &m,
            &inst,
            &values,
            BlockId::new(1),
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
    values.retire_observed(&mut s, site()).unwrap();
    drop(s);
    let mut held = false;
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let values = setup(&m, &mut s);
        let mut state = State::default();
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            state.run(&m, &inst, &values, BlockId::new(1), &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        if !state.lanes.is_empty() {
            held = true;
            assert_eq!(state.lanes[0].0, "A");
            assert!(core::ptr::eq(
                state.lanes[0].1,
                &m.enums[0].variants[0].fields[0]
            ));
        }
        drain(&mut state, &mut work);
        empty(&state);
        let _ = values.retire_observed(work.session, work.site);
    }
    assert!(held);
}
#[test]
fn tag_type_child_stays_owned_through_mismatch_and_original_retirement() {
    let m = fixture();
    let inst = extract(4, 0, Ty::Ptr);
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let values = setup(&m, &mut s);
    let begin = calls.get();
    let mut state = State::default();
    state
        .run(
            &m,
            &inst,
            &values,
            BlockId::new(1),
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
    values.retire_observed(&mut s, site()).unwrap();
    drop(s);
    let mut held = false;
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let values = setup(&m, &mut s);
        let mut state = State::default();
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            state.run(&m, &inst, &values, BlockId::new(1), &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        held |= state.tag == Some(Ty::U8);
        drain(&mut state, &mut work);
        empty(&state);
        let _ = values.retire_observed(work.session, work.site);
    }
    assert!(held);
}
#[test]
fn prior_result_error_and_complete_expected_actual_names_stay_owned_before_transfer() {
    let m = long_enum();
    let inst = insert(4, 1, Ty::Bool, 8);
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let values = setup(&m, &mut s);
    let begin = calls.get();
    let mut state = State::default();
    state
        .run(
            &m,
            &inst,
            &values,
            BlockId::new(1),
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
    values.retire_observed(&mut s, site()).unwrap();
    drop(s);
    let mut held = false;
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let values = setup(&m, &mut s);
        let mut state = State::default();
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            state.run(&m, &inst, &values, BlockId::new(1), &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        held |= state.errors.len() == 1 && !state.expected.is_empty() && !state.actual.is_empty();
        drain(&mut state, &mut work);
        empty(&state);
        let _ = values.retire_observed(work.session, work.site);
    }
    assert!(held);
}
#[test]
fn final_empty_or_nonempty_publication_refusal_returns_no_partial_result() {
    let m = fixture();
    for inst in [extract(0, 0, Ty::Bool), extract(4, 1, Ty::Ptr)] {
        let (_, _, _, end) = run(&m, &inst);
        let mut o = Observer {
            stop: Some(end),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let values = setup(&m, &mut s);
        assert_eq!(
            validate_field_access_observed(&m, &inst, &values, BlockId::new(1), &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let _ = values.retire_observed(&mut s, site());
    }
}
#[test]
fn successful_caller_retirement_preserves_healthy_terminal_and_original_stop() {
    let m = long_enum();
    let inst = extract(4, 1, Ty::Ptr);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let values = setup(&m, &mut s);
    let out = validate_field_access_observed(&m, &inst, &values, BlockId::new(1), &mut s, site())
        .unwrap();
    let begin = calls.get();
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    drop(s);
    assert_eq!(
        *o.events.last().unwrap(),
        ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 0,
            copy_bytes: 0
        }
    );
    drop(values);
    let mut o = Observer {
        stop: Some(begin + 1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let values = setup(&m, &mut s);
    let out = validate_field_access_observed(&m, &inst, &values, BlockId::new(1), &mut s, site())
        .unwrap();
    assert_eq!(
        retire_validation_errors_observed(out, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original field-access stop"
    );
    let _ = values.retire_observed(&mut s, site());
}
