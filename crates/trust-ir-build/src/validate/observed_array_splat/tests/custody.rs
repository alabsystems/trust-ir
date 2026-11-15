// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn prior_element_error_and_complete_zero_spelling_stay_owned_before_transfer() {
    let mut m = fixture(Ty::U64);
    m.types[0] = Ty::Tuple(vec![
        Ty::handle("é".repeat(600), "中".repeat(600)),
        Ty::Bool,
    ]);
    let inst = array(0);
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
        held |= state.errors.len() == 1
            && !state.ty.is_empty()
            && !state.location.is_empty()
            && !state.spelling.is_empty();
        drain(&mut state, &mut work);
        empty(&state);
        let _ = values.retire_observed(work.session, work.site);
    }
    assert!(held);
}
#[test]
fn final_empty_or_nonempty_publication_refuses_without_partial_result() {
    let m = fixture(Ty::Bool);
    for inst in [array(1), array(0)] {
        let (_, _, _, end) = run(&m, &inst);
        let mut o = Observer {
            stop: Some(end),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let values = setup(&m, &mut s);
        assert_eq!(
            validate_array_splat_observed(&m, &inst, &values, BlockId::new(1), &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let _ = values.retire_observed(&mut s, site());
    }
}
#[test]
fn successful_error_caller_retirement_keeps_terminal_receipt_and_original_stop() {
    let m = fixture(Ty::Bool);
    let inst = array(0);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let values = setup(&m, &mut s);
    let out =
        validate_array_splat_observed(&m, &inst, &values, BlockId::new(1), &mut s, site()).unwrap();
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
    let out =
        validate_array_splat_observed(&m, &inst, &values, BlockId::new(1), &mut s, site()).unwrap();
    assert_eq!(
        retire_validation_errors_observed(out, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original array-splat stop"
    );
    let _ = values.retire_observed(&mut s, site());
}
