// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn full_actual_type_and_all_error_strings_remain_owned_before_vector_transfer() {
    let ty = Ty::Tuple(vec![
        Ty::handle("é".repeat(700), "中".repeat(700)),
        Ty::Bool,
    ]);
    let m = fixture(ty);
    let inst = drop_inst(false, 0);
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
    state.retire(&mut Work {
        session: &mut s,
        site: site(),
    });
    retire_validation_errors_observed(take(&mut state.errors), &mut s, site()).unwrap();
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
        held |= !state.op.is_empty()
            && !state.role.is_empty()
            && !state.expected.is_empty()
            && !state.actual.is_empty();
        state.retire(&mut work);
        let _ = retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
        empty(&state);
        let _ = values.retire_observed(work.session, work.site);
    }
    assert!(held);
}
#[test]
fn final_empty_or_nonempty_result_publication_is_never_replaced_with_local_success() {
    for ty in [Ty::Ptr, Ty::Bool] {
        let m = fixture(ty);
        let inst = drop_inst(false, 0);
        let (_, _, _, end) = run(&m, &inst);
        let mut o = Observer {
            stop: Some(end),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let values = setup(&m, &mut s);
        assert_eq!(
            validate_drop_place_observed(&m, &inst, &values, BlockId::new(1), &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let _ = values.retire_observed(&mut s, site());
    }
}
#[test]
fn caller_successful_error_retirement_has_terminal_receipt_and_stop_keeps_original_cause() {
    let m = fixture(Ty::Bool);
    let inst = drop_inst(false, 0);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let values = setup(&m, &mut s);
    let out =
        validate_drop_place_observed(&m, &inst, &values, BlockId::new(1), &mut s, site()).unwrap();
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
        validate_drop_place_observed(&m, &inst, &values, BlockId::new(1), &mut s, site()).unwrap();
    assert_eq!(
        retire_validation_errors_observed(out, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "original drop-place stop");
    let _ = values.retire_observed(&mut s, site());
}
