// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn every_actual_complete_pass_callback_refuses_without_partial_publication() {
    let f = function(vec![node(
        Inst::Select {
            ty: Ty::U32,
            cond: v(3),
            then_val: v(0),
            else_val: v(1),
        },
        &[],
    )]);
    let (_, baseline) = run(&f, None);
    for stop in 1..=baseline.events.len() {
        let mut observer = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            validate_function_types_observed(&f, None, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            "original full type stop"
        );
        assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
        assert!(
            observer
                .events
                .iter()
                .skip(stop)
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn cumulative_work_and_copy_are_not_reset_between_complete_passes() {
    let f = fixture();
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    for _ in 0..2 {
        assert_eq!(
            validate_function_types_observed(&f, None, &mut session, site())
                .unwrap()
                .len(),
            8
        );
    }
    for bytes in [false, true] {
        let mut observer = Observer {
            work_cap: (!bytes).then_some(baseline.work - 1),
            byte_cap: bytes.then_some(baseline.bytes - 1),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            validate_function_types_observed(&f, None, &mut session, site())
                .unwrap()
                .len(),
            8
        );
        assert_eq!(
            validate_function_types_observed(&f, None, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = session.first_refusal().unwrap().progress;
        assert_eq!(
            validate_function_types_observed(&f, None, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(session.first_refusal().unwrap().progress, first);
    }
}
#[test]
fn append_preserves_each_helper_order_and_existing_prefix() {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut s = State {
        errors: vec![error(1), error(2)],
        pending: vec![error(3), error(4), error(5)],
        ..State::default()
    };
    s.append(&mut work).unwrap();
    assert_eq!(
        s.errors,
        vec![error(1), error(2), error(3), error(4), error(5)]
    );
    assert_eq!(s.pending.capacity(), 0);
    s.retire_scratch(&mut work);
    s.retire_errors(&mut work);
    assert!(empty(&s));
}
#[test]
fn append_reservation_stop_keeps_all_pending_owned_rows_and_existing_output() {
    let mut observer = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut s = State {
        pending: vec![ValidationError::OperandNotPointer {
            block: 0,
            op: "load".into(),
            ty: "u32".into(),
        }],
        ..State::default()
    };
    assert_eq!(
        s.append(&mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.pending.len(), 1);
    assert_eq!(s.errors.capacity(), 0);
    s.retire_scratch(&mut work);
    s.retire_errors(&mut work);
    assert!(empty(&s));
    assert_eq!(work.session.first_refusal().unwrap().cause, "bytes");
}
#[test]
fn refused_reversal_keeps_all_partial_rows_owned_until_consuming_retirement() {
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut s = State {
        pending: vec![error(3), error(4), error(5)],
        ..State::default()
    };
    s.append(&mut work).unwrap();
    let events = baseline.events;
    let stop = events
        .iter()
        .position(|e| e.work == 1 && e.copy_bytes == 2 * size_of::<ValidationError>())
        .unwrap()
        + 1;
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut s = State {
        pending: vec![error(3), error(4), error(5)],
        ..State::default()
    };
    assert_eq!(
        s.append(&mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(s.pending.is_empty());
    assert_eq!(s.errors.len(), 3);
    s.retire_scratch(&mut work);
    s.retire_errors(&mut work);
    assert!(empty(&s));
}
#[test]
fn actual_map_constants_pending_helper_and_prior_errors_survive_every_run_refusal() {
    let mut f = fixture();
    f.blocks[0].body.insert(
        0,
        node(
            Inst::Const {
                ty: Ty::I128,
                value: Constant::Int(-1),
            },
            &[9],
        ),
    );
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut s = State::default();
    s.run(&f, context(None), &mut work).unwrap();
    s.retire_scratch(&mut work);
    s.retire_errors(&mut work);
    let (mut map, mut constants, mut pending, mut completed) = (false, false, false, false);
    for stop in 1..=baseline.events.len() {
        let mut observer = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let mut work = Work {
            session: &mut session,
            site: site(),
        };
        let mut s = State::default();
        if s.run(&f, context(None), &mut work).is_err() {
            map |= s.values.is_some();
            constants |= !s.constants.is_empty();
            pending |= !s.pending.is_empty();
            completed |= !s.errors.is_empty();
        }
        s.retire_scratch(&mut work);
        s.retire_errors(&mut work);
        assert!(empty(&s));
    }
    assert!(map && constants && pending && completed);
}
#[test]
fn cleanup_and_final_publication_refuse_only_after_full_context_retirement() {
    let f = fixture();
    let (_, baseline) = run(&f, None);
    let stop = baseline.events.len();
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_function_types_observed(&f, None, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    assert!(observer.events.len() > stop + 10);
    let arm = Rc::new(Cell::new(false));
    let mut observer = Observer {
        cleanup: Some(arm.clone()),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut s = State::default();
    s.run(&f, context(None), &mut work).unwrap();
    assert!(s.values.is_some());
    arm.set(true);
    s.retire_scratch(&mut work);
    assert!(s.values.is_none());
    assert_eq!(s.pending.capacity(), 0);
    assert_eq!(s.constants.capacity(), 0);
    s.retire_errors(&mut work);
    assert!(empty(&s));
    assert_eq!(
        work.publication(),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        work.session.first_refusal().unwrap().cause,
        "original full type cleanup"
    );
}
#[test]
fn initial_header_and_real_first_pass_interior_work_stops_never_publish_smaller_lists() {
    let f = fixture();
    let mut observer = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_function_types_observed(&f, None, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(observer.events.len(), 1);
    let mut f = function(vec![]);
    f.blocks[0]
        .params
        .extend((0..5000).map(|_| (v(100), Ty::U32)));
    let mut observer = Observer {
        work_cap: Some(2000),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut s = State::default();
    // Build the immutable value context before this narrow first-pass stop.
    let mut setup = Observer::default();
    let mut setup_session = ObservedSession::new(InterpretOptions::default(), &mut setup);
    s.values = Some(build_function_value_types_observed(&f, &mut setup_session, site()).unwrap());
    assert_eq!(
        s.first_pass(&f, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    s.retire_scratch(&mut work);
    s.retire_errors(&mut work);
    assert!(empty(&s));
    assert_eq!(work.session.first_refusal().unwrap().cause, "work");
}
