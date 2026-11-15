// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;

#[test]
fn every_actual_callback_refuses_without_returning_partial_types_or_accepting_none() {
    let mut borrow = function(vec![node(Inst::Borrow { ptr: id(1) }, &[7])]);
    borrow.blocks[0]
        .params
        .push((id(1), Ty::FatPtr(FatPtrKind::Str)));
    for (f, value) in [(fixture(), 7), (borrow, 7), (function(vec![]), 99)] {
        let (_, baseline) = run(&f, value);
        for stop in 1..=baseline.events.len() {
            let mut observer = Observer {
                stop: Some(stop),
                ..Observer::default()
            };
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            assert_eq!(
                function_value_type_observed(&f, id(value), &mut session, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(
                session.first_refusal().unwrap().cause,
                "original query stop"
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
}

#[test]
fn repeated_queries_share_original_cumulative_work_copy_caps_and_sticky_refusal() {
    let f = fixture();
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    function_value_type_observed(&f, id(7), &mut session, site()).unwrap();
    function_value_type_observed(&f, id(7), &mut session, site()).unwrap();
    for bytes in [false, true] {
        let mut observer = Observer {
            work_cap: (!bytes).then_some(baseline.work - 1),
            byte_cap: bytes.then_some(baseline.bytes - 1),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert!(
            function_value_type_observed(&f, id(7), &mut session, site())
                .unwrap()
                .is_some()
        );
        assert_eq!(
            function_value_type_observed(&f, id(7), &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = session.first_refusal().unwrap().progress;
        assert_eq!(
            session.first_refusal().unwrap().cause,
            if bytes { "bytes" } else { "work" }
        );
        assert_eq!(
            function_value_type_observed(&f, id(7), &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(session.first_refusal().unwrap().progress, first);
    }
}

#[test]
fn vector_comparison_allocation_is_admitted_before_constructing_its_bool_box() {
    let input = Ty::Vector(Box::new(Ty::Error), 17);
    let mut observer = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut state = State::default();
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    assert_eq!(
        state.materialize(
            Some(Definition::Value(Inferred::Comparison(&input))),
            &mut work
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    // ready's capture admission refuses before even entering make's allocation.
    assert!(state.pending.is_none());
    state.retire(&mut work);
    let mut observer = Observer {
        stop: Some(2),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        Inferred::Comparison(&input).make(&mut Work {
            session: &mut session,
            site: site()
        }),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(observer.events.len(), 2);
    assert!(observer.events[1].copy_bytes >= 2 * size_of::<Ty>());
}

#[test]
fn existing_owned_type_is_not_overwritten_by_a_second_materialization() {
    let mut state = State {
        pending: Some(Ty::Tuple(vec![Ty::Ref(Box::new(Ty::Bool))])),
    };
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    assert_eq!(
        state.materialize(Some(Definition::Value(Inferred::Ptr)), &mut work),
        Err(ObservedValueError::InvalidRange)
    );
    assert!(matches!(state.pending, Some(Ty::Tuple(_))));
    state.retire(&mut work);
    assert!(state.pending.is_none());
}

#[test]
fn complete_pending_nested_type_survives_final_publication_refusal_and_is_explicitly_retired() {
    let f = fixture();
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut state = State::default();
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    state.run(&f, id(7), &mut work).unwrap();
    work.retire_fixed();
    work.publication().unwrap();
    let stop = baseline.events.len();
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut state = State::default();
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    state.run(&f, id(7), &mut work).unwrap();
    assert!(matches!(state.pending, Some(Ty::Tuple(_))));
    work.retire_fixed();
    assert_eq!(
        work.publication(),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(matches!(state.pending, Some(Ty::Tuple(_))));
    state.retire(&mut work);
    assert!(state.pending.is_none());
    assert_eq!(
        work.session.first_refusal().unwrap().cause,
        "original query stop"
    );
    assert!(
        observer
            .events
            .iter()
            .skip(stop)
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
    assert!(observer.events.len() > stop + 4);
}

#[test]
fn actual_nested_type_clone_stops_interiorly_without_publishing_any_partial_type() {
    let f = function(vec![node(
        Inst::Undef {
            ty: Ty::Tuple(vec![Ty::U8; 5000]),
        },
        &[7],
    )]);
    let mut observer = Observer {
        work_cap: Some(300),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut state = State::default();
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    assert_eq!(
        state.run(&f, id(7), &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(state.pending.is_none());
    state.retire(&mut work);
    assert_eq!(work.session.first_refusal().unwrap().cause, "work");
}

#[test]
fn actual_result_id_scan_refuses_interiorly_without_reporting_absence() {
    let f = function(vec![node(
        Inst::Undef { ty: Ty::U32 },
        &(0..5000).collect::<Vec<_>>(),
    )]);
    let mut observer = Observer {
        work_cap: Some(100),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        function_value_type_observed(&f, id(4999), &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "work");
    assert!(observer.events.len() < 200);
}

#[test]
fn real_chain_and_borrow_count_scans_stop_inside_the_original_scope() {
    let mut f = function(
        (1..=30)
            .map(|i| node(Inst::Borrow { ptr: id(i + 1) }, &[i]))
            .collect(),
    );
    f.blocks[0]
        .params
        .push((id(31), Ty::FatPtr(FatPtrKind::Str)));
    let mut observer = Observer {
        work_cap: Some(1000),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        function_value_type_observed(&f, id(1), &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "work");
    let mut observer = Observer {
        work_cap: Some(20),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        scan::borrow_count(
            &f,
            &mut Work {
                session: &mut session,
                site: site()
            }
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "work");
}

#[test]
fn same_observer_cleanup_refusal_keeps_the_original_cause_and_drains_owned_output() {
    let f = fixture();
    let arm = Rc::new(Cell::new(false));
    let mut observer = Observer {
        retirement_stop: Some(arm.clone()),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut state = State::default();
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    state.run(&f, id(7), &mut work).unwrap();
    assert!(state.pending.is_some());
    arm.set(true); // Tighten this same test observer; no new session or grant.
    work.retire_fixed();
    assert_eq!(
        work.publication(),
        Err(ObservedValueError::AdmissionRefused)
    );
    state.retire(&mut work);
    assert!(state.pending.is_none());
    assert_eq!(
        work.session.first_refusal().unwrap().cause,
        "original retirement stop"
    );
}
