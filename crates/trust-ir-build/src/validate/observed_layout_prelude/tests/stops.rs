// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn every_actual_compact_layout_format_merge_cleanup_callback_refuses_without_partial_output() {
    let m = invalid();
    let (_, base) = run(&m);
    for stop in 1..=base.events.len() {
        let mut o = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_module_layout_prelude_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            "original layout prelude stop"
        );
        assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
        assert!(
            o.events
                .iter()
                .skip(stop)
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn cumulative_original_work_and_copy_span_both_tables_and_repeated_calls() {
    let m = invalid();
    let (_, base) = run(&m);
    for bytes in [false, true] {
        let mut o = Observer {
            work_cap: (!bytes).then_some(base.work),
            byte_cap: bytes.then_some(base.bytes),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_module_layout_prelude_observed(&m, &mut s, site())
                .unwrap()
                .len(),
            2
        );
        assert_eq!(
            validate_module_layout_prelude_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = s.first_refusal().unwrap().progress;
        assert_eq!(
            validate_module_layout_prelude_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, first);
        assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    }
}
#[test]
fn actual_returned_owned_error_is_retained_before_its_formatter_header_can_refuse() {
    let mut m = valid();
    m.closure_layouts.clear();
    m.target_info.as_mut().unwrap().triple = format!("custom-{}", "λ".repeat(1000));
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.run(&m, &mut work).unwrap();
    let pairs: Vec<_> = base
        .events
        .windows(2)
        .enumerate()
        .filter(|(_, p)| {
            p[0].phase == ExecutionPhase::Publication
                && p[0].work == 0
                && p[0].copy_bytes == 0
                && p[1].phase == ExecutionPhase::Validation
                && p[1].work == 1
                && p[1].copy_bytes == size_of::<String>()
        })
        .map(|(i, _)| i)
        .collect();
    assert_eq!(pairs.len(), 1);
    let stop = pairs[0] + 2;
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        state.run(&m, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(
        matches!(&state.pending,Some(LayoutError::TargetScalarLayoutUnavailable{triple}) if triple==&m.target_info.as_ref().unwrap().triple)
    );
    assert_eq!(state.spelled.capacity(), 0);
    assert_eq!(state.reason.capacity(), 0);
    assert!(state.table.is_some());
    drain(&mut state, &mut work);
    assert!(empty(&state));
    assert_eq!(
        work.session.first_refusal().unwrap().cause,
        "original layout prelude stop"
    );
}
#[test]
fn complete_reason_stays_owned_across_output_reserve_and_final_error_header_admission() {
    let mut m = invalid();
    m.closure_layouts.clear();
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.run(&m, &mut work).unwrap();
    let events: Vec<_> = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 1
                && e.copy_bytes == size_of::<ValidationError>()
        })
        .map(|(i, _)| i + 1)
        .collect();
    assert_eq!(events.len(), 2);
    for (position, stop) in events.into_iter().enumerate() {
        let mut o = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State::default();
        assert_eq!(
            state.run(&m, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(state.reason, "type table entry ty.7 is missing");
        assert!(state.pending.is_none());
        assert_eq!(state.spelled.capacity(), 0);
        assert!(state.errors.is_empty());
        assert_eq!(state.errors.capacity() == 0, position == 0);
        drain(&mut state, &mut work);
        assert!(empty(&state));
    }
}
#[test]
fn actual_target_prefix_construction_can_stop_before_any_table_or_diagnostic_is_published() {
    let mut m = valid();
    m.target_info.as_mut().unwrap().triple = "x".repeat(5000);
    let mut o = Observer {
        work_cap: Some(100),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        state.run(&m, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(state.table.is_none());
    assert!(state.pending.is_none());
    assert!(state.errors.is_empty());
    assert_eq!(
        work.session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Layout
    );
    drain(&mut state, &mut work);
    assert!(empty(&state));
}
#[test]
fn initial_header_and_final_publication_refuse_before_partial_result_escape() {
    let m = invalid();
    let mut o = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_module_layout_prelude_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(o.events.len(), 1);
    let (_, base) = run(&m);
    let stop = base.events.len();
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_module_layout_prelude_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    assert!(o.events.len() > stop);
    assert!(
        o.events
            .iter()
            .skip(stop)
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn cleanup_refusal_consumes_actual_table_pending_owned_error_and_both_partial_reason_buffers() {
    let m = valid();
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        cleanup: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.run(&m, &mut work).unwrap();
    state.pending = Some(LayoutError::TargetScalarLayoutUnavailable {
        triple: "owned".repeat(1000),
    });
    state.spelled = "spelled".repeat(1000);
    state.reason = "reason".repeat(1000);
    state.errors = vec![ValidationError::TupleLayoutInconsistent {
        reason: "complete".repeat(1000),
    }];
    arm.set(true);
    drain(&mut state, &mut work);
    assert!(empty(&state));
    assert_eq!(work.session.first_refusal().unwrap().cause, "cleanup");
    assert_eq!(
        work.publication(),
        Err(ObservedValueError::AdmissionRefused)
    );
}
