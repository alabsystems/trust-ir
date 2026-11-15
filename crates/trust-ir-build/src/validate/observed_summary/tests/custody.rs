// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn complete_returned_binding_shape_and_local_batches_are_held_before_first_merge_callback() {
    let (m, f, s) = mixed();
    let base = raw_trace(&m, &f, &s, ImportPolicy::Structural);
    // Delimit the actual return→merge seam by BOTH consecutive events, not
    // global equal-sized headers from nested child publications.
    let cuts = base
        .events
        .windows(2)
        .enumerate()
        .filter(|(_, pair)| {
            pair[0].phase == ExecutionPhase::Publication
                && pair[0].work == 1
                && pair[0].copy_bytes == size_of::<Vec<ValidationError>>()
                && pair[1].phase == ExecutionPhase::Validation
                && pair[1].work == 2
                && pair[1].copy_bytes == size_of::<Option<ValidationError>>()
        })
        .map(|(i, _)| i + 2)
        .collect::<Vec<_>>();
    assert_eq!(cuts.len(), 3);
    for (stage, stop) in cuts.into_iter().enumerate() {
        let mut o = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut owner = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut owner,
            site: site(),
        };
        let mut state = State::default();
        assert_eq!(
            state.run(&m, &f, &s, ImportPolicy::Structural, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(state.batch.as_ref().unwrap().len(), [2, 1, 2][stage]);
        assert_eq!(state.errors.len(), [0, 2, 4][stage]);
        assert!(state.pending.is_none() && state.imported.is_none());
        assert_eq!(
            state.finish(Err(ObservedValueError::AdmissionRefused), &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(empty(&state));
        assert_eq!(
            w.session.first_refusal().unwrap().progress,
            base.events[stop - 1]
        );
    }
}
#[test]
fn complete_import_tuple_is_held_before_fallible_unpack_and_citation_publication() {
    let (m, f, s) = mixed();
    let base = raw_trace(&m, &f, &s, ImportPolicy::Structural);
    let cut = base
        .events
        .windows(2)
        .enumerate()
        .filter(|(_, pair)| {
            pair[0].phase == ExecutionPhase::Publication
                && pair[0].copy_bytes
                    == size_of::<Vec<ValidationError>>() + size_of::<SummaryCitation>()
                && pair[1].phase == ExecutionPhase::Validation
                && pair[1].work == 3
                && pair[1].copy_bytes
                    == size_of::<Option<(Vec<ValidationError>, SummaryCitation)>>()
                        + size_of::<Option<IntoIter<ValidationError>>>()
        })
        .map(|(i, _)| i + 2)
        .collect::<Vec<_>>();
    assert_eq!(cut.len(), 1);
    let stop = cut[0];
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut owner = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut owner,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        state.run(&m, &f, &s, ImportPolicy::Structural, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    let (errors, citation) = state.imported.as_ref().unwrap();
    assert_eq!(errors.len(), 1);
    assert!(matches!(
        &errors[0],
        ValidationError::DanglingExternRef { .. }
    ));
    assert_eq!(*citation, SummaryCitation::Absent);
    assert_eq!(state.errors.len(), 3);
    assert!(state.batch.is_none() && state.pending.is_none());
    assert_eq!(
        state.finish(Err(ObservedValueError::AdmissionRefused), &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(empty(&state));
}
#[test]
fn pending_error_and_real_nonempty_batch_tail_survive_output_growth_and_header_refusals() {
    for stop in [3, 4] {
        let mut state = State {
            errors: vec![error("prefix")],
            batch: Some(vec![error("pending"), error("tail1"), error("tail2")].into_iter()),
            ..State::default()
        };
        assert_eq!(state.errors.capacity(), 1);
        let mut o = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut owner = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut owner,
            site: site(),
        };
        assert_eq!(
            state.merge(&mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(state.errors, vec![error("prefix")]);
        assert_eq!(state.pending.as_ref(), Some(&error("pending")));
        assert_eq!(
            state.batch.as_ref().unwrap().as_slice(),
            [error("tail1"), error("tail2")]
        );
        if stop == 3 {
            assert_eq!(state.errors.capacity(), 1);
        } else {
            assert!(state.errors.capacity() >= 3);
        }
        assert_eq!(
            state.finish(Err(ObservedValueError::AdmissionRefused), &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(empty(&state));
    }
}
#[test]
fn later_merge_stop_keeps_already_moved_prefix_second_pending_and_actual_remaining_tail() {
    let mut state = State {
        batch: Some(vec![error("one"), error("two"), error("three")].into_iter()),
        ..State::default()
    };
    let mut o = Observer {
        stop: Some(7),
        ..Observer::default()
    };
    let mut owner = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut owner,
        site: site(),
    };
    assert_eq!(
        state.merge(&mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.errors, vec![error("one")]);
    assert_eq!(state.pending.as_ref(), Some(&error("two")));
    assert_eq!(state.batch.as_ref().unwrap().as_slice(), [error("three")]);
    assert_eq!(
        state.finish(Err(ObservedValueError::AdmissionRefused), &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(empty(&state));
}
fn held() -> State {
    State {
        errors: vec![error(&"prefix".repeat(1000))],
        pending: Some(error(&"pending".repeat(1000))),
        batch: Some(vec![error(&"tail1".repeat(1000)), error(&"tail2".repeat(1000))].into_iter()),
        imported: Some((
            vec![error(&"tuple".repeat(1000))],
            SummaryCitation::ProofBearing,
        )),
        citation: SummaryCitation::Absent,
    }
}
#[test]
fn first_cleanup_stop_still_drains_every_owned_prefix_pending_tail_and_import_tuple() {
    let arm = Rc::new(Cell::new(true));
    let mut state = held();
    let mut o = Observer {
        cleanup: Some(arm),
        ..Observer::default()
    };
    let mut owner = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut owner,
        site: site(),
    };
    assert_eq!(
        state.finish(Ok(()), &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(empty(&state));
    assert_eq!(w.session.first_refusal().unwrap().cause, "cleanup");
}
#[test]
fn typed_failure_without_observer_refusal_still_consumes_all_owned_batch_state() {
    let mut state = held();
    let mut o = Observer::default();
    let mut owner = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut owner,
        site: site(),
    };
    assert_eq!(
        state.finish(Err(ObservedValueError::CapacityOverflow), &mut w),
        Err(ObservedValueError::CapacityOverflow)
    );
    assert!(empty(&state));
    assert!(w.session.first_refusal().is_none());
}
