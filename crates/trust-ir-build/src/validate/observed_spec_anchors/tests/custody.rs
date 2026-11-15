// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn whole_returned_core_batch_is_retained_before_the_first_mapping_callback() {
    let m = bad();
    let (_, base) = run(&m);
    let cuts = base
        .events
        .windows(2)
        .enumerate()
        .filter(|(_, pair)| {
            pair[0].phase == ExecutionPhase::Publication
                && pair[0].work == 1
                && pair[0].copy_bytes == size_of::<Vec<SpecLinkViolation>>()
                && pair[1].phase == ExecutionPhase::Validation
                && pair[1].work == 1
                && pair[1].copy_bytes == size_of::<Option<SpecLinkViolation>>()
        })
        .map(|(i, _)| i + 2)
        .collect::<Vec<_>>();
    assert_eq!(cuts.len(), 1);
    let stop = cuts[0];
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut owner = ObservedSession::new(InterpretOptions::default(), &mut o);
    // Repeat the identical public prefix, including its first State/Work
    // admission. The selected next callback is therefore the actual first
    // mapping callback after the complete child batch was returned.
    owner
        .admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site: site(),
            work: 1,
            copy_bytes: size_of::<State>() + size_of::<Work<'_, '_, Observer>>(),
        })
        .unwrap();
    let mut state = State::default();
    let mut w = Work {
        session: &mut owner,
        site: site(),
    };
    w.admit(
        3,
        size_of::<Vec<SpecLinkViolation>>()
            + size_of::<IntoIter<SpecLinkViolation>>()
            + size_of::<Option<SpecLinkViolation>>(),
    )
    .unwrap();
    state.batch = Some(
        trust_ir::validate_spec_executable_links_observed(&m, w.session, w.site)
            .unwrap()
            .into_iter(),
    );
    assert_eq!(state.batch.as_ref().unwrap().len(), 2);
    assert!(state.pending.is_none());
    assert!(state.errors.is_empty());
    assert_eq!(
        state.merge(&mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.batch.as_ref().unwrap().len(), 2);
    assert!(state.pending.is_none());
    assert!(state.errors.is_empty());
    assert_eq!(
        state.finish(Err(ObservedValueError::AdmissionRefused), &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(empty(&state));
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut owner = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_spec_anchor_functions_observed(&m, &mut owner, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        owner.first_refusal().unwrap().progress,
        base.events[stop - 1]
    );
}
#[test]
fn complete_pending_violation_and_real_tail_survive_output_reserve_and_header_stops() {
    for stop in [4, 5] {
        let mut state = State {
            batch: Some(vec![row("action", "one"), row("projection", "two")].into_iter()),
            ..State::default()
        };
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
        assert_eq!(state.pending, Some(row("action", "one")));
        assert_eq!(
            state.batch.as_ref().unwrap().as_slice(),
            [row("projection", "two")]
        );
        assert!(state.errors.is_empty());
        assert_eq!(state.errors.capacity() == 0, stop == 4);
        assert_eq!(
            state.finish(Err(ObservedValueError::AdmissionRefused), &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(empty(&state));
    }
}
#[test]
fn ignored_row_retirement_refusal_keeps_first_cause_and_prevents_publishing_prior_prefix() {
    let arm = Rc::new(Cell::new(true));
    let mut state = State {
        batch: Some(vec![row("unknown", "owned")].into_iter()),
        errors: vec![ValidationError::InvalidSpecAnchorFunction {
            machine: "prior".repeat(1000),
            action: "a".into(),
            function: 1,
            detail: "detail".repeat(1000),
        }],
        ..State::default()
    };
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
        state.merge(&mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.errors.len(), 1);
    assert_eq!(
        state.finish(Err(ObservedValueError::AdmissionRefused), &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(empty(&state));
    assert_eq!(w.session.first_refusal().unwrap().cause, "cleanup");
}
#[test]
fn cleanup_stop_drains_pending_nonempty_child_tail_and_prior_build_output() {
    let mut state = State {
        pending: Some(row("action", "pending")),
        batch: Some(vec![row("projection", "tail1"), row("action", "tail2")].into_iter()),
        errors: vec![ValidationError::InvalidSpecAnchorFunction {
            machine: "prior".repeat(1000),
            action: "a".into(),
            function: 1,
            detail: "detail".repeat(1000),
        }],
    };
    let arm = Rc::new(Cell::new(true));
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
