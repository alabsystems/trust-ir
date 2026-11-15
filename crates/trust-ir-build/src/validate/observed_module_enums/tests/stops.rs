// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::filter_next,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_connected_callback_refuses_without_shortened_success_or_changed_first_cause() {
    let m = invalid();
    let (_, base) = run(&m);
    for stop in 1..=base.events.len() {
        let mut o = Observer {
            stop: Some(stop),
            ..Default::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_module_enums_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
        assert_eq!(s.first_refusal().unwrap().cause, "original full enum stop");
        assert!(
            o.events
                .iter()
                .skip(stop)
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn original_cumulative_work_and_copy_are_shared_across_all_stages_and_rows() {
    let m = invalid();
    let (_, base) = run(&m);
    for bytes in [false, true] {
        let mut o = Observer {
            work_cap: (!bytes).then_some(base.work),
            byte_cap: bytes.then_some(base.bytes),
            ..Default::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        validate_module_enums_observed(&m, &mut s, site()).unwrap();
        assert_eq!(
            validate_module_enums_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = s.first_refusal().unwrap().progress;
        assert_eq!(
            validate_module_enums_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, first);
    }
}
#[test]
fn real_returned_child_batch_is_retained_before_first_fallible_merge_read() {
    let m = invalid();
    let trigger = Rc::new(Cell::new(false));
    let mut o = Observer {
        trigger: Some(trigger.clone()),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let child = validate_enum_declaration_observed(&m, 0, &mut s, site()).unwrap();
    let mut state = State {
        batch: Some(child.into_iter()),
        ..Default::default()
    };
    // The exact same original session carried the real child return and now
    // refuses the first merge admission before any owning iterator advance.
    trigger.set(true);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    assert_eq!(
        state.merge(&mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.batch.as_ref().unwrap().len(), 1);
    assert!(state.pending.is_none());
    assert_eq!(
        work.session.first_refusal().unwrap().progress.copy_bytes,
        size_of::<Option<ValidationError>>()
    );
    drain(&mut state, &mut work);
    assert!(empty(&state));
}
#[test]
fn owning_error_stays_pending_after_iterator_advance_and_before_output_allocation() {
    let error = ValidationError::ConstTypeMismatch {
        location: "fullλ".repeat(1000),
        expected: "expected".repeat(1000),
        actual: "actual".repeat(1000),
    };
    for stop in [3, 4] {
        let mut o = Observer {
            stop: Some(stop),
            ..Default::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State {
            batch: Some(vec![error.clone()].into_iter()),
            ..Default::default()
        };
        assert_eq!(
            state.merge(&mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(state.pending, Some(error.clone()));
        assert!(state.errors.is_empty());
        assert_eq!(state.errors.capacity() == 0, stop == 3);
        drain(&mut state, &mut work);
        assert!(empty(&state));
    }
}
#[test]
fn later_row_failure_cannot_drop_prior_row_errors_or_remaining_owned_child_errors() {
    let m = invalid();
    let base = private_trace(&m);
    let stop = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 1
                && e.copy_bytes == size_of::<Option<ValidationError>>()
        })
        .next_back()
        .unwrap()
        .0
        + 1;
    let mut o = Observer {
        stop: Some(stop),
        ..Default::default()
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
    assert!(state.errors.len() >= 4);
    assert!(state.batch.is_some());
    drain(&mut state, &mut work);
    assert!(empty(&state));
}
#[test]
fn sticky_cleanup_consumes_pending_iterator_tail_and_all_prior_errors() {
    let errors = original::run(&invalid());
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        cleanup: Some(arm.clone()),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut state = State {
        batch: Some(errors.clone().into_iter()),
        pending: Some(errors[0].clone()),
        errors,
    };
    arm.set(true);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    assert_eq!(
        state.finish(Ok(()), &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(empty(&state));
    assert_eq!(work.session.first_refusal().unwrap().cause, "cleanup");
}
#[test]
fn original_preexisting_stop_prevents_any_new_enum_constituent_call() {
    let m = invalid();
    let mut o = Observer {
        stop: Some(1),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let first = ExecutionProgress {
        phase: ExecutionPhase::ModuleLookup,
        site: site(),
        work: 1,
        copy_bytes: 0,
    };
    assert!(s.admit(first).is_err());
    assert_eq!(
        validate_module_enums_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().progress, first);
    assert_eq!(o.events, vec![first]);
}
#[test]
fn connected_every_stage_uses_the_supplied_instruction_site_and_zero_fuel() {
    let m = invalid();
    let exact = ExecutionSite::Instruction(trust_ir::interpret::InstructionSite {
        function: FuncId::new(8),
        block: BlockId::new(2),
        instruction_index: 1,
    });
    let mut o = Observer::default();
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..Default::default()
        },
        &mut o,
    );
    assert_eq!(
        validate_module_enums_observed(&m, &mut s, exact).unwrap(),
        original::run(&m)
    );
    assert_eq!(s.remaining_fuel(), 0);
    assert!(o.events.iter().all(|e| e.site == exact));
}

#[test]
fn second_row_real_declaration_batch_keeps_prior_prefix_pending_error_and_nonempty_tail() {
    let m = invalid();
    let base = private_trace(&m);
    // Each actual completed child returns its Vec immediately before the
    // parent's first merge read. The fifth such join is the second enum's
    // declaration, after first-row declaration/prelude/fields/encoding.
    let (at, _) = base
        .events
        .windows(2)
        .enumerate()
        .filter(|(_, pair)| {
            pair[0].phase == ExecutionPhase::Publication
                && pair[0].work == 1
                && pair[0].copy_bytes == size_of::<Vec<ValidationError>>()
                && pair[1].phase == ExecutionPhase::Validation
                && pair[1].work == 1
                && pair[1].copy_bytes == size_of::<Option<ValidationError>>()
        })
        .nth(4)
        .unwrap();
    let stop = at + 3; // first output reserve poll, after the iterator advance
    assert_eq!(base.events[stop - 1].phase, ExecutionPhase::Validation);
    assert_eq!(
        (base.events[stop - 1].work, base.events[stop - 1].copy_bytes),
        (1, 0)
    );
    let mut o = Observer {
        stop: Some(stop),
        ..Default::default()
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
    assert_eq!(state.errors, original::run(&m)[..4]);
    assert_eq!(state.pending, Some(ValidationError::DuplicateEnumId(7)));
    let tail = state.batch.as_ref().unwrap();
    assert_eq!(tail.len(), 1);
    assert!(
        matches!(&tail.as_slice()[0],ValidationError::ConstTypeMismatch {expected,..}
        if expected=="field_names empty or exactly 1 entries")
    );
    assert_eq!(
        work.session.first_refusal().unwrap().progress,
        base.events[stop - 1]
    );
    drain(&mut state, &mut work);
    assert!(empty(&state));
}
