// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;

fn trace(m: &Module) -> (Observer, usize, usize, usize) {
    let mut state = seeded();
    assert_eq!(state.errors.len(), state.errors.capacity());
    let images = state.errors.len() * 2 + 1 + state.errors.capacity();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    capture_child(m, &mut state, &mut w).unwrap();
    let begin = calls.get(); // Real complete child has returned and is captured.
    state.merge(&mut w).unwrap();
    let end = calls.get(); // Before finish/caller-owned output disposal.
    let output = state.finish(Ok(()), &mut w).unwrap();
    let mut expected = vec![prefix()];
    expected.extend(child_expected(m));
    assert_eq!(output, expected);
    assert!(empty(&state));
    retire_validation_errors_observed(output, w.session, w.site).unwrap();
    drop(w);
    drop(s);
    (o, begin, end, images)
}
#[test]
fn real_child_batch_is_captured_before_the_first_merge_reader_can_refuse() {
    let m = child_module();
    let expected = child_expected(&m);
    assert_eq!(expected.len(), 3);
    let (base, begin, _, _) = trace(&m);
    let stop = begin + 1;
    let mut state = seeded();
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    capture_child(&m, &mut state, &mut w).unwrap();
    let result = state.merge(&mut w);
    assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
    assert!(state.pending.is_none());
    assert_eq!(state.batch.as_ref().unwrap().as_slice(), expected);
    assert_eq!(state.errors, vec![prefix()]);
    assert_eq!(
        w.session.first_refusal().unwrap().progress,
        base.events[stop - 1]
    );
    assert_eq!(
        state.finish(result, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(empty(&state));
}
#[test]
fn actual_output_reserve_and_transport_stops_hold_pending_tail_and_prior_prefix() {
    let m = child_module();
    let expected = child_expected(&m);
    let (base, begin, _, images) = trace(&m);
    // These are exact relative operations after the identical child return,
    // not a global search for an equal-sized publication or error header.
    assert_eq!(
        (base.events[begin].work, base.events[begin].copy_bytes),
        (2, size_of::<Option<ValidationError>>())
    );
    assert_eq!(
        (
            base.events[begin + 1].work,
            base.events[begin + 1].copy_bytes
        ),
        (1, 0)
    );
    assert_eq!(
        (
            base.events[begin + 2].work,
            base.events[begin + 2].copy_bytes
        ),
        (images, images * size_of::<ValidationError>())
    );
    assert_eq!(
        (
            base.events[begin + 3].work,
            base.events[begin + 3].copy_bytes
        ),
        (1, size_of::<ValidationError>())
    );
    for stop in [begin + 3, begin + 4] {
        let mut state = seeded();
        let mut o = Observer {
            stop: Some(stop),
            cleanup_after: Some(stop),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        capture_child(&m, &mut state, &mut w).unwrap();
        let result = state.merge(&mut w);
        assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
        assert_eq!(state.pending.as_ref(), Some(&expected[0]));
        assert_eq!(state.batch.as_ref().unwrap().as_slice(), &expected[1..]);
        assert_eq!(state.errors, vec![prefix()]);
        assert_eq!(
            state.finish(result, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(empty(&state));
        assert_eq!(
            w.session.first_refusal().unwrap().progress,
            base.events[stop - 1]
        );
        assert_eq!(
            w.session.first_refusal().unwrap().cause,
            "original module-contract stop"
        );
        drop(w);
        drop(s);
        assert_eq!(&o.events[..stop], &base.events[..stop]);
        assert!(
            o.events[stop..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn later_merge_refusal_retains_the_moved_child_prefix_and_the_complete_remaining_tail() {
    let m = child_module();
    let expected = child_expected(&m);
    let (base, begin, end, _) = trace(&m);
    let transfers = base.events[begin..end]
        .windows(2)
        .enumerate()
        .filter(|(_, pair)| {
            pair[0].phase == ExecutionPhase::Validation
                && pair[0].work == 1
                && pair[0].copy_bytes == size_of::<ValidationError>()
                && pair[1].phase == ExecutionPhase::Validation
                && pair[1].work == 2
                && pair[1].copy_bytes == size_of::<Option<ValidationError>>()
        })
        .map(|(i, _)| begin + i + 2)
        .collect::<Vec<_>>();
    assert_eq!(transfers.len(), 3);
    let stop = transfers[0];
    let mut state = seeded();
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    capture_child(&m, &mut state, &mut w).unwrap();
    let result = state.merge(&mut w);
    assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
    assert_eq!(state.errors, vec![prefix(), expected[0].clone()]);
    assert!(state.pending.is_none());
    assert_eq!(state.batch.as_ref().unwrap().as_slice(), &expected[1..]);
    assert_eq!(
        state.finish(result, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(empty(&state));
    assert_eq!(
        w.session.first_refusal().unwrap().progress,
        base.events[stop - 1]
    );
}
#[test]
fn sticky_finish_consumes_pending_full_tail_and_prior_owned_diagnostics() {
    let owned = |label: &str| ValidationError::EffectSummaryViolated {
        function: format!("{label} full name λ\0TAIL"),
        effect: "io",
        block: 7,
        inst: format!("{label} full detail 尾\0TAIL"),
    };
    let mut state = State {
        errors: vec![prefix(), owned("prior")],
        pending: Some(owned("pending")),
        batch: Some(vec![owned("tail0"), owned("tail1")].into_iter()),
    };
    assert_eq!(state.batch.as_ref().unwrap().len(), 2);
    assert!(
        matches!(state.pending.as_ref().unwrap(),ValidationError::EffectSummaryViolated {function,inst,..} if function=="pending full name λ\0TAIL" && inst=="pending full detail 尾\0TAIL")
    );
    let mut o = Observer {
        stop: Some(1),
        cleanup_after: Some(1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let result = w.admit(1, 0);
    let first = w.session.first_refusal().unwrap().progress;
    assert_eq!(
        state.finish(result, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(empty(&state));
    assert_eq!(w.session.first_refusal().unwrap().progress, first);
    assert_eq!(
        w.session.first_refusal().unwrap().cause,
        "original module-contract stop"
    );
    drop(w);
    drop(s);
    assert!(
        o.events[1..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
    assert!(o.events[1..].iter().filter(|e| e.work > 0).count() > 10);
}
