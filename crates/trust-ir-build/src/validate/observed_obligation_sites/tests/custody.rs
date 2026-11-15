// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn actual_row_output_reserve_and_transport_refusal_leave_complete_owned_prefix_intact() {
    let m = fixture();
    let mut state = seeded();
    let old = state.errors.capacity();
    assert_eq!(old, 1);
    let images = 4;
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    state.row(&m, &m.proof_obligations[0], &mut w).unwrap();
    drop(w);
    drop(s);
    let fees = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == images
                && e.copy_bytes == images * size_of::<ValidationError>()
        })
        .map(|(i, _)| i + 1)
        .collect::<Vec<_>>();
    assert_eq!(fees.len(), 1);
    let reserve = fees[0];
    assert_eq!(
        (
            base.events[reserve - 2].work,
            base.events[reserve - 2].copy_bytes
        ),
        (1, 0)
    );
    assert_eq!(
        (base.events[reserve].work, base.events[reserve].copy_bytes),
        (1, size_of::<ValidationError>())
    );
    for stop in [reserve, reserve + 1] {
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
        assert_eq!(
            state.row(&m, &m.proof_obligations[0], &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(state.errors, vec![owned_prefix()]);
        if stop == reserve {
            assert_eq!(state.errors.capacity(), old);
        }
        let _ = retire_validation_errors_observed(take(&mut state.errors), w.session, w.site);
        assert_eq!(state.errors.capacity(), 0);
        assert_eq!(
            w.session.first_refusal().unwrap().progress,
            base.events[stop - 1]
        );
        assert_eq!(
            w.session.first_refusal().unwrap().cause,
            "original obligation-site stop"
        );
    }
}
#[test]
fn later_physical_row_stop_preserves_all_prior_real_diagnostics() {
    let mut m = fixture();
    m.proof_obligations
        .push(obligation(2, Some(99), None, ObligationKind::Precondition));
    let expected = ordinary(&m);
    let mut base = Observer::default();
    let calls = base.calls.clone();
    let mut state = State::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    state.row(&m, &m.proof_obligations[0], &mut w).unwrap();
    let stop = calls.get() + 1;
    state.row(&m, &m.proof_obligations[1], &mut w).unwrap();
    drop(w);
    drop(s);
    let mut state = State::default();
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    state.row(&m, &m.proof_obligations[0], &mut w).unwrap();
    assert_eq!(
        state.row(&m, &m.proof_obligations[1], &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.errors, &expected[..1]);
    let _ = retire_validation_errors_observed(take(&mut state.errors), w.session, w.site);
    assert_eq!(state.errors.capacity(), 0);
    assert_eq!(
        w.session.first_refusal().unwrap().progress,
        base.events[stop - 1]
    );
}
#[test]
fn output_copy_cap_refuses_before_allocating_a_larger_prefix_buffer() {
    let mut state = seeded();
    let old = state.errors.capacity();
    let bytes = (state.errors.len() * 2 + 1 + old) * size_of::<ValidationError>();
    let mut o = Observer {
        byte_cap: Some(bytes - 1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    assert_eq!(
        w.reserve(&mut state.errors),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.errors, vec![owned_prefix()]);
    assert_eq!(state.errors.capacity(), old);
    let _ = retire_validation_errors_observed(take(&mut state.errors), w.session, w.site);
    assert_eq!(state.errors.capacity(), 0);
    assert_eq!(w.session.first_refusal().unwrap().cause, "copy");
}
