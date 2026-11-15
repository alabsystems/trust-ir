// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn complete_pending_field_detail_and_prior_diagnostics_are_held_through_next_fee() {
    let i = bad();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut state = Binding::default();
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    state
        .run(
            &i.module,
            &i.row,
            &i.binding,
            i.env,
            i.statement,
            &i.callees,
            &mut w,
        )
        .unwrap();
    let end = calls.get();
    state.retire_scratch(&mut w);
    retire_validation_errors_observed(take(&mut state.errors), w.session, w.site).unwrap();
    drop(w);
    drop(s);
    let mut saw = false;
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut state = Binding::default();
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            state.run(
                &i.module,
                &i.row,
                &i.binding,
                i.env,
                i.statement,
                &i.callees,
                &mut w
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        saw |= !state.field.is_empty() && !state.reason.is_empty() && !state.errors.is_empty();
        state.retire_scratch(&mut w);
        let _ = retire_validation_errors_observed(take(&mut state.errors), w.session, w.site);
        assert_eq!(state.reason.capacity(), 0);
        assert_eq!(state.field.capacity(), 0);
        assert_eq!(state.errors.capacity(), 0);
    }
    assert!(saw);
}
#[test]
fn final_full_batch_publication_cut_withholds_and_retires_every_owned_diagnostic() {
    let i = bad();
    let (base, end) = run(&i);
    assert_eq!(base.events[end - 1].phase, ExecutionPhase::Publication);
    let mut o = Observer {
        stop: Some(end),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(call(&i, &mut s), Err(ObservedValueError::AdmissionRefused));
    drop(s);
    assert!(!o.events[end..].is_empty());
    assert!(
        o.events[end..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn whole_successful_batch_requires_explicit_caller_cleanup_and_every_cleanup_cut_keeps_firstcause()
{
    let i = bad();
    let mut base = Observer::default();
    let calls = base.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let out = call(&i, &mut s).unwrap();
    assert_eq!(out, oracle(&i));
    let begin = calls.get();
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    let end = calls.get();
    drop(s);
    let tail = &base.events[begin..];
    assert!(tail.len() > 1);
    assert!(
        tail[..tail.len() - 1]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement && e.site == site())
    );
    assert_eq!(
        *tail.last().unwrap(),
        ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 0,
            copy_bytes: 0
        }
    );
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let out = call(&i, &mut s).unwrap();
        assert_eq!(
            retire_validation_errors_observed(out, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().cause, "binding stop");
        drop(s);
        assert_eq!(&o.events[..cut], &base.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
