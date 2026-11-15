// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn cleanup(s: &mut Inherited, w: &mut Work<'_, '_, impl ExecutionObserver>) {
    s.retire_scratch(w);
    let _ = retire_validation_errors_observed(take(&mut s.errors), w.session, w.site);
    assert_eq!(s.errors.capacity(), 0);
    assert_eq!(s.reason.capacity(), 0);
    assert!(s.key.is_none());
    assert!(s.local.is_none());
    assert!(s.selector.candidate.is_none());
}
#[test]
fn whole_returned_local_refusal_and_prior_errors_remain_state_owned_before_next_fee() {
    let m = refused_local();
    let a = input(&m);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut state = Inherited::default();
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    state.run(&a, ImportPolicy::Refuse, &mut w).unwrap();
    let end = calls.get();
    cleanup(&mut state, &mut w);
    drop(w);
    drop(s);
    let mut saw = false;
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut state = Inherited::default();
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            state.run(&a, ImportPolicy::Refuse, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        saw |= matches!(state.local.as_ref(),Some(LocalInheritance::Refused(t))if !t.is_empty())
            && !state.errors.is_empty();
        cleanup(&mut state, &mut w);
    }
    assert!(saw);
}
#[test]
fn whole_returned_lineage_key_remains_owned_across_actual_sealed_lookup_and_refusal() {
    let mut m = fixture();
    m.imports.clear();
    let a = input(&m);
    let auth = authenticated(&m, Some(SiteOutcome::Refused("detail".repeat(600))));
    let policy = ImportPolicy::Authenticated(&auth);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut state = Inherited::default();
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    state.run(&a, policy, &mut w).unwrap();
    let end = calls.get();
    cleanup(&mut state, &mut w);
    drop(w);
    drop(s);
    let mut saw = false;
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut state = Inherited::default();
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            state.run(&a, policy, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        saw |= state
            .key
            .as_ref()
            .is_some_and(|key| key == &m.proof_certificates[2].lineage_ref())
            && !state.errors.is_empty();
        cleanup(&mut state, &mut w);
    }
    assert!(saw);
}
#[test]
fn partial_complete_unicode_message_and_prior_errors_have_no_implicit_drop_on_stop() {
    let mut m = fixture();
    m.imports.clear();
    let a = input(&m);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut state = Inherited::default();
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    state.run(&a, ImportPolicy::Refuse, &mut w).unwrap();
    let end = calls.get();
    cleanup(&mut state, &mut w);
    drop(w);
    drop(s);
    let mut saw = false;
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut state = Inherited::default();
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            state.run(&a, ImportPolicy::Refuse, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        saw |= !state.reason.is_empty() && !state.errors.is_empty();
        cleanup(&mut state, &mut w);
    }
    assert!(saw);
}
#[test]
fn final_full_error_batch_publication_refusal_withholds_and_retires_all_owned_fields() {
    let m = refused_local();
    let a = input(&m);
    let (base, end) = run(&a, ImportPolicy::Refuse);
    assert_eq!(base.events[end - 1].phase, ExecutionPhase::Publication);
    let mut o = Observer {
        stop: Some(end),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        call(&a, ImportPolicy::Refuse, &mut s),
        Err(ObservedValueError::AdmissionRefused)
    );
    drop(s);
    assert!(!o.events[end..].is_empty());
    assert!(
        o.events[end..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn successful_whole_diagnostic_batch_requires_explicit_caller_terminal_cleanup() {
    let m = refused_local();
    let a = input(&m);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = call(&a, ImportPolicy::Refuse, &mut s).unwrap();
    assert_eq!(out, oracle(&a, ImportPolicy::Refuse));
    assert!(out.len() > 1);
    let begin = calls.get();
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    drop(s);
    let tail = &o.events[begin..];
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
}
#[test]
fn every_actual_caller_cleanup_cut_still_consumes_the_complete_batch_under_first_cause() {
    let m = refused_local();
    let a = input(&m);
    let mut base = Observer::default();
    let calls = base.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let out = call(&a, ImportPolicy::Refuse, &mut s).unwrap();
    let begin = calls.get();
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    let end = calls.get();
    drop(s);
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let out = call(&a, ImportPolicy::Refuse, &mut s).unwrap();
        assert_eq!(
            retire_validation_errors_observed(out, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().cause, "inherit stop");
        drop(s);
        assert_eq!(&o.events[..cut], &base.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
