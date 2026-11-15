// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
// Run the real whole earlier reference pass, then the actual observed child
// and production member boundary. The outer grounds method consumes a failed
// member before returning; inspect custody while that member boundary owns it.
fn comparison_state(a: &Authority<'_>, w: &mut Work<'_, '_, Observer>) -> State {
    let mut state = State::default();
    state.references(a, w).unwrap();
    w.admit(1, size_of::<Option<ProofCertificateRef>>())
        .unwrap();
    state.candidate = Some(
        a.module.proof_certificates[1]
            .lineage_ref_observed(w.session, w.site)
            .unwrap(),
    );
    state
}
#[test]
fn complete_child_selector_and_prior_fixed_diagnostics_remain_state_owned_before_comparison() {
    let m = fixture();
    let a = input(&m);
    let mut base = Observer::default();
    let calls = base.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = comparison_state(&a, &mut w);
    let begin = calls.get();
    assert!(state.member(&a.kernel, &mut w).unwrap());
    let end = calls.get();
    let out = state.finish(Ok(()), &mut w).unwrap();
    retire_validation_errors_observed(out, w.session, w.site).unwrap();
    drop(w);
    drop(s);
    assert!(end > begin);
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = comparison_state(&a, &mut w);
        assert_eq!(
            state.member(&a.kernel, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            state.candidate.as_ref(),
            Some(&m.proof_certificates[1].lineage_ref())
        );
        assert!(!state.errors.is_empty());
        assert_eq!(
            state.finish(Err(ObservedValueError::AdmissionRefused), &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(state.candidate.is_none());
        assert_eq!(state.errors.capacity(), 0);
        assert_eq!(w.session.first_refusal().unwrap().cause, "consumer stop");
        drop(w);
        drop(s);
        assert_eq!(&o.events[..cut], &base.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn full_private_currency_outputs_are_consumed_after_every_original_retirement_stop() {
    let m = fixture();
    let mut base = Observer::default();
    let calls = base.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    input(&m).retire(&mut w).unwrap();
    let end = calls.get();
    drop(w);
    drop(s);
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            input(&m).retire(&mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(w.session.first_refusal().unwrap().cause, "consumer stop");
        drop(w);
        drop(s);
        assert_eq!(&o.events[..cut], &base.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn successful_whole_diagnostics_require_explicit_original_caller_terminal_retirement() {
    let m = fixture();
    let a = input(&m);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = call(&a, Group::Contexts, &mut s).unwrap();
    assert_eq!(out, oracle(&a, Group::Contexts));
    assert!(!out.is_empty());
    let begin = calls.get();
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    drop(s);
    let tail = &o.events[begin..];
    assert!(!tail[..tail.len() - 1].is_empty());
    assert!(
        tail[..tail.len() - 1]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement && e.site == site())
    );
    assert_eq!(
        (
            tail.last().unwrap().phase,
            tail.last().unwrap().site,
            tail.last().unwrap().work,
            tail.last().unwrap().copy_bytes
        ),
        (ExecutionPhase::Publication, site(), 0, 0)
    );
}
