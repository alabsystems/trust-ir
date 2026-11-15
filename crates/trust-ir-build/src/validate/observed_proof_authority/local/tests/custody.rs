// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn empty(s: &Local) {
    assert!(s.selector.candidate.is_none());
    assert_eq!(s.selector.errors.capacity(), 0);
    assert_eq!(s.reason.capacity(), 0);
    assert_eq!(s.recorded.capacity(), 0);
}
fn prepare_member(a: &Authority<'_>, state: &mut Local, w: &mut Work<'_, '_, Observer>) {
    w.admit(1, size_of::<Local>()).unwrap();
    a.source(a.module, w).unwrap();
    assert!(matches!(
        state.run(a, &a.module.proof_certificates[1], w),
        Ok(Verdict::Admitted)
    ));
    assert!(state.selector.candidate.is_none());
    w.admit(1, size_of::<Option<ProofCertificateRef>>())
        .unwrap();
    state.selector.candidate = Some(
        a.module.proof_certificates[0]
            .lineage_ref_observed(w.session, w.site)
            .unwrap(),
    );
}
#[test]
fn actual_returned_selector_is_held_through_next_membership_comparison_and_explicit_cleanup() {
    let m = fixture();
    let a = input(&m);
    let mut base = Observer::default();
    let calls = base.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let fuel = s.remaining_fuel();
    let mut state = Local::default();
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    prepare_member(&a, &mut state, &mut w);
    assert_eq!(state.selector.candidate.as_ref(), Some(&a.kernel[0]));
    let begin = calls.get();
    assert!(state.selector.member(&a.kernel, &mut w).unwrap());
    let end = calls.get();
    assert!(end > begin);
    state.retire(&mut w);
    empty(&state);
    assert_eq!(w.session.remaining_fuel(), fuel);
    drop(w);
    drop(s);
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let calls = o.calls.clone();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut state = Local::default();
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        prepare_member(&a, &mut state, &mut w);
        assert_eq!(calls.get(), begin);
        assert_eq!(state.selector.candidate.as_ref(), Some(&a.kernel[0]));
        assert!(matches!(
            state.selector.member(&a.kernel, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert_eq!(state.selector.candidate.as_ref(), Some(&a.kernel[0]));
        assert_eq!(w.session.first_refusal().unwrap().cause, "local stop");
        assert_eq!(
            w.session.first_refusal().unwrap().progress,
            base.events[cut - 1]
        );
        state.retire(&mut w);
        empty(&state);
        assert_eq!(w.session.first_refusal().unwrap().cause, "local stop");
        assert_eq!(
            w.session.first_refusal().unwrap().progress,
            base.events[cut - 1]
        );
        assert_eq!(w.session.remaining_fuel(), fuel);
        drop(w);
        drop(s);
        assert_eq!(&o.events[..cut], &base.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement && e.site == site())
        );
    }
}
#[test]
fn actual_recorded_coverage_vector_and_partial_reason_stay_owned_after_each_next_fee() {
    let m = coverage_fixture();
    let a = input(&m);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut state = Local::default();
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    state.run(&a, &m.proof_certificates[1], &mut w).unwrap();
    let end = calls.get();
    state.retire(&mut w);
    drop(w);
    drop(s);
    let mut saw = false;
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut state = Local::default();
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        assert!(matches!(
            state.run(&a, &m.proof_certificates[1], &mut w),
            Err(ObservedValueError::AdmissionRefused)
        ));
        saw |= state.recorded.len() == 2 && !state.reason.is_empty();
        state.retire(&mut w);
        empty(&state);
    }
    assert!(saw);
}
#[test]
fn final_complete_reason_publication_cut_withholds_the_whole_private_verdict() {
    let m = coverage_fixture();
    let a = input(&m);
    let (base, end) = run(&a, 1);
    assert_eq!(base.events[end - 1].phase, ExecutionPhase::Publication);
    let mut o = Observer {
        stop: Some(end),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(matches!(
        call(&a, 1, &mut s),
        Err(ObservedValueError::AdmissionRefused)
    ));
    drop(s);
    assert!(!o.events[end..].is_empty());
    assert!(
        o.events[end..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn successful_full_reason_is_caller_owned_until_nonempty_cleanup_and_exact_terminal_receipt() {
    let m = coverage_fixture();
    let a = input(&m);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = call(&a, 1, &mut s).unwrap();
    assert!(matches!(&out,LocalInheritance::Refused(t) if t.contains("records [UnwindBounded")));
    let begin = calls.get();
    out.retire_observed(&mut s, site()).unwrap();
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
fn every_actual_result_cleanup_cut_consumes_the_full_reason_and_keeps_original_first_cause() {
    let m = coverage_fixture();
    let a = input(&m);
    let mut base = Observer::default();
    let calls = base.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let out = call(&a, 1, &mut s).unwrap();
    let begin = calls.get();
    out.retire_observed(&mut s, site()).unwrap();
    let end = calls.get();
    drop(s);
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let out = call(&a, 1, &mut s).unwrap();
        assert_eq!(
            out.retire_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().cause, "local stop");
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
fn one_byte_short_total_bill_never_returns_an_admitted_or_partial_refused_result() {
    let m = coverage_fixture();
    let a = input(&m);
    let (base, end) = run(&a, 1);
    let fee: usize = base.events[..end].iter().map(|e| e.copy_bytes).sum();
    assert!(fee > 0);
    let mut o = Observer {
        byte_cap: Some(fee - 1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(matches!(
        call(&a, 1, &mut s),
        Err(ObservedValueError::AdmissionRefused)
    ));
    assert_eq!(s.first_refusal().unwrap().cause, "copy");
}
