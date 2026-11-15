#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn complete_lineage_child_stream_is_followed_by_a_paid_parent_bool_gate() {
    let m = fixture();
    let c = ModuleFunctionCatalog::new(&m);
    let mut child = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut child);
    assert!(
        m.proof_certificates[0]
            .evidence
            .clean_cic_lineage_binds_observed(&m.proof_obligations[0], &c, &mut s, site())
            .unwrap()
    );
    drop(s);
    let (good, _) = run(&m, Mode::Source);
    let start = good
        .events
        .windows(child.events.len())
        .position(|p| p == child.events)
        .unwrap();
    assert_eq!(
        good.events[start + child.events.len()],
        ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site: site(),
            work: size_of::<bool>() + 1,
            copy_bytes: 2 * size_of::<bool>() + size_of::<Option<bool>>()
        }
    );
}
#[test]
fn stopping_at_actual_next_parent_fee_keeps_the_full_child_bool_and_borrowed_owners() {
    let m = fixture();
    let c = ModuleFunctionCatalog::new(&m);
    let mut good = Observer::default();
    let calls = good.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut good);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.run(&m, &c, Mode::Source, &mut w).unwrap();
    let end = calls.get();
    let out = state.finish(Ok(()), &mut w).unwrap();
    retire_validation_errors_observed(out, w.session, w.site).unwrap();
    drop(w);
    drop(s);
    let mut reached = false;
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
        let mut state = State::default();
        let result = state.run(&m, &c, Mode::Source, &mut w);
        if state.lineage == Some(true)
            && w.session.first_refusal().is_some_and(|r| {
                r.progress
                    == ExecutionProgress {
                        phase: ExecutionPhase::Validation,
                        site: site(),
                        work: size_of::<bool>() + 1,
                        copy_bytes: 2 * size_of::<bool>() + size_of::<Option<bool>>(),
                    }
            })
            && state.field.is_empty()
            && state.detail.is_empty()
        {
            reached = true;
            assert!(state.row.is_some() && state.certificate.is_some());
            assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
        }
        assert_eq!(
            state.finish(result, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(
            state.row.is_none()
                && state.certificate.is_none()
                && state.lineage.is_none()
                && state.pending.is_none()
        );
        assert_eq!(
            state.field.capacity() + state.detail.capacity() + state.errors.capacity(),
            0
        );
    }
    assert!(reached);
}
#[test]
fn actual_allocation_cuts_keep_prior_batch_partial_fields_and_full_pending_error() {
    let mut m = fixture();
    m.proof_obligations.push(row(9));
    m.proof_certificates
        .push(cert(&m.proof_obligations[1], Some(directive(None))));
    let c = ModuleFunctionCatalog::new(&m);
    let mut good = Observer::default();
    let calls = good.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut good);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.run(&m, &c, Mode::Source, &mut w).unwrap();
    let end = calls.get();
    let out = state.finish(Ok(()), &mut w).unwrap();
    retire_validation_errors_observed(out, w.session, w.site).unwrap();
    drop(w);
    drop(s);
    let (mut partial, mut pending, mut prior) = (false, false, false);
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
        let mut state = State::default();
        let result = state.run(&m, &c, Mode::Source, &mut w);
        partial |= state.field == "environment" && state.detail.is_empty();
        prior |= !state.errors.is_empty();
        if let Some(ValidationError::CertificateBindingMismatch { field, detail, .. }) =
            &state.pending
        {
            assert_eq!(field, "environment");
            assert_eq!(detail, DETAIL);
            pending = true;
        }
        assert_eq!(
            state.finish(result, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            state.errors.capacity() + state.field.capacity() + state.detail.capacity(),
            0
        );
        assert!(state.pending.is_none());
    }
    assert!(partial && pending && prior);
}
#[test]
fn full_prior_pending_and_partial_text_state_is_consumed_without_masking_held_error() {
    for error in [
        ObservedValueError::CapacityOverflow,
        ObservedValueError::AllocationFailed,
        ObservedValueError::InvalidRange,
    ] {
        let mut o = Observer::default();
        let arm = o.cleanup.clone();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State::default();
        state
            .diagnostic(ProofId::new(7), Mode::Source, &mut w)
            .unwrap();
        state
            .diagnostic(ProofId::new(9), Mode::Source, &mut w)
            .unwrap();
        state.pending = state.errors.pop();
        storage::text(&mut state.field, "partial field", &mut w).unwrap();
        storage::text(&mut state.detail, "partial detail", &mut w).unwrap();
        arm.set(true);
        assert_eq!(state.finish(Err(error), &mut w), Err(error));
        assert_eq!(
            state.errors.capacity() + state.field.capacity() + state.detail.capacity(),
            0
        );
        assert!(state.pending.is_none());
        assert_eq!(w.session.first_refusal().unwrap().cause, "unbound cleanup");
    }
}
#[test]
fn returned_whole_error_batch_has_nonempty_cleanup_prefix_and_exact_terminal_receipt() {
    let m = fixture();
    let c = ModuleFunctionCatalog::new(&m);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = call(&m, &c, Mode::Source, &mut s).unwrap();
    let begin = calls.get();
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    drop(s);
    let tail = &o.events[begin..];
    let (last, prefix) = tail.split_last().unwrap();
    assert!(!prefix.is_empty());
    assert!(
        prefix
            .iter()
            .all(|p| p.phase == ExecutionPhase::ScratchRetirement && p.site == site())
    );
    assert_eq!(
        *last,
        ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 0,
            copy_bytes: 0
        }
    );
}
#[test]
fn final_publication_refusal_consumes_full_transferred_batch_after_state_headers() {
    let m = fixture();
    let c = ModuleFunctionCatalog::new(&m);
    let (good, end) = run(&m, Mode::Source);
    assert_eq!(good.events[end - 1].phase, ExecutionPhase::Publication);
    let mut o = Observer {
        stop: Some(end),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        call(&m, &c, Mode::Source, &mut s),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().progress, good.events[end - 1]);
    drop(s);
    assert!(!o.events[end..].is_empty());
    assert!(
        o.events[end..]
            .iter()
            .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
    );
}
