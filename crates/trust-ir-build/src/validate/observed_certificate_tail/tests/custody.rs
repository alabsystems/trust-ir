// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn prior() -> ValidationError {
    ValidationError::FormulaTextsDisagree {
        site: trust_ir::proof::FormulaSite::SpecTemporal {
            machine: "prior λ\0FULL".into(),
            property: "prior 尾\0FULL".into(),
        },
    }
}
#[test]
fn actual_output_reserve_refuses_before_allocation_and_transport_keeps_capacity_owned() {
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.prepare(&mut w).unwrap();
    let end = calls.get();
    drain(&mut state, &mut w);
    drop(w);
    drop(s);
    for cut in [end - 1, end] {
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
        assert_eq!(
            state.prepare(&mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(state.errors.is_empty());
        if cut == end - 1 {
            assert_eq!(state.errors.capacity(), 0)
        } else {
            assert!(state.errors.capacity() > 0)
        }
        drain(&mut state, &mut w);
        assert!(empty(&state));
    }
}
#[test]
fn full_prior_nested_diagnostic_stays_owned_when_later_lookup_refuses() {
    let m = fixture();
    let mut o = Observer {
        stop: Some(1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State {
        errors: vec![prior()],
    };
    let saved = state.errors.clone();
    assert_eq!(
        state.run(&m, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.errors, saved);
    drain(&mut state, &mut w);
    assert!(empty(&state));
    assert!(w.session.first_refusal().is_some());
}
#[test]
fn sticky_retirement_drains_all_prior_nested_and_current_static_errors() {
    let mut state = State {
        errors: vec![
            prior(),
            ValidationError::DanglingProofCertificate { obligation: 9 },
            prior(),
            ValidationError::TrustedWithoutJustification { obligation: 7 },
        ],
    };
    let mut o = Observer {
        cleanup_after: Some(0),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    drain(&mut state, &mut w);
    assert!(empty(&state));
    assert!(w.session.first_refusal().is_some());
    drop(w);
    drop(s);
    assert!(o.events.len() > 20);
    assert!(
        o.events
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn successful_whole_result_is_only_consumed_by_explicit_original_caller_retirement() {
    let m = fixture();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = validate_module_certificate_integrity_tail_observed(&m, &mut s, site()).unwrap();
    let saved = out.clone();
    let bound = calls.get();
    assert_eq!(out, ordinary(&m));
    assert_eq!(out, saved);
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    drop(s);
    // Explicit caller retirement consumes all payloads, then publishes its
    // own terminal receipt under the original session and site.
    let (publication, cleanup) = o.events[bound..].split_last().unwrap();
    assert!(!cleanup.is_empty());
    assert!(
        cleanup
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement && e.site == site())
    );
    assert_eq!(
        *publication,
        ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 0,
            copy_bytes: 0,
        }
    );
}
