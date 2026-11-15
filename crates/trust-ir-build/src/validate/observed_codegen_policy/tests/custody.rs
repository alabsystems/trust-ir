// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn named() -> ValidationError {
    ValidationError::AssertPanicSiteMissing {
        function: "full pending λ name".repeat(16),
        block: 9,
        inst_index: 7,
    }
}
#[test]
fn whole_pending_error_is_retained_before_output_allocation() {
    let mut o = Observer {
        stop: Some(2),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State {
        pending: Some(named()),
        ..Default::default()
    };
    assert_eq!(
        state.emit(&mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.pending, Some(named()));
    assert_eq!(state.errors.capacity(), 0);
    drain(&mut state, &mut w);
    empty(&state);
}
#[test]
fn whole_pending_error_is_retained_after_allocation_before_transport() {
    let mut o = Observer {
        stop: Some(3),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State {
        pending: Some(named()),
        ..Default::default()
    };
    assert_eq!(
        state.emit(&mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.pending, Some(named()));
    assert!(state.errors.capacity() > 0);
    drain(&mut state, &mut w);
    empty(&state);
}
#[test]
fn partial_and_complete_names_remain_owned_at_actual_interior_string_fees() {
    let mut m = fixture();
    for f in &mut m.functions {
        f.name = "full λ source name".repeat(200);
    }
    let (_, _, end) = run(&m, Rule::PanicSites);
    let mut partial = false;
    let mut complete = false;
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Default::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State::default();
        if state.run(&m, Rule::PanicSites, &mut w).is_err() {
            partial |= !state.text.is_empty() && state.text.len() < m.functions[0].name.len();
            complete |= state.text == m.functions[0].name;
        }
        drain(&mut state, &mut w);
        empty(&state);
    }
    assert!(partial && complete);
}
#[test]
fn prior_rows_and_whole_pending_next_name_are_preserved_until_full_drain() {
    let m = fixture();
    let (_, _, end) = run(&m, Rule::PanicSites);
    let mut seen = false;
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Default::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State::default();
        if state.run(&m, Rule::PanicSites, &mut w).is_err()
            && state.errors.len() == 1
            && state.pending.is_some()
        {
            seen = true;
            assert_eq!(state.errors[0], expected(&m, Rule::PanicSites)[0]);
            assert_eq!(
                state.pending.as_ref(),
                Some(&expected(&m, Rule::PanicSites)[1])
            );
        }
        drain(&mut state, &mut w);
        empty(&state);
    }
    assert!(seen);
}
#[test]
fn real_long_authority_membership_does_not_clone_an_unmatched_value() {
    let mut m = fixture();
    for f in &mut m.functions {
        f.body_gate = Some(trust_ir::BodyGate::gated("unknown λ".repeat(300)));
    }
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.run(&m, Rule::GateEvidence, &mut w).unwrap();
    assert_eq!(state.text.capacity(), 0);
    assert!(state.errors.is_empty());
    drain(&mut state, &mut w);
    empty(&state);
}
#[test]
fn caller_cleanup_refusal_consumes_success_output_and_preserves_original_stop() {
    let m = fixture();
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        cleanup: Some(arm.clone()),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = codegen_policy_errors_observed(&m, Rule::PanicSites, &mut s, site()).unwrap();
    assert_eq!(rows.len(), 6);
    arm.set(true);
    assert_eq!(
        retire_validation_errors_observed(rows, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "cleanup");
    assert_eq!(
        codegen_policy_errors_observed(&m, Rule::GlobalAsm, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
}
#[test]
fn final_publication_refusal_drains_all_errors_with_no_later_normal_callback() {
    let m = fixture();
    let (_, base, end) = run(&m, Rule::PanicSites);
    assert_eq!(base.events[end - 1].phase, ExecutionPhase::Publication);
    let mut o = Observer {
        stop: Some(end),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        codegen_policy_errors_observed(&m, Rule::PanicSites, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    drop(s);
    assert!(
        o.events[end..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn nonzero_cleanup_copy_refusal_drains_all_partial_storage_and_pending_payloads() {
    let mut o = Observer {
        byte_cap: Some(0),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State {
        text: "whole partial text".repeat(20),
        pending: Some(named()),
        errors: vec![named(), named()],
    };
    drain(&mut state, &mut w);
    empty(&state);
    assert_eq!(w.session.first_refusal().unwrap().cause, "copy");
}
