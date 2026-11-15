// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn source<'a>(machine: &'a str, label: &'a str) -> FormulaSiteRef<'a> {
    FormulaSiteRef::SpecInvariant {
        machine,
        invariant: label,
    }
}
#[test]
fn both_complete_raw_labels_are_held_across_output_reserve_and_transfer_refusals() {
    let m = Module::new("");
    let machine = "full M λ\0尾";
    let label = "full I 尾\0λ";
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state
        .formula(source(machine, label), &bad(), &m, &mut w)
        .unwrap();
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
            state.formula(source(machine, label), &bad(), &m, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(state.machine, machine);
        assert_eq!(state.label, label);
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
fn partial_machine_copy_on_actual_formula_route_is_retained_then_retired() {
    let machine = "λ".repeat(2200);
    let m = Module::new("");
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state
        .formula(source(&machine, "label"), &bad(), &m, &mut w)
        .unwrap();
    let end = calls.get();
    drain(&mut state, &mut w);
    drop(w);
    drop(s);
    let mut found = false;
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
        assert_eq!(
            state.formula(source(&machine, "label"), &bad(), &m, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        if !state.machine.is_empty() && state.machine.len() < machine.len() {
            found = true;
            assert!(machine.starts_with(&state.machine));
            assert_eq!(state.label.capacity(), 0);
            assert!(state.errors.is_empty());
        }
        drain(&mut state, &mut w);
        assert!(empty(&state));
    }
    assert!(found);
}
#[test]
fn whole_machine_survives_refusal_before_label_copy_begins() {
    let machine = "whole λ\0尾".repeat(700);
    let label = "label 尾\0λ".repeat(700);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    w.text(&machine, &mut state.machine).unwrap();
    let cut = calls.get() + 1;
    drain(&mut state, &mut w);
    drop(w);
    drop(s);
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
    w.text(&machine, &mut state.machine).unwrap();
    assert_eq!(
        w.text(&label, &mut state.label),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.machine, machine);
    assert_eq!(state.label.capacity(), 0);
    drain(&mut state, &mut w);
    assert!(empty(&state));
}
#[test]
fn prior_owned_site_is_retained_when_the_next_formula_child_stops() {
    let m = Module::new("");
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state
        .formula(
            source("prior machine", "prior invariant"),
            &bad(),
            &m,
            &mut w,
        )
        .unwrap();
    let cut = calls.get() + 1;
    drain(&mut state, &mut w);
    drop(w);
    drop(s);
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
    state
        .formula(
            source("prior machine", "prior invariant"),
            &bad(),
            &m,
            &mut w,
        )
        .unwrap();
    let saved = state.errors.clone();
    assert_eq!(
        state.formula(
            source("later machine", "later invariant"),
            &bad(),
            &m,
            &mut w
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.errors, saved);
    drain(&mut state, &mut w);
    assert!(empty(&state));
}
#[test]
fn sticky_retirement_consumes_partial_labels_and_all_prior_nested_errors() {
    let mut state = State {
        machine: "partial M λ\0full".repeat(500),
        label: "partial I 尾\0full".repeat(500),
        errors: vec![prior(), prior()],
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
fn actual_predicate_child_refusal_preserves_prior_errors_and_never_assembles_site() {
    let mut m = Module::new("");
    m.predicates = vec![trust_ir::pred::Pred::Interval { lo: -3, hi: 8 }];
    let mut f = ProofFormula::new(trust_ir::pred::PRED_FORMULA_SCHEMA, "pred.0");
    f.smtlib = Some("(and (<= -3 self) (<= self 8))".into());
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    f.states_two_texts_observed(&m.pred_table(), &mut s, site())
        .unwrap();
    drop(s);
    let childcut = o
        .events
        .iter()
        .position(|e| e.phase == ExecutionPhase::ScratchRetirement)
        .unwrap()
        + 1;
    let mut o = Observer {
        stop: Some(1 + childcut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State {
        errors: vec![prior()],
        ..State::default()
    };
    let saved = state.errors.clone();
    assert_eq!(
        state.formula(source("uncloned machine", "uncloned label"), &f, &m, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.errors, saved);
    assert_eq!(state.machine.capacity(), 0);
    assert_eq!(state.label.capacity(), 0);
    drain(&mut state, &mut w);
    assert!(empty(&state));
}
#[test]
fn successful_result_labels_stay_owned_until_explicit_original_caller_retirement() {
    let m = fixture();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = validate_module_formula_texts_observed(&m, &mut s, site()).unwrap();
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
