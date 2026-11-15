// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn every_actual_compact_claim_callback_refuses_without_partial_publication() {
    let m = fixture();
    let (_, base) = run(&m);
    for stop in 1..=base.events.len() {
        let mut o = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_module_completeness_claim_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            "original completeness stop"
        );
        assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
        assert!(
            o.events
                .iter()
                .skip(stop)
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn cumulative_original_work_and_copy_span_calls_without_a_new_grant() {
    let m = fixture();
    let (_, base) = run(&m);
    for bytes in [false, true] {
        let mut o = Observer {
            work_cap: (!bytes).then_some(base.work),
            byte_cap: bytes.then_some(base.bytes),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_module_completeness_claim_observed(&m, &mut s, site())
                .unwrap()
                .len(),
            4
        );
        assert_eq!(
            validate_module_completeness_claim_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = s.first_refusal().unwrap().progress;
        assert_eq!(
            validate_module_completeness_claim_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, first);
        assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    }
}
#[test]
fn definition_name_comparison_stops_inside_a_full_equal_prefix() {
    let symbol = format!("{}a", "λ".repeat(4000));
    let name = format!("{}b", "λ".repeat(4000));
    let mut m = Module::new("prefix");
    m.completeness = Some(ModuleCompleteness::Partial(vec![row(&symbol)]));
    m.functions.push(function(0, &name, true));
    let mut o = Observer {
        work_cap: Some(1500),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_module_completeness_claim_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().progress.work, 1024);
    assert!(
        o.events
            .iter()
            .filter(|e| e.work == 1024 && e.copy_bytes == 0)
            .count()
            >= 2
    );
}
#[test]
fn actual_diagnostic_utf8_copy_retains_allocated_empty_and_partial_symbol() {
    let symbol = "λ".repeat(3000);
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.diagnostic(&symbol, Some(1), &mut work).unwrap();
    let pair = base
        .events
        .windows(2)
        .position(|p| p.iter().all(|e| e.work == 1024 && e.copy_bytes == 1024))
        .unwrap();
    let copy = pair + 2;
    for stop in [copy, copy + 1] {
        let mut o = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State::default();
        assert_eq!(
            state.diagnostic(&symbol, Some(1), &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(state.symbol.len(), if stop == copy { 0 } else { 1024 });
        assert!(state.symbol.capacity() >= 1024);
        assert!(state.errors.is_empty());
        drain(&mut state, &mut work);
        assert_eq!(state.symbol.capacity(), 0);
        assert_eq!(state.errors.capacity(), 0);
        assert_eq!(
            work.session.first_refusal().unwrap().cause,
            "original completeness stop"
        );
    }
}
#[test]
fn initial_output_reserve_and_final_publication_refusal_preserve_all_owned_custody() {
    let m = fixture();
    let mut o = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_module_completeness_claim_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(o.events.len(), 1);
    let mut o = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        state.diagnostic("", None, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.errors.capacity(), 0);
    let (_, base) = run(&m);
    let stop = base.events.len();
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_module_completeness_claim_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    assert!(o.events.len() > stop + 4);
}
#[test]
fn original_cleanup_refusal_consumes_partial_and_complete_symbols_before_return() {
    let mut o = Observer {
        cleanup: true,
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State {
        symbol: "λ".repeat(3000),
        errors: vec![ValidationError::DuplicateUnloweredRow {
            symbol: "owned".repeat(1000),
        }],
    };
    drain(&mut state, &mut work);
    assert_eq!(state.symbol.capacity(), 0);
    assert_eq!(state.errors.capacity(), 0);
    assert_eq!(work.session.first_refusal().unwrap().cause, "cleanup");
    assert_eq!(
        work.publication(),
        Err(ObservedValueError::AdmissionRefused)
    );
}
