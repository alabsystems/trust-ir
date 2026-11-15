// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn complete_function_expected_found_strings_stay_owned_before_diagnostic_transfer() {
    let mut m = fixture();
    m.functions[0].name = "éname".repeat(500);
    m.func_types[1].params = vec![Ty::handle("é", "rt::中"); 5];
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let (catalog, values) = setup(&m, &mut s);
    let begin = calls.get();
    let mut state = State::default();
    state
        .run(
            &catalog,
            0,
            0,
            1,
            &values,
            &mut Work {
                session: &mut s,
                site: site(),
            },
        )
        .unwrap();
    let end = calls.get();
    drain(
        &mut state,
        &mut Work {
            session: &mut s,
            site: site(),
        },
    );
    dispose(catalog, values, &mut s);
    drop(s);
    let mut held = false;
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (catalog, values) = setup(&m, &mut s);
        let mut state = State::default();
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            state.run(&catalog, 0, 0, 1, &values, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        held |= !state.name.is_empty() && !state.expected.is_empty() && !state.actual.is_empty();
        drain(&mut state, &mut work);
        empty(&state);
        drop(work);
        dispose(catalog, values, &mut s);
    }
    assert!(held);
}
#[test]
fn full_missing_signature_child_error_is_held_before_parent_reserve() {
    let mut m = fixture();
    m.functions[1].ty = FuncTyId::new(999);
    m.functions[1].name = "中entry".repeat(500);
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let (catalog, values) = setup(&m, &mut s);
    let begin = calls.get();
    let mut state = State::default();
    state
        .run(
            &catalog,
            0,
            0,
            1,
            &values,
            &mut Work {
                session: &mut s,
                site: site(),
            },
        )
        .unwrap();
    let end = calls.get();
    drain(
        &mut state,
        &mut Work {
            session: &mut s,
            site: site(),
        },
    );
    dispose(catalog, values, &mut s);
    drop(s);
    let mut held = false;
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (catalog, values) = setup(&m, &mut s);
        let mut state = State::default();
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            state.run(&catalog, 0, 0, 1, &values, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        held |= matches!(&state.pending,Some(ValidationError::FuncTypeNotFound {func_name,..})if func_name==&m.functions[1].name);
        drain(&mut state, &mut work);
        empty(&state);
        drop(work);
        dispose(catalog, values, &mut s);
    }
    assert!(held);
}
#[test]
fn earlier_location_error_remains_owned_if_later_entry_or_shape_work_stops() {
    let mut m = fixture();
    change_site(&mut m, PanicLocation::Global(GlobalId::new(0)));
    m.globals[0].mutable = true;
    m.func_types[1].params.clear();
    let (_, _, _, end) = run(&m);
    let mut o = Observer {
        stop: Some(end),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (catalog, values) = setup(&m, &mut s);
    assert_eq!(
        validate_panic_site_at_observed(&catalog, 0, 0, 1, &values, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "original panic-site stop");
    dispose(catalog, values, &mut s);
}
#[test]
fn final_empty_and_nonempty_publication_refusal_returns_no_partial_errors() {
    for m in [fixture(), long_symbol()] {
        let (_, _, _, end) = run(&m);
        let mut o = Observer {
            stop: Some(end),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (catalog, values) = setup(&m, &mut s);
        assert_eq!(
            validate_panic_site_at_observed(&catalog, 0, 0, 1, &values, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        dispose(catalog, values, &mut s);
    }
}
#[test]
fn successful_caller_error_retirement_ends_healthy_receipt_and_stop_keeps_first_cause() {
    let m = long_symbol();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (catalog, values) = setup(&m, &mut s);
    let out = validate_panic_site_at_observed(&catalog, 0, 0, 1, &values, &mut s, site()).unwrap();
    let begin = calls.get();
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    drop(s);
    assert_eq!(
        *o.events.last().unwrap(),
        ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 0,
            copy_bytes: 0
        }
    );
    drop((catalog, values));
    let mut o = Observer {
        stop: Some(begin + 1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (catalog, values) = setup(&m, &mut s);
    let out = validate_panic_site_at_observed(&catalog, 0, 0, 1, &values, &mut s, site()).unwrap();
    assert_eq!(
        retire_validation_errors_observed(out, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "original panic-site stop");
    dispose(catalog, values, &mut s);
}
