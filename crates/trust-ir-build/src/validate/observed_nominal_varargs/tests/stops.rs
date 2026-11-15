// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_argument_lookup_graph_copy_allocation_retirement_and_publication_callback_refuses() {
    let (m, f) = fixture();
    let args = [v(1), v(2), v(3)];
    let (_, baseline, start, end) = run(&m, &f, &args, 0, "raw λ\0tail", Mode::Present);
    for cut in start + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let values = build_function_value_types_observed(&f, &mut s, site()).unwrap();
        let nominal = m
            .nominal_type_reachability_observed(&mut s, site())
            .unwrap();
        assert_eq!(
            validate_nominal_varargs_observed(
                &args,
                0,
                &values,
                Some(&nominal),
                "raw λ\0tail",
                &mut s,
                site()
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().cause, "original varargs stop");
        assert_eq!(
            nominal.retire_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            values.retire_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn successive_calls_share_original_cumulative_work_and_copy_without_reset() {
    let (m, f) = fixture();
    let mut baseline = Observer::default();
    let work = baseline.work.clone();
    let bytes = baseline.bytes.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let values = build_function_value_types_observed(&f, &mut s, site()).unwrap();
    let nominal = m
        .nominal_type_reachability_observed(&mut s, site())
        .unwrap();
    let output =
        validate_nominal_varargs_observed(&[v(1)], 0, &values, Some(&nominal), "L", &mut s, site())
            .unwrap();
    retire_validation_errors_observed(output, &mut s, site()).unwrap();
    let work_end = work.get();
    let copy_end = bytes.get();
    nominal.retire_observed(&mut s, site()).unwrap();
    values.retire_observed(&mut s, site()).unwrap();
    for copy in [false, true] {
        let mut o = Observer::default();
        if copy {
            o.byte_cap = Some(copy_end + 1);
        } else {
            o.work_cap = Some(work_end + 1);
        }
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let values = build_function_value_types_observed(&f, &mut s, site()).unwrap();
        let nominal = m
            .nominal_type_reachability_observed(&mut s, site())
            .unwrap();
        let output = validate_nominal_varargs_observed(
            &[v(1)],
            0,
            &values,
            Some(&nominal),
            "L",
            &mut s,
            site(),
        )
        .unwrap();
        retire_validation_errors_observed(output, &mut s, site()).unwrap();
        assert_eq!(
            validate_nominal_varargs_observed(
                &[v(1)],
                0,
                &values,
                Some(&nominal),
                "L",
                &mut s,
                site()
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            nominal.retire_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            values.retire_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
    }
}
#[test]
fn original_site_zero_fuel_and_preexisting_first_cause_survive_the_consumer() {
    let (m, f) = fixture();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut o = Observer::default();
    let mut s = ObservedSession::new(options, &mut o);
    let values = build_function_value_types_observed(&f, &mut s, site()).unwrap();
    let nominal = m
        .nominal_type_reachability_observed(&mut s, site())
        .unwrap();
    let output =
        validate_nominal_varargs_observed(&args(), 0, &values, Some(&nominal), "L", &mut s, site())
            .unwrap();
    retire_validation_errors_observed(output, &mut s, site()).unwrap();
    nominal.retire_observed(&mut s, site()).unwrap();
    values.retire_observed(&mut s, site()).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    let values = ObservedValueTypes::default();
    let mut o = Observer {
        stop: Some(1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        s.admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site: site(),
            work: 1,
            copy_bytes: 0
        })
        .is_err()
    );
    assert_eq!(
        validate_nominal_varargs_observed(&[], 0, &values, None, "", &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "original varargs stop");
    assert_eq!(
        values.retire_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
}
#[test]
fn full_diagnostic_vector_publication_refusal_never_returns_a_shorter_answer() {
    let (m, f) = fixture();
    let args = args();
    let (_, baseline, _, end) = run(&m, &f, &args, 0, "L", Mode::Present);
    assert_eq!(
        baseline.events[end - 1].copy_bytes,
        size_of::<Vec<ValidationError>>()
    );
    let mut o = Observer {
        stop: Some(end),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let values = build_function_value_types_observed(&f, &mut s, site()).unwrap();
    let nominal = m
        .nominal_type_reachability_observed(&mut s, site())
        .unwrap();
    assert_eq!(
        validate_nominal_varargs_observed(&args, 0, &values, Some(&nominal), "L", &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        nominal.retire_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        values.retire_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    drop(s);
    assert_eq!(&o.events[..end], &baseline.events[..end]);
    assert!(
        o.events[end..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
    assert!(o.events.len() > end + 20);
}
