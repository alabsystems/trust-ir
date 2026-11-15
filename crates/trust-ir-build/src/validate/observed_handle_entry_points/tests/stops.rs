// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_full_namespace_callback_refuses_and_keeps_first_cause_without_partial_vector() {
    let (mut m, r) = bad_fixture();
    m.globals.push(global("pinned", Some(address("pinned"))));
    let (_, baseline, end) = run(&m, &r);
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_handle_entry_points_observed(&m, &r, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().cause, "original entrypoint stop");
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
fn complete_expected_signature_diagnostics_constant_rows_and_retirement_share_cumulative_caps() {
    let (m, r) = bad_fixture();
    let (_, baseline, end) = run(&m, &r);
    for copy in [false, true] {
        let limit = baseline.events[..end]
            .iter()
            .map(|e| if copy { e.copy_bytes } else { e.work })
            .sum::<usize>();
        let mut o = Observer::default();
        if copy {
            o.byte_cap = Some(limit + 1)
        } else {
            o.work_cap = Some(limit + 1)
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let out = validate_handle_entry_points_observed(&m, &r, &mut s, site()).unwrap();
        assert_eq!(
            validate_handle_entry_points_observed(&m, &r, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let _ = retire_validation_errors_observed(out, &mut s, site());
    }
}
#[test]
fn original_zero_execution_fuel_request_site_and_preexisting_stop_are_not_replaced() {
    let (m, r) = fixture();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut o = Observer::default();
    let mut s = ObservedSession::new(options, &mut o);
    let out = validate_handle_entry_points_observed(&m, &r, &mut s, site()).unwrap();
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
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
        validate_handle_entry_points_observed(&m, &r, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "original entrypoint stop");
}
#[test]
fn actual_middle_context_byte_chunk_refuses_before_accepting_a_shorter_constant_diagnostic() {
    let (mut m, r) = fixture();
    m.globals
        .push(global(&"raw λ\0".repeat(3000), Some(address("pinned"))));
    let (_, baseline, end) = run(&m, &r);
    let cut = baseline.events[..end]
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation && e.work == 1024 && e.copy_bytes == 1024
        })
        .nth(1)
        .unwrap()
        .0
        + 1;
    let mut o = Observer {
        stop: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_handle_entry_points_observed(&m, &r, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().progress,
        baseline.events[cut - 1]
    );
    drop(s);
    assert_eq!(&o.events[..cut], &baseline.events[..cut]);
}
#[test]
fn every_actual_deep_type_equality_callback_refuses_with_closed_expected_signature_still_owned() {
    let mut ty = Ty::handle("raw λ\0", "rt::Name");
    for _ in 0..32 {
        ty = Ty::Ref(Box::new(ty));
    }
    let p = pin(vec![entry(
        "pinned",
        vec![PinnedTy::Scalar(ty)],
        vec![PinnedTy::Scalar(Ty::Bool)],
    )]);
    let e = &p.entry_points[0];
    let actual = p.func_ty(e);
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let expected = p.func_ty_observed(e, &mut s, site()).unwrap();
    let begin = calls.get();
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    assert!(signature::same(&actual, &expected, &mut work).unwrap());
    let end = calls.get();
    drop(work);
    expected.retire_observed(&mut s, site()).unwrap();
    drop(s);
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let expected = p.func_ty_observed(e, &mut s, site()).unwrap();
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            signature::same(&actual, &expected, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(expected.signature(), &actual);
        drop(work);
        let _ = expected.retire_observed(&mut s, site());
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
