// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_helper_traversal_policy_child_copy_cleanup_and_final_publication_refuses() {
    let (m, r) = fixture();
    let (_, baseline, begin, end) = run(&m, &r, ImportPolicy::Refuse);
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let nominal = m
            .nominal_type_reachability_observed(&mut s, site())
            .unwrap();
        assert_eq!(
            validate_handle_foreign_declarations_observed(
                &m,
                &r,
                &nominal,
                ImportPolicy::Refuse,
                &mut s,
                site()
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().cause, "original foreign stop");
        let _ = nominal.retire_observed(&mut s, site());
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
fn same_session_complete_queries_text_rows_and_caller_cleanup_cumulate_work_and_copy() {
    let (m, r) = fixture();
    let (_, baseline, _, end) = run(&m, &r, ImportPolicy::Refuse);
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
        let nominal = m
            .nominal_type_reachability_observed(&mut s, site())
            .unwrap();
        let out = validate_handle_foreign_declarations_observed(
            &m,
            &r,
            &nominal,
            ImportPolicy::Refuse,
            &mut s,
            site(),
        )
        .unwrap();
        let result = validate_handle_foreign_declarations_observed(
            &m,
            &r,
            &nominal,
            ImportPolicy::Refuse,
            &mut s,
            site(),
        );
        assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
        let _ = retire_validation_errors_observed(out, &mut s, site());
        let _ = nominal.retire_observed(&mut s, site());
    }
}
#[test]
fn original_zero_execution_fuel_request_site_and_first_sticky_cause_survive_queries() {
    let (m, r) = fixture();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut o = Observer::default();
    let mut s = ObservedSession::new(options, &mut o);
    let nominal = m
        .nominal_type_reachability_observed(&mut s, site())
        .unwrap();
    let out = validate_handle_foreign_declarations_observed(
        &m,
        &r,
        &nominal,
        ImportPolicy::Refuse,
        &mut s,
        site(),
    )
    .unwrap();
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    nominal.retire_observed(&mut s, site()).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    let (_, _, begin, _) = run(&m, &r, ImportPolicy::Refuse);
    let mut o = Observer {
        stop: Some(begin + 1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let nominal = m
        .nominal_type_reachability_observed(&mut s, site())
        .unwrap();
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
        validate_handle_foreign_declarations_observed(
            &m,
            &r,
            &nominal,
            ImportPolicy::Refuse,
            &mut s,
            site()
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "original foreign stop");
    let _ = nominal.retire_observed(&mut s, site());
}
#[test]
fn actual_missing_sealed_outcome_branch_observes_and_can_refuse_before_diagnostic_publication() {
    let (m, r) = fixture();
    let a = crate::linked::AuthenticatedImports::default();
    let (_, baseline, begin, end) = run(&m, &r, ImportPolicy::Authenticated(&a));
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let nominal = m
            .nominal_type_reachability_observed(&mut s, site())
            .unwrap();
        assert_eq!(
            validate_handle_foreign_declarations_observed(
                &m,
                &r,
                &nominal,
                ImportPolicy::Authenticated(&a),
                &mut s,
                site()
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        let _ = nominal.retire_observed(&mut s, site());
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
    }
}
