// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_return_lookup_equality_display_and_publication_callback_refuses() {
    let (m, f) = fixture();
    let inst = Inst::Return {
        values: vec![v(0), v(1), v(99)],
    };
    let (_, baseline, begin, end) = run(&m, &f, &inst);
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (values, signature) = setup(&m, &f, &mut s);
        assert_eq!(
            validate_return_instruction_observed(
                &inst,
                signature,
                &values,
                f.entry,
                &mut s,
                site()
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        let _ = values.retire_observed(&mut s, site());
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
fn every_success_and_missing_signature_getter_callback_refuses_without_semantic_absence() {
    let (m, base) = fixture();
    for missing in [false, true] {
        let mut f = base.clone();
        if missing {
            f.ty = FuncTyId::new(99);
        }
        let (_, baseline, end) = getter(&m, &f);
        for cut in 1..=end {
            let mut o = Observer {
                stop: Some(cut),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                function_signature_observed(&m, &f, &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(
                s.first_refusal().unwrap().cause,
                "original return rule stop"
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
}
#[test]
fn repeated_return_queries_share_original_cumulative_work_and_copy_budgets() {
    let (m, f) = fixture();
    let inst = Inst::Return {
        values: vec![v(0), v(1)],
    };
    let (_, baseline, _, end) = run(&m, &f, &inst);
    for copy in [false, true] {
        let cap = baseline.events[..end]
            .iter()
            .map(|e| if copy { e.copy_bytes } else { e.work })
            .sum();
        let mut o = Observer::default();
        if copy {
            o.byte_cap = Some(cap)
        } else {
            o.work_cap = Some(cap)
        }
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (values, signature) = setup(&m, &f, &mut s);
        let first = validate_return_instruction_observed(
            &inst,
            signature,
            &values,
            f.entry,
            &mut s,
            site(),
        )
        .unwrap();
        assert_eq!(
            validate_return_instruction_observed(
                &inst,
                signature,
                &values,
                f.entry,
                &mut s,
                site()
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        let _ = retire_validation_errors_observed(first, &mut s, site());
        let _ = values.retire_observed(&mut s, site());
    }
}
#[test]
fn zero_fuel_and_preexisting_refusal_preserve_original_site_and_first_cause() {
    let (m, f) = fixture();
    let inst = Inst::Return {
        values: vec![v(1), v(0)],
    };
    let mut o = Observer::default();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut s = ObservedSession::new(options, &mut o);
    let (values, signature) = setup(&m, &f, &mut s);
    let out =
        validate_return_instruction_observed(&inst, signature, &values, f.entry, &mut s, site())
            .unwrap();
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    values.retire_observed(&mut s, site()).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    let mut o = Observer {
        stop: Some(1),
        cleanup_after: Some(1),
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
        function_signature_observed(&m, &f, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original return rule stop"
    );
}
