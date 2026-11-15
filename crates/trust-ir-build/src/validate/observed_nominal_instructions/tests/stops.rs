// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_census_child_rule_error_and_publication_callback_refuses_without_partial_output() {
    let (m, f) = fixture();
    for inst in [
        Inst::Copy {
            ty: Ty::Bool,
            operand: v(0),
        },
        Inst::MakeAggregate {
            ty: mixed(),
            variant: None,
            fields: vec![v(1), v(2)],
        },
        Inst::Load {
            ty: handle(),
            ptr: v(4),
            volatile: false,
            align: None,
        },
    ] {
        let node = InstrNode::new(inst);
        let (_, baseline, begin, end) = run(&m, &f, &node, (f.entry, 3), false, false, "λ raw");
        for cut in begin + 1..=end {
            let mut o = Observer {
                stop: Some(cut),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            let (table, nominal, values, guards, slots) = setup(&m, &f, false, false, &mut s);
            assert_eq!(
                validate_nominal_instruction_types_observed(
                    &m,
                    &node,
                    &values,
                    &nominal,
                    f.entry,
                    3,
                    guards.as_ref(),
                    slots.as_ref(),
                    "λ raw",
                    &mut s,
                    site()
                ),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(
                s.first_refusal().unwrap().cause,
                "original nominal instruction stop"
            );
            dispose(table, nominal, values, guards, slots, &mut s);
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
fn repeated_rule_calls_share_cumulative_original_work_and_copy_without_regrant() {
    let (m, f) = fixture();
    let node = InstrNode::new(Inst::Undef { ty: handle() });
    let (_, baseline, _, end) = run(&m, &f, &node, (f.entry, 3), false, false, "L");
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
        let (table, nominal, values, guards, slots) = setup(&m, &f, false, false, &mut s);
        let out = validate_nominal_instruction_types_observed(
            &m,
            &node,
            &values,
            &nominal,
            f.entry,
            3,
            None,
            None,
            "L",
            &mut s,
            site(),
        )
        .unwrap();
        assert_eq!(out.len(), 1);
        assert_eq!(
            validate_nominal_instruction_types_observed(
                &m,
                &node,
                &values,
                &nominal,
                f.entry,
                3,
                None,
                None,
                "L",
                &mut s,
                site()
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        let _ = retire_validation_errors_observed(out, &mut s, site());
        dispose(table, nominal, values, guards, slots, &mut s);
    }
}
#[test]
fn zero_fuel_and_preexisting_first_cause_keep_original_session_and_request_site() {
    let (m, f) = fixture();
    let node = InstrNode::new(Inst::Return {
        values: vec![v(1), v(2)],
    });
    let mut o = Observer::default();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut s = ObservedSession::new(options, &mut o);
    let (table, nominal, values, guards, slots) = setup(&m, &f, false, false, &mut s);
    let out = validate_nominal_instruction_types_observed(
        &m,
        &node,
        &values,
        &nominal,
        f.entry,
        3,
        None,
        None,
        "L",
        &mut s,
        site(),
    )
    .unwrap();
    assert!(out.is_empty());
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    dispose(table, nominal, values, guards, slots, &mut s);
    assert_eq!(s.remaining_fuel(), 0);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    let (_, _, begin, _) = run(&m, &f, &node, (f.entry, 3), false, false, "L");
    let mut o = Observer {
        stop: Some(begin + 1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (table, nominal, values, guards, slots) = setup(&m, &f, false, false, &mut s);
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
        validate_nominal_instruction_types_observed(
            &m,
            &node,
            &values,
            &nominal,
            f.entry,
            3,
            None,
            None,
            "L",
            &mut s,
            site()
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original nominal instruction stop"
    );
    dispose(table, nominal, values, guards, slots, &mut s);
}
#[test]
fn child_operational_refusal_is_never_semantic_missing_slot_and_survives_cleanup_failures() {
    let (m, f) = fixture();
    let node = InstrNode::new(Inst::Load {
        ty: handle(),
        ptr: v(4),
        volatile: false,
        align: None,
    });
    let (_, baseline, begin, end) = run(&m, &f, &node, (f.entry, 3), false, false, "L");
    let cut = begin + (end - begin) / 2;
    let mut o = Observer {
        stop: Some(cut),
        cleanup_after: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (table, nominal, values, guards, slots) = setup(&m, &f, false, false, &mut s);
    assert_eq!(
        validate_nominal_instruction_types_observed(
            &m,
            &node,
            &values,
            &nominal,
            f.entry,
            3,
            None,
            None,
            "L",
            &mut s,
            site()
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original nominal instruction stop"
    );
    dispose(table, nominal, values, guards, slots, &mut s);
    drop(s);
    assert_eq!(&o.events[..cut], &baseline.events[..cut]);
    assert!(
        o.events[cut..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
