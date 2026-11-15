// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn cuts(m: &Module, r: Rule) {
    let (_, base, end) = run(m, r);
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Default::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            codegen_policy_errors_observed(m, r, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            "original codegen policy stop"
        );
        drop(s);
        assert_eq!(&o.events[..cut], &base.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn every_actual_gate_membership_copy_transport_cleanup_and_publication_refuses() {
    cuts(&fixture(), Rule::GateEvidence);
}
#[test]
fn every_actual_assert_kind_and_site_walk_copy_and_publication_refuses() {
    for r in [Rule::PanicKinds, Rule::PanicSites] {
        cuts(&fixture(), r);
    }
}
#[test]
fn every_actual_empty_and_global_asm_callback_refuses_without_a_prefix() {
    for r in rules() {
        cuts(&Module::new("empty"), r);
    }
    cuts(&fixture(), Rule::GlobalAsm);
}
#[test]
fn original_cumulative_work_copy_zero_instruction_fuel_and_interrupt_are_unchanged() {
    let m = fixture();
    for r in rules() {
        let (_, base, end) = run(&m, r);
        for copy in [false, true] {
            let cap = base.events[..end]
                .iter()
                .map(|e| if copy { e.copy_bytes } else { e.work })
                .sum();
            let mut o = Observer {
                work_cap: (!copy).then_some(cap),
                byte_cap: copy.then_some(cap),
                ..Default::default()
            };
            let mut options = InterpretOptions::default();
            options.fuel = 0;
            let mut s = ObservedSession::new(options, &mut o);
            let first = codegen_policy_errors_observed(&m, r, &mut s, site()).unwrap();
            assert_eq!(s.remaining_fuel(), 0);
            assert_eq!(
                codegen_policy_errors_observed(&m, r, &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(
                s.first_refusal().unwrap().cause,
                if copy { "copy" } else { "work" }
            );
            let _ = retire_validation_errors_observed(first, &mut s, site());
        }
        let mut o = Observer {
            arm: Some(Rc::new(Cell::new(true))),
            ..Default::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            codegen_policy_errors_observed(&m, r, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
    }
}
