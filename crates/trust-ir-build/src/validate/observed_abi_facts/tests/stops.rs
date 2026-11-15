// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn every(m: &Module, selected: impl Fn(&ExecutionProgress) -> bool) {
    let (_, base, begin, end) = run(m);
    let cuts: Vec<_> = (begin + 1..=end)
        .filter(|cut| selected(&base.events[cut - 1]))
        .collect();
    assert!(!cuts.is_empty());
    for cut in cuts {
        let mut o = Observer {
            stop: Some(cut),
            ..Default::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let t = LayoutTable::new_observed(m, &mut s, site()).unwrap();
        assert_eq!(
            validate_module_abi_facts_observed(&t, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().cause, "original ABI-group stop");
        dispose(t, &mut s);
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
fn every_actual_untyped_slot_cast_error_lane_context_and_final_callback_refuses() {
    every(&many_errors(), |_| true);
}
#[test]
fn recorded_group_parent_validation_cleanup_and_publication_cuts_refuse() {
    // Canonical wire child is separately exhaustive in its own suite. Here all
    // actual group Validation/Publication/retirement events retain the owner.
    let mut m = typed();
    m.functions[0].calling_conv = trust_ir::CallingConv::Fast;
    every(&m, |e| {
        matches!(
            e.phase,
            ExecutionPhase::Validation
                | ExecutionPhase::Publication
                | ExecutionPhase::ScratchRetirement
        )
    });
}
#[test]
fn second_whole_group_cannot_renew_original_cumulative_work_or_copy() {
    let m = many_errors();
    let (_, base, _, end) = run(&m);
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
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let t = LayoutTable::new_observed(&m, &mut s, site()).unwrap();
        let errors = validate_module_abi_facts_observed(&t, &mut s, site()).unwrap();
        // Hold the first complete successful result while the same session runs
        // out on the second call. No caller disposal cost is skipped/refunded.
        assert_eq!(
            validate_module_abi_facts_observed(&t, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
        let _ = retire_validation_errors_observed(errors, &mut s, site());
        dispose(t, &mut s);
    }
}
#[test]
fn zero_instruction_fuel_stays_zero_and_preexisting_sticky_stop_never_accepts() {
    let m = many_errors();
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        interrupt: Some(arm.clone()),
        ..Default::default()
    };
    let mut opt = InterpretOptions::default();
    opt.fuel = 0;
    let mut s = ObservedSession::new(opt, &mut o);
    let t = LayoutTable::new_observed(&m, &mut s, site()).unwrap();
    let errors = validate_module_abi_facts_observed(&t, &mut s, site()).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
    arm.set(true);
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
        validate_module_abi_facts_observed(&t, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
    let _ = retire_validation_errors_observed(errors, &mut s, site());
    dispose(t, &mut s);
}
