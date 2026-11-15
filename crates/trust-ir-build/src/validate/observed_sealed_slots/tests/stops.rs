// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn inputs<'m, O: ExecutionObserver>(
    m: &'m Module,
    s: &mut ObservedSession<'_, O>,
) -> (
    trust_ir::LayoutTable<'m>,
    trust_ir::ObservedNominalTypeReachability<'m>,
) {
    (
        trust_ir::LayoutTable::new_observed(m, s, site()).unwrap(),
        m.nominal_type_reachability_observed(s, site()).unwrap(),
    )
}
fn release_inputs<O: ExecutionObserver>(
    table: trust_ir::LayoutTable<'_>,
    nominal: trust_ir::ObservedNominalTypeReachability<'_>,
    s: &mut ObservedSession<'_, O>,
) {
    let _ = nominal.retire_observed(s, site());
    s.retirement_step(site(), size_of::<trust_ir::LayoutTable<'_>>() + 1);
    drop(table);
    s.retirement_poll(site());
}
#[test]
fn every_constructor_interior_and_final_publication_callback_refuses_and_drains() {
    let (m, base) = fixture();
    for altered in [false, true] {
        let mut f = base.clone();
        if altered {
            f.blocks[0]
                .body
                .insert(1, allocation(handle(), Some(v(0)), None, 10));
        }
        let (baseline, begin, end) = run(&m, &f);
        for cut in begin + 1..=end {
            let mut o = Observer {
                stop: Some(cut),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            let (table, nominal) = inputs(&m, &mut s);
            assert!(matches!(
                ObservedSealedHandleSlots::new_observed(&table, &f, &nominal, &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            ));
            assert_eq!(
                s.first_refusal().unwrap().cause,
                "original sealed analysis stop"
            );
            release_inputs(table, nominal, &mut s);
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
fn every_access_rule_callback_is_typed_operational_refusal_not_missing_analysis_fallback() {
    let (m, f) = fixture();
    for inst in [
        f.blocks[0].body[2].inst.clone(),
        Inst::Load {
            ty: handle(),
            ptr: v(99),
            volatile: false,
            align: None,
        },
    ] {
        let (_, baseline, begin, end) = access(&m, &f, &inst, &[v(20)], (f.entry, 2), true);
        for cut in begin + 1..=end {
            let mut o = Observer {
                stop: Some(cut),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            let (table, nominal, values, a) = setup(&m, &f, true, &mut s);
            assert_eq!(
                handle_slot_rule_observed(
                    &inst,
                    &[v(20)],
                    &values,
                    f.entry,
                    2,
                    a.as_ref(),
                    &mut s,
                    site()
                ),
                Err(ObservedValueError::AdmissionRefused)
            );
            dispose(table, nominal, values, a, &mut s);
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
fn allocation_predicate_preserves_early_true_and_observes_each_actual_callback() {
    let (m, f) = fixture();
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let (table, nominal) = inputs(&m, &mut s);
    let begin = calls.get();
    assert!(
        ObservedSealedHandleSlots::function_allocates_a_handle_observed(
            &f,
            &nominal,
            &mut s,
            site()
        )
        .unwrap()
    );
    let end = calls.get();
    release_inputs(table, nominal, &mut s);
    drop(s);
    let mut longer = f.clone();
    for _ in 0..50 {
        longer.blocks[0]
            .body
            .push(InstrNode::new(Inst::Unreachable));
    }
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (table, nominal) = inputs(&m, &mut s);
    assert!(
        ObservedSealedHandleSlots::function_allocates_a_handle_observed(
            &longer,
            &nominal,
            &mut s,
            site()
        )
        .unwrap()
    );
    release_inputs(table, nominal, &mut s);
    drop(s);
    assert_eq!(&o.events[..end], &baseline.events[..end]);
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (table, nominal) = inputs(&m, &mut s);
        assert_eq!(
            ObservedSealedHandleSlots::function_allocates_a_handle_observed(
                &f,
                &nominal,
                &mut s,
                site()
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        release_inputs(table, nominal, &mut s);
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
    }
}
#[test]
fn cumulative_original_work_and_copy_budgets_cover_repeated_construction_without_regrant() {
    let (m, f) = fixture();
    let (baseline, _, end) = run(&m, &f);
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
        let (table, nominal) = inputs(&m, &mut s);
        let first =
            ObservedSealedHandleSlots::new_observed(&table, &f, &nominal, &mut s, site()).unwrap();
        assert!(matches!(
            ObservedSealedHandleSlots::new_observed(&table, &f, &nominal, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
        let _ = first.retire_observed(&mut s, site());
        release_inputs(table, nominal, &mut s);
    }
}
#[test]
fn cumulative_rule_queries_hold_original_analysis_and_refuse_without_semantic_result() {
    let (m, f) = fixture();
    let inst = &f.blocks[0].body[2].inst;
    let (_, baseline, _, end) = access(&m, &f, inst, &[v(20)], (f.entry, 2), true);
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
        let (table, nominal, values, a) = setup(&m, &f, true, &mut s);
        assert_eq!(
            handle_slot_rule_observed(
                inst,
                &[v(20)],
                &values,
                f.entry,
                2,
                a.as_ref(),
                &mut s,
                site()
            )
            .unwrap(),
            Ok(())
        );
        assert_eq!(
            handle_slot_rule_observed(
                inst,
                &[v(20)],
                &values,
                f.entry,
                2,
                a.as_ref(),
                &mut s,
                site()
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        dispose(table, nominal, values, a, &mut s);
    }
}
#[test]
fn zero_fuel_and_preexisting_refusal_keep_the_original_site_and_first_cause() {
    let (m, f) = fixture();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut o = Observer::default();
    let mut s = ObservedSession::new(options, &mut o);
    let (table, nominal) = inputs(&m, &mut s);
    let a = ObservedSealedHandleSlots::new_observed(&table, &f, &nominal, &mut s, site()).unwrap();
    a.retire_observed(&mut s, site()).unwrap();
    release_inputs(table, nominal, &mut s);
    assert_eq!(s.remaining_fuel(), 0);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    let (_, begin, _) = run(&m, &f);
    let mut o = Observer {
        stop: Some(begin + 1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (table, nominal) = inputs(&m, &mut s);
    assert!(
        s.admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site: site(),
            work: 1,
            copy_bytes: 0
        })
        .is_err()
    );
    assert!(matches!(
        ObservedSealedHandleSlots::new_observed(&table, &f, &nominal, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    ));
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original sealed analysis stop"
    );
    release_inputs(table, nominal, &mut s);
}
#[test]
fn normal_refusal_survives_all_cleanup_refusals_with_no_partial_analysis_publication() {
    let (m, f) = fixture();
    let (_, begin, end) = run(&m, &f);
    let cut = begin + (end - begin) / 2;
    let mut o = Observer {
        stop: Some(cut),
        cleanup_after: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (table, nominal) = inputs(&m, &mut s);
    assert!(matches!(
        ObservedSealedHandleSlots::new_observed(&table, &f, &nominal, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    ));
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original sealed analysis stop"
    );
    release_inputs(table, nominal, &mut s);
    drop(s);
    assert!(
        o.events[cut..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
