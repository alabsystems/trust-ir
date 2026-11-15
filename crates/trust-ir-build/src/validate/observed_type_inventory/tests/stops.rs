// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_source_walk_child_aggregation_and_publication_callback_can_stop() {
    let mut m = Module::new("");
    m.types = vec![Ty::Tuple(vec![d(), invalid()])];
    let (_, baseline, bound) = run(&m);
    let r = registry();
    for cut in 1..=bound {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_type_table_references_observed(&m, &r, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(s.first_refusal().is_some());
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
fn empty_whole_inventory_cannot_return_default_census_after_refusal() {
    let m = Module::new("");
    let r = registry();
    let (_, _, bound) = run(&m);
    for cut in 1..=bound {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_type_table_references_observed(&m, &r, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
    }
}
#[test]
fn successive_whole_inventories_and_caller_retirement_share_cumulative_limits() {
    let m = fixture();
    let r = registry();
    let (_, baseline, _) = run(&m);
    for copy in [false, true] {
        let mut o = Observer::default();
        if copy {
            o.byte_cap = Some(baseline.bytes + 1)
        } else {
            o.work_cap = Some(baseline.work + 1)
        }
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (out, _) = validate_type_table_references_observed(&m, &r, &mut s, site()).unwrap();
        retire_validation_errors_observed(out, &mut s, site()).unwrap();
        assert_eq!(
            validate_type_table_references_observed(&m, &r, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(s.first_refusal().is_some());
    }
}
#[test]
fn final_whole_tuple_publication_cannot_leak_partial_census_or_prior_diagnostics() {
    let m = fixture();
    let r = registry();
    let (_, baseline, bound) = run(&m);
    assert_eq!(
        baseline.events[bound - 1].copy_bytes,
        size_of::<(Vec<ValidationError>, NominalCensus)>()
    );
    let mut o = Observer {
        stop: Some(bound),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_type_table_references_observed(&m, &r, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    drop(s);
    assert!(o.events.len() > bound);
    assert!(
        o.events[bound..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn original_site_and_zero_interpreter_fuel_are_preserved_through_all_children() {
    let m = fixture();
    let r = registry();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut o = Observer::default();
    let mut s = ObservedSession::new(options, &mut o);
    let (out, c) = validate_type_table_references_observed(&m, &r, &mut s, site()).unwrap();
    assert!(c.dialect && c.handle);
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
}
#[test]
fn already_latched_stop_is_not_replaced_or_granted_a_new_scope() {
    let m = fixture();
    let r = registry();
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
        validate_type_table_references_observed(&m, &r, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original type inventory stop"
    );
    drop(s);
    assert_eq!(o.events.len(), 1);
}
#[test]
fn raw_large_function_location_copy_can_stop_inside_actual_utf8_chunks() {
    let mut m = Module::new("");
    m.functions.push(function(
        &"λ\0尾".repeat(1500),
        vec![Inst::Undef { ty: d() }],
        vec![],
    ));
    let r = registry();
    let (_, baseline, _) = run(&m);
    let cut = baseline
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work >= 1021
                && e.work <= 1024
                && e.copy_bytes == e.work
        })
        .nth(3)
        .unwrap()
        .0
        + 1;
    let mut o = Observer {
        stop: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_type_table_references_observed(&m, &r, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    drop(s);
    assert_eq!(&o.events[..cut], &baseline.events[..cut]);
}
#[test]
fn even_empty_root_buffer_retirement_refusal_prevents_later_attribute_work() {
    let m = Module::new("");
    let r = registry();
    let mut op = DialectInst::new("unread", "unread");
    op.attrs.push(AttrEntry {
        name: "typed".into(),
        value: AttrValue::Ty(invalid()),
    });
    let inst = Inst::DialectOp(Box::new(op));
    let mut o = Observer {
        cleanup_after: Some(0),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        state.instruction(&m, &r, &inst, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.census, NominalCensus::default());
    assert!(state.errors.is_empty());
    drain(&mut state, &mut w);
    assert!(empty(&state));
}
