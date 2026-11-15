// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn complete_actual_catalog_ids_are_held_before_first_parent_read() {
    let m = module(&[9, 1, 9, 1, 9]);
    let catalog = ModuleFunctionCatalog::new(&m);
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let ids = catalog.ambiguous_ids_observed(&mut s, site()).unwrap();
    assert_eq!(ids, vec![1, 9]);
    let mut state = State {
        ids,
        ..Default::default()
    };
    arm.set(true);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    assert_eq!(
        state.emit_functions(&mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.ids, vec![1, 9]);
    assert!(state.errors.is_empty());
    drain(&mut state, &mut w);
    empty(&state);
}
#[test]
fn actual_copy_ids_stay_owned_at_preallocation_and_pretransport_refusals() {
    for cut in [3, 4] {
        let mut o = Observer {
            stop: Some(cut),
            ..Default::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State {
            ids: vec![1, 9],
            ..Default::default()
        };
        assert_eq!(
            state.emit_functions(&mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(state.ids, vec![1, 9]);
        assert_eq!(state.errors.capacity() == 0, cut == 3);
        drain(&mut state, &mut w);
        empty(&state);
    }
}
#[test]
fn prior_function_errors_and_remaining_full_id_vector_survive_later_interior_stop() {
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State {
        ids: vec![1, 9],
        ..Default::default()
    };
    state.emit_functions(&mut w).unwrap();
    let end = calls.get();
    drain(&mut state, &mut w);
    let mut seen = false;
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Default::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State {
            ids: vec![1, 9],
            ..Default::default()
        };
        assert_eq!(
            state.emit_functions(&mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        if state.errors == vec![ValidationError::DuplicateFuncId(1)] {
            seen = true;
            assert_eq!(state.ids, vec![1, 9]);
        }
        drain(&mut state, &mut w);
        empty(&state);
    }
    assert!(seen);
}
#[test]
fn whole_successful_output_and_existing_catalog_remain_caller_owned_until_consumed() {
    let m = module(&[3, 3]);
    let catalog = ModuleFunctionCatalog::new(&m);
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        cleanup: Some(arm.clone()),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let errors = validate_module_function_ids_observed(&catalog, &mut s, site()).unwrap();
    assert_eq!(errors, vec![ValidationError::DuplicateFuncId(3)]);
    assert!(catalog.unique(FuncId::new(3)).is_none());
    arm.set(true);
    assert_eq!(
        retire_validation_errors_observed(errors, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    let _ = catalog.retire_observed(&mut s, site());
    assert_eq!(s.first_refusal().unwrap().cause, "cleanup");
    assert_eq!(
        validate_module_struct_ids_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
}
