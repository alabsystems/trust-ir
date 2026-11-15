// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

#[test]
fn pending_full_ffi_name_survives_distinct_error_reserve_and_move_refusals() {
    let mut module = fixture();
    module.functions.truncate(1);
    module.func_types[0] =
        trust_ir::FuncTy::unrecorded(vec![Ty::Struct(StructId::new(1))], vec![], false);
    let function = &module.functions[0];
    let base = private_trace(&module, function, Rule::Ffi);
    let positions = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 1
                && e.copy_bytes == size_of::<ValidationError>()
        })
        .map(|(i, _)| i + 1)
        .collect::<Vec<_>>();
    assert_eq!(positions.len(), 2);
    for (n, stop) in positions.into_iter().enumerate() {
        let mut observer = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let mut work = Work {
            session: &mut session,
            site: site(),
        };
        let mut state = State::default();
        assert_eq!(
            raw(&mut state, &module, function, Rule::Ffi, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(state.name, function.name);
        assert!(state.errors.is_empty());
        assert_eq!(state.errors.capacity() == 0, n == 0);
        assert_eq!(
            work.session.first_refusal().unwrap().progress,
            base.events[stop - 1]
        );
        drain(&mut state, &mut work);
        assert!(empty(&state));
    }
}
#[test]
fn pending_full_vararg_detail_survives_error_allocation_and_distinct_header_move() {
    let module = fixture();
    let function = function(9, "name'λ\n", CallingConv::Rust, Linkage::Private, true);
    let expected = oracle(&module, &function, Rule::Vararg);
    let detail = match &expected[0] {
        ValidationError::RustAbiVararg { detail, .. } => detail,
        _ => unreachable!(),
    };
    let base = private_trace(&module, &function, Rule::Vararg);
    let positions = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 1
                && [
                    size_of::<ValidationError>(),
                    size_of::<ValidationError>() + size_of::<u32>(),
                ]
                .contains(&e.copy_bytes)
        })
        .map(|(i, _)| i + 1)
        .collect::<Vec<_>>();
    assert_eq!(positions.len(), 2);
    for (n, stop) in positions.into_iter().enumerate() {
        let mut observer = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let mut work = Work {
            session: &mut session,
            site: site(),
        };
        let mut state = State::default();
        assert_eq!(
            raw(&mut state, &module, &function, Rule::Vararg, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(&state.detail, detail);
        assert!(state.errors.is_empty());
        assert_eq!(state.errors.capacity() == 0, n == 0);
        drain(&mut state, &mut work);
        assert!(empty(&state));
    }
}
#[test]
fn interior_raw_name_copy_refusal_retains_the_actual_first_utf8_chunk() {
    let mut module = fixture();
    module.functions.truncate(1);
    module.functions[0].name = "λ".repeat(3000);
    module.func_types[0] =
        trust_ir::FuncTy::unrecorded(vec![Ty::Struct(StructId::new(1))], vec![], false);
    let function = &module.functions[0];
    let base = private_trace(&module, function, Rule::Ffi);
    let positions = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation && e.work == 1024 && e.copy_bytes == 1024
        })
        .map(|(i, _)| i + 1)
        .collect::<Vec<_>>();
    // First reserve and first actual copy are consecutive identical-shaped
    // events. Third match is the second actual copy. If capacity must grow,
    // its separate image charge is 4096 (3072 requested plus 1024 old bytes).
    // An allocator may have supplied spare capacity on the first reserve.
    assert_eq!(positions[1], positions[0] + 1);
    let stop = positions[2];
    let previous = base.events[stop - 2];
    let grew = previous.work == 4096 && previous.copy_bytes == 4096;
    assert!(grew || (previous.work == 1 && previous.copy_bytes == 0));
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        raw(&mut state, &module, function, Rule::Ffi, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.name, "λ".repeat(512));
    assert!(state.name.capacity() >= if grew { 3072 } else { 2048 });
    assert!(state.errors.is_empty());
    drain(&mut state, &mut work);
    assert!(empty(&state));
}
#[test]
fn interior_actual_debug_scalar_refusal_retains_owned_detail_prefix() {
    let module = fixture();
    let function = function(9, "beforeλafter", CallingConv::Rust, Linkage::Private, true);
    let base = private_trace(&module, &function, Rule::Vararg);
    let stop = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 8 * u32::BITS as usize
                && e.copy_bytes == size_of::<core::char::EscapeDebug>()
        })
        .nth(3)
        .unwrap()
        .0
        + 1;
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        raw(&mut state, &module, &function, Rule::Vararg, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.detail, "\"bef");
    assert_eq!(state.name.capacity(), 0);
    assert!(state.errors.is_empty());
    drain(&mut state, &mut work);
    assert!(empty(&state));
}
#[test]
fn later_output_move_refusal_retains_both_prior_diagnostic_and_pending_full_name() {
    let module = fixture();
    let function = &module.functions[0];
    let base = private_trace(&module, function, Rule::Ffi);
    let stop = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 1
                && e.copy_bytes == size_of::<ValidationError>()
        })
        .nth(2)
        .unwrap()
        .0
        + 1;
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        raw(&mut state, &module, function, Rule::Ffi, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.errors, oracle(&module, function, Rule::Ffi)[..1]);
    assert_eq!(state.name, function.name);
    assert_eq!(state.reprs.len(), module.structs.len());
    drain(&mut state, &mut work);
    assert!(empty(&state));
}
#[test]
fn cleanup_refusal_still_consumes_all_repr_rows_partial_strings_and_completed_errors() {
    let module = fixture();
    let function = &module.functions[0];
    let arm = Rc::new(Cell::new(false));
    let mut observer = Observer {
        cleanup: Some(arm.clone()),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    raw(&mut state, &module, function, Rule::Ffi, &mut work).unwrap();
    assert_eq!(state.errors.len(), 6);
    state.name = "pending-name".repeat(1000);
    state.detail = "pending-detail".repeat(1000);
    arm.set(true);
    drain(&mut state, &mut work);
    assert!(empty(&state));
    assert_eq!(work.session.first_refusal().unwrap().cause, "cleanup");
    assert_eq!(
        work.publication(1, size_of::<Vec<ValidationError>>()),
        Err(ObservedValueError::AdmissionRefused)
    );
}
