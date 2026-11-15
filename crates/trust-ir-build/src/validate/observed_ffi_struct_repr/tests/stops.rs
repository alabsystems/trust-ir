// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

#[test]
fn every_public_callback_refuses_with_the_same_entry_and_original_first_cause() {
    let module = fixture();
    let function = function(9, "varargλ", CallingConv::Rust, Linkage::External, false);
    for rule in [Rule::Ffi, Rule::Vararg] {
        let (_, base) = run(&module, &function, rule);
        for stop in 1..=base.events.len() {
            let mut observer = Observer {
                stop: Some(stop),
                ..Observer::default()
            };
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            assert_eq!(
                call(&module, &function, rule, &mut session),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(session.first_refusal().unwrap().cause, "original ABI stop");
            assert_eq!(
                session.first_refusal().unwrap().progress,
                base.events[stop - 1]
            );
            assert!(
                observer
                    .events
                    .iter()
                    .skip(stop)
                    .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn original_work_and_copy_budgets_cumulate_across_complete_calls_without_reset() {
    let module = fixture();
    let function = function(9, "varargλ", CallingConv::Rust, Linkage::External, false);
    for rule in [Rule::Ffi, Rule::Vararg] {
        let (_, base) = run(&module, &function, rule);
        for bytes in [false, true] {
            let mut observer = Observer {
                work_cap: (!bytes).then_some(base.work),
                byte_cap: bytes.then_some(base.bytes),
                ..Observer::default()
            };
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            call(&module, &function, rule, &mut session).unwrap();
            assert_eq!(
                call(&module, &function, rule, &mut session),
                Err(ObservedValueError::AdmissionRefused)
            );
            let first = session.first_refusal().unwrap().progress;
            assert_eq!(
                call(&module, &function, rule, &mut session),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(session.first_refusal().unwrap().progress, first);
            assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
        }
    }
}
#[test]
fn initial_header_and_final_publication_refuse_without_partial_result_escape() {
    let module = fixture();
    let function = function(9, "varargλ", CallingConv::Rust, Linkage::External, false);
    for rule in [Rule::Ffi, Rule::Vararg] {
        let mut observer = Observer {
            byte_cap: Some(0),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            call(&module, &function, rule, &mut session),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(observer.events.len(), 1);
        let (_, base) = run(&module, &function, rule);
        let stop = base.events.len();
        let mut observer = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            call(&module, &function, rule, &mut session),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().progress.phase,
            ExecutionPhase::Publication
        );
        assert!(observer.events.len() > stop);
        assert!(
            observer
                .events
                .iter()
                .skip(stop)
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn preexisting_original_stop_prevents_input_walks_without_replacing_cause() {
    let module = fixture();
    let function = function(9, "varargλ", CallingConv::Rust, Linkage::External, false);
    let mut observer = Observer {
        stop: Some(1),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let first = ExecutionProgress {
        phase: ExecutionPhase::ModuleLookup,
        site: site(),
        work: 7,
        copy_bytes: 0,
    };
    assert!(session.admit(first).is_err());
    for rule in [Rule::Ffi, Rule::Vararg] {
        assert_eq!(
            call(&module, &function, rule, &mut session),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(session.first_refusal().unwrap().progress, first);
    }
    assert_eq!(observer.events, vec![first]);
}
#[test]
fn repr_collection_refuses_interior_before_any_function_or_name_work() {
    let mut module = fixture();
    module.structs = (0..500).map(|id| strukt(id, StructRepr::Rust)).collect();
    let function = &module.functions[0];
    let mut observer = Observer {
        work_cap: Some(100),
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
    assert!(!state.reprs.is_empty() && state.reprs.len() < 500);
    assert!(state.errors.is_empty());
    assert_eq!(state.name.capacity(), 0);
    drain(&mut state, &mut work);
    assert!(empty(&state));
}
#[test]
fn actual_reverse_repr_lookup_can_stop_after_complete_collection_before_diagnostics() {
    let mut module = fixture();
    module.structs = (0..200).map(|id| strukt(id, StructRepr::Rust)).collect();
    module.func_types[0] =
        trust_ir::FuncTy::unrecorded(vec![Ty::Struct(StructId::new(0))], vec![], false);
    let function = &module.functions[0];
    let base = private_trace(&module, function, Rule::Ffi);
    let first = base
        .events
        .iter()
        .position(|event| {
            event.phase == ExecutionPhase::Validation
                && event.work == 1
                && event.copy_bytes == size_of::<ValidationError>()
        })
        .unwrap()
        + 1;
    assert!(first > 100);
    // Two hundred reverse rows supply >600 real lookup callbacks before the
    // first error reserve. This stop is inside lookup, after all collection.
    let stop = first - 100;
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
    assert_eq!(state.reprs.len(), 200);
    assert!(state.errors.is_empty());
    drain(&mut state, &mut work);
    assert!(empty(&state));
}
#[test]
fn typed_private_state_refusal_is_not_an_accepting_empty_diagnostic_list() {
    let module = fixture();
    let function = &module.functions[0];
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State {
        name: "retained".repeat(1000),
        ..State::default()
    };
    let result = raw(&mut state, &module, function, Rule::Ffi, &mut work);
    assert_eq!(result, Err(ObservedValueError::InvalidRange));
    assert_eq!(
        state.finish(result, &mut work),
        Err(ObservedValueError::InvalidRange)
    );
    assert!(empty(&state));
    assert!(work.session.first_refusal().is_none());
    // Generic cleanup may publish only its own terminal zero-cost receipt.
    assert!(
        !observer
            .events
            .iter()
            .any(|e| e.phase == ExecutionPhase::Publication
                && e.copy_bytes == size_of::<Vec<ValidationError>>())
    );
}
#[test]
fn supplied_instruction_site_and_zero_execution_fuel_remain_the_original_context() {
    let module = fixture();
    let function = function(9, "varargλ", CallingConv::Rust, Linkage::External, false);
    let exact = ExecutionSite::Instruction(trust_ir::interpret::InstructionSite {
        function: FuncId::new(7),
        block: BlockId::new(8),
        instruction_index: 99,
    });
    for rule in [Rule::Ffi, Rule::Vararg] {
        let mut observer = Observer::default();
        let mut session = ObservedSession::new(
            InterpretOptions {
                fuel: 0,
                ..InterpretOptions::default()
            },
            &mut observer,
        );
        let out = match rule {
            Rule::Ffi => {
                validate_module_ffi_struct_repr_observed(&module, &mut session, exact).unwrap()
            }
            Rule::Vararg => validate_function_rust_abi_is_not_variadic_observed(
                &module,
                &function,
                &mut session,
                exact,
            )
            .unwrap(),
        };
        assert_eq!(out, oracle(&module, &function, rule));
        assert_eq!(session.remaining_fuel(), 0);
        assert!(observer.events.iter().all(|event| event.site == exact));
    }
}
