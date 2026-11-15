// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
mod custody;
#[test]
fn every_actual_callback_refuses_without_partial_diagnostics_and_keeps_the_original_cause() {
    let mut module = module();
    module.functions[0].blocks.truncate(1);
    module.functions[0].blocks[0].body = vec![branch(0, &[0, 1])];
    seal(
        &mut module,
        vec![SourceLoopProvenance {
            source_loop_id: 0,
            hir_local_id: 10,
            header: BlockId::new(0),
            bindings: vec![binding(
                "arg",
                100,
                SourcePlace::FunctionParameter { index: 0 },
            )],
        }],
    );
    let missing = Module::new("missing");
    for context in [None, Some(&missing)] {
        let (_, baseline) = run(&module.functions[0], context);
        for stop in 1..=baseline.events.len() {
            let mut observer = Observer {
                stop: Some(stop),
                ..Observer::default()
            };
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            assert_eq!(
                validate_function_source_provenance_observed(
                    &module.functions[0],
                    context,
                    &mut session,
                    site()
                ),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(
                session.first_refusal().unwrap().cause,
                "original provenance stop"
            );
            assert_eq!(
                session.first_refusal().unwrap().progress,
                baseline.events[stop - 1]
            );
            assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
            assert!(
                observer
                    .events
                    .iter()
                    .skip(stop)
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn cumulative_work_and_copy_caps_span_calls_and_cannot_be_reset_after_refusal() {
    let module = module();
    let function = &module.functions[0];
    let mut measured = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut measured);
    for _ in 0..2 {
        assert_eq!(
            validate_function_source_provenance_observed(function, None, &mut session, site())
                .unwrap()
                .len(),
            1
        );
    }
    for bytes in [false, true] {
        let mut observer = Observer {
            work_cap: (!bytes).then_some(measured.work - 1),
            byte_cap: bytes.then_some(measured.bytes - 1),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            validate_function_source_provenance_observed(function, None, &mut session, site())
                .unwrap()
                .len(),
            1
        );
        assert_eq!(
            validate_function_source_provenance_observed(function, None, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = session.first_refusal().unwrap().progress;
        assert_eq!(
            validate_function_source_provenance_observed(function, None, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(session.first_refusal().unwrap().progress, first);
        assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    }
}
#[test]
fn initial_header_refusal_precedes_any_digest_cfg_or_source_traversal() {
    let module = module();
    let mut observer = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_function_source_provenance_observed(
            &module.functions[0],
            Some(&module),
            &mut session,
            site()
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "bytes");
    assert_eq!(observer.events.len(), 1);
}
#[test]
fn actual_global_name_comparison_stops_inside_equal_prefix_without_an_accepting_binding_result() {
    let function = function();
    let old_name = format!("{}a", "λ".repeat(3000));
    let new_name = format!("{}b", "λ".repeat(3000));
    let source = SourceLoopProvenance {
        source_loop_id: 0,
        hir_local_id: 10,
        header: BlockId::new(1),
        bindings: vec![binding(
            &new_name,
            500,
            SourcePlace::FunctionParameter { index: 0 },
        )],
    };
    let mut state = State {
        global_names: vec![(500, old_name.as_str(), (0, 0, 0))],
        global_places: vec![((0, 0, 0), 500)],
        ..State::default()
    };
    let mut observer = Observer {
        work_cap: Some(1500),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    assert_eq!(
        state.bindings(
            161,
            &source,
            Some(&function.blocks[0]),
            &function.blocks[1],
            &mut work
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(work.session.first_refusal().unwrap().cause, "work");
    assert_eq!(work.session.first_refusal().unwrap().progress.work, 1024);
    assert_eq!(state.global_names[0].1, old_name);
    assert_eq!(state.local_hir, vec![500]);
    assert!(state.errors.is_empty() && state.detail.is_empty());
    retire(&mut state, &mut work);
    assert!(empty(&state));
    assert!(
        observer
            .events
            .iter()
            .filter(|e| e.phase == ExecutionPhase::Validation
                && e.work == 1024
                && e.copy_bytes == 0)
            .count()
            >= 2
    );
}
#[test]
fn real_wide_switch_case_collection_refuses_inside_the_natural_backedge_helper() {
    let mut function = function();
    function.blocks[2].body = vec![node(Inst::Switch {
        value: v(4),
        default: BlockId::new(1),
        default_args: vec![],
        exhaustive_enum_unreachable: false,
        cases: (0..5000)
            .map(|value| SwitchCase {
                value: Constant::Int(value),
                target: BlockId::new(3),
                args: vec![],
            })
            .collect(),
    })];
    let mut setup = Observer::default();
    let mut setup_session = ObservedSession::new(InterpretOptions::default(), &mut setup);
    let tree = DominatorTree::new_observed(&function, &mut setup_session, site()).unwrap();
    let mut state = State {
        dominators: Some(tree),
        ..State::default()
    };
    let mut observer = Observer {
        work_cap: Some(2000),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    assert_eq!(
        state.backedge(&function, BlockId::new(1), &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(state.dominators.is_some());
    assert!(state.errors.is_empty());
    assert_eq!(work.session.first_refusal().unwrap().cause, "work");
    retire(&mut state, &mut work);
    assert!(empty(&state));
    assert!(
        observer
            .events
            .iter()
            .filter(|e| e.phase == ExecutionPhase::Validation)
            .count()
            > 20
    );
}
#[test]
fn unsupported_semantic_payload_is_operational_refusal_and_consumes_prior_diagnostics() {
    let mut module = module();
    module.types.push(Ty::Error);
    module.functions[0]
        .source_provenance
        .as_mut()
        .unwrap()
        .schema = 2;
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        state.walk(&module.functions[0], Some(&module), &mut work),
        Err(ObservedValueError::UnsupportedValue)
    );
    assert_eq!(state.errors.len(), 2);
    assert!(state.dominators.is_none());
    assert!(work.session.first_refusal().is_none());
    retire(&mut state, &mut work);
    assert!(empty(&state));
    assert!(work.session.first_refusal().is_none());
    assert!(
        observer
            .events
            .iter()
            .any(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
    // Without sticky admission refusal, generic290a cleanup may finish with
    // zero-cost Publication. That publishes no full validator result.
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_function_source_provenance_observed(
            &module.functions[0],
            Some(&module),
            &mut session,
            site()
        ),
        Err(ObservedValueError::UnsupportedValue)
    );
    assert!(session.first_refusal().is_none());
}
