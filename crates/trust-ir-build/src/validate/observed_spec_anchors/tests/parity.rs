// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn action_and_projection_rows_map_to_their_distinct_complete_build_variants() {
    let m = bad();
    let out = run(&m).0;
    assert_eq!(out.len(), 2);
    assert!(
        matches!(&out[0],ValidationError::InvalidSpecAnchorFunction {machine,action,function,detail} if machine=="M" && action=="a" && *function==u32::MAX && detail=="function id is not present in module \"moduleλ\"")
    );
    assert!(
        matches!(&out[1],ValidationError::InvalidSpecProjectionFunction {machine,action,function,detail} if machine=="M" && action=="a" && *function==u32::MAX && detail=="function id is not present in module \"moduleλ\"")
    );
}
#[test]
fn both_modes_valid_sparse_targets_and_body_name_signature_failures_keep_ordinary_parity() {
    for mode in [SpecEnforcementMode::DesignOnly, SpecEnforcementMode::Linked] {
        let mut m = fixture();
        m.spec_modules[0].enforcement = mode;
        m.functions.reverse();
        assert!(run(&m).0.is_empty());
        m.functions[0].name = "wrong".into();
        assert_eq!(run(&m).0.len(), 1);
        m.functions[0].blocks.clear();
        run(&m);
        m.functions[0].blocks.push(Block::new(BlockId::new(0)));
        m.functions[0].name = "project".into();
        m.func_types[0].params = vec![Ty::U8];
        run(&m);
    }
}
#[test]
fn original_filter_drops_other_rows_only_after_complete_same_owner_consumption() {
    let mut state = State {
        batch: Some(
            vec![
                row("action", "one"),
                row("unknown", "ignored"),
                SpecLinkViolation::MachineMissing {
                    machine: "owned".repeat(1000),
                    action: "a".repeat(1000),
                    from: "anchor",
                    detail: "ignored".repeat(1000),
                },
                row("projection", "two"),
            ]
            .into_iter(),
        ),
        ..State::default()
    };
    let mut o = Observer::default();
    let mut owner = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut owner,
        site: site(),
    };
    state.merge(&mut w).unwrap();
    assert_eq!(state.errors.len(), 2);
    assert!(
        matches!(&state.errors[0],ValidationError::InvalidSpecAnchorFunction {machine,..} if machine=="Mone")
    );
    assert!(
        matches!(&state.errors[1],ValidationError::InvalidSpecProjectionFunction {machine,..} if machine=="Mtwo")
    );
    let out = state.finish(Ok(()), &mut w).unwrap();
    assert_eq!(out.len(), 2);
    assert!(empty(&state));
    assert!(w.session.first_refusal().is_none());
}
#[test]
fn every_public_callback_for_empty_and_nonempty_batches_refuses_without_partial_output() {
    for m in [Module::new("empty"), bad()] {
        let (_, base) = run(&m);
        for stop in 1..=base.events.len() {
            let mut o = Observer {
                stop: Some(stop),
                ..Observer::default()
            };
            let mut owner = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                validate_spec_anchor_functions_observed(&m, &mut owner, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(
                owner.first_refusal().unwrap().progress,
                base.events[stop - 1]
            );
            assert!(
                o.events
                    .iter()
                    .skip(stop)
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn cumulative_work_and_copy_limits_stay_in_the_original_session_across_whole_calls() {
    let m = bad();
    let (_, base) = run(&m);
    for bytes in [false, true] {
        let mut o = Observer {
            work_cap: (!bytes).then_some(base.work),
            byte_cap: bytes.then_some(base.bytes),
            ..Observer::default()
        };
        let mut owner = ObservedSession::new(InterpretOptions::default(), &mut o);
        validate_spec_anchor_functions_observed(&m, &mut owner, site()).unwrap();
        assert_eq!(
            validate_spec_anchor_functions_observed(&m, &mut owner, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = owner.first_refusal().unwrap().progress;
        assert_eq!(
            validate_spec_anchor_functions_observed(&m, &mut owner, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(owner.first_refusal().unwrap().progress, first);
        assert_eq!(owner.remaining_fuel(), InterpretOptions::default().fuel);
    }
}
#[test]
fn first_header_and_final_publication_refusals_preserve_full_failure_and_zero_fuel_site() {
    let m = bad();
    let (_, base) = run(&m);
    for stop in [1, base.events.len()] {
        let mut o = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut owner = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_spec_anchor_functions_observed(&m, &mut owner, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            owner.first_refusal().unwrap().progress,
            base.events[stop - 1]
        );
    }
    let exact = ExecutionSite::Instruction(InstructionSite {
        function: FuncId::new(1),
        block: BlockId::new(2),
        instruction_index: usize::MAX,
    });
    let mut o = Observer::default();
    let mut owner = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    assert_eq!(
        validate_spec_anchor_functions_observed(&m, &mut owner, exact).unwrap(),
        super::super::super::validate_spec_anchor_functions(&m)
    );
    assert_eq!(owner.remaining_fuel(), 0);
    assert!(o.events.iter().all(|e| e.site == exact));
}
