// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_callback_of_all_context_and_argument_paths_can_refuse() {
    let module = fixture();
    let values = [v(7), v(9)];
    for query in samples(&module, &values) {
        let base = trace(query);
        for stop in 1..=base.events.len() {
            let mut o = Observer {
                stop: Some(stop),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert!(matches!(
                query.run(&mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            ));
            assert_eq!(s.first_refusal().unwrap().cause, "original context stop");
            assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
            drop(s);
            assert_eq!(o.events.len(), stop);
        }
    }
}
#[test]
fn rejected_final_publication_never_returns_a_fixed_recipe_or_semantic_arg() {
    let module = fixture();
    let values = [v(7), v(9)];
    for query in samples(&module, &values) {
        let base = trace(query);
        let stop = base.events.len();
        assert_eq!(base.events[stop - 1].phase, ExecutionPhase::Publication);
        let mut o = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert!(matches!(
            query.run(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
    }
}
#[test]
fn nested_call_recipe_publication_refusal_cannot_be_turned_into_parameter_context() {
    let what = What::Parameter {
        call: Call {
            mnemonic: "assert",
            kind: CallKind::Panic,
        },
        side: Side::Read,
        index: 7,
    };
    let query = Query::What(what);
    let base = trace(query);
    let hits = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Publication && e.copy_bytes == size_of::<[Piece<'_>; 2]>()
        })
        .map(|(i, _)| i + 1)
        .collect::<Vec<_>>();
    assert_eq!(hits.len(), 1);
    let stop = hits[0];
    assert!(stop < base.events.len());
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(matches!(
        what.parts_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    ));
    drop(s);
    assert_eq!(o.events.len(), stop);
}
#[test]
fn global_name_borrow_admission_can_refuse_after_the_exact_direct_lookup() {
    let module = fixture();
    let query = Query::Label(EffectPlace::Global(g(1)), &module);
    let base = trace(query);
    // begin, direct-slot get, borrowed-name header, final recipe publication.
    assert_eq!(base.events.len(), 4);
    assert_eq!(base.events[2].phase, ExecutionPhase::Validation);
    assert_eq!(base.events[2].copy_bytes, size_of::<&str>());
    let mut o = Observer {
        stop: Some(3),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(matches!(
        root_label_observed(EffectPlace::Global(g(1)), &module, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    ));
    assert_eq!(s.first_refusal().unwrap().progress, base.events[2]);
    assert_eq!(module.globals[1].name, "one");
}
#[test]
fn cumulative_work_and_copy_limits_across_calls_use_the_same_original_owner() {
    let module = fixture();
    let values = [v(7), v(9)];
    for query in samples(&module, &values) {
        let base = trace(query);
        for copy in [false, true] {
            let mut o = Observer {
                work_cap: (!copy).then_some(base.work),
                byte_cap: copy.then_some(base.bytes),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            query.run(&mut s, site()).unwrap();
            assert!(matches!(
                query.run(&mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            ));
            let first = s.first_refusal().unwrap().progress;
            assert_eq!(
                s.first_refusal().unwrap().cause,
                if copy { "copy" } else { "work" }
            );
            assert!(matches!(
                query.run(&mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            ));
            assert_eq!(s.first_refusal().unwrap().progress, first);
        }
    }
}
#[test]
fn first_header_stop_cannot_be_renewed_by_another_context_or_argument_helper() {
    let module = fixture();
    let values = [v(7)];
    let mut o = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut first = None;
    for query in samples(&module, &values) {
        assert!(matches!(
            query.run(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        let progress = s.first_refusal().unwrap().progress;
        assert_eq!(*first.get_or_insert(progress), progress);
    }
    drop(s);
    assert_eq!(o.events.len(), 1);
}
#[test]
fn even_an_out_of_range_none_argument_requires_final_original_publication() {
    for args in [
        Arguments::Values(&[]),
        Arguments::ElementSlot,
        Arguments::Panic {
            operands: None,
            location: PanicLocation::Value(v(0)),
        },
    ] {
        let query = Query::Get(args, usize::MAX);
        let base = trace(query);
        let stop = base.events.len();
        let mut o = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert!(matches!(
            args.get_observed(usize::MAX, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert_eq!(
            s.first_refusal().unwrap().progress.phase,
            ExecutionPhase::Publication
        );
    }
}
#[test]
fn original_exact_instruction_site_and_zero_fuel_cover_every_helper() {
    let module = fixture();
    let values = [v(7), v(9)];
    let exact = ExecutionSite::Instruction(InstructionSite {
        function: FuncId::new(251),
        block: BlockId::new(8),
        instruction_index: usize::MAX,
    });
    let mut o = Observer::default();
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    for query in samples(&module, &values) {
        query.run(&mut s, exact).unwrap();
    }
    assert_eq!(s.remaining_fuel(), 0);
    assert!(s.first_refusal().is_none());
    drop(s);
    assert!(o.events.iter().all(|event| event.site == exact));
}
#[test]
fn fixed_header_refusals_do_not_consume_or_change_borrowed_name_and_value_inputs() {
    let module = fixture();
    let values = vec![v(7), v(9), v(7)];
    let pointer = values.as_ptr();
    let capacity = values.capacity();
    let name = module.globals[1].name.as_ptr();
    for query in [
        Query::Get(Arguments::Values(&values), 0),
        Query::Label(EffectPlace::Global(g(1)), &module),
    ] {
        let base = trace(query);
        let mut o = Observer {
            stop: Some(base.events.len()),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert!(matches!(
            query.run(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        drop(s);
        assert_eq!((values.as_ptr(), values.capacity()), (pointer, capacity));
        assert_eq!(values, [v(7), v(9), v(7)]);
        assert_eq!(module.globals[1].name.as_ptr(), name);
        assert!(
            o.events
                .iter()
                .all(|event| event.phase != ExecutionPhase::ScratchRetirement)
        );
    }
}
