// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_public_callback_for_empty_and_nonempty_paths_refuses_without_partial_errors() {
    for nodes in [
        vec![],
        vec![
            node(load(1), &[]),
            node(
                Inst::HeapAlloc {
                    ty: Ty::U32,
                    count: None,
                    align: None,
                    origin: AllocOrigin::RustHeap,
                },
                &[3],
            ),
            node(
                Inst::Call {
                    callee: FuncId::new(99),
                    args: vec![],
                },
                &[],
            ),
        ],
    ] {
        let (m, f) = fixture(nodes);
        let (_, base, bound) = run(&m, &f, ImportPolicy::Structural);
        for stop in 1..=bound {
            let mut o = Observer {
                stop: Some(stop),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                validate_effect_summary_observed(&m, &f, ImportPolicy::Structural, &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
            drop(s);
            assert!(
                o.events[stop..]
                    .iter()
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn original_work_and_copy_caps_accumulate_across_whole_calls_and_caller_output_retirement() {
    let (m, f) = fixture(vec![node(load(1), &[]), node(store(2), &[])]);
    let (_, base, _) = run(&m, &f, ImportPolicy::Refuse);
    for copy in [false, true] {
        let mut o = Observer {
            cap: (!copy).then_some(base.work),
            byte_cap: copy.then_some(base.bytes),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let out =
            validate_effect_summary_observed(&m, &f, ImportPolicy::Refuse, &mut s, site()).unwrap();
        retire_validation_errors_observed(out, &mut s, site()).unwrap();
        assert_eq!(
            validate_effect_summary_observed(&m, &f, ImportPolicy::Refuse, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = s.first_refusal().unwrap().progress;
        assert_eq!(
            validate_effect_summary_observed(&m, &f, ImportPolicy::Refuse, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, first);
        assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    }
}
#[test]
fn exact_original_instruction_site_and_zero_fuel_cover_the_entire_body_and_cleanup() {
    let (m, f) = fixture(vec![
        node(load(1), &[]),
        node(
            Inst::Call {
                callee: FuncId::new(99),
                args: vec![],
            },
            &[],
        ),
    ]);
    let expected = super::super::super::validate_effect_summary(&m, &f, ImportPolicy::Structural);
    let exact = ExecutionSite::Instruction(InstructionSite {
        function: FuncId::new(0),
        block: BlockId::new(7),
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
    let out =
        validate_effect_summary_observed(&m, &f, ImportPolicy::Structural, &mut s, exact).unwrap();
    assert_eq!(out, expected);
    retire_validation_errors_observed(out, &mut s, exact).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
    assert!(s.first_refusal().is_none());
    drop(s);
    assert!(o.events.iter().all(|e| e.site == exact));
}
#[test]
fn actual_exhaustive_instruction_dispatch_can_refuse_deep_inside_the_body_walk() {
    let (m, f) = fixture(
        (0..200)
            .map(|_| {
                node(
                    Inst::Fence {
                        ordering: Ordering::SeqCst,
                    },
                    &[],
                )
            })
            .collect(),
    );
    let (_, base, bound) = run(&m, &f, ImportPolicy::Structural);
    let visits = base.events[..bound]
        .iter()
        .enumerate()
        .filter(|(_, e)| e.phase == ExecutionPhase::Validation && e.work == 134)
        .map(|(i, _)| i + 1)
        .collect::<Vec<_>>();
    assert_eq!(visits.len(), 200);
    let stop = visits[100];
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_effect_summary_observed(&m, &f, ImportPolicy::Structural, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
}
#[test]
fn final_whole_pass_publication_refusal_never_returns_either_empty_or_nonempty_diagnostics() {
    for ptr in [1, 99] {
        let (m, mut f) = fixture(vec![node(load(ptr), &[])]);
        if ptr == 1 {
            f.summary.as_mut().unwrap().effects =
                Some(EffectSummary::pure().reading(EffectSet::of([p(0)])));
        }
        let (_, base, bound) = run(&m, &f, ImportPolicy::Structural);
        let mut o = Observer {
            stop: Some(bound),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_effect_summary_observed(&m, &f, ImportPolicy::Structural, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, base.events[bound - 1]);
        assert_eq!(
            s.first_refusal().unwrap().progress.phase,
            ExecutionPhase::Publication
        );
    }
}
#[test]
fn repeated_cleanup_refusals_drain_prior_real_reasons_without_changing_the_original_stop() {
    let (m, f) = fixture(vec![
        node(load(1), &[]),
        node(
            Inst::HeapAlloc {
                ty: Ty::U32,
                count: None,
                align: None,
                origin: AllocOrigin::RustHeap,
            },
            &[3],
        ),
        node(
            Inst::Call {
                callee: FuncId::new(99),
                args: vec![],
            },
            &[],
        ),
    ]);
    let (_, base, bound) = run(&m, &f, ImportPolicy::Structural);
    let stop = base.events[..bound]
        .iter()
        .enumerate()
        .filter(|(_, e)| e.phase == ExecutionPhase::Validation && e.work == 134)
        .nth(2)
        .unwrap()
        .0
        + 1;
    let mut o = Observer {
        stop: Some(stop),
        cleanup: true,
        cleanup_after: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_effect_summary_observed(&m, &f, ImportPolicy::Structural, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "original effects stop");
    assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
    drop(s);
    assert!(
        o.events[stop..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
    assert!(o.events[stop..].iter().filter(|e| e.work > 0).count() > 10);
}
