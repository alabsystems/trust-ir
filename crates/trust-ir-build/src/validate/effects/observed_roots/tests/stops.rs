// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_constructor_callback_can_refuse_without_publishing_borrowed_metadata() {
    let f = function(vec![node(
        Inst::Switch {
            value: v(1),
            cases: (1..5)
                .map(|i| SwitchCase {
                    value: Constant::Int(i.into()),
                    target: BlockId::new(i),
                    args: Vec::new(),
                })
                .collect(),
            default: BlockId::new(8),
            default_args: Vec::new(),
            exhaustive_enum_unreachable: false,
        },
        &[],
    )]);
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut original = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let body = ObservedBody::new_observed(&f, &mut original, site()).unwrap();
    let bound = calls.get();
    body.retire_observed(&mut original, site()).unwrap();
    drop(original);
    for stop in 1..=bound {
        let mut o = Observer {
            stop: Some(stop),
            ..Default::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert!(matches!(
            ObservedBody::new_observed(&f, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert_eq!(s.first_refusal().unwrap().cause, "original root stop");
        assert_eq!(
            s.first_refusal().unwrap().progress,
            baseline.events[stop - 1]
        );
        drop(s);
        assert!(
            o.events[stop..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn every_query_callback_can_refuse_without_publishing_a_smaller_root_set() {
    let f = mixed();
    let body = body_fixture(&f);
    let (base, bound) = query_trace(&f, 7);
    for stop in 1..=bound {
        let mut o = Observer {
            stop: Some(stop),
            ..Default::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert!(matches!(
            body.roots_observed(v(7), &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert_eq!(s.first_refusal().unwrap().cause, "original root stop");
        assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
        drop(s);
        assert!(
            o.events[stop..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn query_work_and_copy_caps_accumulate_in_the_original_session_across_calls() {
    let f = mixed();
    let body = body_fixture(&f);
    let (base, bound) = query_trace(&f, 7);
    let work = base.events[..bound].iter().map(|e| e.work).sum();
    let bytes = base.events[..bound].iter().map(|e| e.copy_bytes).sum();
    for copy in [false, true] {
        let mut o = Observer {
            cap: (!copy).then_some(work),
            byte_cap: copy.then_some(bytes),
            ..Default::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let held = body.roots_observed(v(7), &mut s, site()).unwrap();
        assert_eq!(held.rows, expected(&f, 7));
        assert!(matches!(
            body.roots_observed(v(7), &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "bytes" } else { "work" }
        );
        assert!(matches!(
            held.retire_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    }
}
#[test]
fn actual_matching_definition_expansion_can_stop_deep_inside_a_long_chain() {
    let mut nodes = vec![node(alloca(), &[3])];
    for id in 4..104 {
        nodes.push(node(copy(id - 1), &[id]));
    }
    let f = function(nodes);
    let body = body_fixture(&f);
    let (base, bound) = query_trace(&f, 103);
    let stop = base.events[..bound]
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 67
                && e.copy_bytes == 3 * size_of::<Step>() + size_of::<Root>()
        })
        .nth(50)
        .unwrap()
        .0
        + 1;
    let mut o = Observer {
        stop: Some(stop),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(matches!(
        body.roots_observed(v(103), &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    ));
    assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
}
#[test]
fn an_original_first_header_refusal_cannot_be_renewed_by_a_later_query() {
    let f = mixed();
    let body = body_fixture(&f);
    let mut o = Observer {
        byte_cap: Some(0),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(matches!(
        ObservedBody::new_observed(&f, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    ));
    let first = s.first_refusal().unwrap().progress;
    assert!(matches!(
        body.roots_observed(v(7), &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    ));
    assert_eq!(s.first_refusal().unwrap().progress, first);
    drop(s);
    assert_eq!(o.events.len(), 1);
}
#[test]
fn constructor_query_reads_and_cleanup_preserve_exact_instruction_site_and_zero_fuel() {
    let f = mixed();
    let exact = ExecutionSite::Instruction(InstructionSite {
        function: FuncId::new(131),
        block: BlockId::new(9),
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
    let body = ObservedBody::new_observed(&f, &mut s, exact).unwrap();
    let roots = body.roots_observed(v(7), &mut s, exact).unwrap();
    assert_eq!(
        roots.at_observed(0, &mut s, exact).unwrap(),
        Some(Root::Local)
    );
    roots.retire_observed(&mut s, exact).unwrap();
    body.retire_observed(&mut s, exact).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == exact));
}
