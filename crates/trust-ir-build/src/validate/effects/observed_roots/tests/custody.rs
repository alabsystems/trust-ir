// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn weight<T: Copy>(count: usize) -> usize {
    (count + 1) * (size_of::<Option<T>>() + 1)
        + count * (size_of::<T>() + 1)
        + size_of::<Vec<T>>()
        + 1
}
#[test]
fn full_returned_edge_vec_is_held_before_the_first_target_lookup_refuses() {
    let f = function(vec![node(
        Inst::Br {
            target: BlockId::new(0),
            args: vec![v(1)],
        },
        &[],
    )]);
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut state = super::super::entry::Entry::default();
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    assert!(!state.inspect(&f, &mut w).unwrap());
    assert_eq!(state.edges.capacity(), 0);
    drop(w);
    drop(s);
    // This private Entry::inspect has exactly one successor publication and
    // no outer Body/String/map publication. Refuse its very next actual event.
    let publications = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| e.phase == ExecutionPhase::Publication)
        .collect::<Vec<_>>();
    assert_eq!(publications.len(), 1);
    let stop = publications[0].0 + 2;
    let mut o = Observer {
        stop: Some(stop),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = super::super::entry::Entry::default();
    assert!(matches!(
        state.inspect(&f, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    ));
    assert_eq!(state.edges.len(), 1);
    assert_eq!(state.edges[0].target, BlockId::new(0));
    assert!(core::ptr::eq(
        state.edges[0].args.as_ptr(),
        match &f.blocks[0].body[0].inst {
            Inst::Br { args, .. } => args.as_ptr(),
            _ => unreachable!(),
        }
    ));
    w.retire_fixed_vec(&mut state.edges);
    assert_eq!(state.edges.capacity(), 0);
    assert_eq!(
        w.session.first_refusal().unwrap().cause,
        "original root stop"
    );
}
#[test]
fn first_step_descriptor_admission_precedes_actual_trace_queue_allocation() {
    let f = function(Vec::new());
    let body = body_fixture(&f);
    let mut state = Trace::default();
    let mut o = Observer {
        byte_cap: Some(0),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let result = state.walk(&body, v(1), &mut w);
    assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
    assert_eq!(
        (
            state.stack.capacity(),
            state.marks.capacity(),
            state.output.rows.capacity()
        ),
        (0, 0, 0)
    );
    assert!(matches!(
        state.finish(result, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    ));
}
#[test]
fn root_capacity_and_header_move_have_distinct_refusal_ordinals_before_push() {
    for stop in [4, 5] {
        let mut state = Trace::default();
        let mut o = Observer {
            stop: Some(stop),
            ..Default::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        // root(empty): lookup, position header, reserve probe, allocation, push.
        let result = state.root(Root::Local, &mut w);
        assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
        assert!(state.output.rows.is_empty());
        assert_eq!(state.output.rows.capacity() == 0, stop == 4);
        assert!(matches!(
            state.finish(result, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert_eq!(state.output.rows.capacity(), 0);
    }
}
#[test]
fn pending_marks_stack_and_full_root_prefix_survive_stop_and_consume_under_same_owner() {
    let prefix = vec![
        Root::Local,
        Root::Place(EffectPlace::ParamPointee { index: 0 }),
        Root::Untraceable,
    ];
    let mut state = Trace {
        marks: vec![(v(1), Mark::OnPath), (v(2), Mark::Done)],
        stack: vec![Step::Enter(v(1)), Step::Exit(v(2))],
        output: ObservedRoots {
            rows: prefix.clone(),
        },
    };
    let mut o = Observer {
        next: Some(Rc::new(Cell::new(true))),
        cleanup: true,
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let result = state.root(Root::Place(EffectPlace::Global(GlobalId::new(9))), &mut w);
    assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
    assert_eq!(state.output.rows, prefix);
    assert_eq!((state.stack.len(), state.marks.len()), (2, 2));
    assert!(matches!(
        state.finish(result, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    ));
    assert_eq!(
        (
            state.stack.capacity(),
            state.marks.capacity(),
            state.output.rows.capacity()
        ),
        (0, 0, 0)
    );
    drop(w);
    assert_eq!(s.first_refusal().unwrap().cause, "original root stop");
    drop(s);
    assert_eq!(
        o.events
            .iter()
            .filter(|e| e.phase == ExecutionPhase::ScratchRetirement)
            .map(|e| e.work)
            .sum::<usize>(),
        weight::<Step>(2) + weight::<(ValueId, Mark)>(2) + weight::<Root>(3)
    );
}
#[test]
fn refused_canonical_swap_keeps_prior_roots_and_the_new_appended_root_until_cleanup() {
    let original = [
        Root::Place(EffectPlace::ParamPointee { index: 0 }),
        Root::Place(EffectPlace::Global(GlobalId::new(9))),
    ];
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = Trace {
        output: ObservedRoots {
            rows: original.to_vec(),
        },
        ..Default::default()
    };
    state.root(Root::Local, &mut w).unwrap();
    let out = state.finish(Ok(()), &mut w).unwrap();
    out.retire_observed(w.session, w.site).unwrap();
    drop(w);
    drop(s);
    let stop = base
        .events
        .iter()
        .position(|e| {
            e.phase == ExecutionPhase::Validation
                && e.work == 2
                && e.copy_bytes == 2 * size_of::<Root>() + size_of::<usize>()
        })
        .unwrap()
        + 1;
    let mut state = Trace {
        output: ObservedRoots {
            rows: original.to_vec(),
        },
        ..Default::default()
    };
    let mut o = Observer {
        stop: Some(stop),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let result = state.root(Root::Local, &mut w);
    assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
    assert_eq!(state.output.rows, [original[0], original[1], Root::Local]);
    assert!(matches!(
        state.finish(result, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    ));
    assert_eq!(state.output.rows.capacity(), 0);
}
#[test]
fn rejected_final_query_publication_retires_the_complete_canonical_result_only() {
    let f = mixed();
    let body = body_fixture(&f);
    let (base, bound) = query_trace(&f, 7);
    assert_eq!(base.events[bound - 1].phase, ExecutionPhase::Publication);
    let count = expected(&f, 7).len();
    let mut o = Observer {
        stop: Some(bound),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(matches!(
        body.roots_observed(v(7), &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    ));
    drop(s);
    assert!(
        o.events[bound..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
    assert_eq!(
        o.events[bound..].iter().map(|e| e.work).sum::<usize>(),
        weight::<Root>(count)
    );
}
#[test]
fn refused_result_read_preserves_owned_rows_for_explicit_sticky_consuming_retirement() {
    let f = mixed();
    let body = body_fixture(&f);
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        next: Some(arm.clone()),
        ..Default::default()
    };
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let roots = body.roots_observed(v(7), &mut s, site()).unwrap();
    let all = expected(&f, 7);
    arm.set(true);
    assert_eq!(
        roots.at_observed(0, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(roots.rows, all);
    let start = calls.get();
    assert!(matches!(
        roots.retire_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    ));
    assert_eq!(s.first_refusal().unwrap().cause, "original root stop");
    drop(s);
    assert_eq!(
        o.events[start..].iter().map(|e| e.work).sum::<usize>(),
        weight::<Root>(all.len())
    );
}
