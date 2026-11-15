// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn inspect(m: &Module, mut check: impl FnMut(&State<'_>)) {
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut state = State::default();
    let mut w = Work {
        session: &mut session,
        site: site(),
    };
    private_run(&mut state, m, &mut w).unwrap();
    assert_eq!(state.errors, ordinary(m));
    let end = calls.get();
    drain(&mut state, &mut w);
    empty(&state);
    drop(w);
    drop(state);
    drop(session);
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut state = State::default();
        let mut w = Work {
            session: &mut session,
            site: site(),
        };
        assert_eq!(
            private_run(&mut state, m, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        check(&state);
        drain(&mut state, &mut w);
        empty(&state);
        assert_eq!(
            w.session.first_refusal().unwrap().cause,
            "original inline cycle stop"
        );
        drop(w);
        drop(state);
        drop(session);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn actual_nodes_borrowed_pending_edges_and_complete_adjacency_stay_owned_until_full_drain() {
    let m = all_families();
    let (mut nodes, mut pending, mut edges, mut adjacency) = (false, false, false, false);
    inspect(&m, |state| {
        nodes |= !state.nodes.is_empty();
        pending |= !state.pending.is_empty();
        edges |= !state.edges.is_empty();
        adjacency |= !state.successors.is_empty();
    });
    assert!(nodes && pending && edges && adjacency);
}
#[test]
fn actual_dfs_marks_open_stack_and_call_continuations_survive_each_interior_stop() {
    let m = cycle();
    let (mut marks, mut stack, mut calls) = (false, false, false);
    inspect(&m, |state| {
        marks |= state.marks.iter().any(|m| m.on_stack);
        stack |= !state.stack.is_empty();
        calls |= !state.calls.is_empty();
    });
    assert!(marks && stack && calls);
}
#[test]
fn full_pending_sorted_component_and_prior_disjoint_components_are_consumed_after_refusal() {
    let m = several();
    let (mut pending, mut stored, mut saw_unsorted_insertion) = (false, false, false);
    inspect(&m, |state| {
        pending |= !state.component.is_empty();
        stored |= !state.cycles.is_empty();
        // Independently enumerated custody for this exact fixture: dense nodes
        // are struct0, struct1, struct4, struct99. The first SCC pops1 then0;
        // its separately admitted insertion can still own [1,0] before the
        // adjacent swap completes. The other SCCs are singleton2 and3.
        assert!(matches!(
            state.component.as_slice(),
            [] | [1] | [1, 0] | [0, 1] | [2] | [3]
        ));
        saw_unsorted_insertion |= matches!(state.component.as_slice(), [1, 0]);
        // Only complete components enter cycles; their inner order is final
        // even while the separately admitted outer cycle sorting is pending.
        assert!(
            state
                .cycles
                .iter()
                .all(|c| c.windows(2).all(|p| p[0] < p[1]))
        );
    });
    assert!(pending && stored && saw_unsorted_insertion);
}
#[test]
fn actual_whole_returned_type_display_child_is_held_before_any_further_admission() {
    let m = row_text();
    let expected = format!("{}", m.types[0]);
    let mut saw = false;
    // Select only the parent's later full child/text phase via all actual cuts;
    // source/input construction and the ordinary formatter stay outside scope.
    inspect(&m, |state| {
        if !state.render.is_empty() {
            saw = true;
            assert_eq!(state.render, expected);
        }
    });
    assert!(saw);
}
#[test]
fn prior_whole_reports_and_current_partial_raw_diagnostic_remain_parent_owned() {
    let m = several();
    let expected = ordinary(&m);
    let (mut prior, mut text) = (false, false);
    inspect(&m, |state| {
        if !state.errors.is_empty() {
            prior = true;
            assert_eq!(state.errors[0], expected[0]);
        }
        text |= !state.text.is_empty();
    });
    assert!(prior && text);
}
#[test]
fn caller_retains_all_complete_outputs_until_actual_terminal_or_sticky_consuming_retirement() {
    let m = several();
    for refuse in [false, true] {
        let arm = Rc::new(Cell::new(false));
        let mut o = Observer {
            cleanup: Some(arm.clone()),
            ..Observer::default()
        };
        let calls = o.calls.clone();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let out = call(&m, &mut s).unwrap();
        assert_eq!(out, ordinary(&m));
        let begin = calls.get();
        arm.set(refuse);
        let result = retire_validation_errors_observed(out, &mut s, site());
        if refuse {
            assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
            assert_eq!(s.first_refusal().unwrap().cause, "cleanup");
        } else {
            result.unwrap();
            assert!(s.first_refusal().is_none());
        }
        drop(s);
        let tail = &o.events[begin..];
        assert!(!tail.is_empty());
        if refuse {
            assert!(
                tail.iter()
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        } else {
            assert!(
                tail[..tail.len() - 1]
                    .iter()
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
            let end = tail.last().unwrap();
            assert_eq!(
                (end.phase, end.work, end.copy_bytes),
                (ExecutionPhase::Publication, 0, 0)
            );
        }
    }
}
