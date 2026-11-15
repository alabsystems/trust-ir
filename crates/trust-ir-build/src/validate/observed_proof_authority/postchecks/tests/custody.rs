// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn empty(state: &Post) {
    assert_eq!(state.errors.capacity(), 0);
    assert_eq!(state.scratch.reason.capacity(), 0);
    assert_eq!(state.scratch.edges.capacity(), 0);
    assert_eq!(state.scratch.named.capacity(), 0);
    assert_eq!(state.scratch.parents.capacity(), 0);
    assert_eq!(state.scratch.queue.capacity(), 0);
    assert_eq!(state.scratch.path.capacity(), 0);
    assert_eq!(state.scratch.content.capacity(), 0);
    assert!(state.scratch.pending_content.is_none());
}
#[test]
fn partial_reason_and_prior_whole_errors_remain_owned_at_every_next_message_fee() {
    let mut i = fixture();
    i.module.proof_certificates.clear();
    let catalog = ModuleFunctionCatalog::new(&i.module);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut state = Post::default();
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    state
        .composition(&i.module, &catalog, &i.tv, &mut w)
        .unwrap();
    let end = calls.get();
    let out = state.finish(Ok(()), &mut w).unwrap();
    retire_validation_errors_observed(out, w.session, w.site).unwrap();
    drop(w);
    drop(s);
    let mut saw = false;
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut state = Post::default();
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            state.composition(&i.module, &catalog, &i.tv, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        saw |= !state.errors.is_empty() && !state.scratch.reason.is_empty();
        assert_eq!(
            state.finish(Err(ObservedValueError::AdmissionRefused), &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        empty(&state);
    }
    assert!(saw);
}
#[test]
fn complete_returned_v8_bytes_and_prior_groups_stay_owned_through_comparison_and_growth() {
    let i = fixture();
    let catalog = ModuleFunctionCatalog::new(&i.module);
    let rows: Vec<_> = i.rows.iter().collect();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut state = Post::default();
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    state.duplicates(&rows, &catalog, &mut w).unwrap();
    let end = calls.get();
    let out = state.finish(Ok(()), &mut w).unwrap();
    retire_validation_errors_observed(out, w.session, w.site).unwrap();
    drop(w);
    drop(s);
    let mut saw = false;
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut state = Post::default();
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            state.duplicates(&rows, &catalog, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        saw |= state
            .scratch
            .pending_content
            .as_ref()
            .is_some_and(|v| !v.is_empty())
            && !state.scratch.content.is_empty();
        assert_eq!(
            state.finish(Err(ObservedValueError::AdmissionRefused), &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        empty(&state);
    }
    assert!(saw);
}
#[test]
fn actual_graph_edges_named_rows_bfs_parent_queue_and_path_are_retired_after_each_stop() {
    let i = cycle_fixture();
    let catalog = ModuleFunctionCatalog::new(&i.module);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut state = Post::default();
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    state
        .composition(&i.module, &catalog, &i.tv, &mut w)
        .unwrap();
    let end = calls.get();
    let out = state.finish(Ok(()), &mut w).unwrap();
    retire_validation_errors_observed(out, w.session, w.site).unwrap();
    drop(w);
    drop(s);
    let (mut edges, mut named, mut parents, mut queue, mut path) =
        (false, false, false, false, false);
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut state = Post::default();
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            state.composition(&i.module, &catalog, &i.tv, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        edges |= !state.scratch.edges.is_empty();
        named |= !state.scratch.named.is_empty();
        parents |= !state.scratch.parents.is_empty();
        queue |= !state.scratch.queue.is_empty();
        path |= !state.scratch.path.is_empty();
        assert_eq!(
            state.finish(Err(ObservedValueError::AdmissionRefused), &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        empty(&state);
    }
    assert!(edges && named && parents && queue && path);
}
#[test]
fn every_whole_scratch_cleanup_callback_retires_all_buffers_despite_first_sticky_cause() {
    let i = fixture();
    let catalog = ModuleFunctionCatalog::new(&i.module);
    let rows: Vec<_> = i.rows.iter().collect();
    let mut base = Observer::default();
    let calls = base.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut state = Post::default();
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    state.duplicates(&rows, &catalog, &mut w).unwrap();
    let begin = calls.get();
    state.retire_scratch(&mut w);
    let end = calls.get();
    let out = state.finish(Ok(()), &mut w).unwrap();
    retire_validation_errors_observed(out, w.session, w.site).unwrap();
    drop(w);
    drop(s);
    assert!(end > begin);
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut state = Post::default();
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        state.duplicates(&rows, &catalog, &mut w).unwrap();
        state.retire_scratch(&mut w);
        assert_eq!(
            state.finish(Ok(()), &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        empty(&state);
        assert_eq!(w.session.first_refusal().unwrap().cause, "postcheck stop");
    }
}
#[test]
fn successful_whole_output_requires_actual_original_caller_cleanup_and_exact_terminal_receipt() {
    let i = fixture();
    let catalog = ModuleFunctionCatalog::new(&i.module);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = call(&i, &catalog, &mut s).unwrap();
    assert_eq!(out, oracle(&i, &catalog));
    assert!(!out.is_empty());
    let begin = calls.get();
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    drop(s);
    let tail = &o.events[begin..];
    assert!(tail.len() > 1);
    assert!(
        tail[..tail.len() - 1]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement && e.site == site())
    );
    assert_eq!(
        *tail.last().unwrap(),
        ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 0,
            copy_bytes: 0
        }
    );
}
#[test]
fn one_byte_short_output_bill_withholds_all_completed_errors_and_no_partial_result_escapes() {
    let i = fixture();
    let (base, end) = run(&i);
    let fee: usize = base.events[..end].iter().map(|e| e.copy_bytes).sum();
    assert!(fee > 0);
    let catalog = ModuleFunctionCatalog::new(&i.module);
    let mut o = Observer {
        byte_cap: Some(fee - 1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        call(&i, &catalog, &mut s),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "copy");
}
