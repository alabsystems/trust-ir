// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn complete_dominator_child_and_all_case_rows_are_owned_before_post_child_scratch_work() {
    let f = fixture();
    let expected = Ordinary::new(&f);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.build(&f, &mut work).unwrap();
    assert!(state.tree.as_ref().unwrap().is_well_formed());
    assert_eq!(state.edges, expected.edges);
    assert!(state.tags.capacity() > 0);
    assert!(state.edges.capacity() > 0);
    drain(&mut state, &mut work);
    assert!(empty(&state));
}
#[test]
fn every_private_constructor_cut_drains_all_actual_tag_edge_and_tree_owners() {
    let f = fixture();
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.build(&f, &mut work).unwrap();
    let end = calls.get();
    drain(&mut state, &mut work);
    drop(work);
    drop(s);
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State::default();
        assert!(state.build(&f, &mut work).is_err());
        drain(&mut state, &mut work);
        assert!(empty(&state));
        assert_eq!(
            work.session.first_refusal().unwrap().cause,
            "original guard stop"
        );
    }
}
#[test]
fn whole_selected_output_is_held_at_each_post_append_refusal_then_explicitly_drained() {
    let f = fixture();
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let g = ObservedHandleEnumGuards::new_observed(&f, &mut s, site()).unwrap();
    let begin = calls.get();
    let mut out = Vec::new();
    query::selected(
        &g,
        f.blocks[1].id,
        55,
        &[0, 1],
        &mut out,
        &mut Work {
            session: &mut s,
            site: site(),
        },
    )
    .unwrap();
    let end = calls.get();
    assert_eq!(out, vec![0]);
    retire_selected_variants_observed(out, &mut s, site()).unwrap();
    g.retire_observed(&mut s, site()).unwrap();
    drop(s);
    let mut held = false;
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let g = ObservedHandleEnumGuards::new_observed(&f, &mut s, site()).unwrap();
        let mut out = Vec::new();
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        assert!(query::selected(&g, f.blocks[1].id, 55, &[0, 1], &mut out, &mut work).is_err());
        if !out.is_empty() {
            held = true;
            assert_eq!(out, vec![0]);
            assert!(out.capacity() > 0);
        }
        work.rows(take(&mut out));
        assert_eq!(out.capacity(), 0);
        let _ = g.retire_observed(work.session, work.site);
    }
    assert!(held);
}
#[test]
fn successful_selected_result_requires_original_consuming_caller_retirement() {
    let f = fixture();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let g = ObservedHandleEnumGuards::new_observed(&f, &mut s, site()).unwrap();
    let out = g
        .variants_selected_at_observed(f.blocks[1].id, 55, &[0], &mut s, site())
        .unwrap();
    assert_eq!(out, vec![0]);
    let begin = calls.get();
    retire_selected_variants_observed(out, &mut s, site()).unwrap();
    let end = calls.get();
    g.retire_observed(&mut s, site()).unwrap();
    drop(s);
    assert!(
        o.events[begin..end - 1]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
    assert_eq!(
        o.events[end - 1],
        ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 0,
            copy_bytes: 0
        }
    );
}
#[test]
fn first_late_child_retirement_refusal_still_drains_all_other_fields_without_replacement() {
    let f = fixture();
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut state = State::default();
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    state.build(&f, &mut work).unwrap();
    let end = calls.get();
    drain(&mut state, &mut work);
    drop(work);
    drop(s);
    let mut o = Observer {
        stop: Some(end + 1),
        cleanup_after: Some(end + 1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut state = State::default();
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    state.build(&f, &mut work).unwrap();
    assert!(state.tree.is_some() && !state.edges.is_empty() && !state.tags.is_empty());
    drain(&mut state, &mut work);
    assert!(empty(&state));
    assert_eq!(
        work.session.first_refusal().unwrap().cause,
        "original guard stop"
    );
    assert_eq!(work.admit(1, 0), Err(ObservedValueError::AdmissionRefused));
    drop(work);
    drop(s);
    assert!(
        o.events[end + 1..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn full_guard_retirement_keeps_real_nested_dominator_receipt_and_original_request_site() {
    let f = fixture();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let g = ObservedHandleEnumGuards::new_observed(&f, &mut s, site()).unwrap();
    let begin = calls.get();
    g.retire_observed(&mut s, site()).unwrap();
    let end = calls.get();
    drop(s);
    let pubs: Vec<_> = o.events[begin..end]
        .iter()
        .filter(|e| e.phase == ExecutionPhase::Publication)
        .copied()
        .collect();
    assert_eq!(
        pubs,
        vec![
            ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site: site(),
                work: 1,
                copy_bytes: 0
            },
            ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site: site(),
                work: 0,
                copy_bytes: 0
            },
        ]
    );
    assert!(o.events.iter().all(|e| e.site == site()));
}
