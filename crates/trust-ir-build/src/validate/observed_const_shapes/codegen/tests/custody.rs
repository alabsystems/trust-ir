// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn inspect(mut check: impl FnMut(&Front<'_>)) {
    let m = fixture();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut state = Front::default();
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    state.run(&m, &mut w).unwrap();
    let end = calls.get();
    drain(&mut state, &mut w);
    empty(&state);
    drop(w);
    drop(s);
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut state = Front::default();
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            state.run(&m, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        check(&state);
        drain(&mut state, &mut w);
        empty(&state);
        assert_eq!(
            w.session.first_refusal().unwrap().cause,
            "original narrow switch stop"
        );
    }
}
#[test]
fn constructed_table_and_whole_catalog_are_owned_across_later_setup_or_scan_refusal() {
    let (mut table_only, mut both) = (false, false);
    inspect(|s| {
        table_only |= s.layouts.is_some() && s.catalog.is_none();
        both |= s.layouts.is_some() && s.catalog.is_some();
    });
    assert!(table_only && both);
}
#[test]
fn whole_lazy_map_pending_child_and_prior_errors_remain_held_until_parent_cleanup() {
    let (mut map, mut pending, mut row) = (false, false, false);
    inspect(|s| {
        map |= s.literals.values.is_some() && !s.literals.errors.is_empty();
        pending |= !s.literals.pending.is_empty();
        row |= s.literals.row.is_some();
    });
    assert!(map && pending && row);
}
#[test]
fn whole_success_output_remains_original_caller_owned_with_terminal_or_sticky_cleanup() {
    let m = fixture();
    for refuse in [false, true] {
        let arm = Rc::new(Cell::new(false));
        let mut o = Observer {
            cleanup: Some(arm.clone()),
            ..Observer::default()
        };
        let calls = o.calls.clone();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let out = crate::codegen_switch_case_literal_errors_observed(&m, &mut s, site()).unwrap();
        let begin = calls.get();
        arm.set(refuse);
        let result = retire_validation_errors_observed(out, &mut s, site());
        if refuse {
            assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
            assert_eq!(s.first_refusal().unwrap().cause, "cleanup");
        } else {
            result.unwrap();
        }
        drop(s);
        let tail = &o.events[begin..];
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
            let e = tail.last().unwrap();
            assert_eq!(
                (e.phase, e.work, e.copy_bytes),
                (ExecutionPhase::Publication, 0, 0)
            );
        }
    }
}
