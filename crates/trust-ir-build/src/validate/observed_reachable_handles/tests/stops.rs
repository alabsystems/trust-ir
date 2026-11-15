// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_graph_set_display_join_retirement_and_publication_callback_is_refusable() {
    let mut m = Module::new("");
    m.types = vec![handle("A")];
    let roots = [array(0)];
    let (_, baseline, bound) = run(&m, &roots, &[]);
    for cut in 1..=bound {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            reachable_handles_text_observed(&m, &roots, &[], &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            "original handle-name stop"
        );
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn long_actual_identity_comparison_can_stop_inside_a_middle_byte_chunk() {
    let m = Module::new("");
    let prefix = "N".repeat(4096);
    let roots = [
        Ty::handle(format!("{prefix}A"), "rt::N"),
        Ty::handle(format!("{prefix}B"), "rt::N"),
    ];
    let (_, baseline, _) = run(&m, &roots, &[]);
    let cut = baseline
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 1024
                && e.copy_bytes == size_of::<Ordering>()
        })
        .nth(1)
        .unwrap()
        .0
        + 1;
    let mut o = Observer {
        stop: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        reachable_handles_text_observed(&m, &roots, &[], &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    drop(s);
    assert_eq!(&o.events[..cut], &baseline.events[..cut]);
}
#[test]
fn a_middle_ordered_pointer_swap_is_observed_and_keeps_all_borrowed_rows_on_stop() {
    let old = [handle("X"), handle("Y"), handle("Z")];
    let new = handle("A");
    let mut baseline = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State {
        handles: old.iter().collect(),
        ..State::default()
    };
    state.insert(&new, &mut work).unwrap();
    drain(&mut state, &mut work);
    drop(work);
    drop(s);
    let swaps: Vec<_> = baseline
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 3
                && e.copy_bytes == 2 * size_of::<&Ty>() + size_of::<usize>()
        })
        .map(|(i, _)| i + 1)
        .collect();
    assert_eq!(swaps.len(), 3);
    let cut = swaps[1];
    let mut o = Observer {
        stop: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State {
        handles: old.iter().collect(),
        ..State::default()
    };
    assert_eq!(
        state.insert(&new, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.handles.len(), 4);
    for ty in old.iter().chain(core::iter::once(&new)) {
        assert_eq!(
            state
                .handles
                .iter()
                .filter(|p| core::ptr::eq(**p, ty))
                .count(),
            1
        );
    }
    assert!(core::ptr::eq(state.handles[2], &new));
    drain(&mut state, &mut work);
    assert!(empty(&state));
    drop(work);
    drop(s);
    assert_eq!(&o.events[..cut], &baseline.events[..cut]);
}
#[test]
fn successive_closures_and_explicit_caller_string_cleanup_share_cumulative_limits() {
    let m = fixture();
    let roots = [Ty::Closure(ClosureTyId::new(0))];
    let (_, baseline, _) = run(&m, &roots, &[]);
    for copy in [false, true] {
        let mut o = Observer::default();
        if copy {
            o.byte_cap = Some(baseline.bytes + 1);
        } else {
            o.work_cap = Some(baseline.work + 1);
        }
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let output = reachable_handles_text_observed(&m, &roots, &[], &mut s, site()).unwrap();
        {
            let mut work = Work {
                session: &mut s,
                site: site(),
            };
            work.flat(output);
        }
        assert_eq!(
            reachable_handles_text_observed(&m, &roots, &[], &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(s.first_refusal().is_some());
    }
}
#[test]
fn original_site_zero_fuel_and_preexisting_cause_are_never_replaced() {
    let m = fixture();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut o = Observer::default();
    let mut s = ObservedSession::new(options, &mut o);
    let out = reachable_handles_text_observed(
        &m,
        &[Ty::Closure(ClosureTyId::new(0))],
        &[],
        &mut s,
        site(),
    )
    .unwrap();
    {
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        work.flat(out);
    }
    assert_eq!(s.remaining_fuel(), 0);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    let mut o = Observer {
        stop: Some(1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        s.admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site: site(),
            work: 1,
            copy_bytes: 0
        })
        .is_err()
    );
    assert_eq!(
        reachable_handles_text_observed(&m, &[], &[], &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original handle-name stop"
    );
}
#[test]
fn refusing_the_complete_string_publication_retires_the_whole_output_without_text() {
    let m = fixture();
    let roots = [Ty::Closure(ClosureTyId::new(0))];
    let (_, baseline, bound) = run(&m, &roots, &[]);
    assert_eq!(baseline.events[bound - 1].copy_bytes, size_of::<String>());
    let mut o = Observer {
        stop: Some(bound),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        reachable_handles_text_observed(&m, &roots, &[], &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    drop(s);
    assert_eq!(&o.events[..bound], &baseline.events[..bound]);
    assert!(
        o.events[bound..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
    assert!(o.events.len() > bound);
}
