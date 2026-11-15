// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_constructor_lookup_case_dominator_and_publication_callback_refuses() {
    let f = fixture();
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let g = ObservedHandleEnumGuards::new_observed(&f, &mut s, site()).unwrap();
    let end = calls.get();
    g.retire_observed(&mut s, site()).unwrap();
    drop(s);
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert!(matches!(
            ObservedHandleEnumGuards::new_observed(&f, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert_eq!(s.first_refusal().unwrap().cause, "original guard stop");
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
fn every_actual_edge_query_discriminant_append_and_result_publication_callback_refuses() {
    let f = fixture();
    let (baseline, begin, end) = query_trace(&f);
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let g = ObservedHandleEnumGuards::new_observed(&f, &mut s, site()).unwrap();
        assert_eq!(
            g.variants_selected_at_observed(f.blocks[1].id, 55, &[0, 1, 2], &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().cause, "original guard stop");
        let _ = g.retire_observed(&mut s, site());
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
fn every_short_circuit_predicate_callback_refuses_including_final_boolean_publication() {
    let mut f = fixture();
    if let Inst::ExtractField { field, .. } = &mut f.blocks[1].body[0].inst {
        *field = 1;
    }
    let mut baseline = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    assert!(
        ObservedHandleEnumGuards::function_reads_a_non_tag_lane_observed(&f, &mut s, site())
            .unwrap()
    );
    drop(s);
    for cut in 1..=baseline.events.len() {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            ObservedHandleEnumGuards::function_reads_a_non_tag_lane_observed(&f, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
    }
}
#[test]
fn every_guard_retirement_callback_drains_and_refuses_without_new_healthy_publication() {
    let f = fixture();
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let g = ObservedHandleEnumGuards::new_observed(&f, &mut s, site()).unwrap();
    let begin = calls.get();
    g.retire_observed(&mut s, site()).unwrap();
    let end = calls.get();
    drop(s);
    assert_eq!(
        baseline.events[end - 1],
        ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 0,
            copy_bytes: 0
        }
    );
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let g = ObservedHandleEnumGuards::new_observed(&f, &mut s, site()).unwrap();
        assert_eq!(
            g.retire_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().cause, "original guard stop");
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
fn repeated_queries_share_original_cumulative_work_and_copy_instead_of_resetting_grants() {
    let f = fixture();
    let (baseline, _, end) = query_trace(&f);
    for copy in [false, true] {
        let cap = baseline.events[..end]
            .iter()
            .map(|e| if copy { e.copy_bytes } else { e.work })
            .sum::<usize>();
        let mut o = Observer::default();
        if copy {
            o.byte_cap = Some(cap);
        } else {
            o.work_cap = Some(cap);
        }
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let g = ObservedHandleEnumGuards::new_observed(&f, &mut s, site()).unwrap();
        let out = g
            .variants_selected_at_observed(f.blocks[1].id, 55, &[0, 1, 2], &mut s, site())
            .unwrap();
        assert_eq!(
            g.variants_selected_at_observed(f.blocks[1].id, 55, &[0, 1, 2], &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let _ = retire_selected_variants_observed(out, &mut s, site());
        let _ = g.retire_observed(&mut s, site());
        assert!(s.first_refusal().is_some());
    }
}
#[test]
fn zero_execution_fuel_and_preexisting_original_stop_do_not_create_a_new_session() {
    let f = fixture();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut o = Observer::default();
    let mut s = ObservedSession::new(options, &mut o);
    let g = ObservedHandleEnumGuards::new_observed(&f, &mut s, site()).unwrap();
    assert_eq!(selected(&g, f.blocks[1].id, 55, &[0], &mut s), vec![0]);
    g.retire_observed(&mut s, site()).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
    drop(s);
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
    assert!(matches!(
        ObservedHandleEnumGuards::new_observed(&f, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    ));
    assert_eq!(
        ObservedHandleEnumGuards::function_reads_a_non_tag_lane_observed(&f, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "original guard stop");
}
