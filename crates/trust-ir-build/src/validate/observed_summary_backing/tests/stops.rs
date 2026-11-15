// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_refusal_callback_preserves_original_cause_and_denies_the_whole_stage() {
    let (m, f, summary) = fixture();
    let (_, base) = run(&m, &f, &summary, ImportPolicy::Refuse);
    for stop in 1..=base.events.len() {
        let mut o = Observer {
            stop: Some(stop),
            ..Default::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_function_summary_import_backing_observed(
                &m,
                &f,
                &summary,
                ImportPolicy::Refuse,
                &mut s,
                site()
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
        assert_eq!(s.first_refusal().unwrap().cause, "original backing");
    }
}
#[test]
fn complete_pending_refusal_detail_survives_before_output_allocation_and_move() {
    let (m, f, summary) = fixture();
    let trace = {
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State::default();
        state
            .run(&m, &f, &summary, ImportPolicy::Refuse, &mut w)
            .unwrap();
        drop(w);
        drop(s);
        o.events
    };
    let cuts = trace
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.copy_bytes == size_of::<ValidationError>()
                && (e.work == 1 || e.work == 2)
        })
        .map(|(n, _)| n + 1)
        .collect::<Vec<_>>();
    assert_eq!(cuts.len(), 2);
    let expected = oracle::ordinary(&m, &f, &summary, ImportPolicy::Refuse).0;
    for (i, stop) in cuts.into_iter().enumerate() {
        let mut o = Observer {
            stop: Some(stop),
            ..Default::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State::default();
        let result = state.run(&m, &f, &summary, ImportPolicy::Refuse, &mut w);
        assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
        assert!(
            matches!(&expected[0],ValidationError::UnauthenticatedImport {detail,..} if detail==&state.detail)
        );
        assert!(state.errors.is_empty());
        assert_eq!(state.errors.capacity() == 0, i == 0);
        assert_eq!(
            state.finish(result, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(state.detail.capacity(), 0);
        assert_eq!(state.errors.capacity(), 0);
    }
}
#[test]
fn original_work_and_copy_caps_accumulate_across_calls_and_are_not_reissued() {
    let (m, f, summary) = fixture();
    let (_, base) = run(&m, &f, &summary, ImportPolicy::Refuse);
    for copy in [false, true] {
        let mut o = Observer {
            cap: (!copy).then_some(base.work),
            byte_cap: copy.then_some(base.bytes),
            ..Default::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        validate_function_summary_import_backing_observed(
            &m,
            &f,
            &summary,
            ImportPolicy::Refuse,
            &mut s,
            site(),
        )
        .unwrap();
        assert_eq!(
            validate_function_summary_import_backing_observed(
                &m,
                &f,
                &summary,
                ImportPolicy::Refuse,
                &mut s,
                site()
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    }
}
