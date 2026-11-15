// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn actual_late_physical_fallback_can_refuse_before_the_matching_callee_is_reached() {
    let mut m = fixture(false);
    let f = m.functions.pop().unwrap();
    m.functions = (0..256)
        .map(|i| {
            let mut f = f.clone();
            f.id = FuncId::new(1000 + i);
            f
        })
        .collect();
    let base = assert_ordinary(&m, FuncId::new(1255), ImportPolicy::Structural);
    // Fixed-width ID/index/borrowed headers can share sizes. Select an actual
    // middle callback, not a claimed Nth semantic visit from an equal-size
    // filter. With the only match last, no lookup result has published here.
    let stop = base.events.len() / 2;
    assert!(stop > 256);
    assert!(
        base.events[..stop]
            .iter()
            .all(|e| e.phase == ExecutionPhase::Validation)
    );
    let mut o = Observer::stopping(stop);
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        admissible_effects_observed(
            &m,
            FuncId::new(1255),
            ImportPolicy::Structural,
            &mut s,
            site()
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
    drop(s);
    assert_eq!(o.events.len(), stop);
}
#[test]
fn every_lookup_and_policy_callback_refuses_instead_of_semantic_havoc_or_partial_success() {
    for m in [fixture(false), fixture(true), Module::new("empty")] {
        let base = assert_ordinary(&m, FuncId::new(221), ImportPolicy::Structural);
        for stop in 1..=base.events.len() {
            let mut o = Observer {
                stop: Some(stop),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                admissible_effects_observed(
                    &m,
                    FuncId::new(221),
                    ImportPolicy::Structural,
                    &mut s,
                    site()
                ),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
            drop(s);
            assert_eq!(o.events.len(), stop);
        }
    }
}
#[test]
fn work_and_copy_caps_accumulate_without_renewing_the_original_lookup_owner() {
    let m = fixture(false);
    let base = assert_ordinary(&m, FuncId::new(221), ImportPolicy::Refuse);
    for copy in [false, true] {
        let mut o = Observer {
            cap: (!copy).then_some(base.work),
            byte_cap: copy.then_some(base.bytes),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert!(
            admissible_effects_observed(&m, FuncId::new(221), ImportPolicy::Refuse, &mut s, site())
                .unwrap()
                .is_some()
        );
        assert_eq!(
            admissible_effects_observed(&m, FuncId::new(221), ImportPolicy::Refuse, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = s.first_refusal().unwrap().progress;
        assert_eq!(
            function_by_id_observed(&m, FuncId::new(221), &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, first);
        assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    }
}
#[test]
fn zero_fuel_exact_instruction_site_and_final_publication_are_preserved() {
    let m = fixture(false);
    let exact = ExecutionSite::Instruction(InstructionSite {
        function: FuncId::new(9),
        block: BlockId::new(8),
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
    assert!(
        admissible_effects_observed(
            &m,
            FuncId::new(221),
            ImportPolicy::Structural,
            &mut s,
            exact
        )
        .unwrap()
        .is_some()
    );
    assert_eq!(s.remaining_fuel(), 0);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == exact));
    let stop = o.events.len();
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    assert_eq!(
        admissible_effects_observed(
            &m,
            FuncId::new(221),
            ImportPolicy::Structural,
            &mut s,
            exact
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
}
