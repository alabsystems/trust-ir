// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_bound_lookup_signature_equality_display_and_output_callback_refuses() {
    let mut m = fixture();
    m.func_types[1].params = vec![Ty::Bool];
    let node = inst();
    let (_, baseline, begin, end) = run(&m, &node);
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let catalog = setup(&m, &mut s);
        assert_eq!(
            validate_seq_map_observed(&catalog, &node, BlockId::new(1), &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let _ = catalog.retire_observed(&mut s, site());
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
fn cumulative_original_work_and_copy_cover_repeated_forward_checks_without_regrant() {
    let mut m = fixture();
    m.func_types[1].params = vec![Ty::Bool];
    let (_, baseline, _, end) = run(&m, &inst());
    for copy in [false, true] {
        let cap = baseline.events[..end]
            .iter()
            .map(|e| if copy { e.copy_bytes } else { e.work })
            .sum();
        let mut o = Observer::default();
        if copy {
            o.byte_cap = Some(cap)
        } else {
            o.work_cap = Some(cap)
        }
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let catalog = setup(&m, &mut s);
        let first =
            validate_seq_map_observed(&catalog, &inst(), BlockId::new(1), &mut s, site()).unwrap();
        assert_eq!(
            validate_seq_map_observed(&catalog, &inst(), BlockId::new(1), &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let _ = retire_validation_errors_observed(first, &mut s, site());
        let _ = catalog.retire_observed(&mut s, site());
    }
}
#[test]
fn zero_fuel_preexisting_stop_and_first_cause_remain_original() {
    let m = fixture();
    let mut o = Observer::default();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut s = ObservedSession::new(options, &mut o);
    let catalog = setup(&m, &mut s);
    let out =
        validate_seq_map_observed(&catalog, &inst(), BlockId::new(1), &mut s, site()).unwrap();
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    catalog.retire_observed(&mut s, site()).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
    drop(s);
    let (_, _, begin, _) = run(&m, &inst());
    let mut o = Observer {
        stop: Some(begin + 1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let catalog = setup(&m, &mut s);
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
        validate_seq_map_observed(&catalog, &inst(), BlockId::new(1), &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "original SeqMap stop");
    let _ = catalog.retire_observed(&mut s, site());
}
#[test]
fn actual_catalog_stop_is_not_forward_absence_and_cleanup_cannot_replace_cause() {
    let m = fixture();
    let (_, _, begin, _) = run(&m, &inst());
    let cut = begin + 3;
    let mut o = Observer {
        stop: Some(cut),
        cleanup_after: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let catalog = setup(&m, &mut s);
    assert_eq!(
        validate_seq_map_observed(&catalog, &inst(), BlockId::new(1), &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    let _ = catalog.retire_observed(&mut s, site());
    assert_eq!(s.first_refusal().unwrap().cause, "original SeqMap stop");
    drop(s);
    assert!(
        o.events[cut..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
