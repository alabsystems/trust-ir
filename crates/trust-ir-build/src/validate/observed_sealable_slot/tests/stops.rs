// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_query_frame_scan_growth_retirement_and_full_boolean_publication_callback_refuses() {
    let m = fixture();
    for ty in [
        Ty::Struct(StructId::new(1)),
        Ty::Tuple(vec![handle(), Ty::Ref(Box::new(handle()))]),
    ] {
        let (_, baseline, begin, end) = run(&m, &ty);
        for cut in begin + 1..=end {
            let mut o = Observer {
                stop: Some(cut),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            let nominal = m
                .nominal_type_reachability_observed(&mut s, site())
                .unwrap();
            assert_eq!(
                sealable_slot_type_observed(&m, &nominal, &ty, &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(s.first_refusal().unwrap().cause, "original sealable stop");
            let _ = nominal.retire_observed(&mut s, site());
            drop(s);
            assert_eq!(&o.events[..cut], &baseline.events[..cut]);
            assert!(
                o.events[cut..]
                    .iter()
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn cumulative_original_work_and_copy_refuse_repeated_actual_traversals_without_regrant() {
    let m = fixture();
    let ty = Ty::Struct(StructId::new(1));
    let (_, baseline, _, end) = run(&m, &ty);
    for copy in [false, true] {
        let limit = baseline.events[..end]
            .iter()
            .map(|e| if copy { e.copy_bytes } else { e.work })
            .sum::<usize>();
        let mut o = Observer::default();
        if copy {
            o.byte_cap = Some(limit)
        } else {
            o.work_cap = Some(limit)
        }
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let nominal = m
            .nominal_type_reachability_observed(&mut s, site())
            .unwrap();
        assert!(sealable_slot_type_observed(&m, &nominal, &ty, &mut s, site()).unwrap());
        assert_eq!(
            sealable_slot_type_observed(&m, &nominal, &ty, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let _ = nominal.retire_observed(&mut s, site());
    }
}
#[test]
fn zero_instruction_fuel_and_original_request_site_are_retained_through_complete_cleanup() {
    let m = fixture();
    let ty = Ty::Struct(StructId::new(1));
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut o = Observer::default();
    let mut s = ObservedSession::new(options, &mut o);
    let nominal = m
        .nominal_type_reachability_observed(&mut s, site())
        .unwrap();
    assert!(sealable_slot_type_observed(&m, &nominal, &ty, &mut s, site()).unwrap());
    nominal.retire_observed(&mut s, site()).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
}
#[test]
fn first_normal_stop_survives_later_cleanup_refusals_and_cannot_resume_as_false() {
    let m = fixture();
    let ty = Ty::Struct(StructId::new(1));
    let (_, _, begin, end) = run(&m, &ty);
    let cut = begin + (end - begin) / 2;
    let mut o = Observer {
        stop: Some(cut),
        cleanup_after: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let nominal = m
        .nominal_type_reachability_observed(&mut s, site())
        .unwrap();
    assert_eq!(
        sealable_slot_type_observed(&m, &nominal, &ty, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        sealable_slot_type_observed(&m, &nominal, &ty, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    let _ = nominal.retire_observed(&mut s, site());
    assert_eq!(s.first_refusal().unwrap().cause, "original sealable stop");
    drop(s);
    assert!(
        o.events[cut..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
