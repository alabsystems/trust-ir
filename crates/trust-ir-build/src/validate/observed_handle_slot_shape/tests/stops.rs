// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_real_carrier_layout_error_display_alignment_retirement_and_publication_callback_refuses() {
    let m = fixture();
    for (ty, count, align) in [
        (handle(), false, None),
        (handle(), true, None),
        (Ty::Ref(Box::new(handle())), false, None),
        (tuple(), false, None),
        (handle(), false, Some(3)),
    ] {
        let (_, baseline, begin, end) = run(&m, &ty, count, align);
        for cut in begin + 1..=end {
            let mut o = Observer {
                stop: Some(cut),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            let (table, nominal) = setup(&m, &mut s);
            assert_eq!(
                slot_shape_observed(&table, &nominal, &ty, count, align, &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(s.first_refusal().unwrap().cause, "original slot-shape stop");
            dispose(table, nominal, &mut s);
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
fn every_actual_fixed_header_shape_formatter_callback_refuses_and_drops_partial_text() {
    let shape = TyLayoutShape {
        size_bits: u64::MAX,
        align_bits: Some(u64::MAX),
        kind: TyLayoutKind::Array {
            elem: TyId::new(u32::MAX),
            len: u64::MAX,
            stride_bits: u64::MAX,
        },
    };
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let text = layout_text::shape(&shape, &mut work).unwrap();
    let end = calls.get();
    work.flat(text);
    drop(work);
    drop(s);
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            layout_text::shape(
                &shape,
                &mut Work {
                    session: &mut s,
                    site: site()
                }
            ),
            Err(ObservedValueError::AdmissionRefused)
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
fn cumulative_original_work_and_copy_refuse_repeated_success_and_semantic_error_results() {
    let m = fixture();
    for ty in [handle(), tuple()] {
        let (_, baseline, _, end) = run(&m, &ty, false, None);
        for copy in [false, true] {
            let cap = baseline.events[..end]
                .iter()
                .map(|e| if copy { e.copy_bytes } else { e.work })
                .sum::<usize>();
            let mut o = Observer::default();
            if copy {
                o.byte_cap = Some(cap)
            } else {
                o.work_cap = Some(cap)
            }
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            let (table, nominal) = setup(&m, &mut s);
            let first =
                slot_shape_observed(&table, &nominal, &ty, false, None, &mut s, site()).unwrap();
            assert_eq!(
                slot_shape_observed(&table, &nominal, &ty, false, None, &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            dispose_reason(first, &mut s);
            dispose(table, nominal, &mut s);
        }
    }
}
#[test]
fn a_refused_real_layout_is_never_reclassified_as_semantic_no_computable_layout() {
    let m = fixture();
    let ty = tuple();
    let (_, baseline, begin, end) = run(&m, &ty, false, None);
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (table, nominal) = setup(&m, &mut s);
        assert!(matches!(
            slot_shape_observed(&table, &nominal, &ty, false, None, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        dispose(table, nominal, &mut s);
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
    }
}
#[test]
fn zero_instruction_fuel_original_site_and_preexisting_refusal_are_not_recaptured() {
    let m = fixture();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut o = Observer::default();
    let mut s = ObservedSession::new(options, &mut o);
    let (table, nominal) = setup(&m, &mut s);
    assert_eq!(
        slot_shape_observed(&table, &nominal, &handle(), false, None, &mut s, site()).unwrap(),
        Ok(8)
    );
    dispose(table, nominal, &mut s);
    assert_eq!(s.remaining_fuel(), 0);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    let (_, _, begin, _) = run(&m, &handle(), false, None);
    let mut o = Observer {
        stop: Some(begin + 1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (table, nominal) = setup(&m, &mut s);
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
        slot_shape_observed(&table, &nominal, &handle(), false, None, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "original slot-shape stop");
    dispose(table, nominal, &mut s);
}
#[test]
fn first_normal_failure_survives_all_cleanup_refusals_and_no_shorter_result_is_published() {
    let m = fixture();
    let (_, _, begin, end) = run(&m, &tuple(), false, None);
    let cut = begin + (end - begin) / 2;
    let mut o = Observer {
        stop: Some(cut),
        cleanup_after: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (table, nominal) = setup(&m, &mut s);
    assert_eq!(
        slot_shape_observed(&table, &nominal, &tuple(), false, None, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    dispose(table, nominal, &mut s);
    assert_eq!(s.first_refusal().unwrap().cause, "original slot-shape stop");
    drop(s);
    assert!(
        o.events[cut..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
