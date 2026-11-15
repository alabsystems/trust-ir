// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn rows(count: usize) -> Module {
    let mut m = targets();
    let s = m.structs[0].clone();
    let e = m.enums[0].clone();
    let r = m.records[0].clone();
    m.structs = (0..count)
        .map(|i| StructDef {
            id: StructId::new(1000 + i as u32),
            ..s.clone()
        })
        .collect();
    m.enums = (0..count)
        .map(|i| {
            let mut row = e.clone();
            row.id = EnumId::new(1000 + i as u32);
            row
        })
        .collect();
    m.records = (0..count)
        .map(|i| RecordDef {
            id: RecordId::new(1000 + i as u32),
            ..r.clone()
        })
        .collect();
    m
}
fn named(id: u32) -> [Ty; 3] {
    [
        Ty::Struct(StructId::new(id)),
        Ty::Enum(EnumId::new(id)),
        Ty::Record(RecordId::new(id)),
    ]
}
fn set_id(m: &mut Module, row: usize, id: u32) {
    m.structs[row].id = StructId::new(id);
    m.enums[row].id = EnumId::new(id);
    m.records[row].id = RecordId::new(id);
}
#[test]
fn off_index_late_definitions_preserve_actual_named_lookup_success() {
    let mut m = rows(40);
    set_id(&mut m, 39, 7);
    let r = registry();
    for ty in named(7) {
        assert!(run(&m, &r, &ty, "raw location").0.0.is_empty());
    }
    // Out-of-range IDs also use the physical fallback, not only mismatches.
    set_id(&mut m, 39, u32::MAX);
    for ty in named(u32::MAX) {
        assert!(run(&m, &r, &ty, "L").0.0.is_empty());
    }
}
#[test]
fn matching_index_fast_path_and_first_fallback_match_do_not_walk_later_rows() {
    let r = registry();
    for index in [0, 7] {
        let mut small = rows(8);
        let mut large = rows(80);
        set_id(&mut small, index, 7);
        set_id(&mut large, index, 7);
        for ty in named(7) {
            let (_, a, na) = run(&small, &r, &ty, "L");
            let (_, b, nb) = run(&large, &r, &ty, "L");
            assert_eq!(a.events[..na], b.events[..nb]);
        }
    }
}
#[test]
fn absent_and_mismatched_ids_charge_each_actual_fallback_row() {
    let r = registry();
    for id in [7, u32::MAX] {
        let small = rows(8);
        let large = rows(20);
        for ty in named(id) {
            let (a, oa, na) = run(&small, &r, &ty, "L");
            let (b, ob, nb) = run(&large, &r, &ty, "L");
            assert_eq!(a, b);
            assert_eq!(nb - na, 3 * (20 - 8));
            assert_eq!(ob.work - oa.work, 3 * (20 - 8));
        }
    }
}
#[test]
fn every_late_or_absent_lookup_callback_is_a_typed_original_owner_stop() {
    let r = registry();
    for present in [false, true] {
        let mut m = rows(16);
        if present {
            set_id(&mut m, 15, 7);
        }
        for ty in named(7) {
            let (_, baseline, bound) = run(&m, &r, &ty, "raw λ\0tail");
            for cut in 1..=bound {
                let mut o = Observer {
                    stop: Some(cut),
                    ..Observer::default()
                };
                let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
                assert_eq!(
                    validate_type_reference_node_observed(
                        &m,
                        &r,
                        &ty,
                        "raw λ\0tail",
                        &mut s,
                        site()
                    ),
                    Err(ObservedValueError::AdmissionRefused)
                );
                assert_eq!(
                    s.first_refusal().unwrap().cause,
                    "original type-reference stop"
                );
                drop(s);
                assert_eq!(&o.events[..cut], &baseline.events[..cut]);
                assert!(
                    o.events[cut..]
                        .iter()
                        .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
                );
                assert!(o.events.iter().all(|e| e.site == site()));
            }
        }
    }
}
#[test]
fn successive_fallback_scans_cannot_renew_original_cumulative_work_or_copy() {
    let mut m = rows(32);
    set_id(&mut m, 31, 7);
    let r = registry();
    for ty in named(7) {
        let (_, baseline, _) = run(&m, &r, &ty, "L");
        for copy in [false, true] {
            let mut o = Observer::default();
            if copy {
                o.byte_cap = Some(baseline.bytes + 1);
            } else {
                o.work_cap = Some(baseline.work + 1);
            }
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            let (out, _) =
                validate_type_reference_node_observed(&m, &r, &ty, "L", &mut s, site()).unwrap();
            retire_validation_errors_observed(out, &mut s, site()).unwrap();
            assert_eq!(
                validate_type_reference_node_observed(&m, &r, &ty, "L", &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert!(s.first_refusal().is_some());
        }
    }
}
#[test]
fn interior_fallback_stop_retains_and_fully_retires_prior_raw_state() {
    let mut m = rows(24);
    set_id(&mut m, 23, 7);
    let r = registry();
    for ty in named(7) {
        // Identical private State::node entry, including its single dispatch fee.
        // Index conversion/read/mismatch cost three callbacks; each complete
        // fallback row costs read/compare/advance, before the next row's read.
        let cut = 1 + 3 + 3 * 12 + 2;
        let mut baseline = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
        let mut work = Work {
            session: &mut session,
            site: site(),
        };
        let mut state = State::default();
        state.node(&m, &r, &ty, "L", &mut work).unwrap();
        drain(&mut state, &mut work);
        drop(work);
        drop(session);
        assert!(baseline.events.len() > cut);
        let mut o = Observer {
            stop: Some(cut),
            cleanup_after: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State {
            location: "held λ\0FULL".into(),
            detail: "held detail".into(),
            name: "held name".into(),
            runtime: "held runtime".into(),
            errors: vec![prior(), prior()],
            ..State::default()
        };
        assert_eq!(
            state.node(&m, &r, &ty, "L", &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(state.location, "held λ\0FULL");
        assert_eq!(state.errors, vec![prior(), prior()]);
        assert_eq!(
            work.session.first_refusal().unwrap().cause,
            "original type-reference stop"
        );
        drain(&mut state, &mut work);
        assert!(empty(&state));
        assert_eq!(
            work.session.first_refusal().unwrap().cause,
            "original type-reference stop"
        );
        drop(work);
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
        assert!(o.events.len() > cut + 8);
    }
}
