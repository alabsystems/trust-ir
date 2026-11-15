// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn actual_pin_and_entry_first_match_precedence_returns_the_same_borrowed_objects() {
    let r = fixture();
    lookup_events(&r, "early");
    lookup_events(&r, "same");
    lookup_events(&r, "late");
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (p, e) = r
        .entry_for_symbol_observed("same", &mut s, site())
        .unwrap()
        .unwrap();
    assert!(core::ptr::eq(p, &r.pins[1]));
    assert!(core::ptr::eq(e, &r.pins[1].entry_points[1]));
}
#[test]
fn empty_and_exact_raw_symbol_lookup_preserve_case_length_and_unread_input() {
    let r = HandleRegistry {
        pins: vec![pin(vec![entry("λ\0\"same", vec![], vec![])])],
    };
    for symbol in ["", "same", "λ\0\"same", "λ\0\"Same", "λ\0\"same_", "λ"] {
        lookup_events(&r, symbol);
    }
    let empty = HandleRegistry { pins: vec![] };
    assert_eq!(
        lookup_events(&empty, "").events,
        lookup_events(&empty, &"unread λ\0".repeat(4096)).events
    );
}
#[test]
fn every_actual_trusted_entry_symbol_has_original_exact_pointer_identity() {
    let r = HandleRegistry {
        pins: TRUSTED_HANDLE_RUNTIMES.to_vec(),
    };
    for pin in r.pins() {
        for entry in pin.entry_points {
            lookup_events(&r, entry.symbol);
        }
    }
}
#[test]
fn symbol_lookup_does_not_clone_or_read_runtime_path_and_signature_contracts() {
    let a = fixture();
    let mut b = fixture();
    for p in &mut b.pins {
        p.name = Box::leak("ignored λ\0name".repeat(1000).into_boxed_str());
        p.runtime = Box::leak("ignored_runtime".repeat(1000).into_boxed_str());
        let mut entries = p.entry_points.to_vec();
        for e in &mut entries {
            e.role = "changed";
            e.def_path = Box::leak("ignored_path".repeat(1000).into_boxed_str());
            e.params = Box::leak(
                vec![PinnedTy::Scalar(Ty::Tuple(vec![Ty::Bool; 1000]))].into_boxed_slice(),
            );
        }
        p.entry_points = Box::leak(entries.into_boxed_slice());
    }
    for symbol in ["same", "late", "absent"] {
        assert_eq!(
            lookup_events(&a, symbol).events,
            lookup_events(&b, symbol).events
        );
    }
}
#[test]
fn every_actual_nested_row_comparison_cleanup_and_borrow_publication_callback_refuses() {
    let r = fixture();
    for symbol in ["late", "absent"] {
        let baseline = lookup_events(&r, symbol);
        for cut in 1..=baseline.events.len() {
            let mut o = Observer {
                stop: Some(cut),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert!(matches!(
                r.entry_for_symbol_observed(symbol, &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            ));
            assert_eq!(
                s.first_refusal().unwrap().cause,
                "original registry-inner stop"
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
}
#[test]
fn lookups_preserve_original_cumulative_caps_site_zero_fuel_and_preexisting_cause() {
    let r = fixture();
    let baseline = lookup_events(&r, "late");
    for copy in [false, true] {
        let mut o = Observer::default();
        if copy {
            o.byte_cap = Some(baseline.bytes + 1);
        } else {
            o.work_cap = Some(baseline.work + 1);
        }
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        r.entry_for_symbol_observed("late", &mut s, site()).unwrap();
        assert!(matches!(
            r.entry_for_symbol_observed("late", &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
    }
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut o = Observer::default();
    let mut s = ObservedSession::new(options, &mut o);
    r.entry_for_symbol_observed("late", &mut s, site()).unwrap();
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
    assert!(matches!(
        r.entry_for_symbol_observed("late", &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    ));
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original registry-inner stop"
    );
}
