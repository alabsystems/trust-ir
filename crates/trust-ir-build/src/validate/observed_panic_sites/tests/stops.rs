// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_source_origin_byte_lookup_shape_and_publication_callback_refuses() {
    let mut wrong = fixture();
    wrong.func_types[1].params = vec![Ty::handle("é", "rt::中"); 5];
    for m in [fixture(), long_symbol(), wrong] {
        let (_, baseline, begin, end) = run(&m);
        for cut in begin + 1..=end {
            let mut o = Observer {
                stop: Some(cut),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            let (catalog, values) = setup(&m, &mut s);
            assert_eq!(
                validate_panic_site_at_observed(&catalog, 0, 0, 1, &values, &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(s.first_refusal().unwrap().cause, "original panic-site stop");
            dispose(catalog, values, &mut s);
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
fn repeated_queries_share_the_same_original_cumulative_work_and_copy_caps() {
    let m = fixture();
    let (_, baseline, _, end) = run(&m);
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
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (catalog, values) = setup(&m, &mut s);
        let out =
            validate_panic_site_at_observed(&catalog, 0, 0, 1, &values, &mut s, site()).unwrap();
        assert!(out.is_empty());
        assert_eq!(
            validate_panic_site_at_observed(&catalog, 0, 0, 1, &values, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        dispose(catalog, values, &mut s);
    }
}
#[test]
fn zero_instruction_fuel_and_preexisting_stop_preserve_site_and_first_cause() {
    let m = fixture();
    let (_, _, begin, _) = run(&m);
    let mut o = Observer::default();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut s = ObservedSession::new(options, &mut o);
    let (catalog, values) = setup(&m, &mut s);
    assert!(
        validate_panic_site_at_observed(&catalog, 0, 0, 1, &values, &mut s, site())
            .unwrap()
            .is_empty()
    );
    assert_eq!(s.remaining_fuel(), 0);
    dispose(catalog, values, &mut s);
    drop(s);
    let mut o = Observer {
        stop: Some(begin + 1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (catalog, values) = setup(&m, &mut s);
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
        validate_panic_site_at_observed(&catalog, 0, 0, 1, &values, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "original panic-site stop");
    dispose(catalog, values, &mut s);
}
#[test]
fn invalid_physical_source_coordinates_refuse_without_substituting_a_site() {
    let m = fixture();
    for (f, b, i) in [(usize::MAX, 0, 1), (0, usize::MAX, 1), (0, 0, usize::MAX)] {
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (catalog, values) = setup(&m, &mut s);
        assert_eq!(
            validate_panic_site_at_observed(&catalog, f, b, i, &values, &mut s, site()),
            Err(ObservedValueError::InvalidRange)
        );
        dispose(catalog, values, &mut s);
    }
}
#[test]
fn exact_same_length_last_byte_symbol_difference_and_interior_chunk_refusal_are_observed() {
    let a = "é".repeat(3000);
    // Keep byte lengths equal using an ASCII suffix, then change only last byte.
    let a = a + "AB";
    let b = a[..a.len() - 1].to_owned() + "C";
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        !Work {
            session: &mut s,
            site: site()
        }
        .same_text(&a, &b)
        .unwrap()
    );
    drop(s);
    let cut = o.events.len() / 2;
    let mut o = Observer {
        stop: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        Work {
            session: &mut s,
            site: site()
        }
        .same_text(&a, &a),
        Err(ObservedValueError::AdmissionRefused)
    );
}
