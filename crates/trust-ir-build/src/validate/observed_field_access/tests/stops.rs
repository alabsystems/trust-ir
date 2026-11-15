// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_field_tag_variant_type_string_and_publication_callback_refuses() {
    let m = fixture();
    for inst in [
        extract(0, 0, Ty::Ptr),
        extract(4, 0, Ty::Ptr),
        extract(4, 1, Ty::Ptr),
        insert(4, 0, Ty::Ptr, 8),
    ] {
        let (_, baseline, begin, end) = run(&m, &inst);
        for cut in begin + 1..=end {
            let mut o = Observer {
                stop: Some(cut),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            let values = setup(&m, &mut s);
            assert_eq!(
                validate_field_access_observed(&m, &inst, &values, BlockId::new(1), &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(
                s.first_refusal().unwrap().cause,
                "original field-access stop"
            );
            let _ = values.retire_observed(&mut s, site());
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
fn late_nominal_fallback_rows_are_actually_interruptible_not_opaque_getters() {
    let mut m = fixture();
    m.structs = (0..24)
        .map(|i| structure(i + 100, vec![Ty::Bool]))
        .collect();
    m.structs.push(structure(77, vec![Ty::U64]));
    m.functions[0].blocks[0].params[0].1 = Ty::Struct(StructId::new(77));
    let inst = extract(0, 0, Ty::Bool);
    let (_, baseline, begin, end) = run(&m, &inst);
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let values = setup(&m, &mut s);
        assert_eq!(
            validate_field_access_observed(&m, &inst, &values, BlockId::new(1), &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let _ = values.retire_observed(&mut s, site());
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
    }
}
#[test]
fn repeated_queries_share_original_cumulative_work_and_copy_caps() {
    let m = fixture();
    let inst = extract(4, 1, Ty::Ptr);
    let (_, baseline, _, end) = run(&m, &inst);
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
        let values = setup(&m, &mut s);
        let out =
            validate_field_access_observed(&m, &inst, &values, BlockId::new(1), &mut s, site())
                .unwrap();
        assert_eq!(
            validate_field_access_observed(&m, &inst, &values, BlockId::new(1), &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let _ = retire_validation_errors_observed(out, &mut s, site());
        let _ = values.retire_observed(&mut s, site());
    }
}
#[test]
fn zero_instruction_fuel_and_preexisting_stop_preserve_original_context() {
    let m = fixture();
    let inst = extract(4, 0, Ty::U8);
    let (_, _, begin, _) = run(&m, &inst);
    let mut o = Observer::default();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut s = ObservedSession::new(options, &mut o);
    let values = setup(&m, &mut s);
    assert!(
        validate_field_access_observed(&m, &inst, &values, BlockId::new(1), &mut s, site())
            .unwrap()
            .is_empty()
    );
    assert_eq!(s.remaining_fuel(), 0);
    values.retire_observed(&mut s, site()).unwrap();
    drop(s);
    let mut o = Observer {
        stop: Some(begin + 1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let values = setup(&m, &mut s);
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
        validate_field_access_observed(&m, &inst, &values, BlockId::new(1), &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    let _ = values.retire_observed(&mut s, site());
}
#[test]
fn unread_field_payloads_do_not_become_fake_layout_or_expanded_read_credit() {
    let mut traces = Vec::new();
    for ty in [
        Ty::Bool,
        Ty::Tuple(vec![Ty::handle("huge", "rt::unused"); 400]),
    ] {
        let mut m = fixture();
        m.structs[0].fields.push(field(ty));
        let inst = extract(0, 0, Ty::Bool);
        let (_, o, begin, end) = run(&m, &inst);
        traces.push(o.events[begin..end].to_vec());
    }
    assert_eq!(traces[0], traces[1]);
}
