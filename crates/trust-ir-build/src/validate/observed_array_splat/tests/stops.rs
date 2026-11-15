// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_lookup_type_byte_retirement_and_final_publication_callback_refuses() {
    let m = fixture(Ty::U64);
    for inst in [
        array(0),
        array(2),
        Inst::ArraySplat {
            ty: Ty::Tuple(vec![Ty::handle("é", "rt::中"); 4]),
            value: v(0),
        },
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
                validate_array_splat_observed(&m, &inst, &values, BlockId::new(1), &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(
                s.first_refusal().unwrap().cause,
                "original array-splat stop"
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
fn repeated_calls_share_same_original_cumulative_logical_work_and_copy() {
    let m = fixture(Ty::Bool);
    let inst = array(0);
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
            validate_array_splat_observed(&m, &inst, &values, BlockId::new(1), &mut s, site())
                .unwrap();
        assert_eq!(out.len(), 1);
        assert_eq!(
            validate_array_splat_observed(&m, &inst, &values, BlockId::new(1), &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let _ = retire_validation_errors_observed(out, &mut s, site());
        let _ = values.retire_observed(&mut s, site());
    }
}
#[test]
fn zero_instruction_fuel_and_preexisting_stop_keep_original_context_and_cause() {
    let m = fixture(Ty::Bool);
    let inst = array(u64::MAX);
    let (_, _, begin, _) = run(&m, &inst);
    let mut o = Observer::default();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut s = ObservedSession::new(options, &mut o);
    let values = setup(&m, &mut s);
    assert!(
        validate_array_splat_observed(&m, &inst, &values, BlockId::new(1), &mut s, site())
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
        validate_array_splat_observed(&m, &inst, &values, BlockId::new(1), &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    let _ = values.retire_observed(&mut s, site());
}
