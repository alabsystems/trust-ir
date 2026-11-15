// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_trusted_pin_entry_keeps_the_exact_original_func_ty() {
    for pin in TRUSTED_HANDLE_RUNTIMES {
        for entry in pin.entry_points {
            signature_events(pin, entry);
        }
    }
}
#[test]
fn empty_raw_handle_and_arbitrary_scalar_slots_keep_order_and_no_abi_or_varargs() {
    let mut p = pin(vec![]);
    p.name = "λ\0\"raw";
    p.runtime = "raw::尾\n";
    signature_events(&p, &entry("empty", vec![], vec![]));
    let e = entry(
        "mixed",
        vec![
            PinnedTy::Scalar(Ty::Bool),
            PinnedTy::Handle,
            PinnedTy::Scalar(Ty::Tuple(vec![
                Ty::I128,
                Ty::handle("unvalidated", "raw::Nested"),
            ])),
        ],
        vec![PinnedTy::Handle, PinnedTy::Scalar(Ty::U128)],
    );
    signature_events(&p, &e);
}
#[test]
fn complete_nested_scalar_clone_does_not_strip_or_normalize_input_structure() {
    let p = pin(vec![]);
    let mut nested = Ty::Tuple(vec![Ty::Bool, Ty::handle("Name", "Runtime")]);
    for _ in 0..64 {
        nested = Ty::Ref(Box::new(nested));
    }
    let e = entry(
        "nested",
        vec![PinnedTy::Scalar(nested)],
        vec![PinnedTy::Scalar(Ty::Tuple(vec![Ty::U8; 64]))],
    );
    signature_events(&p, &e);
}
#[test]
fn every_slot_child_clone_handle_allocation_copy_cleanup_and_publication_callback_refuses() {
    let p = pin(vec![]);
    let e = entry(
        "mixed",
        vec![
            PinnedTy::Handle,
            PinnedTy::Scalar(Ty::Tuple(vec![Ty::Bool, Ty::U8])),
        ],
        vec![PinnedTy::Handle],
    );
    let (baseline, bound) = signature_events(&p, &e);
    for cut in 1..=bound {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert!(matches!(
            p.func_ty_observed(&e, &mut s, site()),
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
#[test]
fn successive_complete_signature_and_explicit_retirement_share_cumulative_limits() {
    let p = pin(vec![]);
    let e = entry(
        "H",
        vec![PinnedTy::Handle],
        vec![PinnedTy::Scalar(Ty::Bool)],
    );
    let (baseline, _) = signature_events(&p, &e);
    for copy in [false, true] {
        let mut o = Observer::default();
        if copy {
            o.byte_cap = Some(baseline.bytes + 1);
        } else {
            o.work_cap = Some(baseline.work + 1);
        }
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        p.func_ty_observed(&e, &mut s, site())
            .unwrap()
            .retire_observed(&mut s, site())
            .unwrap();
        assert!(matches!(
            p.func_ty_observed(&e, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
    }
}
#[test]
fn exact_original_fuel_first_cause_full_publication_and_healthy_retirement_receipts() {
    let p = pin(vec![]);
    let e = entry(
        "H",
        vec![PinnedTy::Handle],
        vec![PinnedTy::Scalar(Ty::Bool)],
    );
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(options, &mut o);
    let output = p.func_ty_observed(&e, &mut s, site()).unwrap();
    let start = calls.get();
    output.retire_observed(&mut s, site()).unwrap();
    let end = calls.get();
    assert_eq!(s.remaining_fuel(), 0);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert!(
        o.events[start..end]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement
                || (e.phase == ExecutionPhase::Publication && e.work == 0 && e.copy_bytes == 0))
    );
    assert_eq!(
        o.events[end - 1],
        ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 0,
            copy_bytes: 0
        }
    );
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
        p.func_ty_observed(&e, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    ));
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original registry-inner stop"
    );
    let (baseline, bound) = signature_events(&p, &e);
    let mut o = Observer {
        stop: Some(bound),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        baseline.events[bound - 1].copy_bytes,
        size_of::<ObservedPinnedFuncTy>()
    );
    assert!(matches!(
        p.func_ty_observed(&e, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    ));
    drop(s);
    assert!(
        o.events[bound..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
