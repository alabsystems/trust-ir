// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn every(m: &Module, c: &Constant, t: &Ty) {
    let (_, baseline, begin, end) = run(m, c, t);
    let layouts = m.layout_table();
    let functions = ModuleFunctionCatalog::new(m);
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let ctx =
            ObservedConstantSymbols::new_observed(&layouts, &functions, &mut s, site()).unwrap();
        assert_eq!(
            validate_constant_against_ty_observed(&ctx, c, t, "constant.root", &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            "original typedconstant stop"
        );
        let _ = ctx.retire_observed(&mut s, site());
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
fn every_actual_tree_path_field_label_uniform_class_and_error_callback_refuses() {
    let m = fixture();
    let (c, t) = nested();
    every(&m, &c, &t);
}
#[test]
fn every_actual_utf8_raw_uniform_byte_and_complete_spelling_callback_refuses() {
    let m = fixture();
    for utf8 in [false, true] {
        every(
            &m,
            &Constant::Bytes {
                data: vec![0xff; 4],
                utf8,
            },
            &Ty::Array(TyId::new(0), 4),
        );
    }
    every(
        &m,
        &Constant::Array(vec![Constant::Float(-0.0); 2]),
        &Ty::Array(TyId::new(2), 2),
    );
}
#[test]
fn every_actual_enum_assignment_and_inhabitance_child_callback_refuses() {
    let m = fixture();
    for c in [
        Constant::Aggregate(vec![Constant::Int(0), Constant::Int(300)]),
        Constant::Aggregate(vec![Constant::Int(2)]),
    ] {
        every(&m, &c, &Ty::Enum(EnumId::new(0)));
    }
}
#[test]
fn every_actual_thin_str_and_slice_child_callback_retains_typed_stop() {
    let m = fixture();
    for (c, t) in [
        (sym("G", 0), Ty::Ref(Box::new(Ty::U8))),
        (
            fat("bytes", 1, Constant::Int(1)),
            Ty::FatPtr(FatPtrKind::Str),
        ),
        (
            fat("u16", 1, Constant::Int(1)),
            Ty::FatPtr(FatPtrKind::Slice(TyId::new(2))),
        ),
    ] {
        every(&m, &c, &t);
    }
}
#[test]
fn repeated_complete_walks_keep_both_original_cumulative_caps() {
    let m = fixture();
    let (c, t) = nested();
    let (_, baseline, _, end) = run(&m, &c, &t);
    let layouts = m.layout_table();
    let functions = ModuleFunctionCatalog::new(&m);
    for copy in [false, true] {
        let mut o = Observer::default();
        let cap = baseline.events[..end]
            .iter()
            .map(|e| if copy { e.copy_bytes } else { e.work })
            .sum();
        if copy {
            o.byte_cap = Some(cap)
        } else {
            o.work_cap = Some(cap)
        }
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let ctx =
            ObservedConstantSymbols::new_observed(&layouts, &functions, &mut s, site()).unwrap();
        let out =
            validate_constant_against_ty_observed(&ctx, &c, &t, "constant.root", &mut s, site())
                .unwrap();
        assert_eq!(
            validate_constant_against_ty_observed(&ctx, &c, &t, "constant.root", &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
        let _ = retire_validation_errors_observed(out, &mut s, site());
        let _ = ctx.retire_observed(&mut s, site());
    }
}
#[test]
fn zero_instruction_fuel_and_preexisting_stop_do_not_recapture_or_renew_owner() {
    let m = fixture();
    let (c, t) = nested();
    let layouts = m.layout_table();
    let functions = ModuleFunctionCatalog::new(&m);
    let mut o = Observer::default();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut s = ObservedSession::new(options, &mut o);
    let ctx = ObservedConstantSymbols::new_observed(&layouts, &functions, &mut s, site()).unwrap();
    let out = validate_constant_against_ty_observed(&ctx, &c, &t, "constant.root", &mut s, site())
        .unwrap();
    assert_eq!(out, original(&m, &c, &t, "constant.root"));
    assert_eq!(s.remaining_fuel(), 0);
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    ctx.retire_observed(&mut s, site()).unwrap();
    drop(s);
    let mut o = Observer {
        stop: Some(3),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let ctx = ObservedConstantSymbols::new_observed(&layouts, &functions, &mut s, site()).unwrap();
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
        validate_constant_against_ty_observed(&ctx, &c, &t, "constant.root", &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original typedconstant stop"
    );
    let _ = ctx.retire_observed(&mut s, site());
}
