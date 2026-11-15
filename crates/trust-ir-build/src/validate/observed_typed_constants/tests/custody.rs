// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn inspect(m: &Module, c: &Constant, t: &Ty, mut check: impl FnMut(&State<'_>)) {
    // Exact same private entry on both paths: no public-header ordinal guess.
    let layouts = m.layout_table();
    let functions = ModuleFunctionCatalog::new(m);
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let ctx = ObservedConstantSymbols::new_observed(&layouts, &functions, &mut s, site()).unwrap();
    let begin = calls.get();
    let mut state = State::new(c, t, "constant.root");
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    state.run(&ctx, &mut work).unwrap();
    let end = calls.get();
    drain(&mut state, &mut work);
    empty(&state);
    drop(work);
    drop(s);
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let ctx =
            ObservedConstantSymbols::new_observed(&layouts, &functions, &mut s, site()).unwrap();
        let mut state = State::new(c, t, "constant.root");
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            state.run(&ctx, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        check(&state);
        drain(&mut state, &mut work);
        empty(&state);
        assert_eq!(
            work.session.first_refusal().unwrap().cause,
            "original typedconstant stop"
        );
        let _ = ctx.retire_observed(work.session, work.site);
    }
}
#[test]
fn all_partial_paths_frames_uniform_tables_and_prior_errors_are_fully_drained() {
    let m = fixture();
    let (c, t) = nested();
    let mut saw = false;
    inspect(&m, &c, &t, |s| {
        saw |= !s.pending.is_empty() && !s.errors.is_empty();
    });
    assert!(saw);
}
#[test]
fn full_enum_assignment_is_parent_owned_through_all_later_child_stops() {
    let m = fixture();
    let c = Constant::Aggregate(vec![Constant::Int(2)]);
    let mut saw = false;
    inspect(&m, &c, &Ty::Enum(EnumId::new(0)), |s| {
        if let Some(v) = &s.discriminants {
            assert_eq!(v, &vec![0, 1, 2]);
            saw = true;
        }
    });
    assert!(saw);
}
#[test]
fn complete_child_render_and_prior_error_stay_owned_before_diagnostic_transfer() {
    let m = fixture();
    let name = "é🦀runtime".repeat(100);
    let c = Constant::Aggregate(vec![Constant::Int(300), sym(&name, -7)]);
    let t = Ty::Tuple(vec![Ty::U8, Ty::handle("é🦀Handle".repeat(100), name)]);
    let mut saw = false;
    inspect(&m, &c, &t, |s| {
        saw |= !s.errors.is_empty() && !s.expected.is_empty() && !s.actual.is_empty();
    });
    assert!(saw);
}
#[test]
fn whole_layout_arc_and_semantic_error_are_owned_before_next_parent_admission() {
    let mut m = fixture();
    let mut arc = false;
    inspect(
        &m,
        &fat("u16", 0, Constant::Int(1)),
        &Ty::FatPtr(FatPtrKind::Slice(TyId::new(2))),
        |s| {
            arc |= s.layout.is_some();
        },
    );
    assert!(arc);
    m.types.push(Ty::Tuple(vec![Ty::Bool]));
    m.globals.push(global(
        "tuple",
        Ty::Array(TyId::new(4), 1),
        Some(Constant::Uninit),
    ));
    let mut error = false;
    inspect(
        &m,
        &fat("tuple", 0, Constant::Int(1)),
        &Ty::FatPtr(FatPtrKind::Slice(TyId::new(4))),
        |s| {
            error |= s.layout_error.is_some();
        },
    );
    assert!(error);
}
#[test]
fn owning_pointer_reason_string_stays_parent_owned_until_full_error_transfer() {
    let mut m = fixture();
    m.globals[0].ty = Ty::handle("é🦀Handle".repeat(100), "é🦀Runtime".repeat(100));
    let spelling = m.globals[0].ty.to_string();
    let mut saw = false;
    inspect(&m, &sym("G", 0), &Ty::Ref(Box::new(Ty::Bool)), |s| {
        if let Some(PointerConstantRefusal::PointeeTypeMismatch { global_ty }) = &s.reason {
            assert_eq!(global_ty, &spelling);
            saw = true;
        }
    });
    assert!(saw);
}
#[test]
fn successful_errors_require_explicit_caller_retirement_and_keep_terminal_receipt() {
    let m = fixture();
    let (c, t) = nested();
    let layouts = m.layout_table();
    let functions = ModuleFunctionCatalog::new(&m);
    for refuse in [false, true] {
        let arm = Rc::new(Cell::new(false));
        let mut o = Observer {
            cleanup: Some(arm.clone()),
            ..Observer::default()
        };
        let calls = o.calls.clone();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let ctx =
            ObservedConstantSymbols::new_observed(&layouts, &functions, &mut s, site()).unwrap();
        let out =
            validate_constant_against_ty_observed(&ctx, &c, &t, "constant.root", &mut s, site())
                .unwrap();
        assert_eq!(out, original(&m, &c, &t, "constant.root"));
        let before = calls.get();
        arm.set(refuse);
        let result = retire_validation_errors_observed(out, &mut s, site());
        if refuse {
            assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
            assert_eq!(s.first_refusal().unwrap().cause, "cleanup");
        } else {
            result.unwrap();
        }
        let end = calls.get();
        let _ = ctx.retire_observed(&mut s, site());
        drop(s);
        let tail = &o.events[before..end];
        if refuse {
            assert!(
                tail.iter()
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        } else {
            assert!(
                tail[..tail.len() - 1]
                    .iter()
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
            let e = tail.last().unwrap();
            assert_eq!(
                (e.phase, e.work, e.copy_bytes),
                (ExecutionPhase::Publication, 0, 0)
            );
        }
    }
}
