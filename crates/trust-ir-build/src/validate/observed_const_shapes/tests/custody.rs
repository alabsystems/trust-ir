// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn inspect(m: &Module, mut check: impl FnMut(&State<'_>)) {
    let layouts = m.layout_table();
    let functions = ModuleFunctionCatalog::new(m);
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let symbols =
        ObservedConstantSymbols::new_observed(&layouts, &functions, &mut s, site()).unwrap();
    let begin = calls.get();
    let mut state = State::default();
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    state.run(&symbols, None, &mut work).unwrap();
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
        let symbols =
            ObservedConstantSymbols::new_observed(&layouts, &functions, &mut s, site()).unwrap();
        let mut state = State::default();
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            state.run(&symbols, None, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        check(&state);
        drain(&mut state, &mut work);
        empty(&state);
        assert_eq!(
            work.session.first_refusal().unwrap().cause,
            "original const-shapes stop"
        );
        let _ = symbols.retire_observed(work.session, work.site);
    }
}
#[test]
fn complete_typed_child_vector_is_owned_before_first_error_merge_fee() {
    let m = fixture();
    let mut saw = false;
    inspect(&m, |s| {
        saw |= !s.pending.is_empty() && !s.here.is_empty();
    });
    assert!(saw);
}
#[test]
fn popped_complete_child_error_is_owned_before_parent_reserve_or_push() {
    let m = fixture();
    let mut saw = false;
    inspect(&m, |s| {
        if let Some(ValidationError::ConstTypeMismatch {
            location,
            expected,
            actual,
        }) = &s.row
        {
            assert!(!location.is_empty() && !expected.is_empty() && !actual.is_empty());
            saw = true;
        }
    });
    assert!(saw);
}
#[test]
fn complete_lazy_function_map_is_parent_owned_through_case_and_retirement_stops() {
    let m = fixture();
    let mut saw = false;
    inspect(&m, |s| {
        saw |= s.values.is_some() && s.here.contains("switch case");
    });
    assert!(saw);
}
#[test]
fn partial_canonical_frames_and_prior_diagnostics_drain_without_a_smaller_success() {
    let mut m = fixture();
    m.globals.push(global(
        "tree",
        Ty::Tuple(vec![Ty::U128, Ty::U128]),
        Some(Constant::Aggregate(vec![
            Constant::U128(u128::MAX),
            Constant::U128(1),
        ])),
    ));
    let root = m.globals.last().unwrap().initializer.as_ref().unwrap();
    let layouts = m.layout_table();
    let functions = ModuleFunctionCatalog::new(&m);
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let symbols =
        ObservedConstantSymbols::new_observed(&layouts, &functions, &mut session, site()).unwrap();
    let mut state = State::default();
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    state.run(&symbols, None, &mut work).unwrap();
    assert!(!state.errors.is_empty());
    let begin = calls.get();
    assert_eq!(state.canonical(root, &mut work), Ok(false));
    let end = calls.get();
    drain(&mut state, &mut work);
    empty(&state);
    symbols.retire_observed(work.session, work.site).unwrap();
    drop(work);
    drop(session);
    let mut saw = false;
    for cut in begin + 1..=end {
        let mut observer = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let symbols =
            ObservedConstantSymbols::new_observed(&layouts, &functions, &mut session, site())
                .unwrap();
        let mut state = State::default();
        let mut work = Work {
            session: &mut session,
            site: site(),
        };
        state.run(&symbols, None, &mut work).unwrap();
        let prior = state.errors.len();
        assert!(prior > 0);
        // one() retires canonical frames before propagating its result.
        // Inspect the real canonical helper before that caller cleanup, with
        // real prior diagnostics and the SAME cumulative session still live.
        assert_eq!(
            state.canonical(root, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(state.errors.len(), prior);
        saw |= !state.canonical_pending.is_empty() && !state.errors.is_empty();
        drain(&mut state, &mut work);
        empty(&state);
        assert_eq!(
            work.session.first_refusal().unwrap().cause,
            "original const-shapes stop"
        );
        let _ = symbols.retire_observed(work.session, work.site);
    }
    assert!(saw);
}
#[test]
fn equal_byte_foreign_nominal_summary_is_refused_before_context_or_source_walk() {
    let m = fixture();
    let other = m.clone();
    let layouts = m.layout_table();
    let functions = ModuleFunctionCatalog::new(&m);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let summary = other
        .nominal_type_reachability_observed(&mut s, site())
        .unwrap();
    assert!(core::ptr::eq(summary.source_module(), &other));
    let before = calls.get();
    assert_eq!(
        validate_const_shapes_observed(&layouts, &functions, Some(&summary), &mut s, site()),
        Err(ObservedValueError::InvalidRange)
    );
    assert_eq!(calls.get(), before + 1);
    assert!(s.first_refusal().is_none());
    summary.retire_observed(&mut s, site()).unwrap();
}
#[test]
fn successful_whole_output_requires_original_caller_retirement_with_terminal_receipt() {
    let m = fixture();
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
        let out =
            validate_const_shapes_observed(&layouts, &functions, None, &mut s, site()).unwrap();
        assert_eq!(out, original(&m, false));
        let begin = calls.get();
        arm.set(refuse);
        let result = retire_validation_errors_observed(out, &mut s, site());
        if refuse {
            assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
            assert_eq!(s.first_refusal().unwrap().cause, "cleanup");
        } else {
            result.unwrap();
        }
        drop(s);
        let tail = &o.events[begin..];
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
