// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn inspect(
    m: &Module,
    selected: impl Fn(&ExecutionProgress) -> bool,
    mut check: impl FnMut(&State<'_>),
) {
    // Baseline and interrupted calls use the SAME private entry (no public
    // initial-header callback offset). Refusal ordinal is actual, not guessed.
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let t = LayoutTable::new_observed(m, &mut s, site()).unwrap();
    let begin = calls.get();
    let mut state = State::default();
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    state.run(&t, &mut w).unwrap();
    let end = calls.get();
    drain(&mut state, &mut w);
    empty(&state);
    drop(w);
    drop(state);
    dispose(t, &mut s);
    drop(s);
    let cuts: Vec<_> = (begin + 1..=end)
        .filter(|cut| selected(&o.events[cut - 1]))
        .collect();
    assert!(!cuts.is_empty());
    for cut in cuts {
        let mut o = Observer {
            stop: Some(cut),
            ..Default::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let t = LayoutTable::new_observed(m, &mut s, site()).unwrap();
        let mut state = State::default();
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            state.run(&t, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        check(&state);
        drain(&mut state, &mut w);
        empty(&state);
        assert_eq!(
            w.session.first_refusal().unwrap().cause,
            "original ABI-group stop"
        );
        drop(w);
        drop(state);
        dispose(t, &mut s);
    }
}
#[test]
fn complete_layout_arc_is_parent_owned_before_size_read_or_retirement() {
    let m = one(Ty::U64, fact(PassMode::Ignore));
    let mut saw = false;
    inspect(
        &m,
        |_| true,
        |state| {
            if let Some(Ok(shape)) = &state.layout {
                saw = true;
                assert_eq!(shape.size_bytes(), Some(8));
            }
        },
    );
    assert!(saw);
}
#[test]
fn complete_layout_error_is_parent_owned_before_semantic_unavailable_detail() {
    let m = one(Ty::Sequence(TyId::new(100)), fact(PassMode::Ignore));
    let mut saw = false;
    inspect(
        &m,
        |_| true,
        |state| saw |= matches!(&state.layout, Some(Err(_))),
    );
    assert!(saw);
}
#[test]
fn full_legacy_reconciliation_error_is_held_before_error_vector_reservation() {
    let mut m = typed();
    m.functions[0].calling_conv = trust_ir::CallingConv::Fast;
    let expected = m.func_types[0]
        .abi
        .as_ref()
        .unwrap()
        .reconcile_function(&m.functions[0])
        .unwrap_err();
    let mut saw = false;
    inspect(
        &m,
        |e| e.phase == ExecutionPhase::Validation && e.work == 1,
        |state| {
            if let Some(Err(text)) = &state.pending_abi {
                saw = true;
                assert_eq!(text, &expected);
            }
        },
    );
    assert!(saw);
}
#[test]
fn prior_errors_partial_detail_slot_and_pending_slot_stay_owned_until_full_drain() {
    let m = many_errors();
    let (mut errors, mut detail, mut slot, mut pending) = (false, false, false, false);
    inspect(
        &m,
        |_| true,
        |s| {
            errors |= !s.errors.is_empty();
            detail |= !s.detail.is_empty();
            slot |= !s.slot.is_empty();
            pending |= !s.pending_slot.is_empty();
        },
    );
    assert!(errors && detail && slot && pending);
}
#[test]
fn whole_signature_semantic_error_is_held_and_never_replaced_by_target_failure() {
    let mut m = typed();
    m.functions.clear();
    m.target_info = None;
    m.func_types[0].abi.as_mut().unwrap().convention.clear();
    let sig = &m.func_types[0];
    let expected = sig.abi.as_ref().unwrap().validate(sig).unwrap_err();
    let mut saw = false;
    inspect(
        &m,
        |e| e.phase == ExecutionPhase::Validation && e.work == 1,
        |state| {
            if let Some(Err(text)) = &state.pending_abi {
                saw = true;
                assert_eq!(text, &expected);
            }
        },
    );
    assert!(saw);
}
#[test]
fn caller_owns_whole_successful_error_vector_through_exact_retirement_terminal() {
    let m = many_errors();
    for refuse in [false, true] {
        let arm = Rc::new(Cell::new(false));
        let mut o = Observer {
            cleanup: Some(arm.clone()),
            ..Default::default()
        };
        let calls = o.calls.clone();
        let trace = o.trace.clone();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let t = LayoutTable::new_observed(&m, &mut s, site()).unwrap();
        let errors = validate_module_abi_facts_observed(&t, &mut s, site()).unwrap();
        assert_eq!(errors, original(&m));
        let begin = calls.get();
        arm.set(refuse);
        let result = retire_validation_errors_observed(errors, &mut s, site());
        let end = calls.get();
        if refuse {
            assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
            assert_eq!(s.first_refusal().unwrap().cause, "cleanup");
        } else {
            result.unwrap();
        }
        {
            let events = trace.borrow();
            let tail = &events[begin..end];
            assert!(!tail.is_empty());
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
        dispose(t, &mut s);
    }
}
