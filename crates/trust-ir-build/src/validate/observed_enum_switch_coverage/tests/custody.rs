// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn inspect(m: &Module, mut check: impl FnMut(&State<'_, '_>)) {
    let layouts = m.layout_table();
    let mut base = Observer::default();
    let calls = base.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let values = setup(m, &mut s);
    let begin = calls.get();
    let mut state = State::default();
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    state
        .run(&layouts, &m.functions[0], &values, &mut w)
        .unwrap();
    let end = calls.get();
    drain(&mut state, &mut w);
    empty(&state);
    values.retire_observed(w.session, w.site).unwrap();
    drop(w);
    drop(s);
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let values = setup(m, &mut s);
        let mut state = State::default();
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            state.run(&layouts, &m.functions[0], &values, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        check(&state);
        drain(&mut state, &mut w);
        empty(&state);
        assert_eq!(
            w.session.first_refusal().unwrap().cause,
            "original enum-coverage stop"
        );
        let _ = values.retire_observed(w.session, w.site);
    }
}
#[test]
fn full_discriminant_child_vector_and_borrowed_definition_are_owned_before_next_fee() {
    let m = fixture();
    let mut saw = false;
    inspect(&m, |s| {
        if s.discriminants == [0, 1] {
            saw = true;
            assert!(s.selection.is_some());
            assert!(!s.enum_ty.is_empty());
        }
    });
    assert!(saw);
}
#[test]
fn whole_widening_definition_bits_and_coverage_buffers_drain_after_interior_stop() {
    let m = signed();
    let (mut widen, mut bits, mut covered) = (false, false, false);
    inspect(&m, |s| {
        widen |= s.widen.len() == 2 && !s.definitions.is_empty();
        bits |= s.disc_bits.len() == 2;
        covered |= s.covered.len() == 2;
    });
    assert!(widen && bits && covered);
}
#[test]
fn full_literal_reason_missing_string_and_prior_errors_remain_parent_owned() {
    let mut m = fixture();
    m.enums[0].variants[1].name = "é🦀".repeat(300);
    m.functions[0].blocks[0].body[1] = switch(1, vec![Constant::Int(9)]);
    let (mut literal, mut missing, mut complete) = (false, false, false);
    inspect(&m, |s| {
        literal |= s.literal == "9" && s.reason.starts_with("case value 9");
        missing |= !s.errors.is_empty() && s.reason.contains(&m.enums[0].variants[1].name);
        complete |= s.reason.ends_with("}, so the default arm is reachable") && !s.here.is_empty();
    });
    assert!(literal && missing && complete);
}
#[test]
fn whole_success_errors_stay_original_caller_owned_until_healthy_terminal_or_sticky_cleanup() {
    let m = fixture();
    let layouts = m.layout_table();
    for refuse in [false, true] {
        let arm = Rc::new(Cell::new(false));
        let mut o = Observer {
            cleanup: Some(arm.clone()),
            ..Observer::default()
        };
        let calls = o.calls.clone();
        let trace = o.trace.clone();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let values = setup(&m, &mut s);
        let out = validate_exhaustive_switch_cases_observed(
            &layouts,
            &m.functions[0],
            &values,
            &mut s,
            site(),
        )
        .unwrap();
        let begin = calls.get();
        arm.set(refuse);
        let result = retire_validation_errors_observed(out, &mut s, site());
        if refuse {
            assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
            assert_eq!(s.first_refusal().unwrap().cause, "cleanup");
        } else {
            result.unwrap();
        }
        let end = calls.get();
        {
            let rows = trace.borrow();
            let tail = &rows[begin..end];
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
        // This input map remains the SAME original session's caller custody;
        // inspecting a copied test trace never replaces or renews its owner.
        let _ = values.retire_observed(&mut s, site());
    }
}
