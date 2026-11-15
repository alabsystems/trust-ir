// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn inspect(m: &Module, rule: Rule, mut check: impl FnMut(&State)) {
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut state = State::default();
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    state_run(&mut state, m, rule, &mut w).unwrap();
    let end = calls.get();
    drain(&mut state, &mut w);
    empty(&state);
    drop(w);
    drop(s);
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut state = State::default();
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            state_run(&mut state, m, rule, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        check(&state);
        drain(&mut state, &mut w);
        empty(&state);
        assert_eq!(
            w.session.first_refusal().unwrap().cause,
            "original module-tail stop"
        );
    }
}
#[test]
fn complete_owning_layout_error_is_held_before_any_next_diagnostic_fee() {
    let m = custom();
    let mut saw = false;
    inspect(&m, Rule::Casts, |s| {
        if let Some(Err(LayoutError::TargetScalarLayoutUnavailable { triple })) = &s.result {
            assert_eq!(triple, &m.target_info.as_ref().unwrap().triple);
            saw = true;
        }
    });
    assert!(saw);
}
#[test]
fn complete_cast_strings_and_prior_rows_are_held_until_parent_error_transfer() {
    let m = fixture();
    let mut complete = false;
    let mut prior = false;
    inspect(&m, Rule::Casts, |s| {
        complete |= s.op == "transmute"
            && s.src == "u8"
            && s.dst == "u64"
            && s.reason == "cast layout sizes differ: 8b -> 64b";
        prior |= !s.errors.is_empty() && s.result.is_some();
    });
    assert!(complete && prior);
}
#[test]
fn exhaustive_copy_guarded_cast_evidence_retires_all_variants_after_sticky_stop() {
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
    let mut state = State::default();
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    for value in [
        CastLayoutEvidence::NotLayoutSensitive,
        CastLayoutEvidence::PointerCast {
            src: trust_ir::PointerLayoutShape::thin(64),
            dst: trust_ir::PointerLayoutShape::thin(32),
        },
        CastLayoutEvidence::SameSize {
            size_bits: u64::MAX,
            src_align_bits: Some(128),
            dst_align_bits: None,
        },
        CastLayoutEvidence::ReifyFnPointer { pointer_bits: 128 },
    ] {
        state.result = Some(Ok(value));
        state.retire_result(&mut w);
        assert!(state.result.is_none());
    }
    assert_eq!(
        w.session.first_refusal().unwrap().cause,
        "original module-tail stop"
    );
    drain(&mut state, &mut w);
    empty(&state);
}
#[test]
fn whole_success_outputs_require_original_caller_terminal_or_sticky_retirement() {
    let m = fixture();
    for rule in [Rule::Casts, Rule::Facts] {
        for refuse in [false, true] {
            let arm = Rc::new(Cell::new(false));
            let mut o = Observer {
                cleanup: Some(arm.clone()),
                ..Observer::default()
            };
            let calls = o.calls.clone();
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            let out = call(&m, rule, &mut s).unwrap();
            assert_eq!(out, original(&m, rule));
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
}
