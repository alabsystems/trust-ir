// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_constructor_and_query_callback_refuses_and_retires_context() {
    for m in [fixture(), closure()] {
        let (_, baseline, begin, end) = run(&m);
        for cut in begin + 1..=end {
            let mut o = Observer {
                stop: Some(cut),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            let (catalog, values, nominal) = setup(&m, &mut s);
            match ObservedIndirectCalls::new_observed(&catalog, 0, &mut s, site()) {
                Err(e) => assert_eq!(e, ObservedValueError::AdmissionRefused),
                Ok(mut c) => {
                    assert_eq!(
                        c.validate_at_observed(0, 1, &values, Some(&nominal), &mut s, site()),
                        Err(ObservedValueError::AdmissionRefused)
                    );
                    assert!(c.closures.is_none() && c.pointers.is_none());
                    assert_eq!(
                        c.retire_observed(&mut s, site()),
                        Err(ObservedValueError::AdmissionRefused)
                    );
                }
            }
            assert_eq!(s.first_refusal().unwrap().cause, "original indirect stop");
            dispose(catalog, values, nominal, &mut s);
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
fn long_name_type_and_prior_diagnostics_every_callback_keeps_first_cause() {
    let mut m = fixture();
    m.functions[0].name = "é🦀caller".repeat(300);
    m.functions[1].name = "中target".repeat(300);
    m.functions[1].calling_conv = CallingConv::Fast;
    m.functions[1].ty = FuncTyId::new(2);
    m.functions[0].blocks[0].body[1].inst = call(10, 1, &[1, 0]);
    let (e, baseline, begin, end) = run(&m);
    assert_eq!(e.len(), 4);
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (catalog, values, nominal) = setup(&m, &mut s);
        if let Ok(mut c) = ObservedIndirectCalls::new_observed(&catalog, 0, &mut s, site()) {
            assert_eq!(
                c.validate_at_observed(0, 1, &values, Some(&nominal), &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert!(c.closures.is_none() && c.pointers.is_none());
        }
        assert_eq!(s.first_refusal().unwrap().cause, "original indirect stop");
        dispose(catalog, values, nominal, &mut s);
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
    }
}
#[test]
fn repeated_cached_edges_share_original_cumulative_work_and_copy() {
    let m = fixture();
    let (_, baseline, _, end) = run(&m);
    for copy in [false, true] {
        let total = baseline.events[..end]
            .iter()
            .map(|e| if copy { e.copy_bytes } else { e.work })
            .sum();
        let mut o = Observer::default();
        if copy {
            o.byte_cap = Some(total)
        } else {
            o.work_cap = Some(total)
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (catalog, values, nominal) = setup(&m, &mut s);
        let mut c = ObservedIndirectCalls::new_observed(&catalog, 0, &mut s, site()).unwrap();
        let out = c
            .validate_at_observed(0, 1, &values, Some(&nominal), &mut s, site())
            .unwrap();
        assert!(out.is_empty());
        assert_eq!(
            c.validate_at_observed(0, 1, &values, Some(&nominal), &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(c.closures.is_none() && c.pointers.is_none());
        dispose(catalog, values, nominal, &mut s);
    }
}
#[test]
fn zero_instruction_fuel_and_original_site_survive_actual_pointer_resolution() {
    let m = fixture();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut o = Observer::default();
    let mut s = ObservedSession::new(options, &mut o);
    let (catalog, values, nominal) = setup(&m, &mut s);
    let mut c = ObservedIndirectCalls::new_observed(&catalog, 0, &mut s, site()).unwrap();
    let out = c
        .validate_at_observed(0, 1, &values, Some(&nominal), &mut s, site())
        .unwrap();
    assert!(out.is_empty());
    assert_eq!(s.remaining_fuel(), 0);
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    c.retire_observed(&mut s, site()).unwrap();
    dispose(catalog, values, nominal, &mut s);
}
#[test]
fn invalid_physical_coordinates_are_operational_and_drain_all_actual_caches() {
    let m = fixture();
    for (function, block, index) in [(usize::MAX, 0, 0), (0, usize::MAX, 0), (0, 0, usize::MAX)] {
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (catalog, values, nominal) = setup(&m, &mut s);
        match ObservedIndirectCalls::new_observed(&catalog, function, &mut s, site()) {
            Err(e) => {
                assert_eq!(function, usize::MAX);
                assert_eq!(e, ObservedValueError::InvalidRange)
            }
            Ok(mut c) => {
                assert_eq!(
                    c.validate_at_observed(block, index, &values, Some(&nominal), &mut s, site()),
                    Err(ObservedValueError::InvalidRange)
                );
                assert!(c.closures.is_none() && c.pointers.is_none());
            }
        }
        dispose(catalog, values, nominal, &mut s);
    }
}
#[test]
fn preexisting_refusal_at_first_query_header_still_consumes_all_context_children() {
    let m = fixture();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    // Obtain the exact constructor endpoint, not a guessed equal-size event.
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (catalog, values, nominal) = setup(&m, &mut s);
    let c = ObservedIndirectCalls::new_observed(&catalog, 0, &mut s, site()).unwrap();
    let end = calls.get();
    c.retire_observed(&mut s, site()).unwrap();
    dispose(catalog, values, nominal, &mut s);
    drop(s);
    let mut o = Observer {
        stop: Some(end + 1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (catalog, values, nominal) = setup(&m, &mut s);
    let mut c = ObservedIndirectCalls::new_observed(&catalog, 0, &mut s, site()).unwrap();
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
        c.validate_at_observed(0, 1, &values, Some(&nominal), &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(c.closures.is_none() && c.pointers.is_none());
    dispose(catalog, values, nominal, &mut s);
}

fn closure_cc_refusal_case(family: u8) -> Module {
    let mut module = closure();
    module.functions[1].name = "é🦀closure-target".repeat(160);
    module.functions[1].calling_conv = CallingConv::Rust;
    // Preserve actual earlier argument and physical-signature diagnostics,
    // then exercise the new convention diagnostic after their owned strings.
    module.func_types[3].params[0] = Ty::U8;
    let (callee, sig, args, calling_conv) =
        (v(10), FuncTyId::new(1), vec![v(1), v(0)], CallingConv::C);
    module.functions[0].blocks[0].body[1].inst = match family {
        0 => Inst::CallIndirect {
            callee,
            sig,
            args,
            calling_conv,
        },
        1 => Inst::CallIndirectCannotUnwind {
            callee,
            sig,
            args,
            calling_conv,
        },
        2 => Inst::InvokeIndirect {
            callee,
            sig,
            args,
            calling_conv,
            normal_dest: BlockId::new(2),
            normal_args: vec![],
            unwind_dest: BlockId::new(3),
        },
        _ => unreachable!(),
    };
    module
}

fn closure_cc_refusal_expected(module: &Module) -> Vec<ValidationError> {
    // Keep the frozen pre-convention oracle intact and consume its full
    // earlier diagnostic prefix; the sole additive obligation is explicit.
    let mut expected = original::original(module, 0, 1);
    assert_eq!(expected.len(), 3);
    assert!(matches!(
        expected[0],
        ValidationError::CallIndirectArgTypeMismatch { .. }
    ));
    assert!(matches!(
        expected[1],
        ValidationError::CallIndirectArgTypeMismatch { .. }
    ));
    assert!(matches!(
        expected[2],
        ValidationError::CallIndirectClosureTargetMismatch { .. }
    ));
    expected.push(ValidationError::CallEdgeConvMismatch {
        block: module.functions[0].blocks[0].id.index(),
        callee: module.functions[1].name.clone(),
        declared: "ccc".into(),
        actual: "rustcc".into(),
    });
    expected
}

fn closure_cc_refusal_baseline(module: &Module) -> (Vec<ValidationError>, Observer, usize, usize) {
    let expected = closure_cc_refusal_expected(module);
    let mut observer = Observer::default();
    let calls = observer.calls.clone();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let (catalog, values, nominal) = setup(module, &mut session);
    let begin = calls.get();
    let mut context =
        ObservedIndirectCalls::new_observed(&catalog, 0, &mut session, site()).unwrap();
    let errors = context
        .validate_at_observed(0, 1, &values, Some(&nominal), &mut session, site())
        .unwrap();
    let end = calls.get();
    assert_eq!(errors, expected);
    retire_validation_errors_observed(errors, &mut session, site()).unwrap();
    context.retire_observed(&mut session, site()).unwrap();
    dispose(catalog, values, nominal, &mut session);
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    drop(session);
    assert!(
        observer.events[begin..]
            .iter()
            .all(|event| event.site == site())
    );
    (expected, observer, begin, end)
}

#[test]
fn closure_convention_diagnostic_callbacks_and_caps_retire_all_owned_state() {
    // Local indirect-edge diagnostics only: this does not claim whole-module
    // or Invoke CFG admission. All three dispatch families reach one checker.
    for family in 0..3 {
        let module = closure_cc_refusal_case(family);
        let (expected, baseline, begin, end) = closure_cc_refusal_baseline(&module);
        for cut in begin + 1..=end {
            let mut observer = Observer {
                stop: Some(cut),
                ..Observer::default()
            };
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            let (catalog, values, nominal) = setup(&module, &mut session);
            match ObservedIndirectCalls::new_observed(&catalog, 0, &mut session, site()) {
                Err(error) => assert_eq!(error, ObservedValueError::AdmissionRefused),
                Ok(mut context) => {
                    assert_eq!(
                        context.validate_at_observed(
                            0,
                            1,
                            &values,
                            Some(&nominal),
                            &mut session,
                            site()
                        ),
                        Err(ObservedValueError::AdmissionRefused)
                    );
                    assert!(context.closures.is_none() && context.pointers.is_none());
                    assert_eq!(
                        context.retire_observed(&mut session, site()),
                        Err(ObservedValueError::AdmissionRefused)
                    );
                }
            }
            assert_eq!(
                session.first_refusal().unwrap().cause,
                "original indirect stop"
            );
            dispose(catalog, values, nominal, &mut session);
            assert_eq!(
                session.first_refusal().unwrap().cause,
                "original indirect stop"
            );
            drop(session);
            assert_eq!(&observer.events[..cut], &baseline.events[..cut]);
            assert!(
                observer.events[cut..]
                    .iter()
                    .all(|event| { event.phase == ExecutionPhase::ScratchRetirement })
            );
        }

        // Derive cumulative limits from actual callbacks, not new policy
        // budgets. A published first query cannot reset the original owner.
        for copy in [false, true] {
            let total = baseline.events[..end]
                .iter()
                .map(|event| if copy { event.copy_bytes } else { event.work })
                .sum::<usize>();
            assert!(total > 0);
            let mut observer = Observer::default();
            if copy {
                observer.byte_cap = Some(total);
            } else {
                observer.work_cap = Some(total);
            }
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            let (catalog, values, nominal) = setup(&module, &mut session);
            let mut context =
                ObservedIndirectCalls::new_observed(&catalog, 0, &mut session, site()).unwrap();
            let published = context
                .validate_at_observed(0, 1, &values, Some(&nominal), &mut session, site())
                .unwrap();
            assert_eq!(published, expected);
            assert!(session.first_refusal().is_none());
            assert_eq!(
                context.validate_at_observed(0, 1, &values, Some(&nominal), &mut session, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert!(context.closures.is_none() && context.pointers.is_none());
            let cause = if copy { "copy" } else { "work" };
            assert_eq!(session.first_refusal().unwrap().cause, cause);
            // The first published diagnostics remain owned until explicitly
            // retired, even after a later query drains the private caches.
            let _ = retire_validation_errors_observed(published, &mut session, site());
            assert_eq!(
                context.retire_observed(&mut session, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            dispose(catalog, values, nominal, &mut session);
            assert_eq!(session.first_refusal().unwrap().cause, cause);
            assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
        }
    }

    // Inspect the same actual private State boundary to witness ownership at
    // the new error's reserve/transfer callbacks, then prove every field empty.
    let module = closure_cc_refusal_case(0);
    let expected = closure_cc_refusal_expected(&module);
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let (catalog, values, nominal) = setup(&module, &mut session);
    let mut context =
        ObservedIndirectCalls::new_observed(&catalog, 0, &mut session, site()).unwrap();
    let begin = calls.get();
    let mut state = State::default();
    state
        .run(
            &mut context,
            0,
            1,
            &values,
            Some(&nominal),
            &mut Work {
                session: &mut session,
                site: site(),
            },
        )
        .unwrap();
    let end = calls.get();
    assert_eq!(state.errors, expected);
    state.retire_scratch(&mut Work {
        session: &mut session,
        site: site(),
    });
    retire_validation_errors_observed(take(&mut state.errors), &mut session, site()).unwrap();
    empty(&state);
    context.retire_observed(&mut session, site()).unwrap();
    dispose(catalog, values, nominal, &mut session);
    drop(session);

    let mut saw_new_convention_buffers_with_prior_errors = false;
    for cut in begin + 1..=end {
        let mut observer = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let (catalog, values, nominal) = setup(&module, &mut session);
        let mut context =
            ObservedIndirectCalls::new_observed(&catalog, 0, &mut session, site()).unwrap();
        let mut state = State::default();
        let mut work = Work {
            session: &mut session,
            site: site(),
        };
        assert_eq!(
            state.run(&mut context, 0, 1, &values, Some(&nominal), &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        saw_new_convention_buffers_with_prior_errors |= state.errors.len() == 3
            && state.name == module.functions[1].name
            && state.expected == "ccc"
            && state.actual == "rustcc";
        state.retire_scratch(&mut work);
        let _ = retire_validation_errors_observed(take(&mut state.errors), work.session, site());
        empty(&state);
        context.retire_inner(&mut work);
        assert!(context.closures.is_none() && context.pointers.is_none());
        drop(work);
        assert_eq!(
            session.first_refusal().unwrap().cause,
            "original indirect stop"
        );
        dispose(catalog, values, nominal, &mut session);
        drop(session);
        assert_eq!(&observer.events[..cut], &baseline.events[..cut]);
        assert!(
            observer.events[cut..]
                .iter()
                .all(|event| { event.phase == ExecutionPhase::ScratchRetirement })
        );
    }
    assert!(saw_new_convention_buffers_with_prior_errors);
}
