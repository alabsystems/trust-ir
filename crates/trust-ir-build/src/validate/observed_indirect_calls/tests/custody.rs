// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn successful_context_borrows_exact_catalog_function_and_holds_private_caches() {
    let m = fixture();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (catalog, values, nominal) = setup(&m, &mut s);
    let mut c = ObservedIndirectCalls::new_observed(&catalog, 0, &mut s, site()).unwrap();
    assert!(core::ptr::eq(c.catalog, &catalog));
    assert!(core::ptr::eq(c.function, &m.functions[0]));
    let out = c
        .validate_at_observed(0, 1, &values, Some(&nominal), &mut s, site())
        .unwrap();
    assert!(out.is_empty());
    assert!(c.closures.is_some());
    assert!(
        c.pointers
            .as_ref()
            .unwrap()
            .cache_state()
            .provenance_index_built
    );
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    c.retire_inner(&mut Work {
        session: &mut s,
        site: site(),
    });
    assert!(c.closures.is_none() && c.pointers.is_none());
    c.retire_observed(&mut s, site()).unwrap();
    dispose(catalog, values, nominal, &mut s);
}
#[test]
fn prior_errors_and_full_expected_actual_strings_are_owned_before_transfer_admission() {
    let mut m = fixture();
    m.functions[1].name = "éname".repeat(300);
    m.functions[1].calling_conv = CallingConv::Fast;
    m.functions[1].ty = FuncTyId::new(2);
    m.functions[0].blocks[0].body[1].inst = call(10, 1, &[1, 0]);
    let (_, _, _, end) = run(&m);
    let mut saw_full = false;
    let mut saw_prior = false;
    // Baseline the SAME private State::run entry after identical context setup.
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let (catalog, values, nominal) = setup(&m, &mut s);
    let mut c = ObservedIndirectCalls::new_observed(&catalog, 0, &mut s, site()).unwrap();
    let begin = calls.get();
    let mut state = State::default();
    state
        .run(
            &mut c,
            0,
            1,
            &values,
            Some(&nominal),
            &mut Work {
                session: &mut s,
                site: site(),
            },
        )
        .unwrap();
    let private_end = calls.get();
    state.retire_scratch(&mut Work {
        session: &mut s,
        site: site(),
    });
    retire_validation_errors_observed(take(&mut state.errors), &mut s, site()).unwrap();
    c.retire_observed(&mut s, site()).unwrap();
    dispose(catalog, values, nominal, &mut s);
    drop(s);
    assert!(private_end < end);
    for cut in begin + 1..=private_end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (catalog, values, nominal) = setup(&m, &mut s);
        let mut c = ObservedIndirectCalls::new_observed(&catalog, 0, &mut s, site()).unwrap();
        let mut state = State::default();
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            state.run(&mut c, 0, 1, &values, Some(&nominal), &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        saw_full |=
            !state.name.is_empty() && !state.expected.is_empty() && !state.actual.is_empty();
        saw_prior |= state.errors.len() >= 2;
        state.retire_scratch(&mut work);
        let _ = retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
        empty(&state);
        c.retire_inner(&mut work);
        assert!(c.closures.is_none() && c.pointers.is_none());
        drop(work);
        dispose(catalog, values, nominal, &mut s);
    }
    assert!(saw_full && saw_prior);
}
#[test]
fn final_empty_and_nonempty_result_publication_refusal_drains_both_cache_children() {
    for mismatch in [false, true] {
        let mut m = fixture();
        m.functions[1].calling_conv = if mismatch {
            CallingConv::Fast
        } else {
            CallingConv::C
        };
        let (_, _, _, end) = run(&m);
        let mut o = Observer {
            stop: Some(end),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (catalog, values, nominal) = setup(&m, &mut s);
        let mut c = ObservedIndirectCalls::new_observed(&catalog, 0, &mut s, site()).unwrap();
        assert_eq!(
            c.validate_at_observed(0, 1, &values, Some(&nominal), &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(c.closures.is_none() && c.pointers.is_none());
        dispose(catalog, values, nominal, &mut s);
    }
}

#[test]
fn healthy_caller_retirement_ends_zero_publication_after_complete_child_cleanup() {
    let m = fixture();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (catalog, values, nominal) = setup(&m, &mut s);
    let mut c = ObservedIndirectCalls::new_observed(&catalog, 0, &mut s, site()).unwrap();
    let out = c
        .validate_at_observed(0, 1, &values, Some(&nominal), &mut s, site())
        .unwrap();
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    c.retire_observed(&mut s, site()).unwrap();
    drop(s);
    assert_eq!(
        *o.events.last().unwrap(),
        ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 0,
            copy_bytes: 0
        }
    );
    // Caller-owned module/values/nominal/catalog remain separate stores.
    drop((catalog, values, nominal));
}
#[test]
fn cached_second_edge_still_uses_its_own_actual_coordinates_and_operands() {
    let mut m = fixture();
    m.functions[0].blocks[0]
        .body
        .insert(2, InstrNode::new(call(10, 1, &[0, 1])));
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (catalog, values, nominal) = setup(&m, &mut s);
    let mut c = ObservedIndirectCalls::new_observed(&catalog, 0, &mut s, site()).unwrap();
    for index in [1, 2, 3] {
        let out = c
            .validate_at_observed(0, index, &values, Some(&nominal), &mut s, site())
            .unwrap();
        assert_eq!(out, original::original(&m, 0, index));
        retire_validation_errors_observed(out, &mut s, site()).unwrap();
    }
    c.retire_observed(&mut s, site()).unwrap();
    dispose(catalog, values, nominal, &mut s);
}
#[test]
fn joined_closure_parameter_lists_short_circuit_without_clone_or_abi_normalization() {
    let mut m = closure();
    m.func_types[3].abi = Some(abi());
    assert!(run(&m).0.is_empty());
    m.func_types[3].params[0] = Ty::U8;
    let e = run(&m).0;
    assert!(matches!(
        &e[..],
        [ValidationError::CallIndirectClosureTargetMismatch { .. }]
    ));
    m.func_types[3].is_vararg = true;
    assert_eq!(run(&m).0.len(), 1);
}

#[test]
fn invalid_drained_context_cannot_publish_an_empty_nonindirect_result_on_reuse() {
    let m = fixture();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (catalog, values, nominal) = setup(&m, &mut s);
    let mut c = ObservedIndirectCalls::new_observed(&catalog, 0, &mut s, site()).unwrap();
    assert_eq!(
        c.validate_at_observed(0, usize::MAX, &values, Some(&nominal), &mut s, site()),
        Err(ObservedValueError::InvalidRange)
    );
    assert!(c.closures.is_none() && c.pointers.is_none());
    assert_eq!(
        c.validate_at_observed(0, 2, &values, Some(&nominal), &mut s, site()),
        Err(ObservedValueError::InvalidRange)
    );
    assert!(s.first_refusal().is_none());
    c.retire_observed(&mut s, site()).unwrap();
    dispose(catalog, values, nominal, &mut s);
}
