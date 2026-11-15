// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn private_end(m: &Module) -> usize {
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut state = State::default();
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    state.run(m, &mut work).unwrap();
    let end = calls.get();
    drain(&mut state, &mut work);
    empty(&state);
    end
}
#[test]
fn whole_child_result_rows_remain_parent_owned_across_later_capture_query_refusal() {
    let mut m = fixture();
    m.functions[0].proofs.clear();
    m.functions[0].blocks[0].body[0] = node(
        Inst::Call {
            callee: FuncId::new(9),
            args: vec![],
        },
        &[10],
    );
    let end = private_end(&m);
    let mut held = false;
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut state = State::default();
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            state.run(&m, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        if !state.results.is_empty() {
            held = true;
            assert_eq!(
                state.results,
                vec![(1, ClosureTyId::new(2)), (2, ClosureTyId::new(1))]
            );
        }
        drain(&mut state, &mut work);
        empty(&state);
    }
    assert!(held);
}
#[test]
fn complete_function_name_capture_string_and_prior_diagnostics_survive_until_transfer() {
    let m = rich();
    let end = private_end(&m);
    let (mut first, mut prior) = (false, false);
    let expected = m.closure_types[1].captures[1].to_string();
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut state = State::default();
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            state.run(&m, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        first |= state.name == m.functions[0].name && state.capture == expected;
        prior |= state.errors.len() == 1 && state.capture == expected;
        drain(&mut state, &mut work);
        empty(&state);
    }
    assert!(first && prior);
}
#[test]
fn final_empty_or_nonempty_module_publication_never_transfers_after_refusal() {
    for empty in [false, true] {
        let mut m = fixture();
        if empty {
            m.functions[0].proofs.clear();
            m.functions[0].blocks[0].body[0].proofs.clear();
        }
        let (_, _, end) = run(&m);
        let mut o = Observer {
            stop: Some(end),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_closure_purity_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
    }
}
#[test]
fn successful_caller_disposal_preserves_mandatory_healthy_terminal_and_first_stop() {
    let m = rich();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = validate_closure_purity_observed(&m, &mut s, site()).unwrap();
    let begin = calls.get();
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
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
    let mut o = Observer {
        stop: Some(begin + 1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = validate_closure_purity_observed(&m, &mut s, site()).unwrap();
    assert_eq!(
        retire_validation_errors_observed(out, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original closure-purity stop"
    );
}
