// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_same_private_return_cut_holds_prior_errors_and_full_type_children_until_drain() {
    let (mut m, f) = fixture();
    m.func_types[0].returns = vec![
        Ty::U64,
        Ty::Tuple(vec![Ty::handle("Name", "rt::Name"), Ty::Bool]),
    ];
    let inst = Inst::Return {
        values: vec![v(0), v(1), v(99)],
    };
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let (values, signature) = setup(&m, &f, &mut s);
    let begin = calls.get();
    let mut state = State::default();
    state
        .run(
            &inst,
            signature,
            &values,
            f.entry,
            &mut Work {
                session: &mut s,
                site: site(),
            },
        )
        .unwrap();
    let end = calls.get();
    drain(
        &mut state,
        &mut Work {
            session: &mut s,
            site: site(),
        },
    );
    values.retire_observed(&mut s, site()).unwrap();
    drop(s);
    let (mut prior, mut child) = (false, false);
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (values, signature) = setup(&m, &f, &mut s);
        let mut state = State::default();
        assert_eq!(
            state.run(
                &inst,
                signature,
                &values,
                f.entry,
                &mut Work {
                    session: &mut s,
                    site: site()
                }
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        prior |= !state.errors.is_empty();
        child |= state.expected.capacity() != 0 || state.actual.capacity() != 0;
        drain(
            &mut state,
            &mut Work {
                session: &mut s,
                site: site(),
            },
        );
        assert!(empty(&state));
        let _ = values.retire_observed(&mut s, site());
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
    assert!(prior && child);
}
#[test]
fn full_missing_signature_error_stays_caller_owned_until_same_session_consuming_retirement() {
    let (m, mut f) = fixture();
    f.ty = FuncTyId::new(99);
    f.name = "complete λ\0".repeat(1000);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let error = function_signature_observed(&m, &f, &mut s, site())
        .unwrap()
        .unwrap_err();
    assert_eq!(
        error,
        ValidationError::FuncTypeNotFound {
            func_name: f.name.clone(),
            func_ty_id: 99
        }
    );
    retire_validation_error_observed(error, &mut s, site()).unwrap();
    let end = calls.get();
    drop(s);
    assert_eq!(
        o.events[end - 1],
        ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 0,
            copy_bytes: 0
        }
    );
}
#[test]
fn all_partial_return_fields_and_prior_output_drain_under_sticky_first_refusal() {
    let mut state = State {
        expected: "whole expected λ".repeat(400),
        actual: "whole actual λ".repeat(400),
        errors: vec![
            ValidationError::ReturnTypeMismatch {
                block: 1,
                expected: "prior expected".repeat(300),
                actual: "prior actual".repeat(300),
            },
            ValidationError::ReturnArityMismatch {
                block: 1,
                expected: 2,
                actual: 3,
            },
        ],
    };
    let mut o = Observer {
        stop: Some(1),
        cleanup_after: Some(1),
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
    drain(
        &mut state,
        &mut Work {
            session: &mut s,
            site: site(),
        },
    );
    assert!(empty(&state));
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original return rule stop"
    );
    drop(s);
    assert!(
        o.events[1..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn final_whole_return_output_publication_failure_consumes_every_prior_error() {
    let (m, f) = fixture();
    let inst = Inst::Return {
        values: vec![v(0), v(1), v(99)],
    };
    let (_, baseline, _, end) = run(&m, &f, &inst);
    let mut o = Observer {
        stop: Some(end),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (values, signature) = setup(&m, &f, &mut s);
    assert_eq!(
        validate_return_instruction_observed(&inst, signature, &values, f.entry, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    let _ = values.retire_observed(&mut s, site());
    drop(s);
    assert_eq!(&o.events[..end], &baseline.events[..end]);
    assert!(
        o.events[end..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
