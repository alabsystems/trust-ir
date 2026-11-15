// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn large() -> Module {
    let mut m = fixture();
    for p in &mut m.proof_obligations {
        p.source
            .as_mut()
            .unwrap()
            .public
            .as_mut()
            .unwrap()
            .obligation_id = "invalid?".to_string() + &"D".repeat(3000);
    }
    m
}
fn prefix(m: &Module, copy: bool) -> (Observer, usize) {
    let row = &m.proof_obligations[1];
    let source = row.source.as_ref().unwrap();
    let public = source.public.as_ref().unwrap();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = seeded();
    // Exact real State.row prefix through its optional first raw duplicate copy,
    // including the earlier real scalar diagnostic. No inferred global ordinal.
    assert!(w.source_id(&source.source_id).unwrap());
    assert!(w.source_id(&source.assertion_id).unwrap());
    w.admit(1, size_of::<Option<ProofObligationSourceRange>>())
        .unwrap();
    assert!(source.range.is_none());
    w.admit(1, size_of::<Option<&PublicObligationIdentity>>())
        .unwrap();
    assert!(!w.public_id(&public.obligation_id).unwrap());
    state.prepare(&mut w).unwrap();
    state
        .errors
        .push(ValidationError::InvalidPublicObligationId {
            obligation: row.id.index(),
        });
    w.admit(2, size_of::<ProofDigestAlgorithm>()).unwrap();
    assert_eq!(
        public.semantic_digest.algorithm,
        ProofDigestAlgorithm::Sha256
    );
    w.admit(64, size_of::<ProofDigest>()).unwrap();
    assert!(!public.semantic_digest.is_zero());
    assert_eq!(
        w.first_public(m, 1, &public.obligation_id).unwrap(),
        Some(5)
    );
    if copy {
        w.text(&public.obligation_id, &mut state.public_id).unwrap();
    }
    let bound = calls.get();
    drain(&mut state, &mut w);
    assert!(empty(&state));
    drop(w);
    drop(s);
    (o, bound)
}
fn row_trace(m: &Module) -> Observer {
    let row = &m.proof_obligations[1];
    let source = row.source.as_ref().unwrap();
    let public = source.public.as_ref().unwrap();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = seeded();
    state.row(m, row, source, 1, &mut w).unwrap();
    assert_eq!(
        state.errors,
        vec![
            prior(),
            ValidationError::InvalidPublicObligationId { obligation: 7 },
            ValidationError::DuplicatePublicObligationId {
                obligation_id: public.obligation_id.clone(),
                first_obligation: 5,
                duplicate_obligation: 7
            }
        ]
    );
    drain(&mut state, &mut w);
    assert!(empty(&state));
    drop(w);
    drop(s);
    o
}
#[test]
fn complete_invalid_duplicate_id_is_owned_before_output_preparation_can_refuse() {
    let m = large();
    let (partial, bound) = prefix(&m, true);
    let base = row_trace(&m);
    assert_eq!(&partial.events[..bound], &base.events[..bound]);
    let stop = bound + 1;
    let p = &m.proof_obligations[1];
    let source = p.source.as_ref().unwrap();
    let full = &source.public.as_ref().unwrap().obligation_id;
    let mut o = Observer {
        stop: Some(stop),
        cleanup_after: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = seeded();
    assert_eq!(
        state.row(&m, p, source, 1, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(&state.public_id, full);
    assert_eq!(
        state.errors,
        vec![
            prior(),
            ValidationError::InvalidPublicObligationId { obligation: 7 }
        ]
    );
    drain(&mut state, &mut w);
    assert!(empty(&state));
    assert_eq!(
        w.session.first_refusal().unwrap().progress,
        base.events[stop - 1]
    );
    assert_eq!(
        w.session.first_refusal().unwrap().cause,
        "original obligation-source stop"
    );
}
#[test]
fn partial_raw_duplicate_copy_preserves_owned_prefix_prior_errors_and_whole_borrowed_input() {
    let m = large();
    let (_, bound) = prefix(&m, false);
    let base = row_trace(&m);
    let stop = bound + 5;
    assert_eq!(
        (
            base.events[bound + 2].work,
            base.events[bound + 2].copy_bytes
        ),
        (1024, 1024)
    );
    assert_eq!(
        (
            base.events[bound + 3].work,
            base.events[bound + 3].copy_bytes
        ),
        (1024, 1024)
    );
    let p = &m.proof_obligations[1];
    let source = p.source.as_ref().unwrap();
    let full = &source.public.as_ref().unwrap().obligation_id;
    assert!(full.len() > 2048);
    let mut o = Observer {
        stop: Some(stop),
        cleanup_after: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = seeded();
    assert_eq!(
        state.row(&m, p, source, 1, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.public_id, &full[..1024]);
    assert_eq!(full.len(), 3008);
    assert_eq!(
        state.errors,
        vec![
            prior(),
            ValidationError::InvalidPublicObligationId { obligation: 7 }
        ]
    );
    drain(&mut state, &mut w);
    assert!(empty(&state));
    assert_eq!(
        w.session.first_refusal().unwrap().progress,
        base.events[stop - 1]
    );
    drop(w);
    drop(s);
    assert!(
        o.events[stop..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn actual_output_reserve_and_transport_refusal_holds_complete_raw_id_and_all_prior_output() {
    let pending = || State {
        public_id: "complete raw public id λ\0TAIL".into(),
        errors: vec![prior()],
    };
    let mut base = Observer::default();
    {
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = pending();
        assert_eq!(state.errors.len(), state.errors.capacity());
        state.prepare(&mut w).unwrap();
        drain(&mut state, &mut w);
    }
    assert_eq!((base.events[0].work, base.events[0].copy_bytes), (1, 0));
    assert_eq!(
        (base.events[1].work, base.events[1].copy_bytes),
        (4, 4 * size_of::<ValidationError>())
    );
    assert_eq!(
        (base.events[2].work, base.events[2].copy_bytes),
        (1, size_of::<ValidationError>() + size_of::<String>())
    );
    for stop in [2, 3] {
        let mut o = Observer {
            stop: Some(stop),
            cleanup_after: Some(stop),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = pending();
        let capacity = state.errors.capacity();
        assert_eq!(
            state.prepare(&mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(state.public_id, "complete raw public id λ\0TAIL");
        assert_eq!(state.errors, vec![prior()]);
        if stop == 2 {
            assert_eq!(state.errors.capacity(), capacity);
        }
        drain(&mut state, &mut w);
        assert!(empty(&state));
        assert_eq!(
            w.session.first_refusal().unwrap().progress,
            base.events[stop - 1]
        );
    }
}
#[test]
fn a_later_actual_source_row_stop_retains_the_full_earlier_owned_duplicate_diagnostic() {
    let mut m = fixture();
    m.proof_obligations.push(row(9, Some(source("public-id"))));
    let p = &m.proof_obligations[1];
    let s1 = p.source.as_ref().unwrap();
    let mut base = Observer::default();
    let calls = base.calls.clone();
    let bound;
    {
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = seeded();
        state.row(&m, p, s1, 1, &mut w).unwrap();
        bound = calls.get();
        drain(&mut state, &mut w);
    }
    let stop = bound + 1;
    let mut o = Observer {
        stop: Some(stop),
        cleanup_after: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = seeded();
    state.row(&m, p, s1, 1, &mut w).unwrap();
    let exact = vec![
        prior(),
        ValidationError::DuplicatePublicObligationId {
            obligation_id: "public-id".into(),
            first_obligation: 5,
            duplicate_obligation: 7,
        },
    ];
    assert_eq!(state.errors, exact);
    let next = &m.proof_obligations[2];
    assert_eq!(
        state.row(&m, next, next.source.as_ref().unwrap(), 2, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.errors, exact);
    drain(&mut state, &mut w);
    assert!(empty(&state));
    assert_eq!(
        w.session.first_refusal().unwrap().cause,
        "original obligation-source stop"
    );
}
#[test]
fn refused_successful_caller_retirement_consumes_full_raw_diagnostics_and_never_renews_session() {
    let m = fixture();
    let (expected, base, bound) = run(&m);
    let stop = bound + 1;
    assert_eq!(
        base.events[stop - 1].phase,
        ExecutionPhase::ScratchRetirement
    );
    let mut o = Observer {
        stop: Some(stop),
        cleanup_after: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = validate_module_obligation_source_observed(&m, &mut s, site()).unwrap();
    assert_eq!(out, expected);
    assert!(s.first_refusal().is_none());
    assert_eq!(
        retire_validation_errors_observed(out, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
    assert_eq!(
        validate_module_obligation_source_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original obligation-source stop"
    );
    drop(s);
    assert!(
        o.events[stop..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
