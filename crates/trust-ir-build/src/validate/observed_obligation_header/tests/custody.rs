// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn trace(ns: &str, name: &str) -> Observer {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = seeded();
    state.unpinned(17, ns, name, &mut w).unwrap();
    assert_eq!(
        state.errors,
        vec![
            prior(),
            ValidationError::UnpinnedCustomObligationNamespace {
                obligation: 17,
                namespace: ns.into(),
                name: name.into()
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
fn complete_raw_namespace_is_retained_before_first_label_copy_with_all_prior_output() {
    let ns = "namespaceλ\0FULL".repeat(300);
    let name = "label尾\0FULL".repeat(300);
    let mut prefix = Observer::default();
    let calls = prefix.calls.clone();
    let bound;
    {
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut prefix);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = seeded();
        w.text(&ns, &mut state.namespace).unwrap();
        bound = calls.get();
        drain(&mut state, &mut w);
    }
    let base = trace(&ns, &name);
    assert_eq!(&prefix.events[..bound], &base.events[..bound]);
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
    assert_eq!(
        state.unpinned(17, &ns, &name, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.namespace, ns);
    assert!(state.name.is_empty());
    assert_eq!(state.errors, vec![prior()]);
    drain(&mut state, &mut w);
    assert!(empty(&state));
    assert_eq!(
        w.session.first_refusal().unwrap().progress,
        base.events[stop - 1]
    );
    assert_eq!(
        w.session.first_refusal().unwrap().cause,
        "original obligation-header stop"
    );
}
#[test]
fn partial_label_copy_keeps_complete_namespace_and_original_label_input_until_sticky_drain() {
    let ns = "raw namespace";
    let name = "λ".repeat(1200);
    let mut prefix = Observer::default();
    let calls = prefix.calls.clone();
    let bound;
    {
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut prefix);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = seeded();
        w.text(ns, &mut state.namespace).unwrap();
        bound = calls.get();
        drain(&mut state, &mut w);
    }
    let base = trace(ns, &name);
    assert_eq!(&prefix.events[..bound], &base.events[..bound]);
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
        state.unpinned(17, ns, &name, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.namespace, ns);
    assert_eq!(state.name, &name[..1024]);
    assert_eq!(state.errors, vec![prior()]);
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
fn actual_output_preparation_reserve_and_transport_cutoffs_keep_whole_names_and_prefix() {
    let pending = || State {
        namespace: "full namespace λ\0TAIL".into(),
        name: "full label 尾\0TAIL".into(),
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
        (1, size_of::<ValidationError>() + 2 * size_of::<String>())
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
        let before = state.errors.capacity();
        assert_eq!(
            state.prepare(&mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(state.namespace, "full namespace λ\0TAIL");
        assert_eq!(state.name, "full label 尾\0TAIL");
        assert_eq!(state.errors, vec![prior()]);
        if stop == 2 {
            assert_eq!(state.errors.capacity(), before);
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
fn a_later_real_namespace_row_stop_preserves_the_complete_earlier_diagnostic() {
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
        state.unpinned(17, "bad1λ", "full1尾", &mut w).unwrap();
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
    state.unpinned(17, "bad1λ", "full1尾", &mut w).unwrap();
    let prior = state.errors.clone();
    assert_eq!(prior.len(), 2);
    assert_eq!(
        state.unpinned(18, "bad2λ", "full2尾", &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.errors, prior);
    drain(&mut state, &mut w);
    assert!(empty(&state));
    assert_eq!(
        w.session.first_refusal().unwrap().cause,
        "original obligation-header stop"
    );
}
