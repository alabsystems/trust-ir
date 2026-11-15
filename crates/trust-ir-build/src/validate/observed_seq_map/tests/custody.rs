// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_private_same_entry_cut_holds_full_display_and_partial_text_until_drain() {
    let mut m = fixture();
    m.func_types[1].params = vec![Ty::Tuple(vec![Ty::U64, Ty::Bool])];
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let catalog = setup(&m, &mut s);
    let begin = calls.get();
    let mut state = State::default();
    state
        .run(
            &catalog,
            &inst(),
            BlockId::new(1),
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
    catalog.retire_observed(&mut s, site()).unwrap();
    drop(s);
    let (mut render, mut text) = (false, false);
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let catalog = setup(&m, &mut s);
        let mut state = State::default();
        assert_eq!(
            state.run(
                &catalog,
                &inst(),
                BlockId::new(1),
                &mut Work {
                    session: &mut s,
                    site: site()
                }
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        render |= state.render.capacity() != 0;
        text |= state.actual.capacity() != 0 || state.expected.capacity() != 0;
        drain(
            &mut state,
            &mut Work {
                session: &mut s,
                site: site(),
            },
        );
        assert!(empty(&state));
        let _ = catalog.retire_observed(&mut s, site());
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
    assert!(render && text);
}
#[test]
fn complete_returned_getter_error_is_pending_before_any_output_reserve() {
    let mut m = fixture();
    m.functions[1].ty = FuncTyId::new(99);
    m.functions[1].name = "whole λ".repeat(100);
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let catalog = setup(&m, &mut s);
    let begin = calls.get();
    let mut state = State::default();
    state
        .run(
            &catalog,
            &inst(),
            BlockId::new(1),
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
    catalog.retire_observed(&mut s, site()).unwrap();
    drop(s);
    let mut held = false;
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let catalog = setup(&m, &mut s);
        let mut state = State::default();
        assert_eq!(
            state.run(
                &catalog,
                &inst(),
                BlockId::new(1),
                &mut Work {
                    session: &mut s,
                    site: site()
                }
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        if let Some(error) = &state.pending {
            assert_eq!(
                error,
                &ValidationError::FuncTypeNotFound {
                    func_name: m.functions[1].name.clone(),
                    func_ty_id: 99
                }
            );
            held = true;
        }
        drain(
            &mut state,
            &mut Work {
                session: &mut s,
                site: site(),
            },
        );
        assert!(empty(&state));
        let _ = catalog.retire_observed(&mut s, site());
    }
    assert!(held);
}
#[test]
fn pending_prior_and_all_partial_fields_drain_under_sticky_first_refusal() {
    let mut state = State {
        name: "name λ".repeat(200),
        expected: "expected".repeat(200),
        actual: "actual".repeat(200),
        render: "full render".repeat(200),
        pending: Some(ValidationError::FuncTypeNotFound {
            func_name: "whole pending".repeat(200),
            func_ty_id: 99,
        }),
        errors: vec![ValidationError::SeqMapFwdSignatureMismatch {
            block: 1,
            fwd: "prior".repeat(200),
            expected: "prior expected".repeat(200),
            actual: "prior actual".repeat(200),
        }],
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
    assert_eq!(s.first_refusal().unwrap().cause, "original SeqMap stop");
    drop(s);
    assert!(
        o.events[1..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn final_whole_result_publication_failure_consumes_all_diagnostics_and_retains_healthy_contract() {
    let mut m = fixture();
    m.func_types[1].params = vec![Ty::Bool];
    let (_, baseline, _, end) = run(&m, &inst());
    let mut o = Observer {
        stop: Some(end),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let catalog = setup(&m, &mut s);
    assert_eq!(
        validate_seq_map_observed(&catalog, &inst(), BlockId::new(1), &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    let _ = catalog.retire_observed(&mut s, site());
    drop(s);
    assert_eq!(&o.events[..end], &baseline.events[..end]);
    assert!(
        o.events[end..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
    assert_eq!(
        *baseline.events.last().unwrap(),
        ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 0,
            copy_bytes: 0
        }
    );
}
