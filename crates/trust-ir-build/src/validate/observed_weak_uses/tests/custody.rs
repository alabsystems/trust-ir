// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn inspect(m: &Module, mut check: impl FnMut(&State<'_>)) {
    let catalog = ModuleFunctionCatalog::new(m);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut state = State::default();
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    state.run(&catalog, &mut work).unwrap();
    let end = calls.get();
    drain(&mut state, &mut work);
    empty(&state);
    drop(work);
    drop(s);
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
            state.run(&catalog, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        check(&state);
        drain(&mut state, &mut work);
        empty(&state);
        assert_eq!(
            work.session.first_refusal().unwrap().cause,
            "original weak-use stop"
        );
    }
}
#[test]
fn actual_singleton_definition_rows_remain_borrowed_and_held_through_origin_stop() {
    let m = fixture();
    let mut saw = false;
    inspect(&m, |s| {
        if s.definitions.len() == 2 {
            saw = true;
            assert!(s.definitions.iter().any(|(n,i)|*n==1&&matches!(i,Inst::Const{value:Constant::SymbolAddr{symbol,..},..}if symbol=="weak")));
        }
    });
    assert!(saw);
}
#[test]
fn complete_direct_location_and_name_are_owned_before_error_reserve_or_transfer() {
    let mut m = fixture();
    m.functions[0].blocks[0].body = vec![InstrNode::new(Inst::Call {
        callee: FuncId::new(9),
        args: vec![],
    })];
    let mut saw = false;
    inspect(&m, |s| {
        saw |= s.location == "function 'caller' bb7 instruction 0"
            && s.name == "weak"
            && s.errors.is_empty();
    });
    assert!(saw);
}
#[test]
fn both_complete_signature_strings_are_owned_before_parent_error_transfer() {
    let mut m = fixture();
    m.functions[0].blocks[0].body.truncate(3);
    let mut saw = false;
    inspect(&m, |s| {
        saw |= s.declared == "call functy.0 (()) -> (()) through the weak address"
            && s.actual == "target functy.1 ((bool)) -> ((u64))"
            && s.name == "weak";
    });
    assert!(saw);
}
#[test]
fn actual_nested_tree_current_and_frame_capacity_remain_held_until_observed_cleanup() {
    let mut m = fixture();
    m.functions[0].blocks[0].body = vec![switch(vec![Constant::Record(vec![(
        "x".into(),
        Constant::Array(vec![symbol("weak")]),
    )])])];
    let Inst::Switch { cases, .. } = &m.functions[0].blocks[0].body[0].inst else {
        panic!("actual switch fixture");
    };
    let root = &cases[0].value;
    let catalog = ModuleFunctionCatalog::new(&m);
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut state = State::default();
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    state
        .location(
            &m.functions[0],
            BlockId::new(7),
            0,
            Some(0),
            false,
            &mut work,
        )
        .unwrap();
    let begin = calls.get();
    state.switch_tree(&catalog, root, &mut work).unwrap();
    let end = calls.get();
    drain(&mut state, &mut work);
    empty(&state);
    drop(work);
    drop(session);
    let mut saw = false;
    for cut in begin + 1..=end {
        let mut observer = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let mut state = State::default();
        let mut work = Work {
            session: &mut session,
            site: site(),
        };
        state
            .location(
                &m.functions[0],
                BlockId::new(7),
                0,
                Some(0),
                false,
                &mut work,
            )
            .unwrap();
        // node() retires the tree before propagating its result. Inspect the
        // actual tree helper before that caller cleanup, with the same source
        // literal, location and cumulative original session still live.
        assert_eq!(
            state.switch_tree(&catalog, root, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        saw |= state.current.is_some() && state.frames.len() >= 2 && !state.location.is_empty();
        drain(&mut state, &mut work);
        empty(&state);
        assert_eq!(
            work.session.first_refusal().unwrap().cause,
            "original weak-use stop"
        );
    }
    assert!(saw);
}
#[test]
fn prior_diagnostics_and_complete_switch_detail_survive_later_refusal() {
    let m = fixture();
    let mut saw = false;
    inspect(&m, |s| {
        saw |= !s.errors.is_empty()
            && s.symbol == "weak"
            && s.detail == "a switch case value (compare it with `icmp` against a ptr instead)"
            && !s.here.is_empty();
    });
    assert!(saw);
}
#[test]
fn successful_whole_output_requires_original_caller_healthy_terminal_or_sticky_retirement() {
    let m = fixture();
    let catalog = ModuleFunctionCatalog::new(&m);
    for refuse in [false, true] {
        let arm = Rc::new(Cell::new(false));
        let mut o = Observer {
            cleanup: Some(arm.clone()),
            ..Observer::default()
        };
        let calls = o.calls.clone();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let out = validate_weak_declaration_uses_observed(&catalog, &mut s, site()).unwrap();
        assert_eq!(out, original(&m));
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
