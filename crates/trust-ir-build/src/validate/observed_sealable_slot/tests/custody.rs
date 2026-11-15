// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_private_cut_retains_actual_pending_frames_and_active_ids_until_exhaustive_retirement() {
    let m = fixture();
    let ty = Ty::Struct(StructId::new(1));
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let nominal = m
        .nominal_type_reachability_observed(&mut s, site())
        .unwrap();
    let begin = calls.get();
    let mut state = State::default();
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    assert!(state.run(&m, &nominal, &ty, &mut work).unwrap());
    let end = calls.get();
    state.retire(&mut work);
    let _ = nominal.retire_observed(work.session, site());
    drop(work);
    drop(s);
    let mut held = false;
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let nominal = m
            .nominal_type_reachability_observed(&mut s, site())
            .unwrap();
        let mut state = State::default();
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        assert!(state.run(&m, &nominal, &ty, &mut work).is_err());
        if !state.visiting.is_empty() && !state.frames.is_empty() {
            held = true;
            assert!(state.frames.capacity() > 0 && state.visiting.capacity() > 0);
        }
        state.retire(&mut work);
        assert!(empty(&state));
        let _ = nominal.retire_observed(work.session, site());
    }
    assert!(held);
}
#[test]
fn false_short_circuit_keeps_unvisited_continuations_for_owned_cleanup_without_scanning_tail() {
    let mut m = fixture();
    m.structs[0].fields[0].ty = Ty::Ref(Box::new(handle()));
    m.structs[0].fields.push(FieldDef {
        name: "tail".into(),
        ty: handle(),
        offset: None,
    });
    let ty = Ty::Struct(StructId::new(0));
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let nominal = m
        .nominal_type_reachability_observed(&mut s, site())
        .unwrap();
    let mut state = State::default();
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    assert!(!state.run(&m, &nominal, &ty, &mut work).unwrap());
    assert!(!state.frames.is_empty());
    assert_eq!(state.visiting, vec![StructId::new(0)]);
    state.retire(&mut work);
    assert!(empty(&state));
    nominal.retire_observed(work.session, site()).unwrap();
}
#[test]
fn successful_path_has_empty_active_stack_but_retained_capacity_is_still_charged_and_retired() {
    let m = fixture();
    let ty = Ty::Struct(StructId::new(1));
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let nominal = m
        .nominal_type_reachability_observed(&mut s, site())
        .unwrap();
    let mut state = State::default();
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    assert!(state.run(&m, &nominal, &ty, &mut work).unwrap());
    assert!(state.frames.is_empty() && state.visiting.is_empty());
    assert!(state.frames.capacity() > 0 && state.visiting.capacity() > 0);
    let begin = calls.get();
    state.retire(&mut work);
    let end = calls.get();
    assert!(empty(&state));
    nominal.retire_observed(work.session, site()).unwrap();
    drop(work);
    drop(s);
    assert!(end > begin);
    assert!(
        o.events[begin..end]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn late_cleanup_refusal_drops_both_capacity_owners_and_retains_first_original_cause() {
    let m = fixture();
    let ty = Ty::Struct(StructId::new(1));
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let nominal = m
        .nominal_type_reachability_observed(&mut s, site())
        .unwrap();
    let mut state = State::default();
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    assert!(state.run(&m, &nominal, &ty, &mut work).unwrap());
    let end = calls.get();
    state.retire(&mut work);
    let _ = nominal.retire_observed(work.session, site());
    drop(work);
    drop(s);
    let mut o = Observer {
        stop: Some(end + 1),
        cleanup_after: Some(end + 1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let nominal = m
        .nominal_type_reachability_observed(&mut s, site())
        .unwrap();
    let mut state = State::default();
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    assert!(state.run(&m, &nominal, &ty, &mut work).unwrap());
    state.retire(&mut work);
    assert!(empty(&state));
    assert_eq!(
        work.publication(),
        Err(ObservedValueError::AdmissionRefused)
    );
    let _ = nominal.retire_observed(work.session, site());
    assert_eq!(
        work.session.first_refusal().unwrap().cause,
        "original sealable stop"
    );
}
