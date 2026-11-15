// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn private_bounds(m: &Module, inst: &Inst) -> (usize, usize) {
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (layouts, values) = setup(m, &mut s);
    let begin = calls.get();
    let mut state = State::default();
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    state
        .run(&layouts, inst, &values, BlockId::new(1), &mut work)
        .unwrap();
    let end = calls.get();
    drain(&mut state, &mut work);
    empty(&state);
    values.retire_observed(work.session, work.site).unwrap();
    (begin, end)
}
#[test]
fn complete_assigned_discriminants_are_held_across_child_query_and_parent_refusal() {
    let m = fixture();
    let inst = make(Ty::Enum(EnumId::new(0)), Some(0), &[1, 0]);
    let (begin, end) = private_bounds(&m, &inst);
    let mut held = false;
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (layouts, values) = setup(&m, &mut s);
        let mut state = State::default();
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            state.run(&layouts, &inst, &values, BlockId::new(1), &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        if !state.discriminants.is_empty() {
            held = true;
            assert_eq!(state.discriminants, vec![0, 1, 2]);
        }
        drain(&mut state, &mut work);
        empty(&state);
        let _ = values.retire_observed(work.session, work.site);
    }
    assert!(held);
}
#[test]
fn complete_uninhabited_enum_names_and_location_remain_owned_before_error_transfer() {
    let m = long_void();
    let inst = make(Ty::Enum(EnumId::new(0)), Some(2), &[]);
    let (begin, end) = private_bounds(&m, &inst);
    let mut held = false;
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (layouts, values) = setup(&m, &mut s);
        let mut state = State::default();
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            state.run(&layouts, &inst, &values, BlockId::new(1), &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        held |= state.enum_name == m.enums[0].name
            && state.variant_name == m.enums[0].variants[2].name
            && !state.location.is_empty();
        drain(&mut state, &mut work);
        empty(&state);
        let _ = values.retire_observed(work.session, work.site);
    }
    assert!(held);
}
#[test]
fn prior_uniform_error_survives_full_expected_actual_strings_until_later_failure() {
    let mut m = fixture();
    m.types[0] = Ty::Tuple(vec![
        Ty::handle("é".repeat(700), "中".repeat(700)),
        Ty::Bool,
    ]);
    let inst = make(Ty::Array(TyId::new(0), 2), None, &[1, 1]);
    let (begin, end) = private_bounds(&m, &inst);
    let mut held = false;
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (layouts, values) = setup(&m, &mut s);
        let mut state = State::default();
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            state.run(&layouts, &inst, &values, BlockId::new(1), &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        held |= state.errors.len() == 1 && !state.expected.is_empty() && !state.actual.is_empty();
        drain(&mut state, &mut work);
        empty(&state);
        let _ = values.retire_observed(work.session, work.site);
    }
    assert!(held);
}
#[test]
fn final_empty_and_nonempty_publication_cannot_escape_original_refusal() {
    let m = fixture();
    for inst in [
        make(Ty::Tuple(vec![]), None, &[]),
        make(Ty::Array(TyId::new(0), 1), None, &[1]),
    ] {
        let (_, _, _, end) = run(&m, &inst);
        let mut o = Observer {
            stop: Some(end),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (layouts, values) = setup(&m, &mut s);
        assert_eq!(
            validate_make_aggregate_observed(
                &layouts,
                &inst,
                &values,
                BlockId::new(1),
                &mut s,
                site()
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        let _ = values.retire_observed(&mut s, site());
    }
}
#[test]
fn successful_error_caller_retirement_has_real_terminal_receipt_and_original_stop() {
    let m = long_void();
    let inst = make(Ty::Enum(EnumId::new(0)), Some(2), &[]);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (layouts, values) = setup(&m, &mut s);
    let out =
        validate_make_aggregate_observed(&layouts, &inst, &values, BlockId::new(1), &mut s, site())
            .unwrap();
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
    drop((layouts, values));
    let mut o = Observer {
        stop: Some(begin + 1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (layouts, values) = setup(&m, &mut s);
    let out =
        validate_make_aggregate_observed(&layouts, &inst, &values, BlockId::new(1), &mut s, site())
            .unwrap();
    assert_eq!(
        retire_validation_errors_observed(out, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original make-aggregate stop"
    );
    let _ = values.retire_observed(&mut s, site());
}
#[test]
fn borrowed_lane_views_reference_actual_declarations_and_never_expand_array_length() {
    let m = fixture();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let fields = lanes::Lanes::Fields(&m.structs[0].fields);
    assert!(core::ptr::eq(
        fields.at(1, &mut work).unwrap().unwrap(),
        &m.structs[0].fields[1].ty
    ));
    let types = lanes::Lanes::Types(&m.enums[0].variants[0].fields);
    assert!(core::ptr::eq(
        types.at(0, &mut work).unwrap().unwrap(),
        &m.enums[0].variants[0].fields[0]
    ));
    let repeated = lanes::Lanes::Repeated(&m.types[0], usize::MAX);
    assert_eq!(repeated.len(&mut work).unwrap(), usize::MAX);
    assert!(core::ptr::eq(
        repeated.at(usize::MAX - 1, &mut work).unwrap().unwrap(),
        &m.types[0]
    ));
    assert!(repeated.at(usize::MAX, &mut work).unwrap().is_none());
    assert!(work.session.first_refusal().is_none());
}
