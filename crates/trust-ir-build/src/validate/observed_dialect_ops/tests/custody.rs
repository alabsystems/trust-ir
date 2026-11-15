// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn actual_known_type_prefix_rows_stay_borrowed_until_complete_original_retirement() {
    let m = fixture();
    let n = node(
        trust_ir::dialect::vector::pack_lanes(vec_ty(Ty::I32, 4), [v(0), v(1), v(999), v(0)]),
        1,
    );
    let (begin, end) = bounds(&m, &n, None);
    let mut held = false;
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let values = setup(&m, &mut s);
        let mut state = State::default();
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            state.run(&m, &n, &values, None, BlockId::new(1), &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        if !state.operand_tys.is_empty() {
            held = true;
            assert_eq!(state.operand_tys[0], &Ty::I32);
            assert!(state.operand_tys.len() <= 2);
        }
        drain(&mut state, &mut w);
        empty(&state);
        let _ = values.retire_observed(w.session, w.site);
    }
    assert!(held);
}
#[test]
fn complete_prior_builtin_error_is_held_through_full_schema_error_before_batch_transfer() {
    let m = fixture();
    let n = node(DialectInst::new("vector", "bad"), 0);
    let r = schema();
    let expected = original(&m, &n, Some(&r));
    let (begin, end) = bounds(&m, &n, Some(&r));
    let mut held = false;
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let values = setup(&m, &mut s);
        let mut state = State::default();
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            state.run(&m, &n, &values, Some(&r), BlockId::new(1), &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        if !state.errors.is_empty() {
            assert_eq!(state.errors[0], expected[0]);
        }
        held |= state.errors.len() == 1
            && state.reason == "dialect schema mismatch: UnknownDialect(\"vector\")";
        drain(&mut state, &mut w);
        empty(&state);
        let _ = values.retire_observed(w.session, w.site);
    }
    assert!(held);
}
#[test]
fn complete_raw_debug_child_string_remains_owned_through_next_parent_copy_fee() {
    let m = fixture();
    let ty = Ty::Tuple(vec![Ty::handle("é'\n".repeat(8), "中\t")]);
    let expected = format!("{ty:?}");
    let op = DialectInst::new("vector", "pack_lanes").with_result_ty(ty);
    let n = node(op, 1);
    let (begin, end) = bounds(&m, &n, None);
    let mut held = false;
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let values = setup(&m, &mut s);
        let mut state = State::default();
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            state.run(&m, &n, &values, None, BlockId::new(1), &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        held |= state.temporary == expected;
        drain(&mut state, &mut w);
        empty(&state);
        let _ = values.retire_observed(w.session, w.site);
    }
    assert!(held);
}
#[test]
fn partial_attribute_seen_storage_and_pending_full_unknown_name_are_consumed_after_refusal() {
    let m = fixture();
    let r = schema();
    let n = node(operation().with_attr("unknown", AttrValue::U64(0)), 1);
    let (begin, end) = bounds(&m, &n, Some(&r));
    let (mut seen, mut full) = (false, false);
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let values = setup(&m, &mut s);
        let mut state = State::default();
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            state.run(&m, &n, &values, Some(&r), BlockId::new(1), &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        seen |= state.seen == [true];
        full |= state.reason == "dialect schema mismatch: UnknownAttribute(\"unknown\")";
        drain(&mut state, &mut w);
        empty(&state);
        let _ = values.retire_observed(w.session, w.site);
    }
    assert!(seen && full);
}
#[test]
fn final_empty_or_full_two_error_publication_refusal_cannot_publish_partial_batch() {
    let m = fixture();
    let r = schema();
    for (n, registry) in [
        (node(DialectInst::new("gpu", "barrier"), 0), None),
        (node(DialectInst::new("vector", "bad"), 0), Some(&r)),
    ] {
        let (_, _, _, end) = run(&m, &n, registry);
        let mut o = Observer {
            stop: Some(end),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let values = setup(&m, &mut s);
        assert_eq!(
            validate_dialect_node_observed(
                &m,
                &n,
                &values,
                registry,
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
fn returned_whole_batch_caller_cleanup_has_full_retirement_prefix_terminal_and_sticky_cause() {
    let m = fixture();
    let n = node(DialectInst::new("vector", "bad"), 0);
    let r = schema();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let values = setup(&m, &mut s);
    let out =
        validate_dialect_node_observed(&m, &n, &values, Some(&r), BlockId::new(1), &mut s, site())
            .unwrap();
    assert_eq!(out.len(), 2);
    let begin = calls.get();
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    let end = calls.get();
    values.retire_observed(&mut s, site()).unwrap();
    drop(s);
    let (last, prefix) = o.events[begin..end].split_last().unwrap();
    assert!(!prefix.is_empty());
    assert!(
        prefix
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement && e.site == site())
    );
    assert_eq!(
        *last,
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
    let values = setup(&m, &mut s);
    let out =
        validate_dialect_node_observed(&m, &n, &values, Some(&r), BlockId::new(1), &mut s, site())
            .unwrap();
    assert_eq!(
        retire_validation_errors_observed(out, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "original dialect stop");
    let _ = values.retire_observed(&mut s, site());
}
