// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn every_pointer_and_vector_mask_callback_refuses_under_original_owner() {
    for f in [
        fixture(),
        function(Inst::Select {
            ty: Ty::Vector(Box::new(Ty::I32), 4),
            cond: v(3),
            then_val: v(1),
            else_val: v(2),
        }),
    ] {
        let values = values(&f);
        let (_, baseline) = run(&f, 64);
        for stop in 1..=baseline.events.len() {
            let mut observer = Observer {
                stop: Some(stop),
                ..Observer::default()
            };
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            assert_eq!(
                validate_pointer_select_operands_observed(
                    0,
                    &f.blocks[0].body[0].inst,
                    &values,
                    64,
                    &mut session,
                    site()
                ),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(
                session.first_refusal().unwrap().cause,
                "original pointer/select stop"
            );
            assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
            assert!(
                observer
                    .events
                    .iter()
                    .skip(stop)
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn cumulative_work_and_copy_are_shared_across_distinct_calls_and_sticky_on_retry() {
    let f = fixture();
    let values = values(&f);
    let inst = &f.blocks[0].body[0].inst;
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    for _ in 0..2 {
        assert_eq!(
            validate_pointer_select_operands_observed(0, inst, &values, 64, &mut session, site())
                .unwrap()
                .len(),
            3
        );
    }
    for bytes in [false, true] {
        let mut observer = Observer {
            work_cap: (!bytes).then_some(baseline.work - 1),
            byte_cap: bytes.then_some(baseline.bytes - 1),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            validate_pointer_select_operands_observed(0, inst, &values, 64, &mut session, site())
                .unwrap()
                .len(),
            3
        );
        assert_eq!(
            validate_pointer_select_operands_observed(0, inst, &values, 64, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = session.first_refusal().unwrap().progress;
        assert_eq!(
            validate_pointer_select_operands_observed(0, inst, &values, 64, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(session.first_refusal().unwrap().progress, first);
    }
}
#[test]
fn every_pending_text_completed_error_and_owned_mask_is_retired_before_refusal_returns() {
    let f = function(Inst::Select {
        ty: Ty::Vector(Box::new(Ty::I32), 4),
        cond: v(3),
        then_val: v(1),
        else_val: v(2),
    });
    let values = values(&f);
    let inst = &f.blocks[0].body[0].inst;
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut s = State::default();
    s.check(0, inst, &values, 64, &mut work).unwrap();
    s.retire_scratch(&mut work);
    s.retire_errors(&mut work);
    let (mut text, mut prior, mut mask) = (false, false, false);
    for stop in 1..=baseline.events.len() {
        let mut observer = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let mut work = Work {
            session: &mut session,
            site: site(),
        };
        let mut s = State::default();
        if s.check(0, inst, &values, 64, &mut work).is_err() {
            text |= !s.expected.is_empty() && !s.actual.is_empty();
            prior |= !s.errors.is_empty();
            mask |= matches!(s.pending_ty, Some(Ty::Vector(..)));
        }
        s.retire_scratch(&mut work);
        s.retire_errors(&mut work);
        assert!(empty(&s));
    }
    assert!(text && prior && mask);
}
#[test]
fn diagnostic_growth_is_admitted_before_pending_owned_fields_move() {
    let mut observer = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut s = State {
        op: "ptr_metadata".into(),
        pointer: "fatptr<str>".into(),
        expected: "u64".into(),
        actual: "u16".into(),
        ..State::default()
    };
    assert_eq!(
        s.commit(Diagnostic::Metadata(0), &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        (&*s.op, &*s.pointer, &*s.expected, &*s.actual),
        ("ptr_metadata", "fatptr<str>", "u64", "u16")
    );
    assert_eq!(s.errors.capacity(), 0);
    s.retire_scratch(&mut work);
    s.retire_errors(&mut work);
    assert!(empty(&s));
}
#[test]
fn vector_mask_box_is_admitted_before_actual_allocation() {
    let f = function(Inst::Select {
        ty: Ty::Vector(Box::new(Ty::I32), 4),
        cond: v(3),
        then_val: v(99),
        else_val: v(98),
    });
    let values = values(&f);
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut s = State::default();
    s.check(0, &f.blocks[0].body[0].inst, &values, 64, &mut work)
        .unwrap();
    s.retire_scratch(&mut work);
    s.retire_errors(&mut work);

    // Option<Ty> and Ty may have equal sizes, and other operations can emit
    // the same pair. Bind the exact known-lookup publication plus header/Box
    // sequence before testing the real preallocation/postallocation states.
    let header = ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site: site(),
        work: 1,
        copy_bytes: size_of::<Option<Ty>>(),
    };
    let allocation = ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site: site(),
        work: 1,
        copy_bytes: size_of::<Ty>(),
    };
    let lookup_publication = ExecutionProgress {
        phase: ExecutionPhase::Publication,
        site: site(),
        work: 1,
        copy_bytes: size_of::<Option<&Ty>>(),
    };
    let locations = baseline
        .events
        .windows(3)
        .enumerate()
        .filter_map(|(index, triple)| {
            (triple == [lookup_publication, header, allocation]).then_some(index + 1)
        })
        .collect::<Vec<_>>();
    assert_eq!(locations.len(), 1, "exactly one lookup/header/Box sequence");
    let header_index = locations[0];
    assert!(header_index > 0);
    assert_eq!(
        baseline.events[header_index - 1],
        ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 1,
            copy_bytes: size_of::<Option<&Ty>>()
        }
    );
    // That preceding publication is the actual known condition lookup; the
    // two selected values are absent, so they construct no expected mask.
    let box_index = header_index + 1;
    let box_ordinal = box_index + 1;
    assert!(box_index + 1 < baseline.events.len());
    for stop in [box_ordinal, box_ordinal + 1] {
        let mut observer = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let mut work = Work {
            session: &mut session,
            site: site(),
        };
        let mut s = State::default();
        assert_eq!(
            s.check(0, &f.blocks[0].body[0].inst, &values, 64, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            work.session.first_refusal().unwrap().progress,
            baseline.events[stop - 1]
        );
        assert_eq!(
            work.session.first_refusal().unwrap().cause,
            "original pointer/select stop"
        );
        assert_eq!(
            work.session.remaining_fuel(),
            InterpretOptions::default().fuel
        );
        assert!(s.errors.is_empty());
        if stop == box_ordinal {
            // The distinct real allocation admission has refused: no Box is
            // yet owned, even if its size equals the preceding Option header.
            assert!(s.pending_ty.is_none());
        } else {
            // Allow exactly that admission, then refuse the very next actual
            // callback. The complete newly allocated mask is already retained.
            assert!(matches!(s.pending_ty.as_ref(), Some(Ty::Vector(inner, 4))
                if matches!(inner.as_ref(), Ty::Bool)));
        }
        s.retire_scratch(&mut work);
        s.retire_errors(&mut work);
        assert!(empty(&s));
        assert_eq!(
            work.session.first_refusal().unwrap().progress,
            baseline.events[stop - 1]
        );
        assert_eq!(
            work.session.first_refusal().unwrap().cause,
            "original pointer/select stop"
        );
        assert!(
            observer
                .events
                .iter()
                .skip(stop)
                .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn publication_and_cleanup_stops_consume_all_diagnostics_and_owned_expected_type() {
    let f = fixture();
    let values = values(&f);
    let (_, baseline) = run(&f, 64);
    let stop = baseline.events.len();
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_pointer_select_operands_observed(
            0,
            &f.blocks[0].body[0].inst,
            &values,
            64,
            &mut session,
            site()
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    assert!(observer.events.len() > stop + 10);
    let arm = Rc::new(Cell::new(false));
    let mut observer = Observer {
        cleanup: Some(arm.clone()),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut s = State::default();
    s.check(0, &f.blocks[0].body[0].inst, &values, 64, &mut work)
        .unwrap();
    assert!(s.pending_ty.is_some());
    assert_eq!(s.errors.len(), 3);
    arm.set(true);
    s.retire_scratch(&mut work);
    s.retire_errors(&mut work);
    assert!(empty(&s));
    assert_eq!(
        work.publication(),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        work.session.first_refusal().unwrap().cause,
        "original pointer/select cleanup"
    );
}
#[test]
fn deep_actual_equality_and_wide_spelling_refuse_inside_real_operations() {
    let ty = Ty::Tuple(vec![Ty::U32; 5000]);
    let mut f = function(Inst::Select {
        ty,
        cond: v(2),
        then_val: v(1),
        else_val: v(1),
    });
    f.blocks[0].params[1].1 = Ty::Tuple(vec![Ty::U32; 4999].into_iter().chain([Ty::I32]).collect());
    let values = values(&f);
    let mut observer = Observer {
        work_cap: Some(10000),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_pointer_select_operands_observed(
            0,
            &f.blocks[0].body[0].inst,
            &values,
            64,
            &mut session,
            site()
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "work");
    let wide = Ty::Handle(Box::new(HandleTy::new("λ".repeat(6000), "runtime")));
    let mut observer = Observer {
        work_cap: Some(5000),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut s = State::default();
    assert_eq!(
        s.invalid(0, "ptr_data", &wide, "type is not pointer-like", &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.op, "ptr_data");
    s.retire_scratch(&mut work);
    s.retire_errors(&mut work);
    assert!(empty(&s));
    assert_eq!(work.session.first_refusal().unwrap().cause, "work");
    assert!(
        observer
            .events
            .iter()
            // Real scalar classification now prepays the complete pinned Unicode
            // table bound as well as the fixed scalar guards. Observe both
            // actual classifications, including the one refused by the cap.
            .filter(|e| e.phase == ExecutionPhase::Validation
                && e.copy_bytes == size_of::<core::char::EscapeDebug>()
                && e.work >= 8 * u32::BITS as usize)
            .count()
            >= 2
    );
}
