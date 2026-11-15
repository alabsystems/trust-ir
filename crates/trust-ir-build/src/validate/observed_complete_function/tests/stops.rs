// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn every_complete_actual_callback_refuses_without_smaller_diagnostic_publication() {
    let f = simple();
    let (_, baseline) = observed(&f, None);
    for stop in 1..=baseline.events.len() {
        let mut observer = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert!(matches!(
            validate_function_observed(&f, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert_eq!(
            session.first_refusal().unwrap().cause,
            "original complete function stop"
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
#[test]
fn cumulative_original_work_and_copy_limits_span_all_passes_and_repeated_calls() {
    let f = fixture();
    let (_, baseline) = observed(&f, None);
    for bytes in [false, true] {
        let mut observer = Observer {
            work_cap: (!bytes).then_some(baseline.work),
            byte_cap: bytes.then_some(baseline.bytes),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            validate_function_observed(&f, &mut session, site()).unwrap(),
            validate_function(&f)
        );
        assert_eq!(
            validate_function_observed(&f, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = session.first_refusal().unwrap().progress;
        assert_eq!(
            validate_function_observed(&f, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(session.first_refusal().unwrap().progress, first);
        assert_eq!(
            session.first_refusal().unwrap().cause,
            if bytes { "bytes" } else { "work" }
        );
    }
}
#[test]
fn header_admission_precedes_any_constituent_or_owned_state_allocation() {
    let f = fixture();
    let mut observer = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_function_observed(&f, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(observer.events.len(), 1);
}
#[test]
fn every_merge_stop_keeps_all_owned_errors_until_explicit_consuming_retirement() {
    let mut base = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut s = State {
        pending: vec![owned_error(), error(2), owned_error()],
        ..State::default()
    };
    s.merge(&mut work).unwrap();
    let count = base.events.len();
    let mut saw_pending = false;
    let mut saw_output = false;
    let mut saw_reversal = false;
    for stop in 1..=count {
        let mut observer = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let mut work = Work {
            session: &mut session,
            site: site(),
        };
        let mut s = State {
            pending: vec![owned_error(), error(2), owned_error()],
            ..State::default()
        };
        assert_eq!(
            s.merge(&mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        saw_pending |= !s.pending.is_empty();
        saw_output |= !s.errors.is_empty();
        saw_reversal |= s.pending.capacity() == 0 && s.errors.len() == 3;
        drain(&mut s, &mut work);
        assert!(empty(&s));
        assert_eq!(
            work.session.first_refusal().unwrap().cause,
            "original complete function stop"
        );
    }
    assert!(saw_pending && saw_output && saw_reversal);
}
#[test]
fn actual_returned_helper_and_prior_diagnostics_are_owned_across_outer_refusal() {
    let f = fixture();
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut s = State::default();
    s.run(&f, None, DEFAULT_POINTER_BITS, &mut work).unwrap();
    let count = observer.events.len();
    let (mut helper, mut prior) = (false, false);
    for stop in 1..=count {
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
        if s.run(&f, None, DEFAULT_POINTER_BITS, &mut work).is_err() {
            helper |= !s.pending.is_empty();
            prior |= !s.errors.is_empty();
        }
        drain(&mut s, &mut work);
        assert!(empty(&s));
    }
    assert!(helper && prior);
}
#[test]
fn final_publication_refusal_drains_completed_owned_diagnostics() {
    let f = fixture();
    let (_, baseline) = observed(&f, None);
    let stop = baseline.events.len();
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_function_observed(&f, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    assert!(observer.events.len() > stop);
    assert!(
        observer
            .events
            .iter()
            .skip(stop)
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn sticky_original_refusal_survives_cleanup_refusals_and_all_owned_rows_retire() {
    let mut observer = Observer {
        stop: Some(1),
        cleanup: true,
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut s = State {
        pending: vec![owned_error()],
        errors: vec![owned_error()],
        indirect: true,
    };
    assert_eq!(work.admit(1, 0), Err(ObservedValueError::AdmissionRefused));
    drain(&mut s, &mut work);
    assert!(empty(&s));
    assert_eq!(
        work.session.first_refusal().unwrap().cause,
        "original complete function stop"
    );
    assert_eq!(
        work.publication(),
        Err(ObservedValueError::AdmissionRefused)
    );
}
#[test]
fn supported_float_switch_keeps_all_prior_diagnostics_and_withholds_them_on_stop() {
    let mut f = fixture();
    f.blocks[0].body.pop();
    f.blocks[0].body.push(InstrNode::new(Inst::Switch {
        value: v(2),
        default: BlockId::new(0),
        default_args: vec![],
        cases: vec![trust_ir::inst::SwitchCase {
            value: Constant::Float(1.5),
            target: BlockId::new(0),
            args: vec![],
        }],
        exhaustive_enum_unreachable: false,
    }));
    let report = parity(&f, None);
    assert!(!report.errors.is_empty());
    assert_eq!(report.errors, validate_function(&f));
    let (_, baseline) = observed(&f, None);
    let stop = baseline.events.len();
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_function_observed(&f, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().cause,
        "original complete function stop"
    );
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    assert_eq!(&observer.events[..stop], baseline.events.as_slice());
    assert!(
        observer.events[stop..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
