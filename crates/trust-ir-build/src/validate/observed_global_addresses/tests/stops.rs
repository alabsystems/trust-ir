// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn each_actual_visit_growth_error_and_publication_stop_refuses() {
    let m = fixture();
    let (_, base) = run(&m);
    for stop in 1..=base.events.len() {
        let mut o = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_module_global_addresses_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().cause, "original global stop");
        assert!(
            o.events
                .iter()
                .skip(stop)
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn cumulative_original_work_and_copy_do_not_reset_across_module_calls() {
    let m = fixture();
    let (_, base) = run(&m);
    for bytes in [false, true] {
        let mut o = Observer {
            work_cap: (!bytes).then_some(base.work),
            byte_cap: bytes.then_some(base.bytes),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_module_global_addresses_observed(&m, &mut s, site())
                .unwrap()
                .len(),
            18
        );
        assert_eq!(
            validate_module_global_addresses_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if bytes { "bytes" } else { "work" }
        );
        assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    }
}
#[test]
fn initial_header_refusal_and_actual_wide_body_stop_do_not_publish_prefixes() {
    let m = fixture();
    let mut o = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_module_global_addresses_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(o.events.len(), 1);
    let mut m = fixture();
    m.functions[0].blocks[0].body = vec![InstrNode::new(Inst::NullPtr); 10_000];
    let mut o = Observer {
        work_cap: Some(100),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_module_global_addresses_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "work");
    assert!(o.events.len() < 200);
}
#[test]
fn final_refusal_observes_all_completed_error_retirement() {
    let m = fixture();
    let (_, base) = run(&m);
    let stop = base.events.len();
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_module_global_addresses_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    assert!(o.events.len() > stop + 18);
    assert!(
        o.events
            .iter()
            .skip(stop)
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn error_reserve_is_admitted_before_fixed_diagnostic_construction() {
    let mut o = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut errors = Vec::new();
    assert_eq!(
        work.fixed(&mut errors, 3, 9),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(errors.capacity(), 0);
}
