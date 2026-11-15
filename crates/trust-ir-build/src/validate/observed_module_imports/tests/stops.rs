// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn every_actual_compact_callback_refuses_without_partial_import_diagnostics() {
    let m = fixture();
    let (_, base) = run(&m);
    for stop in 1..=base.events.len() {
        let mut o = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_module_imports_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().cause, "original import stop");
        assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
        assert!(
            o.events
                .iter()
                .skip(stop)
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn cumulative_original_work_and_copy_cover_both_passes_and_repeated_calls() {
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
            validate_module_imports_observed(&m, &mut s, site())
                .unwrap()
                .len(),
            4
        );
        assert_eq!(
            validate_module_imports_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = s.first_refusal().unwrap().progress;
        assert_eq!(
            validate_module_imports_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, first);
        assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    }
}
#[test]
fn producer_other_comparison_refuses_inside_actual_equal_prefix_not_before_it() {
    let a = row("same").with_producer(Producer::Other(format!("{}a", "λ".repeat(4000))));
    let b = row("same").with_producer(Producer::Other(format!("{}b", "λ".repeat(4000))));
    let mut o = Observer {
        work_cap: Some(1500),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    assert_eq!(
        work.import_equal(&a, &b),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(work.session.first_refusal().unwrap().progress.work, 1024);
    assert_eq!(work.session.first_refusal().unwrap().cause, "work");
    assert!(
        o.events
            .iter()
            .filter(|e| e.work == 1024 && e.copy_bytes == 0)
            .count()
            >= 2
    );
}
#[test]
fn duplicate_name_copy_refusal_retains_allocated_empty_and_partial_utf8_text() {
    let name = "λ".repeat(3000);
    let mut m = Module::new("names");
    m.imports = vec![row(&name), row(&name)];
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.interning(&m, &mut work).unwrap();
    let pairs: Vec<_> = base
        .events
        .windows(2)
        .enumerate()
        .filter(|(_, p)| p.iter().all(|e| e.work == 1024 && e.copy_bytes == 1024))
        .map(|(i, _)| i)
        .collect();
    assert_eq!(pairs.len(), 1);
    let copy = pairs[0] + 2;
    for stop in [copy, copy + 1] {
        let mut o = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State::default();
        assert_eq!(
            state.interning(&m, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(state.errors.is_empty());
        assert!(state.first.capacity() >= 1024);
        assert_eq!(state.first.len(), if stop == copy { 0 } else { 1024 });
        assert!(name.starts_with(&state.first));
        drain(&mut state, &mut work);
        assert!(empty(&state));
        assert_eq!(
            work.session.first_refusal().unwrap().cause,
            "original import stop"
        );
    }
}
#[test]
fn both_identity_names_stay_owned_across_actual_output_reserve_and_header_refusal() {
    let mut m = Module::new("two-names");
    m.imports = vec![row("first-owned"), row("second-owned")];
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.identity(&m, &mut work).unwrap();
    let events: Vec<_> = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| e.work == 1 && e.copy_bytes == size_of::<ValidationError>())
        .map(|(i, _)| i + 1)
        .collect();
    assert_eq!(events.len(), 2);
    for (position, stop) in events.into_iter().enumerate() {
        let mut o = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State::default();
        assert_eq!(
            state.identity(&m, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(state.first, "first-owned");
        assert_eq!(state.second, "second-owned");
        assert!(state.errors.is_empty());
        assert_eq!(state.errors.capacity() == 0, position == 0);
        drain(&mut state, &mut work);
        assert!(empty(&state));
    }
}
#[test]
fn initial_header_and_final_publication_refusals_never_publish_a_smaller_list() {
    let m = fixture();
    let mut o = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_module_imports_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(o.events.len(), 1);
    let (_, base) = run(&m);
    let stop = base.events.len();
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_module_imports_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    assert!(o.events.len() > stop + 4);
    assert!(
        o.events
            .iter()
            .skip(stop)
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn refused_original_cleanup_consumes_both_partial_names_and_complete_owned_errors() {
    let mut o = Observer {
        cleanup: true,
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State {
        first: "λ".repeat(3000),
        second: "p".repeat(4000),
        errors: vec![ValidationError::ImportIdentityConflict {
            first: 0,
            conflicting: 1,
            first_name: "old".repeat(1000),
            conflicting_name: "new".repeat(1000),
        }],
    };
    drain(&mut state, &mut work);
    assert!(empty(&state));
    assert_eq!(
        work.session.first_refusal().unwrap().cause,
        "original cleanup"
    );
    assert_eq!(
        work.publication(),
        Err(ObservedValueError::AdmissionRefused)
    );
}
