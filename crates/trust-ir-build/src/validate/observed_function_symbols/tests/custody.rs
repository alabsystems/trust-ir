// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn actual_name_copy_keeps_allocated_empty_or_partial_utf8_before_attribution_starts() {
    let first = function(1, &"λ".repeat(3000));
    let second = function(2, &first.name);
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    state.duplicate(&first, &second, &mut work).unwrap();
    drain(&mut state, &mut work);
    let pairs = baseline
        .events
        .windows(2)
        .enumerate()
        .filter(|(_, p)| p.iter().all(|e| e.work == 1024 && e.copy_bytes == 1024))
        .map(|(i, _)| i)
        .collect::<Vec<_>>();
    assert_eq!(pairs.len(), 1);
    let copy = pairs[0] + 2;
    for stop in [copy, copy + 1] {
        let mut observer = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let mut work = Work {
            session: &mut session,
            site: site(),
        };
        let mut state = State::default();
        assert_eq!(
            state.duplicate(&first, &second, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(state.name.capacity() >= 1024);
        assert_eq!(state.name.len(), if stop == copy { 0 } else { 1024 });
        assert!(state.first_producer.is_none());
        assert!(state.first_path.is_none());
        assert!(state.errors.is_empty());
        drain(&mut state, &mut work);
        assert!(empty(&state));
    }
}
#[test]
fn partial_other_producer_is_owned_inside_its_option_before_later_fields_or_output_work() {
    let mut first = function(1, "same");
    first.producer = Some(Producer::Other("λ".repeat(3000)));
    let second = function(2, "same");
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    state.duplicate(&first, &second, &mut work).unwrap();
    drain(&mut state, &mut work);
    let pairs = baseline
        .events
        .windows(2)
        .enumerate()
        .filter(|(_, p)| p.iter().all(|e| e.work == 1024 && e.copy_bytes == 1024))
        .map(|(i, _)| i)
        .collect::<Vec<_>>();
    assert_eq!(pairs.len(), 1);
    let stop = pairs[0] + 3;
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        state.duplicate(&first, &second, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.name, "same");
    assert_eq!(state.first_producer, Some(Producer::Other("λ".repeat(512))));
    assert!(state.second_producer.is_none());
    assert!(state.first_path.is_none());
    assert!(state.errors.is_empty());
    drain(&mut state, &mut work);
    assert!(empty(&state));
    assert_eq!(
        work.session.first_refusal().unwrap().cause,
        "original symbol stop"
    );
    assert!(
        observer
            .events
            .iter()
            .skip(stop)
            .any(|e| e.phase == ExecutionPhase::ScratchRetirement
                && e.work == 1024 + size_of::<String>() + 1)
    );
}
#[test]
fn optional_path_header_refusal_distinguishes_absent_from_owned_empty_before_text_copy() {
    let source = Some("λpath".to_owned());
    for (stop, owned) in [(1, false), (2, true)] {
        let mut observer = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let mut work = Work {
            session: &mut session,
            site: site(),
        };
        let mut output = None;
        assert_eq!(
            work.path(&source, &mut output),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(output.is_some(), owned);
        if let Some(text) = &output {
            assert_eq!((text.len(), text.capacity()), (0, 0));
        }
        work.retire_path(output.take());
        assert!(output.is_none());
        assert_eq!(
            work.session.first_refusal().unwrap().cause,
            "original symbol stop"
        );
    }
}
#[test]
fn every_complete_attribution_field_stays_owned_through_reserve_and_header_move_refusal() {
    let mut first = function(9, "same");
    first.producer = Some(Producer::Other("first-owned".into()));
    first.display_path = Some("".into());
    let mut second = function(2, "same");
    second.producer = Some(Producer::Other("second-owned".into()));
    second.display_path = Some("second-path".into());
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    state.duplicate(&first, &second, &mut work).unwrap();
    drain(&mut state, &mut work);
    let positions = baseline
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 1
                && e.copy_bytes == size_of::<ValidationError>()
        })
        .map(|(i, _)| i + 1)
        .collect::<Vec<_>>();
    assert_eq!(positions.len(), 2);
    for (n, stop) in positions.into_iter().enumerate() {
        let mut observer = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let mut work = Work {
            session: &mut session,
            site: site(),
        };
        let mut state = State::default();
        assert_eq!(
            state.duplicate(&first, &second, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(state.name, "same");
        assert_eq!(state.first_producer, first.producer);
        assert_eq!(state.second_producer, second.producer);
        assert_eq!(state.first_path, first.display_path);
        assert_eq!(state.second_path, second.display_path);
        assert!(state.errors.is_empty());
        assert_eq!(state.errors.capacity() == 0, n == 0);
        drain(&mut state, &mut work);
        assert!(empty(&state));
    }
}
#[test]
fn refused_cleanup_consumes_all_partial_options_and_completed_nested_diagnostics() {
    let mut observer = Observer {
        cleanup: true,
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State {
        name: "λ".repeat(1000),
        first_producer: Some(Producer::Other("a".repeat(3000))),
        second_producer: Some(Producer::Other("b".repeat(4000))),
        first_path: Some(String::new()),
        second_path: Some("path".repeat(2000)),
        errors: fixtures::ordinary(&fixtures::fixture()),
    };
    drain(&mut state, &mut work);
    assert!(empty(&state));
    assert_eq!(work.session.first_refusal().unwrap().cause, "cleanup stop");
    assert_eq!(
        work.publication(),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(
        observer
            .events
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
    for bytes in [2000, 3000, 4000, 0, 8000] {
        assert!(
            observer
                .events
                .iter()
                .any(|e| e.work == bytes + size_of::<String>() + 1)
        );
    }
}
#[test]
fn original_sticky_cause_survives_consuming_every_producer_and_path_case() {
    let mut observer = Observer {
        stop: Some(1),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let first = ExecutionProgress {
        phase: ExecutionPhase::ModuleLookup,
        site: site(),
        work: 37,
        copy_bytes: 0,
    };
    assert!(session.admit(first).is_err());
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    for value in fixtures::producers() {
        work.retire_producer(value);
    }
    for value in [None, Some(String::new()), Some("λ\0path".into())] {
        work.retire_path(value);
    }
    assert_eq!(work.session.first_refusal().unwrap().progress, first);
    assert_eq!(
        work.session.first_refusal().unwrap().cause,
        "original symbol stop"
    );
    assert_eq!(
        work.publication(),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(
        observer.events[1..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
