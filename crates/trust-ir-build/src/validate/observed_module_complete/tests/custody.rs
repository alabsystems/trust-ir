// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn actual_symbol_chunk_stop_keeps_partial_owned_text_before_any_row_exists() {
    let symbol = "λ".repeat(3000);
    let rows = vec![row(&symbol, Some("path"), "reason")];
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    state.copy_rows(&rows, &mut work).unwrap();
    drain(&mut state, &mut work);
    let pairs = baseline
        .events
        .windows(2)
        .enumerate()
        .filter(|(_, p)| p.iter().all(|e| e.work == 1024 && e.copy_bytes == 1024))
        .map(|(i, _)| i)
        .collect::<Vec<_>>();
    assert_eq!(pairs.len(), 1);
    let first_copy = pairs[0] + 2;
    for stop in [first_copy, first_copy + 1] {
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
            state.copy_rows(&rows, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(state.symbol.capacity() >= 1024);
        assert_eq!(
            state.symbol.len(),
            if stop == first_copy { 0 } else { 1024 }
        );
        assert!(state.rows.is_empty());
        assert!(state.path.is_none());
        assert_eq!(state.reason.capacity(), 0);
        drain(&mut state, &mut work);
        assert!(empty(&state));
        assert_eq!(
            work.session.first_refusal().unwrap().cause,
            "original completeness stop"
        );
    }
}
#[test]
fn optional_path_header_is_admitted_then_retained_before_its_first_fallible_copy() {
    let rows = vec![row("", Some("λpath"), "reason")];
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    state.copy_rows(&rows, &mut work).unwrap();
    drain(&mut state, &mut work);
    let positions = baseline
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 1
                && e.copy_bytes == size_of::<Option<String>>()
        })
        .map(|(i, _)| i + 1)
        .collect::<Vec<_>>();
    assert_eq!(positions.len(), 1);
    for (stop, owned) in [(positions[0], false), (positions[0] + 1, true)] {
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
            state.copy_rows(&rows, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(state.path.is_some(), owned);
        if let Some(path) = &state.path {
            assert_eq!((path.len(), path.capacity()), (0, 0));
        }
        assert!(state.rows.is_empty());
        drain(&mut state, &mut work);
        assert!(empty(&state));
    }
}
#[test]
fn all_three_pending_fields_survive_distinct_row_reserve_and_move_refusals() {
    let rows = vec![row("symbol-owned", Some("path-owned"), "reason-owned")];
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    state.copy_rows(&rows, &mut work).unwrap();
    drain(&mut state, &mut work);
    let positions = baseline
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 1
                && e.copy_bytes == size_of::<UnloweredRow>()
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
            state.copy_rows(&rows, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(state.symbol, "symbol-owned");
        assert_eq!(state.path.as_deref(), Some("path-owned"));
        assert_eq!(state.reason, "reason-owned");
        assert!(state.rows.is_empty());
        assert_eq!(state.rows.capacity() == 0, n == 0);
        drain(&mut state, &mut work);
        assert!(empty(&state));
    }
}
#[test]
fn a_completed_prior_row_stays_owned_alongside_the_next_partial_symbol_until_cleanup() {
    let rows = vec![
        row("prior", Some("prior-path"), "prior-reason"),
        row(&"λ".repeat(3000), None, "later"),
    ];
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    state.copy_rows(&rows, &mut work).unwrap();
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
        state.copy_rows(&rows, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.rows, vec![rows[0].clone()]);
    assert_eq!(state.symbol, "λ".repeat(512));
    drain(&mut state, &mut work);
    assert!(empty(&state));
    assert_eq!(
        work.session.first_refusal().unwrap().cause,
        "original completeness stop"
    );
    for bytes in [
        "prior".len(),
        "prior-path".len(),
        "prior-reason".len(),
        1024,
    ] {
        assert!(
            observer
                .events
                .iter()
                .skip(stop)
                .any(|e| e.phase == ExecutionPhase::ScratchRetirement
                    && e.work == bytes + size_of::<String>() + 1)
        );
    }
}
