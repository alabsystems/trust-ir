// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn refused_cleanup_consumes_pending_fields_prior_rows_and_a_completed_owned_outcome() {
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
        symbol: "λ".repeat(1000),
        path: Some("pending-path".into()),
        reason: "pending-reason".into(),
        rows: vec![row("finished", Some("finished-path"), "finished-reason")],
        outcome: Err(CompletenessError::ModuleIncomplete {
            rows: vec![row("published-pending", None, "owned-reason")],
        }),
    };
    drain(&mut state, &mut work);
    assert!(empty(&state));
    assert_eq!(work.session.first_refusal().unwrap().cause, "cleanup stop");
    assert_eq!(
        work.publication(1, size_of::<Result<(), CompletenessError>>()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(
        observer
            .events
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
    for bytes in [
        2000,
        "pending-path".len(),
        "pending-reason".len(),
        "finished".len(),
        "finished-path".len(),
        "finished-reason".len(),
        "published-pending".len(),
        "owned-reason".len(),
    ] {
        assert!(
            observer
                .events
                .iter()
                .any(|e| e.work == bytes + size_of::<String>() + 1)
        );
    }
}
#[test]
fn consuming_prestopped_error_preserves_original_cause_through_every_secondary_refusal() {
    #[derive(Default)]
    struct RejectEvery {
        events: Vec<ExecutionProgress>,
    }
    impl ExecutionObserver for RejectEvery {
        type Refusal = &'static str;
        fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
            self.events.push(event);
            Err(if event.phase == ExecutionPhase::ScratchRetirement {
                "secondary cleanup stop"
            } else {
                "original owner stop"
            })
        }
    }
    let error = CompletenessError::ModuleIncomplete {
        rows: fixtures::rows(),
    };
    let expected = retired(error.clone())
        .events
        .into_iter()
        .filter(|e| e.phase == ExecutionPhase::ScratchRetirement)
        .collect::<Vec<_>>();
    let mut observer = RejectEvery::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let first = ExecutionProgress {
        phase: ExecutionPhase::ModuleLookup,
        site: site(),
        work: 31,
        copy_bytes: 0,
    };
    assert!(session.admit(first).is_err());
    assert_eq!(
        error.retire_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().cause,
        "original owner stop"
    );
    assert_eq!(session.first_refusal().unwrap().progress, first);
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    assert_eq!(observer.events[1..], expected);
}
