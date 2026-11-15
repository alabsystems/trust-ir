// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual common diagnostics finish route; no Authority/currency fixture.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    next: Rc<Cell<usize>>,
    stop: Rc<Cell<Option<usize>>>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, p: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(p);
        self.next.set(self.events.len());
        if self.stop.get() == Some(self.events.len()) {
            Err("original stop")
        } else {
            Ok(())
        }
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(644))
}
fn inputs() -> Vec<ValidationError> {
    vec![
        ValidationError::GatedEvidenceMismatch {
            function: 17,
            detail: "whole already owned diagnostic λ".repeat(70),
        },
        ValidationError::GatedEvidenceMismatch {
            function: 18,
            detail: "second complete diagnostic".into(),
        },
    ]
}
#[test]
fn three_held_local_errors_survive_actual_common_finish_cleanup_refusal_and_whole_batch_disposal() {
    for error in [
        ObservedValueError::CapacityOverflow,
        ObservedValueError::AllocationFailed,
        ObservedValueError::InvalidRange,
    ] {
        let errors = inputs();
        let mut o = Observer::default();
        let next = Rc::clone(&o.next);
        let stop = Rc::clone(&o.stop);
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State {
            errors,
            candidate: None,
        };
        let held = Err(error);
        stop.set(Some(next.get() + 1));
        assert_eq!(state.finish(held, &mut w), Err(error));
        assert!(state.errors.is_empty());
        assert!(state.candidate.is_none());
        assert_eq!(s.first_refusal().unwrap().cause, "original stop");
        drop(s);
        assert!(!o.events.is_empty());
        assert!(
            o.events
                .iter()
                .all(|p| p.phase == ExecutionPhase::ScratchRetirement && p.site == site())
        );
    }
}
#[test]
fn a_previously_healthy_whole_batch_is_still_withheld_on_the_same_cleanup_refusal() {
    let errors = inputs();
    let mut o = Observer::default();
    let stop = Rc::clone(&o.stop);
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State {
        errors,
        candidate: None,
    };
    stop.set(Some(1));
    assert_eq!(
        state.finish(Ok(()), &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(state.errors.is_empty());
    assert_eq!(s.first_refusal().unwrap().cause, "original stop");
}
#[test]
fn normal_common_finish_preserves_complete_errors_and_the_existing_publication_receipt() {
    let errors = inputs();
    let expected = errors.clone();
    let mut o = Observer::default();
    let next = Rc::clone(&o.next);
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State {
        errors,
        candidate: None,
    };
    let actual = state.finish(Ok(()), &mut w).unwrap();
    assert_eq!(actual, expected);
    assert!(state.errors.is_empty());
    drop(w);
    let end = next.get();
    retire_validation_errors_observed(actual, &mut s, site()).unwrap();
    drop(s);
    assert_eq!(
        o.events[end - 1],
        ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 1,
            copy_bytes: size_of::<Vec<ValidationError>>()
        }
    );
}

#[test]
fn a_held_local_result_and_later_original_cause_remain_distinct_through_every_cleanup_tail() {
    let held = Err(ObservedValueError::AllocationFailed);
    let errors = inputs();
    let mut o = Observer::default();
    let stop = Rc::clone(&o.stop);
    stop.set(Some(1));
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let p = ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site: site(),
        work: 3,
        copy_bytes: 5,
    };
    assert!(s.admit(p).is_err());
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State {
        errors,
        candidate: None,
    };
    assert_eq!(
        state.finish(held, &mut w),
        Err(ObservedValueError::AllocationFailed)
    );
    drop(w);
    assert_eq!(s.first_refusal().unwrap().progress, p);
    assert_eq!(s.first_refusal().unwrap().cause, "original stop");
    assert!(state.errors.is_empty());
    drop(s);
    assert!(
        o.events[1..]
            .iter()
            .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
    );
}
