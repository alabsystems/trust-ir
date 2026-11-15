// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Private recorded-label fixtures are not linked authentication evidence.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use trust_ir::interpret::InterpretOptions;

#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop: Option<usize>,
    work: usize,
    copy: usize,
    work_cap: Option<usize>,
    copy_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop == Some(self.events.len()) {
            return Err("handle-outcome stop");
        }
        self.work = self.work.checked_add(event.work).ok_or("overflow")?;
        self.copy = self.copy.checked_add(event.copy_bytes).ok_or("overflow")?;
        if self.work_cap.is_some_and(|cap| self.work > cap) {
            return Err("work");
        }
        if self.copy_cap.is_some_and(|cap| self.copy > cap) {
            return Err("copy");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(317))
}
fn fixture() -> AuthenticatedImports {
    let mut auth = AuthenticatedImports::default();
    for key in (0..100).map(|n| n * 2).chain([u32::MAX]) {
        auth.handle_declarations.insert(
            key,
            match key % 3 {
                0 => SiteOutcome::Authenticated,
                1 => SiteOutcome::Reported,
                _ => SiteOutcome::Refused(format!("retained{key}λ\0")),
            },
        );
    }
    auth
}
fn baseline(auth: &AuthenticatedImports, key: u32) -> Observer {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        auth.handle_declaration_outcome_observed(FuncId::new(key), &mut session, site())
            .unwrap(),
        auth.handle_declaration_outcome(FuncId::new(key))
    );
    drop(session);
    observer
}

#[test]
fn every_key_gap_and_u32_boundary_borrows_the_exact_original_outcome_without_mutation() {
    let auth = fixture();
    let before = auth.clone();
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    for key in (0..202).chain([u32::MAX - 1, u32::MAX]) {
        let actual = auth
            .handle_declaration_outcome_observed(FuncId::new(key), &mut session, site())
            .unwrap();
        let expected = auth.handle_declaration_outcome(FuncId::new(key));
        assert_eq!(actual, expected);
        if let (Some(actual), Some(expected)) = (actual, expected) {
            assert!(
                std::ptr::eq(actual, expected),
                "return the existing stored row, not a clone"
            );
        }
    }
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    assert_eq!(auth.handle_declarations, before.handle_declarations);
    assert!(auth.digests().is_empty() && auth.authenticated_inheritances().is_empty());
}

#[test]
fn handle_outcomes_do_not_read_summary_or_inheritance_rosters_with_the_same_key() {
    let mut auth = AuthenticatedImports::default();
    auth.record_backed_by(FuncId::new(7), SiteOutcome::Authenticated);
    assert!(baseline(&auth, 7).events.last().unwrap().phase == ExecutionPhase::Publication);
    assert!(auth.handle_declaration_outcome(FuncId::new(7)).is_none());
    auth.handle_declarations
        .insert(7, SiteOutcome::Refused("separate exact handle row".into()));
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert!(
        matches!(auth.handle_declaration_outcome_observed(FuncId::new(7), &mut session, site()).unwrap(), Some(SiteOutcome::Refused(detail)) if detail == "separate exact handle row")
    );
    assert_eq!(
        auth.backed_by_outcome(FuncId::new(7)),
        Some(&SiteOutcome::Authenticated)
    );
    assert!(auth.inherited.is_empty() && auth.handle_declaration_bodies.is_empty());
}

#[test]
fn every_real_cursor_compare_and_publication_callback_can_refuse_without_an_absent_fallback() {
    let auth = fixture();
    let full = baseline(&auth, u32::MAX);
    assert!(full.events.len() > 200);
    assert_eq!(
        full.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    for stop in 1..=full.events.len() {
        let mut observer = Observer {
            stop: Some(stop),
            ..Default::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            auth.handle_declaration_outcome_observed(FuncId::new(u32::MAX), &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let (first_progress, first_cause) = {
            let first = session.first_refusal().unwrap();
            (first.progress, first.cause)
        };
        assert_eq!(first_progress, full.events[stop - 1]);
        assert_eq!(first_cause, "handle-outcome stop");
        assert_eq!(
            auth.handle_declaration_outcome_observed(FuncId::new(0), &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let retained = session.first_refusal().unwrap();
        assert_eq!(retained.progress, first_progress);
        assert_eq!(retained.cause, first_cause);
        drop(session);
        assert_eq!(observer.events, full.events[..stop]);
    }
    assert!(matches!(
        auth.handle_declaration_outcome(FuncId::new(u32::MAX)),
        Some(SiteOutcome::Authenticated)
    ));
}

#[test]
fn same_original_work_and_copy_ledgers_accumulate_without_execution_fuel_or_site_changes() {
    let auth = fixture();
    let full = baseline(&auth, u32::MAX);
    for copy in [false, true] {
        let mut observer = Observer {
            work_cap: (!copy).then_some(full.work),
            copy_cap: copy.then_some(full.copy),
            ..Default::default()
        };
        let mut session = ObservedSession::new(
            InterpretOptions {
                fuel: 0,
                ..Default::default()
            },
            &mut observer,
        );
        auth.handle_declaration_outcome_observed(FuncId::new(u32::MAX), &mut session, site())
            .unwrap();
        assert_eq!(
            auth.handle_declaration_outcome_observed(FuncId::new(u32::MAX), &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
        assert_eq!(session.first_refusal().unwrap().progress.site, site());
        assert_eq!(session.remaining_fuel(), 0);
    }
}

#[test]
fn borrowed_refusal_detail_and_unrelated_payloads_remain_unread_and_fully_retained() {
    let mut auth = fixture();
    auth.handle_declarations
        .insert(u32::MAX, SiteOutcome::Refused("small".into()));
    let before = baseline(&auth, u32::MAX);
    let detail = "full raw λ\0\n".repeat(10_000);
    auth.handle_declarations
        .insert(u32::MAX, SiteOutcome::Refused(detail.clone()));
    for key in 0..32 {
        auth.backed_by
            .insert(key, SiteOutcome::Refused(detail.clone()));
    }
    let after = baseline(&auth, u32::MAX);
    assert_eq!(
        before.events, after.events,
        "only integer keys and borrowed row addresses are inspected"
    );
    assert!(
        matches!(auth.handle_declaration_outcome(FuncId::new(u32::MAX)), Some(SiteOutcome::Refused(retained)) if retained == &detail)
    );
    assert!(auth.handle_declaration_bodies.is_empty());
}

#[test]
fn the_refactored_summary_scanner_retains_the_exact_same_trace_as_the_handle_scanner() {
    let mut auth = fixture();
    auth.backed_by = auth.handle_declarations.clone();
    for key in [0, 1, 100, 199, u32::MAX] {
        let handle = baseline(&auth, key);
        let mut observer = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            auth.backed_by_outcome_observed(FuncId::new(key), &mut session, site())
                .unwrap(),
            auth.backed_by_outcome(FuncId::new(key))
        );
        drop(session);
        assert_eq!(observer.events, handle.events);
    }
}
