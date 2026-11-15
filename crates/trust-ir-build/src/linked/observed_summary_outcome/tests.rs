// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN. Private in-memory outcome fixtures grant no proof authority.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::validate::{
    ImportPolicy,
    observed_summary_backing::{
        SummaryCitation, validate_function_summary_import_backing_observed,
    },
};
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::{BlockId, FuncTyId, ProofId};
use trust_ir::{ExternRef, Function, FunctionSummary, ModuleImport};
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop: Option<usize>,
    work: usize,
    cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        if self.stop == Some(self.events.len()) {
            return Err("outcome stop");
        };
        self.work = self.work.checked_add(e.work).ok_or("overflow")?;
        if self.cap.is_some_and(|n| self.work > n) {
            return Err("work");
        };
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(158))
}
fn fixture() -> AuthenticatedImports {
    let mut a = AuthenticatedImports::default();
    for i in (0..100).map(|i| i * 2) {
        a.record_backed_by(
            FuncId::new(i),
            match i % 3 {
                0 => SiteOutcome::Authenticated,
                1 => SiteOutcome::Reported,
                _ => SiteOutcome::Refused(format!("refused{i}λ")),
            },
        );
    }
    a
}
#[test]
fn actual_ordered_map_scan_matches_original_get_for_every_key_gap_and_boundary() {
    let a = fixture();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    for n in (0..201).chain([u32::MAX]) {
        let id = FuncId::new(n);
        assert_eq!(
            a.backed_by_outcome_observed(id, &mut s, site()).unwrap(),
            a.backed_by_outcome(id)
        );
    }
    assert!(s.first_refusal().is_none());
    assert!(a.digests().is_empty() && a.authenticated_inheritances().is_empty());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
}
#[test]
fn interior_map_cursor_refusal_does_not_return_none_or_a_different_outcome() {
    let a = fixture();
    let trace = {
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert!(
            a.backed_by_outcome_observed(FuncId::new(u32::MAX), &mut s, site())
                .unwrap()
                .is_none()
        );
        drop(s);
        o.events
    };
    let at = trace
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.copy_bytes == size_of::<Option<(&u32, &SiteOutcome)>>()
        })
        .nth(50)
        .unwrap()
        .0
        + 1;
    let mut o = Observer {
        stop: Some(at),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        a.backed_by_outcome_observed(FuncId::new(u32::MAX), &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().progress, trace[at - 1]);
    assert_eq!(a.backed_by.len(), 100);
}
#[test]
fn same_original_outcome_budget_cumulates_and_preserves_zero_execution_fuel() {
    let a = fixture();
    let cap = {
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        a.backed_by_outcome_observed(FuncId::new(198), &mut s, site())
            .unwrap();
        drop(s);
        o.work
    };
    let mut o = Observer {
        cap: Some(cap),
        ..Default::default()
    };
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..Default::default()
        },
        &mut o,
    );
    a.backed_by_outcome_observed(FuncId::new(198), &mut s, site())
        .unwrap();
    assert_eq!(
        a.backed_by_outcome_observed(FuncId::new(198), &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "work");
    assert_eq!(s.remaining_fuel(), 0);
}
#[test]
fn positive_reported_refused_and_absent_outcomes_keep_the_actual_summary_policy() {
    for outcome in [
        Some(SiteOutcome::Authenticated),
        Some(SiteOutcome::Reported),
        Some(SiteOutcome::Refused("full-λ\n'".repeat(1000))),
        None,
    ] {
        let mut a = AuthenticatedImports::default();
        if let Some(v) = outcome.clone() {
            a.record_backed_by(FuncId::new(7), v)
        };
        let mut m = Module::new("citation");
        m.imports
            .push(ModuleImport::new("far", ProofDigest::sha256([4; 32])));
        let f = Function::new(FuncId::new(7), "f", FuncTyId::new(0), BlockId::new(0));
        let mut summary = FunctionSummary::new();
        summary.proved = true;
        summary.backed_by =
            Some(ExternRef::new(ImportId::new(0), "symbol").relying_on(ProofId::new(3)));
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let (errors, claim) = validate_function_summary_import_backing_observed(
            &m,
            &f,
            &summary,
            ImportPolicy::Authenticated(&a),
            &mut s,
            site(),
        )
        .unwrap();
        assert_eq!(claim, SummaryCitation::ProofBearing);
        match outcome {
            Some(SiteOutcome::Authenticated) | Some(SiteOutcome::Reported) => {
                assert!(errors.is_empty())
            }
            Some(SiteOutcome::Refused(detail)) => assert!(
                matches!(&errors[..],[ValidationError::UnauthenticatedImport {detail:actual,..}] if actual==&detail)
            ),
            None => assert!(
                matches!(&errors[..],[ValidationError::UnauthenticatedImport {detail,..}] if detail.contains("was not examined"))
            ),
        }
        assert!(a.digests().is_empty() && a.authenticated_inheritances().is_empty());
    }
}
#[test]
fn actual_authenticated_summary_lookup_stop_refuses_instead_of_defaulting_to_a_backed_claim() {
    let a = fixture();
    let mut m = Module::new("citation");
    m.imports
        .push(ModuleImport::new("far", ProofDigest::sha256([4; 32])));
    let f = Function::new(FuncId::new(198), "f", FuncTyId::new(0), BlockId::new(0));
    let mut summary = FunctionSummary::new();
    summary.proved = true;
    summary.backed_by =
        Some(ExternRef::new(ImportId::new(0), "symbol").relying_on(ProofId::new(3)));
    let trace = {
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        validate_function_summary_import_backing_observed(
            &m,
            &f,
            &summary,
            ImportPolicy::Authenticated(&a),
            &mut s,
            site(),
        )
        .unwrap();
        drop(s);
        o.events
    };
    let at = trace
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 101
                && e.copy_bytes == size_of::<Option<(&u32, &SiteOutcome)>>()
        })
        .nth(50)
        .unwrap()
        .0
        + 1;
    let mut o = Observer {
        stop: Some(at),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_function_summary_import_backing_observed(
            &m,
            &f,
            &summary,
            ImportPolicy::Authenticated(&a),
            &mut s,
            site()
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "outcome stop");
}
#[test]
fn final_borrowed_lookup_publication_can_refuse_without_mutating_the_existing_roster() {
    let a = fixture();
    let trace = {
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        a.backed_by_outcome_observed(FuncId::new(0), &mut s, site())
            .unwrap();
        drop(s);
        o.events
    };
    let mut o = Observer {
        stop: Some(trace.len()),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        a.backed_by_outcome_observed(FuncId::new(0), &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    assert_eq!(
        a.backed_by_outcome(FuncId::new(0)),
        Some(&SiteOutcome::Authenticated)
    );
}
