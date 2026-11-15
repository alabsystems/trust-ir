// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Test-only private sealed outcomes; none are runtime authority evidence.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::validate::{
    HandleRegistry, ImportPolicy, ValidationError, call_handle_foreign_test,
    retire_validation_errors_observed, run_handle_foreign_test,
};
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, InterpretOptions,
    ObservedSession, ObservedValueError,
};
use trust_ir::value::{BlockId, FuncTyId};
use trust_ir::{ExternRef, FuncTy, Function, FunctionSummary, Ty};
fn fixture() -> (Module, HandleRegistry) {
    let mut m = Module::new("");
    m.func_types = vec![FuncTy::unrecorded(
        vec![Ty::handle("Name", "rt::Name")],
        vec![],
        false,
    )];
    let mut f = Function::new(
        FuncId::new(41),
        "foreign λ'\"\n\0",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    let mut summary = FunctionSummary::new();
    summary.backed_by = Some(ExternRef::new(ImportId::new(0), "unread symbol"));
    f.summary = Some(summary);
    m.functions.push(f);
    (m, HandleRegistry::from_pins(&[]).unwrap())
}
#[test]
fn actual_sealed_authenticated_and_reported_handle_outcomes_skip_refusal_and_wrong_map_cannot_override()
 {
    let (m, r) = fixture();
    for outcome in [SiteOutcome::Authenticated, SiteOutcome::Reported] {
        let mut auth = AuthenticatedImports::default();
        auth.handle_declarations
            .insert(FuncId::new(41).index(), outcome.clone());
        auth.backed_by
            .insert(41, SiteOutcome::Refused("WRONG TABLE".repeat(1000)));
        assert!(run_handle_foreign_test(&m, &r, ImportPolicy::Authenticated(&auth)).is_empty());
        assert_eq!(
            auth.handle_declaration_outcome(FuncId::new(41)),
            Some(&outcome)
        );
        assert!(
            auth.digests.is_empty()
                && auth.admitted.is_empty()
                && auth.handle_declaration_bodies.is_empty()
        );
    }
}
#[test]
fn actual_sealed_refusal_keeps_every_raw_byte_and_empty_refusal_stays_a_named_refusal() {
    let (m, r) = fixture();
    for detail in [String::new(), "raw λ'\"\n\0尾".repeat(2049) + "TAIL"] {
        let mut auth = AuthenticatedImports::default();
        auth.handle_declarations
            .insert(41, SiteOutcome::Refused(detail.clone()));
        auth.backed_by.insert(41, SiteOutcome::Authenticated);
        let out = run_handle_foreign_test(&m, &r, ImportPolicy::Authenticated(&auth));
        assert!(
            matches!(&out[..],[ValidationError::HandleForeignDeclaration {function:41,name,handle,detail:actual}] if name==&m.functions[0].name && handle.contains("Name") && actual==&detail)
        );
    }
}
#[test]
fn absent_actual_handle_outcome_refuses_even_when_other_sealed_map_authenticates_same_id() {
    let (m, r) = fixture();
    let mut auth = AuthenticatedImports::default();
    auth.backed_by.insert(41, SiteOutcome::Authenticated);
    auth.handle_declarations
        .insert(40, SiteOutcome::Authenticated);
    auth.handle_declarations.insert(42, SiteOutcome::Reported);
    assert!(
        matches!(&run_handle_foreign_test(&m,&r,ImportPolicy::Authenticated(&auth))[..],[ValidationError::HandleForeignDeclaration {detail,..}] if detail=="its `backed_by` was not examined by the linked validator")
    );
}
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    calls: Rc<Cell<usize>>,
    stop: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            Err("sealed foreign stop")
        } else {
            Ok(())
        }
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(1017))
}
#[test]
fn every_actual_sealed_cursor_and_full_foreign_branch_callback_refuses_without_minting_outcomes() {
    let (m, r) = fixture();
    let mut auth = AuthenticatedImports::default();
    for id in 0..42 {
        auth.handle_declarations
            .insert(id, SiteOutcome::Refused("retained raw λ\0".into()));
    }
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let nominal = m
        .nominal_type_reachability_observed(&mut s, site())
        .unwrap();
    let begin = calls.get();
    let out = call_handle_foreign_test(
        &m,
        &r,
        &nominal,
        ImportPolicy::Authenticated(&auth),
        &mut s,
        site(),
    )
    .unwrap();
    let end = calls.get();
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    nominal.retire_observed(&mut s, site()).unwrap();
    drop(s);
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let nominal = m
            .nominal_type_reachability_observed(&mut s, site())
            .unwrap();
        assert_eq!(
            call_handle_foreign_test(
                &m,
                &r,
                &nominal,
                ImportPolicy::Authenticated(&auth),
                &mut s,
                site()
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().cause, "sealed foreign stop");
        let _ = nominal.retire_observed(&mut s, site());
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
        assert_eq!(auth.handle_declarations.len(), 42);
    }
    assert!(
        auth.digests.is_empty()
            && auth.admitted.is_empty()
            && auth.handle_declaration_bodies.is_empty()
    );
}
#[test]
fn missing_backing_never_reads_or_population_prices_unrelated_sealed_outcomes() {
    let (mut m, r) = fixture();
    m.functions[0].summary.as_mut().unwrap().backed_by = None;
    let empty = AuthenticatedImports::default();
    let mut populated = AuthenticatedImports::default();
    for id in 0..256 {
        populated
            .handle_declarations
            .insert(id, SiteOutcome::Refused("unread payload λ\0".repeat(1000)));
    }
    let mut traces = vec![];
    for auth in [&empty, &populated] {
        let mut o = Observer::default();
        let calls = o.calls.clone();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let nominal = m
            .nominal_type_reachability_observed(&mut s, site())
            .unwrap();
        let begin = calls.get();
        let output = call_handle_foreign_test(
            &m,
            &r,
            &nominal,
            ImportPolicy::Authenticated(auth),
            &mut s,
            site(),
        )
        .unwrap();
        let end = calls.get();
        assert!(
            matches!(&output[..], [ValidationError::HandleForeignDeclaration{detail,..}] if detail.starts_with("no `backed_by`"))
        );
        retire_validation_errors_observed(output, &mut s, site()).unwrap();
        nominal.retire_observed(&mut s, site()).unwrap();
        drop(s);
        traces.push(o.events[begin..end].to_vec());
    }
    assert_eq!(traces[0], traces[1]);
}
