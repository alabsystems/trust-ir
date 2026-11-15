// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; private fixtures record labels, not authenticated evidence.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::validate::ImportPolicy;
use crate::validate::observed_effect_admission::{
    admissible_effects_observed,
    tests::{Observer, assert_ordinary, fixture, site},
};
use trust_ir::interpret::{InterpretOptions, ObservedSession, ObservedValueError};
#[test]
fn only_the_exact_stored_authenticated_outcome_admits_a_declaration_effect_pointer() {
    let m = fixture(true);
    for outcome in [
        None,
        Some(SiteOutcome::Authenticated),
        Some(SiteOutcome::Reported),
        Some(SiteOutcome::Refused("full λ\0".repeat(1000))),
    ] {
        let mut auth = AuthenticatedImports::default();
        let expected = matches!(outcome.as_ref(), Some(SiteOutcome::Authenticated));
        if let Some(outcome) = outcome {
            auth.record_backed_by(FuncId::new(221), outcome);
        }
        assert_ordinary(&m, FuncId::new(221), ImportPolicy::Authenticated(&auth));
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            admissible_effects_observed(
                &m,
                FuncId::new(221),
                ImportPolicy::Authenticated(&auth),
                &mut s,
                site()
            )
            .unwrap()
            .is_some(),
            expected
        );
        assert!(auth.digests().is_empty() && auth.authenticated_inheritances().is_empty());
    }
}
#[test]
fn recorded_labels_never_admit_interposable_symbols_and_definitions_keep_the_original_rule() {
    for declaration in [false, true] {
        for linkage in [
            trust_ir::Linkage::Weak,
            trust_ir::Linkage::LinkOnce,
            trust_ir::Linkage::ExternalWeak,
        ] {
            let mut m = fixture(declaration);
            m.functions[0].linkage = linkage;
            let mut auth = AuthenticatedImports::default();
            auth.record_backed_by(FuncId::new(221), SiteOutcome::Authenticated);
            assert_ordinary(&m, FuncId::new(221), ImportPolicy::Authenticated(&auth));
            let mut o = Observer::default();
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert!(
                admissible_effects_observed(
                    &m,
                    FuncId::new(221),
                    ImportPolicy::Authenticated(&auth),
                    &mut s,
                    site()
                )
                .unwrap()
                .is_none()
            );
        }
    }
    let m = fixture(false);
    let mut auth = AuthenticatedImports::default();
    auth.record_backed_by(
        FuncId::new(221),
        SiteOutcome::Refused("not used for a definition".into()),
    );
    assert_ordinary(&m, FuncId::new(221), ImportPolicy::Authenticated(&auth));
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        admissible_effects_observed(
            &m,
            FuncId::new(221),
            ImportPolicy::Authenticated(&auth),
            &mut s,
            site()
        )
        .unwrap()
        .is_some()
    );
}
#[test]
fn every_actual_recorded_map_lookup_callback_refuses_without_authentication_or_havoc_fallback() {
    let m = fixture(true);
    let mut auth = AuthenticatedImports::default();
    for i in 0..221 {
        auth.record_backed_by(FuncId::new(i), SiteOutcome::Reported);
    }
    auth.record_backed_by(FuncId::new(221), SiteOutcome::Authenticated);
    let base = assert_ordinary(&m, FuncId::new(221), ImportPolicy::Authenticated(&auth));
    let before = auth.backed_by.clone();
    for stop in 1..=base.events.len() {
        let mut o = Observer::stopping(stop);
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            admissible_effects_observed(
                &m,
                FuncId::new(221),
                ImportPolicy::Authenticated(&auth),
                &mut s,
                site()
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
        drop(s);
        assert_eq!(o.events.len(), stop);
    }
    assert_eq!(auth.backed_by, before);
    assert!(auth.digests().is_empty() && auth.authenticated_inheritances().is_empty());
}
#[test]
fn unrelated_recorded_outcomes_and_large_refusal_text_cannot_be_reused_as_authentication() {
    let m = fixture(true);
    let mut auth = AuthenticatedImports::default();
    auth.record_backed_by(FuncId::new(220), SiteOutcome::Authenticated);
    auth.record_backed_by(FuncId::new(222), SiteOutcome::Authenticated);
    assert_ordinary(&m, FuncId::new(221), ImportPolicy::Authenticated(&auth));
    let refusal = "λ\0".repeat(100000) + "TAIL";
    auth.record_backed_by(FuncId::new(221), SiteOutcome::Refused(refusal.clone()));
    assert_ordinary(&m, FuncId::new(221), ImportPolicy::Authenticated(&auth));
    assert!(
        matches!(auth.backed_by_outcome(FuncId::new(221)),Some(SiteOutcome::Refused(text)) if text==&refusal)
    );
    assert!(auth.digests().is_empty() && auth.authenticated_inheritances().is_empty());
}
