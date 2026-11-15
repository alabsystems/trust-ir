// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN: private stored-outcome fixtures, never proof authority.
use super::*;
use crate::validate::observed_summary::tests::assert_ordinary;
use crate::validate::{ImportPolicy, ValidationError};
use trust_ir::proof::ProofFormula;
use trust_ir::value::{BlockId, FuncTyId, ProofId};
use trust_ir::{Block, ExternRef, FuncTy, Function, FunctionSummary, ModuleImport};
fn fixture() -> (Module, Function, FunctionSummary) {
    let mut m = Module::new("stored outcome");
    m.func_types.push(FuncTy::unrecorded(vec![], vec![], false));
    let f = Function::new(FuncId::new(23), "f", FuncTyId::new(0), BlockId::new(0));
    m.functions.push(f.clone());
    m.imports
        .push(ModuleImport::new("dep", ProofDigest::sha256([4; 32])));
    let mut s = FunctionSummary::new();
    s.proved = true;
    s.requires.push(ProofFormula::new("opaque", "text"));
    s.backed_by = Some(ExternRef::new(ImportId::new(0), "f").relying_on(ProofId::new(1)));
    (m, f, s)
}
#[test]
fn every_original_stored_outcome_is_forwarded_through_the_whole_summary_policy() {
    let (m, f, s) = fixture();
    for outcome in [
        SiteOutcome::Authenticated,
        SiteOutcome::Reported,
        SiteOutcome::Refused("actual full refusal λ".into()),
    ] {
        let mut auth = AuthenticatedImports::default();
        let refused = matches!(&outcome, SiteOutcome::Refused(_));
        auth.record_backed_by(f.id, outcome);
        let out = assert_ordinary(&m, &f, &s, ImportPolicy::Authenticated(&auth));
        assert_eq!(out.len(), usize::from(refused));
        assert!(auth.digests().is_empty() && auth.authenticated_inheritances().is_empty());
    }
}
#[test]
fn a_stored_authenticated_label_cannot_make_a_definition_skip_local_missing_rows() {
    let (mut m, mut f, s) = fixture();
    f.blocks.push(Block::new(BlockId::new(0)));
    m.functions[0] = f.clone();
    let mut auth = AuthenticatedImports::default();
    auth.record_backed_by(f.id, SiteOutcome::Authenticated);
    let out = assert_ordinary(&m, &f, &s, ImportPolicy::Authenticated(&auth));
    assert_eq!(out.len(), 1);
    assert!(
        matches!(&out[0],ValidationError::InvalidFunctionSummary {detail,..} if detail.starts_with("requires clause 0 `"))
    );
    assert!(auth.digests().is_empty() && auth.authenticated_inheritances().is_empty());
}
#[test]
fn earlier_binding_errors_and_complete_stored_refusal_remain_ordered_without_second_missing_error()
{
    let (m, f, mut s) = fixture();
    s.requires[0].schema = " ".into();
    let refused = "full λ\0".repeat(2000) + "TAIL";
    let mut auth = AuthenticatedImports::default();
    auth.record_backed_by(f.id, SiteOutcome::Refused(refused.clone()));
    let out = assert_ordinary(&m, &f, &s, ImportPolicy::Authenticated(&auth));
    assert_eq!(out.len(), 2);
    assert!(
        matches!(&out[0],ValidationError::InvalidFunctionSummary {detail,..} if detail=="requires clause 0 has an empty schema")
    );
    assert!(
        matches!(&out[1],ValidationError::UnauthenticatedImport {detail,site:"backed_by",..} if detail==&refused)
    );
}
