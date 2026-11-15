// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn empty_and_valid_summaries_match_the_complete_original_function() {
    let (m, f, mut s) = fixture();
    assert!(run(&m, &f, &s, ImportPolicy::Structural).0.is_empty());
    s.params.push("x".into());
    let mut c = ProofFormula::new("opaque", "text");
    c.bindings.push((
        "x".into(),
        ClauseBinding {
            sort: ClauseSort::Bool,
            place: ClausePlace::Param { index: 0 },
        },
    ));
    s.requires.push(c);
    assert!(run(&m, &f, &s, ImportPolicy::Structural).0.is_empty());
}
#[test]
fn all_four_nonempty_stages_keep_the_complete_original_error_order() {
    let (m, f, s) = mixed();
    let out = run(&m, &f, &s, ImportPolicy::Structural).0;
    assert_eq!(out.len(), 6);
    assert!(
        matches!(&out[0],ValidationError::InvalidFunctionSummary {detail,..} if detail=="requires clause 0 has an empty schema")
    );
    assert!(
        matches!(&out[1],ValidationError::InvalidFunctionSummary {detail,..} if detail=="requires clause 1 has an empty schema")
    );
    assert!(
        matches!(&out[2],ValidationError::InvalidFunctionSummary {detail,..} if detail.starts_with("summary lists 0"))
    );
    assert!(matches!(&out[3], ValidationError::DanglingExternRef { .. }));
    assert!(
        matches!(&out[4],ValidationError::InvalidFunctionSummary {detail,..} if detail=="requires clause 1 duplicates clause 0")
    );
    assert!(
        matches!(&out[5],ValidationError::InvalidFunctionSummary {detail,..} if detail.starts_with("requires clause 0 `"))
    );
}
#[test]
fn every_role_keeps_binding_resolution_shape_and_missing_backing_diagnostics() {
    for role in 0..3 {
        let (m, f, mut s) = fixture();
        s.proved = true;
        let mut c = ProofFormula::new("opaque", "text");
        c.bindings.push((
            "x".into(),
            ClauseBinding {
                sort: ClauseSort::Bool,
                place: ClausePlace::Param { index: u32::MAX },
            },
        ));
        match role {
            0 => s.requires.push(c),
            1 => s.ensures.push(c),
            _ => s.decreases.push(c),
        };
        assert_eq!(run(&m, &f, &s, ImportPolicy::Refuse).0.len(), 3);
    }
}
#[test]
fn ssa_type_refusal_is_preserved_before_shape_and_exact_local_clause_matching() {
    let (mut m, mut f, mut s) = fixture();
    f.blocks[0].params.push((ValueId::new(7), Ty::U32));
    m.functions[0] = f.clone();
    let mut c = ProofFormula::new("opaque", "text");
    c.bindings.push((
        "ssa".into(),
        ClauseBinding {
            sort: ClauseSort::Bool,
            place: ClausePlace::Value(ValueId::new(7)),
        },
    ));
    s.requires.push(c);
    assert_eq!(run(&m, &f, &s, ImportPolicy::Structural).0.len(), 2);
}
#[test]
fn declaration_citation_keeps_structural_refusal_and_missing_authenticated_policy_distinct() {
    let (mut m, mut f, mut s) = fixture();
    f.blocks.clear();
    m.functions[0] = f.clone();
    m.imports.push(ModuleImport::new(
        "dep",
        trust_ir::proof::ProofDigest::sha256([4; 32]),
    ));
    s.requires.push(ProofFormula::new("opaque", "text"));
    s.params.push("x".into());
    s.proved = true;
    assert_eq!(run(&m, &f, &s, ImportPolicy::Structural).0.len(), 1);
    s.backed_by = Some(ExternRef::new(ImportId::new(0), "f").relying_on(ProofId::new(1)));
    assert!(run(&m, &f, &s, ImportPolicy::Structural).0.is_empty());
    assert_eq!(run(&m, &f, &s, ImportPolicy::Refuse).0.len(), 1);
    let auth = crate::linked::AuthenticatedImports::default();
    assert_eq!(
        run(&m, &f, &s, ImportPolicy::Authenticated(&auth)).0.len(),
        1
    );
}
#[test]
fn a_cited_definition_still_needs_local_rows_and_failed_rows_still_refute() {
    let (mut m, f, mut s) = fixture();
    m.imports.push(ModuleImport::new(
        "dep",
        trust_ir::proof::ProofDigest::sha256([4; 32]),
    ));
    s.requires.push(ProofFormula::new("opaque", "text"));
    s.params.push("x".into());
    s.proved = true;
    s.backed_by = Some(ExternRef::new(ImportId::new(0), "f").relying_on(ProofId::new(1)));
    m.proof_obligations.push(row(
        9,
        ObligationKind::Precondition,
        ProofStatus::Failed,
        None,
    ));
    assert_eq!(run(&m, &f, &s, ImportPolicy::Structural).0.len(), 2);
    assert_eq!(run(&m, &f, &s, ImportPolicy::Refuse).0.len(), 3);
}
#[test]
fn exact_scoped_role_rows_and_duplicate_clauses_preserve_raw_formula_identity() {
    let (mut m, f, mut s) = fixture();
    let c = ProofFormula::new("opaque", "text");
    s.params.push("x".into());
    s.proved = true;
    s.requires = vec![c.clone(), c.clone()];
    s.ensures = vec![c.clone()];
    m.proof_obligations.push(row(
        1,
        ObligationKind::Precondition,
        ProofStatus::Certified,
        Some(c.clone()),
    ));
    m.proof_obligations.push(row(
        2,
        ObligationKind::Postcondition,
        ProofStatus::Discharged,
        Some(c),
    ));
    let out = run(&m, &f, &s, ImportPolicy::Structural).0;
    assert_eq!(out.len(), 1);
    assert!(
        matches!(&out[0],ValidationError::InvalidFunctionSummary {detail,..} if detail=="requires clause 1 duplicates clause 0")
    );
}
#[test]
fn unproved_opaque_payloads_remain_unread_through_the_whole_summary() {
    let (m, f, mut s) = fixture();
    s.params.push("x".into());
    s.requires.push(ProofFormula::new("opaque", "text"));
    let (_, before) = run(&m, &f, &s, ImportPolicy::Structural);
    s.requires[0].payload = "unused".repeat(100000);
    s.requires[0].smtlib = Some("unused".repeat(100000));
    let (_, after) = run(&m, &f, &s, ImportPolicy::Structural);
    assert_eq!(before.events, after.events);
}
#[test]
fn body_effects_and_other_module_rules_are_not_mistaken_for_summary_checks() {
    let (m, mut f, mut s) = fixture();
    s.effects = Some(trust_ir::EffectSummary::pure());
    f.blocks[0].params.push((ValueId::new(77), Ty::Error));
    f.blocks[0]
        .body
        .push(trust_ir::InstrNode::new(Inst::HeapAlloc {
            ty: Ty::U8,
            count: None,
            align: None,
            origin: trust_ir::inst::AllocOrigin::RustHeap,
        }));
    f.ty = FuncTyId::new(u32::MAX);
    f.summary = Some(s.clone());
    assert!(run(&m, &f, &s, ImportPolicy::Structural).0.is_empty());
    assert_eq!(
        super::super::super::effects::validate_effect_summary(&m, &f, ImportPolicy::Structural)
            .len(),
        1
    );
}
#[test]
fn original_instruction_site_and_zero_fuel_survive_all_four_stages() {
    let (m, f, s) = mixed();
    let exact = ExecutionSite::Instruction(InstructionSite {
        function: FuncId::new(2),
        block: BlockId::new(3),
        instruction_index: usize::MAX,
    });
    let mut o = Observer::default();
    let mut owner = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    assert_eq!(
        validate_function_summary_observed(&m, &f, &s, ImportPolicy::Structural, &mut owner, exact)
            .unwrap(),
        super::super::super::validate_function_summary(&m, &f, &s, ImportPolicy::Structural)
    );
    assert_eq!(owner.remaining_fuel(), 0);
    assert!(o.events.iter().all(|e| e.site == exact));
}
