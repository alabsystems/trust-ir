// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn unproved_skips_even_duplicate_clauses_and_failed_rows() {
    let (m, f, mut summary) = mixed();
    summary.proved = false;
    assert!(
        execute(&m, &f, &summary, SummaryCitation::Absent)
            .0
            .is_empty()
    );
}
#[test]
fn empty_proved_summary_has_no_invented_missing_clause_error() {
    let (m, mut f, summary) = fixture();
    for body in [true, false] {
        if !body {
            f.blocks.clear();
        }
        for citation in [SummaryCitation::Absent, SummaryCitation::ProofBearing] {
            assert!(execute(&m, &f, &summary, citation).0.is_empty());
        }
    }
}
#[test]
fn three_roles_emit_the_exact_missing_row_diagnostics_in_role_order() {
    let (m, f, mut summary) = fixture();
    summary.requires = vec![formula("r")];
    summary.ensures = vec![formula("e")];
    summary.decreases = vec![formula("d")];
    let out = execute(&m, &f, &summary, SummaryCitation::Absent).0;
    assert_eq!(out.len(), 3);
    for (detail, (name, kind, text)) in details(&out).iter().zip([
        ("requires", "Precondition", "r"),
        ("ensures", "Postcondition", "e"),
        ("decreases", "Termination", "d"),
    ]) {
        assert_eq!(
            *detail,
            format!(
                "{name} clause 0 `[opaque-schema] {text}` has no Discharged/Certified {kind} row scoped to this function stating exactly this clause (rows stating other clauses do not count)"
            )
        );
    }
}
#[test]
fn duplicates_are_per_role_and_name_the_first_earlier_physical_index() {
    let (m, f, mut summary) = fixture();
    summary.requires = vec![formula("x"), formula("y"), formula("x"), formula("x")];
    summary.ensures = vec![formula("x"), formula("x")];
    let out = execute(&m, &f, &summary, SummaryCitation::Absent).0;
    let text = details(&out);
    assert_eq!(
        &text[..3],
        [
            "requires clause 2 duplicates clause 0",
            "requires clause 3 duplicates clause 0",
            "ensures clause 1 duplicates clause 0"
        ]
    );
    assert_eq!(out.len(), 6); // Three unique per-role clauses still need rows.
}
#[test]
fn all_five_statuses_and_formula_presence_match_the_original_discharged_tier() {
    for status in [
        ProofStatus::Pending,
        ProofStatus::Discharged,
        ProofStatus::Failed,
        ProofStatus::Trusted,
        ProofStatus::Certified,
    ] {
        for present in [false, true] {
            let (mut m, f, mut summary) = fixture();
            summary.requires = vec![formula("r")];
            m.proof_obligations.push(row(
                5,
                ObligationKind::Precondition,
                status,
                present.then(|| formula("r")),
                Some(f.id),
            ));
            let out = execute(&m, &f, &summary, SummaryCitation::Absent).0;
            assert_eq!(
                out.len(),
                usize::from(!(present && status.is_discharged_tier()))
                    + usize::from(status == ProofStatus::Failed)
            );
        }
    }
}
#[test]
fn wrong_scope_and_every_noncontract_kind_neither_back_nor_refute() {
    let (mut m, f, mut summary) = fixture();
    summary.requires = vec![formula("r")];
    let kinds = [
        ObligationKind::LoopInvariant,
        ObligationKind::TypeInvariant,
        ObligationKind::RefinementType,
        ObligationKind::TranslationValidation,
        ObligationKind::MemorySafety,
        ObligationKind::PanicFreedom,
        ObligationKind::TemporalSafety,
        ObligationKind::Liveness,
        ObligationKind::ArithmeticSafety,
        ObligationKind::BoundsCheck,
        ObligationKind::GiveBackRefinement,
        ObligationKind::Ownership,
        ObligationKind::Custom {
            namespace: "λ".repeat(3000),
            name: "other".into(),
        },
    ];
    for kind in kinds {
        for status in [ProofStatus::Certified, ProofStatus::Failed] {
            m.proof_obligations
                .push(row(3, kind.clone(), status, Some(formula("r")), Some(f.id)));
        }
    }
    for owner in [None, Some(FuncId::new(999))] {
        for status in [ProofStatus::Certified, ProofStatus::Failed] {
            m.proof_obligations.push(row(
                3,
                ObligationKind::Precondition,
                status,
                Some(formula("r")),
                owner,
            ));
        }
    }
    assert_eq!(
        execute(&m, &f, &summary, SummaryCitation::Absent).0.len(),
        1
    );
}
#[test]
fn role_matching_never_substitutes_another_contract_kind() {
    let (mut m, f, mut summary) = fixture();
    let same = formula("shared");
    summary.requires = vec![same.clone()];
    summary.ensures = vec![same.clone()];
    summary.decreases = vec![same.clone()];
    m.proof_obligations.push(row(
        0,
        ObligationKind::Postcondition,
        ProofStatus::Certified,
        Some(same),
        Some(f.id),
    ));
    let out = execute(&m, &f, &summary, SummaryCitation::Absent).0;
    assert_eq!(out.len(), 2);
    assert!(details(&out)[0].starts_with("requires"));
    assert!(details(&out)[1].starts_with("decreases"));
}
#[test]
fn failed_ids_keep_physical_order_and_duplicates_before_missing_row_errors() {
    let (mut m, f, mut summary) = fixture();
    summary.requires = vec![formula("r")];
    for id in [u32::MAX, 0, u32::MAX] {
        m.proof_obligations.push(row(
            id,
            ObligationKind::Precondition,
            ProofStatus::Failed,
            Some(formula("different")),
            Some(f.id),
        ));
    }
    let out = execute(&m, &f, &summary, SummaryCitation::Absent).0;
    assert_eq!(out.len(), 4);
    for (detail, id) in details(&out)[..3].iter().zip([u32::MAX, 0, u32::MAX]) {
        assert_eq!(
            *detail,
            format!(
                "summary claims `proved` while contract obligation #{id}, scoped to this function, is Failed"
            )
        );
    }
    assert!(details(&out)[3].starts_with("requires clause 0"));
}
#[test]
fn absent_citation_declarations_get_one_aggregate_per_nonempty_role_after_duplicates() {
    let (mut m, mut f, mut summary) = fixture();
    f.blocks.clear();
    summary.requires = vec![formula("r"), formula("r")];
    summary.ensures = vec![formula("e")];
    summary.decreases = vec![formula("d")];
    m.proof_obligations.push(row(
        7,
        ObligationKind::Precondition,
        ProofStatus::Certified,
        Some(formula("r")),
        Some(f.id),
    ));
    let out = execute(&m, &f, &summary, SummaryCitation::Absent).0;
    assert_eq!(out.len(), 4);
    assert_eq!(details(&out)[0], "requires clause 1 duplicates clause 0");
    for (text, prefix) in details(&out)[1..].iter().zip([
        "summary claims `proved` with 2 requires clause(s)",
        "summary claims `proved` with 1 ensures clause(s)",
        "summary claims `proved` with 1 decreases clause(s)",
    ]) {
        assert!(text.starts_with(prefix));
    }
}
#[test]
fn cited_declarations_still_report_duplicates_and_failed_rows_but_no_local_absence() {
    let (m, mut f, summary) = mixed();
    f.blocks.clear();
    let out = execute(&m, &f, &summary, SummaryCitation::ProofBearing).0;
    assert_eq!(out.len(), 2);
    assert_eq!(details(&out)[0], "requires clause 1 duplicates clause 0");
    assert!(details(&out)[1].contains("#91, scoped to this function, is Failed"));
}
#[test]
fn a_definition_cannot_use_the_citation_marker_to_skip_local_backing() {
    let (m, f, summary) = mixed();
    assert_eq!(
        execute(&m, &f, &summary, SummaryCitation::Absent).0,
        execute(&m, &f, &summary, SummaryCitation::ProofBearing).0
    );
}
#[test]
fn all_raw_formula_fields_and_ordered_bindings_participate_in_matching() {
    let (mut m, f, mut summary) = fixture();
    let mut clause = formula("payload");
    clause.smtlib = Some("rendering".into());
    clause.sort = Some("sort".into());
    clause.bindings = vec![
        (
            "a".into(),
            ClauseBinding {
                sort: ClauseSort::BitVec(8),
                place: ClausePlace::Param { index: 0 },
            },
        ),
        (
            "b".into(),
            ClauseBinding {
                sort: ClauseSort::Array(Box::new(ClauseSort::Int), Box::new(ClauseSort::Bool)),
                place: ClausePlace::ResultSlot { index: 0 },
            },
        ),
    ];
    summary.requires = vec![clause.clone()];
    for axis in 0..9 {
        let mut candidate = clause.clone();
        match axis {
            0 => {}
            1 => candidate.schema.push('!'),
            2 => candidate.payload.push('!'),
            3 => candidate.smtlib = None,
            4 => candidate.sort = Some(String::new()),
            5 => candidate.bindings[0].0.push('!'),
            6 => candidate.bindings[0].1.sort = ClauseSort::BitVec(9),
            7 => candidate.bindings[0].1.place = ClausePlace::Param { index: 1 },
            8 => candidate.bindings.swap(0, 1),
            _ => unreachable!(),
        }
        m.proof_obligations = vec![row(
            2,
            ObligationKind::Precondition,
            ProofStatus::Certified,
            Some(candidate),
            Some(f.id),
        )];
        assert_eq!(
            execute(&m, &f, &summary, SummaryCitation::Absent).0.len(),
            usize::from(axis != 0)
        );
    }
}
#[test]
fn none_and_some_empty_optional_strings_are_not_duplicate_or_backing_wildcards() {
    let (mut m, f, mut summary) = fixture();
    let plain = formula("");
    let mut empty = plain.clone();
    empty.smtlib = Some(String::new());
    summary.requires = vec![plain.clone(), empty.clone()];
    m.proof_obligations.push(row(
        2,
        ObligationKind::Precondition,
        ProofStatus::Discharged,
        Some(plain),
        Some(f.id),
    ));
    let out = execute(&m, &f, &summary, SummaryCitation::Absent).0;
    assert_eq!(out.len(), 1);
    assert!(details(&out)[0].starts_with("requires clause 1 ``"));
    empty.smtlib = None;
    empty.sort = Some(String::new());
    summary.requires[1] = empty;
    assert_eq!(
        execute(&m, &f, &summary, SummaryCitation::Absent).0.len(),
        1
    );
}
#[test]
fn clause_text_preserves_raw_unicode_nuls_backticks_and_smtlib_precedence() {
    let (m, f, mut summary) = fixture();
    let mut a = ProofFormula::new("schema\0λ", "payload`\n文");
    let mut b = a.clone();
    b.smtlib = Some("actual`\0\n文".into());
    a.sort = Some("ignored display".into());
    summary.requires = vec![a, b];
    let out = execute(&m, &f, &summary, SummaryCitation::Absent).0;
    assert_eq!(out.len(), 2);
    assert!(details(&out)[0].contains("`[schema\0λ] payload`\n文`"));
    assert!(details(&out)[1].contains("`actual`\0\n文`"));
}
#[test]
fn late_exact_row_and_duplicate_exact_rows_back_one_unique_clause() {
    let (mut m, f, mut summary) = fixture();
    summary.requires = vec![formula("target"), formula("target")];
    for n in 0..80 {
        m.proof_obligations.push(row(
            n,
            ObligationKind::Precondition,
            ProofStatus::Discharged,
            Some(formula("other!")),
            Some(f.id),
        ));
    }
    for _ in 0..2 {
        m.proof_obligations.push(row(
            1,
            ObligationKind::Precondition,
            ProofStatus::Certified,
            Some(formula("target")),
            Some(f.id),
        ));
    }
    let out = execute(&m, &f, &summary, SummaryCitation::Absent).0;
    assert_eq!(details(&out), ["requires clause 1 duplicates clause 0"]);
}
#[test]
fn each_role_has_its_own_exact_rows_and_duplicates_even_with_one_shared_formula() {
    let (mut m, f, mut summary) = fixture();
    let shared = formula("same across roles");
    summary.requires = vec![shared.clone(), shared.clone()];
    summary.ensures = vec![shared.clone(), shared.clone()];
    summary.decreases = vec![shared.clone(), shared.clone()];
    for (id, kind, status) in [
        (1, ObligationKind::Precondition, ProofStatus::Discharged),
        (2, ObligationKind::Postcondition, ProofStatus::Certified),
        (3, ObligationKind::Termination, ProofStatus::Discharged),
    ] {
        m.proof_obligations
            .push(row(id, kind, status, Some(shared.clone()), Some(f.id)));
    }
    let out = execute(&m, &f, &summary, SummaryCitation::Absent).0;
    assert_eq!(
        details(&out),
        [
            "requires clause 1 duplicates clause 0",
            "ensures clause 1 duplicates clause 0",
            "decreases clause 1 duplicates clause 0"
        ]
    );
}
