// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn empty_absent_formula_and_all_other_binding_places_stay_outside_this_constituent() {
    assert!(run(&Module::new("")).0.is_empty());
    let mut m = fixture();
    m.proof_obligations[0].formula = None;
    assert!(run(&m).0.is_empty());
    let places = [
        ClausePlace::Param { index: u32::MAX },
        ClausePlace::ResultSlot { index: u32::MAX },
        ClausePlace::MutParamExit { index: u32::MAX },
        ClausePlace::World,
        ClausePlace::WorldPre,
        ClausePlace::WorldPost,
        ClausePlace::Unwind,
        ClausePlace::Value(ValueId::new(u32::MAX)),
        ClausePlace::ParamPointeeEntry { index: u32::MAX },
    ];
    m.proof_obligations[0].spec = None;
    m.proof_obligations[0].formula = Some(formula(
        places
            .into_iter()
            .map(|p| ("opaque", p, nested()))
            .collect(),
    ));
    assert!(run(&m).0.is_empty());
}
#[test]
fn all_five_reference_refusals_keep_distinct_exact_reasons_then_unresolved_binding() {
    let reasons = [
        "only a Liveness or TemporalSafety obligation states a temporal property",
        "no SpecModule of this module carries that machine name",
        "the machine name is ambiguous in this module",
        "that machine declares no temporal property of that name",
        "that machine declares the temporal property more than once",
    ];
    for (case, reason) in reasons.into_iter().enumerate() {
        let mut m = fixture();
        match case {
            0 => m.proof_obligations[0].kind = ObligationKind::MemorySafety,
            1 => m.spec_modules.clear(),
            2 => m.spec_modules.push(m.spec_modules[0].clone()),
            3 => m.spec_modules[0].temporal.clear(),
            4 => {
                let t = m.spec_modules[0].temporal[0].clone();
                m.spec_modules[0].temporal.push(t);
            }
            _ => unreachable!(),
        }
        let errors = run(&m).0;
        assert_eq!(errors.len(), 2);
        assert_eq!(
            errors[0],
            ValidationError::UnresolvedObligationSpecRef {
                obligation: 3,
                machine: "M".into(),
                temporal: "T".into(),
                reason
            }
        );
        assert!(matches!(
            errors[1],
            ValidationError::InvalidObligationBinding { .. }
        ));
    }
}
#[test]
fn both_temporal_kinds_resolve_all_five_forms_without_inspecting_carried_formula_payloads() {
    for kind in [ObligationKind::Liveness, ObligationKind::TemporalSafety] {
        for form in forms() {
            let mut m = fixture();
            m.proof_obligations[0].kind = kind.clone();
            m.proof_obligations[0].formula = None;
            m.spec_modules[0].temporal[0].form = form;
            assert!(run(&m).0.is_empty());
        }
    }
}
#[test]
fn out_of_range_variable_stops_later_sort_spelling_and_primed_checks() {
    let mut m = fixture();
    m.proof_obligations[0].formula = Some(formula(vec![(
        "y",
        ClausePlace::SpecVarNext { index: u32::MAX },
        nested(),
    )]));
    let errors = run(&m).0;
    assert_eq!(errors.len(), 1);
    assert_eq!(
        errors[0],
        ValidationError::InvalidObligationBinding {
            obligation: 3,
            detail: format!(
                "binds \"y\" to SpecVarNext {}, but machine \"M\" declares 2 state variable(s)",
                u32::MAX
            )
        }
    );
}
#[test]
fn declared_seven_sort_variants_and_legacy_fallback_match_exact_original_mismatch_text() {
    for sort in [
        ClauseSort::Bool,
        ClauseSort::Int,
        ClauseSort::BitVec(0),
        ClauseSort::Float {
            eb: 0,
            sb: u32::MAX,
        },
        ClauseSort::RoundingMode,
        ClauseSort::Array(Box::new(ClauseSort::Int), Box::new(ClauseSort::Bool)),
        nested(),
    ] {
        let mut m = fixture();
        m.spec_modules[0].vars[0] = SpecVar::new("x", "unread").with_sort(sort.clone());
        let other = if sort == ClauseSort::Bool {
            ClauseSort::Int
        } else {
            ClauseSort::Bool
        };
        m.proof_obligations[0].formula = Some(formula(vec![(
            "x",
            ClausePlace::SpecVar { index: 0 },
            other,
        )]));
        assert_eq!(run(&m).0.len(), 1);
        m.proof_obligations[0].formula = Some(formula(vec![(
            "x",
            ClausePlace::SpecVar { index: 0 },
            sort,
        )]));
        assert!(run(&m).0.is_empty());
    }
    for tag in [
        "Bool",
        "Int",
        "BitVec(4294967295)",
        "-7..8",
        "opaque",
        "-0..0",
    ] {
        let mut m = fixture();
        m.spec_modules[0].vars[0] = SpecVar::new("x", tag);
        m.proof_obligations[0].formula = Some(formula(vec![(
            "x",
            ClausePlace::SpecVar { index: 0 },
            ClauseSort::RoundingMode,
        )]));
        run(&m);
    }
}
#[test]
fn spelled_variable_uses_first_physical_name_even_when_later_duplicates_match_the_index() {
    let mut m = fixture();
    m.spec_modules[0].vars = vec![SpecVar::new("dup", "Int"), SpecVar::new("dup", "Int")];
    m.proof_obligations[0].formula = Some(formula(vec![(
        "dup",
        ClausePlace::SpecVar { index: 1 },
        ClauseSort::Int,
    )]));
    assert_eq!(run(&m).0.len(), 1);
    m.proof_obligations[0].formula = Some(formula(vec![(
        "dup",
        ClausePlace::SpecVar { index: 0 },
        ClauseSort::Int,
    )]));
    assert!(run(&m).0.is_empty());
}
#[test]
fn mismatch_then_spelling_then_primed_diagnostics_follow_physical_binding_order() {
    let mut m = fixture();
    let p = m.proof_obligations[0].formula.as_ref().unwrap().bindings[0].clone();
    m.proof_obligations[0]
        .formula
        .as_mut()
        .unwrap()
        .bindings
        .push(p);
    let errors = run(&m).0;
    assert_eq!(errors.len(), 6);
    assert_eq!(&errors[..3], &errors[3..]);
    let details = errors[..3]
        .iter()
        .map(|e| match e {
            ValidationError::InvalidObligationBinding { detail, .. } => detail.as_str(),
            _ => panic!("wrong variant"),
        })
        .collect::<Vec<_>>();
    assert!(details[0].contains("declares sort Int"));
    assert!(details[1].contains("state variable 1"));
    assert!(details[2].contains("SUCCESSOR state"));
}
#[test]
fn primed_places_are_legal_only_for_the_two_fairness_tags_even_without_relation_payloads() {
    for (index, form) in forms().into_iter().enumerate() {
        let mut m = fixture();
        m.spec_modules[0].temporal[0].form = form;
        m.proof_obligations[0].formula = Some(formula(vec![(
            "x",
            ClausePlace::SpecVarNext { index: 0 },
            ClauseSort::Int,
        )]));
        assert_eq!(run(&m).0.len(), usize::from(index < 3));
    }
}
#[test]
fn complete_raw_names_unicode_debug_escaping_and_recursive_sort_text_are_preserved() {
    let mut m = fixture();
    m.spec_modules[0].name = "Mλ\n\"'\\\0".repeat(400);
    m.spec_modules[0].temporal[0].name = "T尾\t".repeat(400);
    m.proof_obligations[0].spec = Some(SpecObligationRef::new(
        &m.spec_modules[0].name,
        &m.spec_modules[0].temporal[0].name,
    ));
    m.spec_modules[0].vars[0].name = "x\nλ\"'\\".repeat(400);
    m.spec_modules[0].vars[0].sort = Some(nested());
    let errors = run(&m).0;
    assert_eq!(errors.len(), 3);
    let mut unresolved = m.clone();
    unresolved.spec_modules.clear();
    let errors = run(&unresolved).0;
    assert!(
        matches!(&errors[0],ValidationError::UnresolvedObligationSpecRef {machine,temporal,..}
        if machine==&m.spec_modules[0].name && temporal==&m.spec_modules[0].temporal[0].name)
    );
}
#[test]
fn unused_descriptions_formula_text_and_unrelated_spec_metadata_do_not_enter_the_walk() {
    let m = fixture();
    let (_, a, cut_a) = run(&m);
    let mut huge = m.clone();
    huge.proof_obligations[0].description = "unused".repeat(100_000);
    huge.proof_obligations[0].formula.as_mut().unwrap().payload = "unused".repeat(100_000);
    huge.spec_modules[0].actions.push("unused".repeat(100_000));
    huge.spec_modules[0].temporal[0].form = TemporalForm::Always(ProofFormula::new(
        "unused".repeat(100_000),
        "unused".repeat(100_000),
    ));
    let (_, b, cut_b) = run(&huge);
    assert_eq!(cut_a, cut_b);
    assert_eq!(a.events, b.events);
}
