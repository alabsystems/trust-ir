// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn complete_inventory_keeps_exact_original_order_and_both_leads_to_leaves() {
    let m = fixture();
    let (out, _, _) = run(&m);
    let sites: Vec<_> = out
        .into_iter()
        .map(|e| match e {
            ValidationError::FormulaTextsDisagree { site } => site,
            _ => panic!("wrong diagnostic"),
        })
        .collect();
    assert_eq!(
        sites,
        vec![
            FormulaSite::Obligation(ProofId::new(3)),
            FormulaSite::SummaryClause {
                function: FuncId::new(7),
                clause: "requires",
                index: 1
            },
            FormulaSite::SummaryClause {
                function: FuncId::new(7),
                clause: "ensures",
                index: 0
            },
            FormulaSite::SummaryClause {
                function: FuncId::new(7),
                clause: "decreases",
                index: 0
            },
            FormulaSite::SpecInvariant {
                machine: "M".into(),
                invariant: "I".into()
            },
            FormulaSite::SpecTemporal {
                machine: "M".into(),
                property: "A".into()
            },
            FormulaSite::SpecTemporal {
                machine: "M".into(),
                property: "L".into()
            },
            FormulaSite::SpecTemporal {
                machine: "M".into(),
                property: "L".into()
            },
            FormulaSite::SpecTemporal {
                machine: "M".into(),
                property: "W".into()
            }
        ]
    );
}
#[test]
fn empty_and_absent_carriers_produce_no_disagreement_or_label_copy() {
    let mut m = Module::new("");
    assert!(run(&m).0.is_empty());
    m.proof_obligations.push(obligation(7, None));
    m.functions.push(Function::new(
        FuncId::new(1),
        "unread",
        FuncTyId::new(0),
        BlockId::new(0),
    ));
    let mut spec = SpecModule::new("huge λ\0".repeat(10000));
    spec.invariants
        .push(SpecInvariant::new("ignored 尾".repeat(10000), "ignored"));
    spec.temporal.push(SpecTemporal::new(
        "ignored".repeat(10000),
        TemporalForm::StrongFair {
            action: "ignored".into(),
            relation: None,
        },
    ));
    m.spec_modules.push(spec);
    let (_, large, _) = run(&m);
    m.spec_modules[0].name = "M".into();
    m.spec_modules[0].invariants[0].name = "I".into();
    m.spec_modules[0].temporal[0].name = "T".into();
    let (_, short, _) = run(&m);
    assert_eq!(large.events, short.events);
}
#[test]
fn raw_unicode_nul_labels_are_owned_whole_without_normalization() {
    let mut m = Module::new("");
    let name = " raw λ\0尾\n".repeat(1000);
    let label = " invariant \0尾 λ ".repeat(900);
    let mut spec = SpecModule::new(&name);
    spec.invariants
        .push(SpecInvariant::new(&label, "ignored").with_typed(bad()));
    m.spec_modules.push(spec);
    assert_eq!(
        run(&m).0,
        vec![ValidationError::FormulaTextsDisagree {
            site: FormulaSite::SpecInvariant {
                machine: name,
                invariant: label
            }
        }]
    );
}
#[test]
fn summary_clauses_keep_physical_functions_and_original_clause_indices() {
    let mut m = Module::new("");
    m.functions = vec![
        function(9, vec![good(), bad(), good(), bad()], vec![], vec![bad()]),
        function(9, vec![bad()], vec![bad(), good(), bad()], vec![]),
    ];
    let out = run(&m).0;
    assert_eq!(out.len(), 6);
    assert!(
        matches!(&out[3],ValidationError::FormulaTextsDisagree{site:FormulaSite::SummaryClause{function,clause:"requires",index:0}} if *function==FuncId::new(9))
    );
}
#[test]
fn repeated_spec_and_property_labels_keep_all_physical_errors() {
    let mut m = fixture();
    let spec = m.spec_modules[0].clone();
    m.spec_modules.push(spec);
    let out = run(&m).0;
    assert_eq!(out.len(), 14);
    assert_eq!(&out[4..9], &out[9..14]);
}
#[test]
fn every_temporal_form_and_recorded_or_absent_fairness_relation_is_exact() {
    let mut m = Module::new("");
    let mut spec = SpecModule::new("M");
    for form in [
        TemporalForm::Always(bad()),
        TemporalForm::Eventually(bad()),
        TemporalForm::LeadsTo(good(), bad()),
        TemporalForm::LeadsTo(bad(), good()),
        TemporalForm::WeakFair {
            action: "W".into(),
            relation: Some(bad()),
        },
        TemporalForm::StrongFair {
            action: "S".into(),
            relation: Some(bad()),
        },
        TemporalForm::WeakFair {
            action: "W".into(),
            relation: None,
        },
        TemporalForm::StrongFair {
            action: "S".into(),
            relation: None,
        },
    ] {
        spec.temporal.push(SpecTemporal::new("T", form));
    }
    m.spec_modules.push(spec);
    assert_eq!(run(&m).0.len(), 6);
}
#[test]
fn actual_predicate_schema_child_matches_then_detects_rendering_tampering() {
    let mut m = Module::new("");
    m.predicates = vec![trust_ir::pred::Pred::FiniteSet(vec![
        trust_ir::Constant::SymbolAddr {
            symbol: "raw λ\0尾".repeat(1200),
            addend: -9,
        },
    ])];
    let text = m
        .pred_table()
        .smtlib_of(trust_ir::value::PredId::new(0))
        .unwrap();
    let mut f = ProofFormula::new(trust_ir::pred::PRED_FORMULA_SCHEMA, "pred.0");
    f.smtlib = Some(text);
    m.proof_obligations.push(obligation(7, Some(f)));
    assert!(run(&m).0.is_empty());
    m.proof_obligations[0]
        .formula
        .as_mut()
        .unwrap()
        .smtlib
        .as_mut()
        .unwrap()
        .push(' ');
    assert_eq!(run(&m).0.len(), 1);
}
#[test]
fn opaque_absent_and_claim_formulas_keep_the_original_group_outcome() {
    let mut m = Module::new("");
    let mut opaque = ProofFormula::new("opaque", "false");
    opaque.smtlib = Some("true".into());
    let absent = ProofFormula::new("smtlib2", "false");
    let mut claim = ProofFormula::new(
        trust_ir::proof::OwnedFormulaSchema::LineageTransformBinding.name(),
        "unread",
    );
    claim.smtlib = Some("true".into());
    m.proof_obligations = vec![
        obligation(1, Some(opaque)),
        obligation(2, Some(absent)),
        obligation(3, Some(claim)),
    ];
    assert_eq!(
        run(&m).0,
        vec![ValidationError::FormulaTextsDisagree {
            site: FormulaSite::Obligation(ProofId::new(3))
        }]
    );
}
