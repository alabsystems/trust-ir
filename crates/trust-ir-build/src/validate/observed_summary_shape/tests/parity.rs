// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn empty_summary_and_recorded_parameter_count_follow_the_original_arity_conditions() {
    let (m, f, mut summary) = fixture();
    assert!(execute(&m, &f, &summary).0.is_empty());
    summary.params = vec!["one".into()];
    assert_eq!(execute(&m, &f, &summary).0.len(), 1);
    summary.params.push("two".into());
    assert!(execute(&m, &f, &summary).0.is_empty());
    summary.params.push("three".into());
    assert_eq!(execute(&m, &f, &summary).0.len(), 1);
}
#[test]
fn all_three_clause_roles_trigger_parameter_arity_including_decreases_alone() {
    for role in 0..3 {
        let (m, f, mut summary) = fixture();
        let clause = trust_ir::proof::ProofFormula::new("opaque", "body");
        match role {
            0 => summary.requires.push(clause),
            1 => summary.ensures.push(clause),
            _ => summary.decreases.push(clause),
        };
        assert_eq!(execute(&m, &f, &summary).0.len(), 1);
    }
}
#[test]
fn missing_signature_skips_the_arity_comparison_but_reports_every_parameter_place() {
    let (mut m, f, mut summary) = fixture();
    m.func_types.clear();
    summary.params = vec!["mismatch".into()];
    summary.effects =
        Some(
            EffectSummary::pure().reading(EffectSet::Places(vec![EffectPlace::ParamPointee {
                index: u32::MAX,
            }])),
        );
    let out = execute(&m, &f, &summary).0;
    assert_eq!(out.len(), 1);
    assert!(
        matches!(&out[0],ValidationError::InvalidFunctionSummary {detail,..} if detail=="effects.reads names the pointee of parameter 4294967295, but functy.0 is not declared in this module")
    );
}
#[test]
fn both_sides_preserve_canonical_order_empty_duplicate_descending_and_place_resolution() {
    let (m, f, mut summary) = fixture();
    let sets = [
        EffectSet::Nothing,
        EffectSet::Everything,
        EffectSet::Places(Vec::new()),
        EffectSet::Places(vec![
            EffectPlace::ParamPointee { index: 0 },
            EffectPlace::ParamPointee { index: 1 },
            EffectPlace::Global(GlobalId::new(0)),
        ]),
        EffectSet::Places(vec![
            EffectPlace::Global(GlobalId::new(0)),
            EffectPlace::ParamPointee { index: 0 },
        ]),
        EffectSet::Places(vec![
            EffectPlace::ParamPointee { index: 2 },
            EffectPlace::ParamPointee { index: 2 },
        ]),
    ];
    for a in &sets {
        for b in &sets {
            summary.effects = Some(EffectSummary::pure().reading(a.clone()).writing(b.clone()));
            execute(&m, &f, &summary);
        }
    }
}
#[test]
fn maximal_ids_have_full_unsigned_diagnostics_and_global_lookups_use_actual_indices() {
    let (m, f, mut summary) = fixture();
    summary.effects = Some(
        EffectSummary::pure()
            .reading(EffectSet::Places(vec![
                EffectPlace::Global(GlobalId::new(0)),
                EffectPlace::Global(GlobalId::new(u32::MAX)),
            ]))
            .writing(EffectSet::Places(vec![EffectPlace::ParamPointee {
                index: u32::MAX,
            }])),
    );
    let out = execute(&m, &f, &summary).0;
    assert_eq!(out.len(), 2);
    assert!(
        matches!(&out[0],ValidationError::InvalidFunctionSummary {detail,..} if detail=="effects.reads names global #4294967295, which this module does not declare")
    );
    assert!(
        matches!(&out[1],ValidationError::InvalidFunctionSummary {detail,..} if detail.contains("4294967295") && detail.ends_with("2 parameter(s)"))
    );
}
#[test]
fn names_clause_payload_proved_and_effect_flags_remain_opaque_to_this_constituent() {
    let (m, mut f, mut summary) = fixture();
    f.name = "λ\n'".repeat(10000);
    summary.params = vec!["".into(), " \n".repeat(10000)];
    summary.proved = true;
    summary.requires.push(trust_ir::proof::ProofFormula::new(
        "",
        "unvalidated arbitrary payload",
    ));
    for effects in [
        None,
        Some(EffectSummary::pure()),
        Some(EffectSummary::top()),
    ] {
        summary.effects = effects;
        assert!(execute(&m, &f, &summary).0.is_empty());
    }
}
#[test]
fn original_diagnostic_order_is_arity_then_read_shape_and_places_then_write_shape_and_places() {
    let (m, f, summary) = mixed();
    let out = execute(&m, &f, &summary).0;
    assert_eq!(out.len(), 7);
    let text: Vec<_> = out
        .iter()
        .map(|e| match e {
            ValidationError::InvalidFunctionSummary { detail, .. } => detail.as_str(),
            _ => panic!("variant"),
        })
        .collect();
    assert!(text[0].starts_with("summary lists 1"));
    assert!(text[1].starts_with("effects.reads is not canonical:"));
    assert_eq!(text[2], text[3]);
    assert!(text[4].starts_with("effects.writes is not canonical:"));
    assert!(text[5].contains("global #5"));
    assert!(text[6].contains("global #1"));
}
