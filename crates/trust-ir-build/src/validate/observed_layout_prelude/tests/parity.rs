// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn actual_valid_reordered_tuple_and_closure_tables_have_original_clean_diagnostics() {
    assert!(run(&valid()).0.is_empty());
}
#[test]
fn both_semantic_failures_remain_ordered_and_closure_reason_has_the_exact_prefix() {
    assert_eq!(run(&invalid()).0,vec![ValidationError::TupleLayoutInconsistent{reason:"type table entry ty.7 is missing".into()},ValidationError::TupleLayoutInconsistent{reason:"Module.closure_layouts: closure layout closure.9 has incoherent or ambiguous declared metadata".into()}]);
}
#[test]
fn first_bad_tuple_and_independent_closure_check_preserve_original_duplicate_and_missing_target_answers()
 {
    let original = valid();
    for case in 0..4 {
        let mut m = original.clone();
        match case {
            0 => m.target_info = None,
            1 => m.tuple_layouts[0].field_offsets.clear(),
            2 => m.tuple_layouts.push(m.tuple_layouts[0].clone()),
            3 => m.closure_layouts.push(m.closure_layouts[0].clone()),
            _ => unreachable!(),
        }
        assert!(!run(&m).0.is_empty());
    }
}
#[test]
fn actual_owned_off_scalar_target_error_uses_exact_full_unicode_debug_spelling() {
    let mut m = valid();
    m.target_info.as_mut().unwrap().triple = "custom-'λ\n\0".repeat(5);
    let (out, _) = run(&m);
    assert_eq!(out.len(), 2);
    let target = &m.target_info.as_ref().unwrap().triple;
    let reason = format!("target {target:?} is outside TrustIR's canonical scalar-layout set");
    assert_eq!(
        out[0],
        ValidationError::TupleLayoutInconsistent {
            reason: reason.clone()
        }
    );
    assert_eq!(
        out[1],
        ValidationError::TupleLayoutInconsistent {
            reason: format!("{CLOSURE_LAYOUT_TABLE_REASON_PREFIX}{reason}")
        }
    );
}
#[test]
fn private_fresh_table_ordinary_memo_stays_empty_across_actual_observed_success_and_error_queries()
{
    for m in [valid(), invalid()] {
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State::default();
        state.run(&m, &mut work).unwrap();
        let stats = state.table.as_ref().unwrap().stats();
        assert_eq!(stats.nodes, 0);
        assert_eq!(stats.definitions_indexed, 0);
        assert_eq!(stats.tuple_rows_indexed, 0);
        assert_eq!(stats.closure_rows_indexed, 0);
        assert_eq!(stats.inhabitedness_nodes, 0);
        assert_eq!(stats.reach_nodes, 0);
        drain(&mut state, &mut work);
        assert!(empty(&state));
    }
}
#[test]
fn absent_layout_tables_do_not_walk_unrelated_large_type_or_function_payloads() {
    let mut m = Module::new("unrelated");
    m.types.push(Ty::Tuple(vec![Ty::Error; 10_000]));
    assert!(run(&m).0.is_empty());
}
