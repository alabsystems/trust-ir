// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn actual_signature_and_entry_success_match_the_original_module_diagnostic_projection() {
    let (m, f) = fixture();
    assert!(run(&m, &f).0.is_empty());
}
#[test]
fn short_and_long_entry_arity_keep_complete_expected_and_actual_lists() {
    let (m, base) = fixture();
    for short in [true, false] {
        let mut f = base.clone();
        if short {
            f.blocks[0].params.pop();
        } else {
            f.blocks[0].params.push((ValueId::new(9), Ty::U8));
        }
        let out = run(&m, &f).0;
        assert!(
            matches!(&out[..],[ValidationError::EntryParamsMismatch{expected,actual,..}] if expected=="(bool, u64)"&&actual.starts_with("(bool"))
        );
    }
}
#[test]
fn first_physical_entry_wins_even_when_duplicate_entry_ids_are_invalid_elsewhere() {
    let (m, mut f) = fixture();
    let mut duplicate = f.blocks[0].clone();
    duplicate.params.clear();
    f.blocks.push(duplicate);
    assert!(run(&m, &f).0.is_empty());
    f.blocks.swap(0, 1);
    assert_eq!(run(&m, &f).0.len(), 1);
}
#[test]
fn bodyless_unknown_signature_and_absent_entry_are_only_local_no_diagnostic_lanes() {
    let (m, base) = fixture();
    let mut f = base.clone();
    f.blocks.clear();
    assert!(run(&m, &f).0.is_empty());
    let mut f = base.clone();
    f.ty = FuncTyId::new(99);
    assert!(run(&m, &f).0.is_empty());
    let mut f = base;
    f.entry = BlockId::new(99);
    assert!(run(&m, &f).0.is_empty());
}
#[test]
fn top_level_refinement_defers_only_to_the_separate_consumption_rule() {
    let (mut m, mut f) = fixture();
    f.blocks[0].params[0].1 = Ty::Refine(TyId::new(0), PredId::new(0));
    assert!(run(&m, &f).0.is_empty());
    f.blocks[0].params[0].1 = Ty::Bool;
    m.func_types[0].params[0] = Ty::Refine(TyId::new(0), PredId::new(99));
    assert!(run(&m, &f).0.is_empty());
}
#[test]
fn nested_refinement_does_not_create_a_top_level_equality_exemption() {
    let (mut m, mut f) = fixture();
    m.func_types[0].params[0] = Ty::Tuple(vec![Ty::Bool]);
    f.blocks[0].params[0].1 = Ty::Tuple(vec![Ty::Refine(TyId::new(0), PredId::new(0))]);
    assert_eq!(run(&m, &f).0.len(), 1);
}
#[test]
fn first_non_refined_type_mismatch_and_complete_raw_function_name_are_preserved() {
    let (m, mut f) = mismatch();
    f.name = "λ raw\0尾\n".repeat(2000);
    let out = run(&m, &f).0;
    assert!(
        matches!(&out[..],[ValidationError::EntryParamsMismatch{func_name,actual,..}]if func_name==&f.name&&actual.contains("rt::Name"))
    );
}
#[test]
fn diagnostic_renders_full_type_tail_even_when_first_pair_already_mismatched() {
    let (mut m, mut f) = fixture();
    m.func_types[0].params = vec![Ty::Bool, Ty::Tuple(vec![Ty::Bool; 200])];
    f.blocks[0].params = vec![
        (ValueId::new(0), Ty::U8),
        (ValueId::new(1), Ty::Tuple(vec![Ty::U64; 200])),
    ];
    let out = run(&m, &f).0;
    assert!(
        matches!(&out[..],[ValidationError::EntryParamsMismatch{expected,actual,..}]if expected.matches("bool").count()==201&&actual.matches("u64").count()==200)
    );
}
