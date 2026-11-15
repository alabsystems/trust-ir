// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn complete_cast_and_value_fact_rules_each_match_entire_actual_ordinary_order() {
    let m = fixture();
    assert_eq!(run(&m, Rule::Casts).0.len(), 3);
    let out = run(&m, Rule::Facts).0;
    assert_eq!(out.len(), 4);
    assert!(matches!(
        out[0],
        ValidationError::ValueRangeInverted {
            lo: i128::MAX,
            hi: i128::MIN,
            ..
        }
    ));
    assert!(matches!(
        out[1],
        ValidationError::KnownBitsContradiction { overlap: 1, .. }
    ));
    assert!(matches!(
        out[2],
        ValidationError::KnownBitsContradiction { overlap: 1, .. }
    ));
    assert!(matches!(
        out[3],
        ValidationError::ValueRangeInverted { lo: 2, hi: 1, .. }
    ));
}
#[test]
fn all_layout_sensitive_opcode_success_families_preserve_actual_evidence() {
    let mut m = fixture();
    m.functions[0].blocks[0].body = vec![
        cast(CastOp::PtrToPtr, Ty::Ptr, Ty::Ptr),
        cast(CastOp::Bitcast, Ty::U32, Ty::I32),
        cast(CastOp::Transmute, Ty::U32, Ty::F32),
        cast(CastOp::ReifyFnPointer, Ty::Func(FuncTyId::new(0)), Ty::Ptr),
    ];
    assert!(run(&m, Rule::Casts).0.is_empty());
}
#[test]
fn nonlayout_casts_keep_the_same_module_tail_skip_without_skipping_other_rows() {
    let mut m = fixture();
    m.functions[0].blocks[0].body = vec![
        cast(CastOp::Trunc, Ty::Bool, Ty::Error),
        cast(CastOp::PtrToInt, Ty::handle("H", "rt::H"), Ty::Error),
        cast(CastOp::Transmute, Ty::U8, Ty::U64),
    ];
    assert_eq!(run(&m, Rule::Casts).0.len(), 1);
}
#[test]
fn handle_closure_bool_and_pointer_metadata_refusals_keep_full_original_reasons() {
    let mut m = fixture();
    m.functions[0].blocks[0].body = vec![
        cast(CastOp::Bitcast, Ty::handle("H", "rt::H"), Ty::U8),
        cast(CastOp::Transmute, Ty::Closure(ClosureTyId::new(0)), Ty::U8),
        cast(CastOp::Bitcast, Ty::Bool, Ty::U8),
        cast(CastOp::PtrToPtr, Ty::Ptr, Ty::FatPtr(FatPtrKind::Str)),
        cast(CastOp::ReifyFnPointer, Ty::U64, Ty::Ptr),
    ];
    assert_eq!(run(&m, Rule::Casts).0.len(), 5);
}
#[test]
fn complete_custom_target_unicode_errors_are_preserved_for_each_actual_cast() {
    let m = custom();
    let out = run(&m, Rule::Casts).0;
    assert_eq!(out.len(), 2);
    assert!(out.iter().all(|e|matches!(e,ValidationError::CastLayoutUnsupported{reason,..}if reason.contains(&m.target_info.as_ref().unwrap().triple))));
}
#[test]
fn missing_declared_tuple_layout_and_deep_type_spelling_are_not_normalized() {
    let mut m = fixture();
    let mut ty = Ty::handle("é🦀", "runtime");
    for _ in 0..20 {
        ty = Ty::Ref(Box::new(ty));
    }
    m.functions[0].blocks[0].body = vec![
        cast(CastOp::Bitcast, Ty::Tuple(vec![Ty::U8]), Ty::U8),
        cast(CastOp::ReifyFnPointer, ty, Ty::Ptr),
    ];
    assert_eq!(run(&m, Rule::Casts).0.len(), 2);
}
#[test]
fn value_fact_equal_fullwidth_and_nonoverlapping_boundaries_preserve_success() {
    let mut m = fixture();
    m.functions[0].blocks.clear();
    m.functions[0].proofs = vec![
        ProofAnnotation::ValueRange {
            lo: i128::MIN,
            hi: i128::MAX,
        },
        ProofAnnotation::ValueRange {
            lo: i128::MAX,
            hi: i128::MAX,
        },
        ProofAnnotation::KnownBits {
            zeros: u128::MAX - 1,
            ones: 1,
        },
        ProofAnnotation::KnownBits {
            zeros: 0,
            ones: u128::MAX,
        },
    ];
    assert!(run(&m, Rule::Facts).0.is_empty());
}
#[test]
fn every_function_node_and_unreachable_block_fact_runs_without_proofref_or_status_authority() {
    let mut m = fixture();
    m.functions[0]
        .proofs
        .push(ProofAnnotation::BranchWeights(vec![1; 1024]));
    let mut b = Block::new(BlockId::new(99));
    let mut n = InstrNode::new(Inst::Unreachable);
    n.proofs = vec![ProofAnnotation::KnownBits {
        zeros: 1u128 << 127,
        ones: u128::MAX,
    }];
    b.body.push(n);
    m.functions[0].blocks.push(b);
    let mut second = Function::new(
        FuncId::new(8),
        "declaration",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    second.proofs = vec![ProofAnnotation::ValueRange { lo: 1, hi: 0 }];
    m.functions.push(second);
    let out = run(&m, Rule::Facts).0;
    assert_eq!(out.len(), 6);
    assert!(
        matches!(out[4],ValidationError::KnownBitsContradiction{overlap,..}if overlap==1u128<<127)
    );
    assert!(matches!(
        out[5],
        ValidationError::ValueRangeInverted { function: 8, .. }
    ));
}
