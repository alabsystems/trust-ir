// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    non_snake_case,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn actual_single_mutable_element_forward_signature_matches_original() {
    let m = fixture();
    assert!(run(&m, &inst()).0.is_empty());
}
#[test]
fn missing_or_duplicate_forward_id_is_refused_before_sequence_spelling() {
    let mut m = fixture();
    m.functions[1].id = FuncId::new(10);
    let mut node = inst();
    if let Inst::SeqMap { ty, .. } = &mut node {
        *ty = Ty::Bool;
    }
    assert!(matches!(
        &run(&m, &node).0[..],
        [ValidationError::SeqMapFwdNotFound { fwd_id: 9, .. }]
    ));
    let mut m = fixture();
    m.functions.push(m.functions[1].clone());
    assert!(matches!(
        &run(&m, &inst()).0[..],
        [ValidationError::SeqMapFwdNotFound { .. }]
    ));
}
#[test]
fn unresolved_actual_forward_signature_returns_original_complete_getter_error() {
    let mut m = fixture();
    m.functions[1].ty = FuncTyId::new(99);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let catalog = setup(&m, &mut s);
    let out =
        validate_seq_map_observed(&catalog, &inst(), BlockId::new(1), &mut s, site()).unwrap();
    assert_eq!(
        out,
        vec![ValidationError::FuncTypeNotFound {
            func_name: "forward".into(),
            func_ty_id: 99
        }]
    );
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    catalog.retire_observed(&mut s, site()).unwrap();
}
#[test]
fn nonsequence_and_dangling_element_id_preserve_original_type_diagnostic() {
    let m = fixture();
    for ty in [Ty::Bool, Ty::Sequence(TyId::new(99))] {
        let mut node = inst();
        if let Inst::SeqMap { ty: actual, .. } = &mut node {
            *actual = ty;
        }
        assert!(matches!(
            &run(&m, &node).0[..],
            [ValidationError::SeqMapTypeNotSequence { .. }]
        ));
    }
}
#[test]
fn nonempty_returns_varargs_wrong_arity_and_nonmutable_parameter_all_refuse() {
    let base = fixture();
    for signature in [
        FuncTy::unrecorded(vec![Ty::RefMut(Box::new(Ty::U64))], vec![Ty::Bool], false),
        FuncTy::unrecorded(vec![Ty::RefMut(Box::new(Ty::U64))], vec![], true),
        FuncTy::unrecorded(vec![], vec![], false),
        FuncTy::unrecorded(vec![Ty::Ref(Box::new(Ty::U64))], vec![], false),
        FuncTy::unrecorded(vec![Ty::RefMut(Box::new(Ty::U32))], vec![], false),
    ] {
        let mut m = base.clone();
        m.func_types[1] = signature;
        assert!(matches!(
            &run(&m, &inst()).0[..],
            [ValidationError::SeqMapFwdSignatureMismatch { .. }]
        ));
    }
}
#[test]
fn whole_nested_element_is_compared_without_making_a_layout_or_reversibility_claim() {
    let mut m = fixture();
    m.types[0] = Ty::Tuple(vec![Ty::U64, Ty::Bool]);
    m.func_types[1].params[0] = Ty::RefMut(Box::new(m.types[0].clone()));
    assert!(run(&m, &inst()).0.is_empty());
    if let Ty::RefMut(inner) = &mut m.func_types[1].params[0] {
        **inner = Ty::Tuple(vec![Ty::Bool, Ty::U64]);
    }
    assert_eq!(run(&m, &inst()).0.len(), 1);
}
#[test]
fn full_raw_forward_name_and_exact_parameter_return_spelling_are_retained() {
    let mut m = fixture();
    m.functions[1].name = "λ\0raw尾\n".repeat(2000);
    m.func_types[1].params = vec![Ty::Bool, Ty::Tuple(vec![Ty::U64; 100])];
    m.func_types[1].returns = vec![Ty::Bool, Ty::U8];
    let out = run(&m, &inst()).0;
    assert!(
        matches!(&out[..],[ValidationError::SeqMapFwdSignatureMismatch{fwd,expected,actual,..}]if fwd==&m.functions[1].name&&expected=="fn(&mut u64)"&&actual.starts_with("fn(bool, ")&&actual.ends_with(") -> (bool, u8)")&&actual.matches("u64").count()==100)
    );
}
#[test]
fn unrelated_opcode_is_not_a_SeqMap_acceptance_or_proof_route() {
    let m = fixture();
    assert!(run(&m, &Inst::Return { values: vec![] }).0.is_empty());
}
