// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn exact_direct_call_arguments_preserve_original_empty_diagnostics() {
    let m = fixture();
    assert!(run(&m, &call(&[1, 0]), true).0.is_empty());
}
#[test]
fn short_long_and_each_known_mismatch_keep_original_count_then_type_order() {
    let m = fixture();
    for args in [&[][..], &[0][..], &[0, 1, 1][..]] {
        run(&m, &call(args), true);
    }
    let out = run(&m, &call(&[0, 1, 1]), true).0;
    assert!(matches!(
        &out[..],
        [
            ValidationError::CallArgCountMismatch { .. },
            ValidationError::CallArgTypeMismatch { arg_index: 0, .. },
            ValidationError::CallArgTypeMismatch { arg_index: 1, .. }
        ]
    ));
}
#[test]
fn missing_and_duplicate_callees_never_select_a_name_or_signature() {
    let mut m = fixture();
    m.functions[1].id = FuncId::new(10);
    assert!(matches!(
        &run(&m, &call(&[1, 0]), true).0[..],
        [ValidationError::CalleeNotFound { callee_id: 9, .. }]
    ));
    let mut m = fixture();
    let mut second = m.functions[1].clone();
    second.name = "other".into();
    m.functions.push(second);
    assert!(matches!(
        &run(&m, &call(&[1, 0]), true).0[..],
        [ValidationError::CalleeNotFound { callee_id: 9, .. }]
    ));
}
#[test]
fn actual_missing_signature_returns_whole_original_getter_diagnostic() {
    let mut m = fixture();
    m.functions[1].ty = FuncTyId::new(99);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (catalog, values, nominal) = setup(&m, true, &mut s);
    let out = validate_direct_call_observed(
        &catalog,
        &m.functions[0],
        &call(&[1, 0]),
        &values,
        nominal.as_ref(),
        BlockId::new(1),
        &mut s,
        site(),
    )
    .unwrap();
    assert_eq!(
        out,
        vec![ValidationError::FuncTypeNotFound {
            func_name: "target".into(),
            func_ty_id: 99
        }]
    );
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    dispose(catalog, values, nominal, &mut s);
}
#[test]
fn fixed_prefix_and_nominal_varargs_errors_precede_original_fixed_argument_errors() {
    let mut m = fixture();
    m.func_types[1].is_vararg = true;
    let out = run(&m, &call(&[0, 1, 2, 3, 2]), true).0;
    assert!(matches!(
        &out[..],
        [
            ValidationError::InvalidHandleUse { .. },
            ValidationError::InvalidDialectType { .. },
            ValidationError::InvalidHandleUse { .. },
            ValidationError::CallArgTypeMismatch { arg_index: 0, .. },
            ValidationError::CallArgTypeMismatch { arg_index: 1, .. }
        ]
    ));
    assert!(run(&m, &call(&[1, 0, 1]), true).0.is_empty());
}
#[test]
fn unknown_argument_type_stays_skipped_and_cannot_hide_known_later_type_mismatch() {
    let m = fixture();
    let out = run(&m, &call(&[99, 1]), true).0;
    assert!(matches!(
        &out[..],
        [ValidationError::CallArgTypeMismatch { arg_index: 1, .. }]
    ));
}
#[test]
fn call_and_cannot_unwind_defer_refinement_but_invoke_keeps_original_mismatch() {
    let mut m = fixture();
    m.functions[0].blocks[0].params[1].1 = Ty::Refine(TyId::new(0), PredId::new(0));
    assert!(run(&m, &call(&[1, 0]), true).0.is_empty());
    assert!(
        run(
            &m,
            &Inst::CallCannotUnwind {
                callee: FuncId::new(9),
                args: vec![v(1), v(0)]
            },
            true
        )
        .0
        .is_empty()
    );
    let out = run(
        &m,
        &Inst::Invoke {
            callee: FuncId::new(9),
            args: vec![v(1), v(0)],
            normal_dest: BlockId::new(2),
            normal_args: vec![],
            unwind_dest: BlockId::new(3),
        },
        true,
    )
    .0;
    assert!(matches!(
        &out[..],
        [ValidationError::CallArgTypeMismatch { arg_index: 0, .. }]
    ));
}
#[test]
fn complete_producer_display_matches_all_stable_tokens_and_raw_quoted_other() {
    for producer in [
        None,
        Some(Producer::TRust),
        Some(Producer::Clean),
        Some(Producer::TrustIr),
        Some(Producer::TSwift),
        Some(Producer::TC),
        Some(Producer::Other("λ\0\n'\"尾".into())),
    ] {
        let mut m = fixture();
        m.functions[0].producer = producer.clone();
        m.functions[1].producer = producer.clone();
        let out = run(&m, &call(&[]), true).0;
        let expected = producer.as_ref().map(ToString::to_string);
        assert!(
            matches!(&out[..],[ValidationError::CallArgCountMismatch{caller_producer,callee_producer,..}]if caller_producer==&expected&&callee_producer==&expected)
        );
    }
}
#[test]
fn full_raw_callee_and_type_text_are_not_shortened_or_normalized() {
    let mut m = fixture();
    m.functions[1].name = "λ raw\0尾\n".repeat(3000);
    m.func_types[1].params[0] = Ty::Tuple(vec![Ty::U64; 200]);
    let out = run(&m, &call(&[0, 0]), true).0;
    assert!(
        matches!(&out[..],[ValidationError::CallArgTypeMismatch{callee,expected,..}]if callee==&m.functions[1].name&&expected.matches("u64").count()==200)
    );
}
#[test]
fn last_definition_type_rows_and_each_original_direct_opcode_are_used() {
    let mut m = fixture();
    m.functions[0].blocks[0].body.insert(
        0,
        InstrNode::new(Inst::Undef { ty: Ty::Bool }).with_result(v(1)),
    );
    for inst in [
        call(&[1, 0]),
        Inst::CallCannotUnwind {
            callee: FuncId::new(9),
            args: vec![v(1), v(0)],
        },
        Inst::Invoke {
            callee: FuncId::new(9),
            args: vec![v(1), v(0)],
            normal_dest: BlockId::new(2),
            normal_args: vec![],
            unwind_dest: BlockId::new(3),
        },
    ] {
        assert_eq!(run(&m, &inst, true).0.len(), 1);
    }
}
#[test]
fn actual_scalar_only_legacy_optional_summary_lane_does_not_require_new_nominal_analysis() {
    let mut m = fixture();
    m.func_types[0].params.truncate(2);
    m.functions[0].blocks[0].params.truncate(2);
    m.func_types[1].is_vararg = true;
    assert!(run(&m, &call(&[1, 0, 1, 99]), false).0.is_empty());
}
#[test]
fn non_direct_opcode_is_only_this_diagnostic_constituents_no_output_lane() {
    let m = fixture();
    assert!(run(&m, &Inst::Return { values: vec![] }, true).0.is_empty());
}
