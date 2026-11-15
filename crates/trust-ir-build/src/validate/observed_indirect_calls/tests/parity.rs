// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn all_three_actual_indirect_families_preserve_argument_and_pointer_checks() {
    for family in 0..3 {
        let mut m = fixture();
        let (callee, sig, args, calling_conv) =
            (v(10), FuncTyId::new(1), vec![v(1), v(0)], CallingConv::C);
        m.functions[0].blocks[0].body[1].inst = match family {
            0 => Inst::CallIndirect {
                callee,
                sig,
                args,
                calling_conv,
            },
            1 => Inst::CallIndirectCannotUnwind {
                callee,
                sig,
                args,
                calling_conv,
            },
            _ => Inst::InvokeIndirect {
                callee,
                sig,
                args,
                calling_conv,
                normal_dest: BlockId::new(2),
                normal_args: vec![],
                unwind_dest: BlockId::new(3),
            },
        };
        if family == 2 {
            m.functions[0].blocks[0].body.pop();
            for id in [2, 3] {
                let mut b = Block::new(BlockId::new(id));
                b.body.push(InstrNode::new(Inst::Return { values: vec![] }));
                m.functions[0].blocks.push(b);
            }
        }
        let errors = run(&m).0;
        assert_eq!(errors.len(), 2);
        assert!(
            errors
                .iter()
                .all(|e| matches!(e, ValidationError::CallIndirectArgTypeMismatch { .. }))
        );
    }
}
#[test]
fn exact_original_missing_signature_early_skip_is_single_edge_diagnostic() {
    let mut m = fixture();
    m.functions[0].blocks[0].body[1].inst = call(10, 999, &[3]);
    assert!(matches!(
        &run(&m).0[..],
        [ValidationError::CallIndirectSigNotFound { sig_id: 999, .. }]
    ));
}
#[test]
fn rust_variadic_nominal_order_count_unknown_and_refinement_defer_match_original() {
    let mut m = fixture();
    m.func_types[1].is_vararg = true;
    m.func_types[1].params = vec![Ty::Bool];
    m.functions[0].blocks[0].body[1].inst = call(4, 1, &[0, 2, 3, 999]);
    if let Inst::CallIndirect { calling_conv, .. } = &mut m.functions[0].blocks[0].body[1].inst {
        *calling_conv = CallingConv::Rust;
    }
    let e = run(&m).0;
    assert!(matches!(e[0], ValidationError::RustAbiVararg { .. }));
    assert!(matches!(e[1], ValidationError::InvalidHandleUse { .. }));
    assert!(matches!(e[2], ValidationError::InvalidDialectType { .. }));
    m.func_types[1].params = vec![Ty::Bool, Ty::U64, Ty::Bool];
    m.functions[0].blocks[0].body[1].inst = call(4, 1, &[999]);
    assert!(matches!(
        &run(&m).0[..],
        [ValidationError::CallIndirectArgCountMismatch { .. }]
    ));
    m.func_types[1].is_vararg = false;
    m.func_types[1].params = vec![Ty::Refine(TyId::new(0), PredId::new(0))];
    m.functions[0].blocks[0].body[1].inst = call(4, 1, &[1]);
    assert!(run(&m).0.is_empty());
}
#[test]
fn raw_malformed_equal_signature_abi_is_data_but_edge_lowered_convention_is_checked() {
    let mut m = fixture();
    m.func_types[1].abi = Some(abi());
    assert!(run(&m).0.is_empty());
    m.func_types[1].abi.as_mut().unwrap().lowered_convention = CallingConv::Fast;
    assert!(matches!(
        &run(&m).0[..],
        [ValidationError::InvalidSignatureAbi { .. }]
    ));
}
#[test]
fn closure_apparent_signature_missing_type_and_physical_target_contract_are_exact() {
    let mut m = closure();
    assert!(run(&m).0.is_empty());
    m.closure_types[0].func = FuncTyId::new(2);
    assert!(matches!(
        &run(&m).0[..],
        [ValidationError::CallIndirectClosureSigMismatch { .. }]
    ));
    m.closure_types.clear();
    assert!(matches!(
        &run(&m).0[..],
        [ValidationError::ClosureTypeNotFound { .. }]
    ));
    let mut m = closure();
    m.func_types[3].params.remove(0);
    let e = run(&m).0;
    let ValidationError::CallIndirectClosureTargetMismatch {
        expected, actual, ..
    } = &e[0]
    else {
        panic!()
    };
    assert_eq!(expected, "(bool, bool, u64)) -> (()");
    assert_eq!(actual, "(bool, u64)) -> (()");
}
#[test]
fn closure_copy_targets_and_original_missing_or_ambiguous_target_skip_are_preserved() {
    let mut m = closure();
    m.functions[0].blocks[0].body.insert(
        1,
        InstrNode::new(Inst::Copy {
            ty: Ty::Closure(ClosureTyId::new(0)),
            operand: v(10),
        })
        .with_result(v(11)),
    );
    m.functions[0].blocks[0].body[2].inst = call(11, 1, &[0, 1]);
    let expected = original::original(&m, 0, 2);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (catalog, values, nominal) = setup(&m, &mut s);
    let mut c = ObservedIndirectCalls::new_observed(&catalog, 0, &mut s, site()).unwrap();
    let out = c
        .validate_at_observed(0, 2, &values, Some(&nominal), &mut s, site())
        .unwrap();
    assert_eq!(out, expected);
    assert!(out.is_empty());
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    c.retire_observed(&mut s, site()).unwrap();
    dispose(catalog, values, nominal, &mut s);
    let mut missing = closure();
    missing.functions.pop();
    assert!(run(&missing).0.is_empty());
    let mut duplicate = closure();
    duplicate.functions.push(duplicate.functions[1].clone());
    assert!(run(&duplicate).0.is_empty());
}
#[test]
fn static_pointer_missing_or_ambiguous_targets_refuse_and_dynamic_parameter_is_not_static() {
    let mut m = fixture();
    m.functions.pop();
    assert!(matches!(
        &run(&m).0[..],
        [ValidationError::CalleeNotFound { callee_id: 9, .. }]
    ));
    let mut m = fixture();
    m.functions.push(m.functions[1].clone());
    assert!(matches!(
        &run(&m).0[..],
        [ValidationError::CalleeNotFound { .. }]
    ));
    let mut m = fixture();
    m.functions[1].calling_conv = CallingConv::Fast;
    assert!(matches!(
        &run(&m).0[..],
        [ValidationError::CallEdgeConvMismatch { .. }]
    ));
    m.functions[0].blocks[0].body[1].inst = call(4, 1, &[0, 1]);
    assert!(run(&m).0.is_empty());
}
#[test]
fn static_signature_ids_and_all_convention_spelling_diagnostics_match_original() {
    let mut m = fixture();
    m.functions[1].ty = FuncTyId::new(2);
    assert!(matches!(
        &run(&m).0[..],
        [ValidationError::CallEdgeSignatureMismatch { .. }]
    ));
    for conv in CallingConv::ALL {
        if conv == CallingConv::C {
            continue;
        }
        let mut m = fixture();
        m.functions[1].calling_conv = conv;
        let e = run(&m).0;
        assert!(matches!(
            &e[..],
            [ValidationError::CallEdgeConvMismatch { .. }]
        ));
    }
}

#[test]
fn actual_copy_reify_pointer_chain_is_consumed_at_its_real_node() {
    let mut m = fixture();
    m.functions[1].calling_conv = CallingConv::Fast;
    m.functions[0].blocks[0].body.insert(
        1,
        InstrNode::new(Inst::Copy {
            ty: Ty::Func(FuncTyId::new(1)),
            operand: v(10),
        })
        .with_result(v(11)),
    );
    m.functions[0].blocks[0].body.insert(
        2,
        InstrNode::new(Inst::Cast {
            op: trust_ir::inst::CastOp::ReifyFnPointer,
            src_ty: Ty::Func(FuncTyId::new(1)),
            dst_ty: Ty::Ptr,
            operand: v(11),
        })
        .with_result(v(12)),
    );
    m.functions[0].blocks[0].body[3].inst = call(12, 1, &[0, 1]);
    assert!(matches!(
        &run_at(&m, 0, 3).0[..],
        [ValidationError::CallEdgeConvMismatch { .. }]
    ));
}
#[test]
fn original_missing_target_signature_skips_only_its_local_physical_contract() {
    let mut m = closure();
    m.functions[1].ty = FuncTyId::new(999);
    assert!(run(&m).0.is_empty());
    let mut m = fixture();
    m.functions[1].ty = FuncTyId::new(999);
    assert!(run(&m).0.is_empty());
}
#[test]
fn sparse_maximum_block_ids_and_decimal_diagnostic_text_match_original() {
    let mut m = fixture();
    m.functions[0].entry = BlockId::new(u32::MAX);
    m.functions[0].blocks[0].id = BlockId::new(u32::MAX);
    m.func_types[1].is_vararg = true;
    m.functions[0].blocks[0].body[1].inst = call(4, 1, &[0, 1]);
    if let Inst::CallIndirect { calling_conv, .. } = &mut m.functions[0].blocks[0].body[1].inst {
        *calling_conv = CallingConv::Rust;
    }
    let e = run(&m).0;
    let ValidationError::RustAbiVararg { detail, .. } = &e[0] else {
        panic!()
    };
    assert!(detail.contains("bb4294967295"));
}
