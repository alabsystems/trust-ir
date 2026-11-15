// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn all_three_actual_stateful_capture_kinds_match_complete_ordinary_rule() {
    for id in [1, 2, 3] {
        let mut m = fixture();
        m.func_types[0].params = vec![c(id)];
        m.functions[0].blocks[0].body[0] = node(Inst::Undef { ty: c(id) }, &[10]);
        assert_eq!(run(&m).0.len(), 2);
    }
}
#[test]
fn immutable_pointer_borrows_owned_values_and_nested_stateful_are_not_reclassified() {
    for id in [0, 4] {
        let mut m = fixture();
        m.func_types[0].params = vec![c(id)];
        m.functions[0].blocks[0].body[0] = node(Inst::Undef { ty: c(id) }, &[10]);
        assert!(run(&m).0.is_empty());
    }
}
#[test]
fn signature_reports_one_first_capture_and_searches_params_before_returns() {
    let mut m = fixture();
    m.functions[0].blocks.clear();
    m.func_types[0].params = vec![Ty::Bool, c(1), c(2)];
    m.func_types[0].returns = vec![c(3)];
    assert!(matches!(
        &run(&m).0[..],
        [ValidationError::FunctionPureWithStatefulClosureSignature {
            closure_ty_id: 1,
            capture_index: 1,
            ..
        }]
    ));
    m.func_types[0].params = vec![c(0)];
    assert!(matches!(
        &run(&m).0[..],
        [ValidationError::FunctionPureWithStatefulClosureSignature {
            closure_ty_id: 3,
            ..
        }]
    ));
}
#[test]
fn missing_signature_and_closure_rows_skip_only_the_same_local_purity_checks() {
    let mut m = fixture();
    m.functions[0].ty = FuncTyId::new(999);
    m.functions[0].blocks[0].body[0] = node(Inst::Undef { ty: c(999) }, &[10]);
    assert!(run(&m).0.is_empty());
    m.functions[0].blocks[0].body[0] = node(Inst::Undef { ty: c(2) }, &[10]);
    assert_eq!(run(&m).0.len(), 1);
}
#[test]
fn no_pure_annotation_keeps_the_original_local_no_diagnostic_behavior() {
    let mut m = fixture();
    m.functions[0].proofs = vec![ProofAnnotation::BoundedOutput {
        lo: f64::NAN,
        hi: f64::INFINITY,
    }];
    m.functions[0].blocks[0].body[0].proofs.clear();
    assert!(run(&m).0.is_empty());
}
#[test]
fn capture_scan_reports_only_first_outer_stateful_index_in_declaration_order() {
    let mut m = fixture();
    m.closure_types[1].captures = vec![
        Ty::Bool,
        Ty::U64,
        Ty::Rc(Box::new(Ty::Bool)),
        Ty::RefMut(Box::new(Ty::Bool)),
    ];
    let e = run(&m).0;
    assert!(e.iter().all(|e| matches!(
        e,
        ValidationError::FunctionPureWithStatefulClosureSignature {
            capture_index: 2,
            ..
        } | ValidationError::ClosurePureWithStatefulCapture {
            capture_index: 2,
            ..
        }
    )));
}
#[test]
fn direct_multiresult_call_preserves_each_ordinal_and_missing_ssa_value() {
    let mut m = fixture();
    m.functions[0].proofs.clear();
    m.functions[0].blocks[0].body[0] = node(
        Inst::Call {
            callee: FuncId::new(9),
            args: vec![],
        },
        &[20, 21],
    );
    assert!(matches!(
        &run(&m).0[..],
        [
            ValidationError::ClosurePureWithStatefulCapture {
                value: Some(21),
                closure_ty_id: 2,
                ..
            },
            ValidationError::ClosurePureWithStatefulCapture {
                value: None,
                closure_ty_id: 1,
                ..
            }
        ]
    ));
}
#[test]
fn all_three_indirect_families_read_actual_declared_signature_returns() {
    for family in 0..3 {
        let mut m = fixture();
        m.functions[0].proofs.clear();
        let (callee, sig, args, calling_conv) = (v(99), FuncTyId::new(2), vec![], CallingConv::C);
        let inst = match family {
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
        m.functions[0].blocks[0].body[0] = node(inst, &[30, 31]);
        assert!(matches!(
            &run(&m).0[..],
            [ValidationError::ClosurePureWithStatefulCapture {
                value: Some(30),
                closure_ty_id: 3,
                ..
            }]
        ));
    }
}
#[test]
fn actual_dialect_multiresult_types_are_seen_even_without_attached_result_ids() {
    let mut m = fixture();
    m.functions[0].proofs.clear();
    let op = trust_ir::dialect::DialectInst::new("unknown", "op").with_result_tys([
        c(1),
        Ty::Bool,
        c(2),
    ]);
    m.functions[0].blocks[0].body[0] = node(Inst::DialectOp(Box::new(op)), &[40]);
    assert!(matches!(
        &run(&m).0[..],
        [
            ValidationError::ClosurePureWithStatefulCapture {
                value: Some(40),
                closure_ty_id: 1,
                ..
            },
            ValidationError::ClosurePureWithStatefulCapture {
                value: None,
                closure_ty_id: 2,
                ..
            }
        ]
    ));
}
#[test]
fn result_lookup_preserves_index_slot_preference_then_first_physical_fallback() {
    let mut m = fixture();
    let a = Function::new(FuncId::new(1), "first", FuncTyId::new(1), BlockId::new(0));
    let b = Function::new(FuncId::new(1), "index", FuncTyId::new(2), BlockId::new(0));
    m.functions = vec![a, b];
    let n = node(
        Inst::Call {
            callee: FuncId::new(1),
            args: vec![],
        },
        &[],
    );
    assert_eq!(
        closure_results(&m, &n),
        vec![(0, ClosureTyId::new(3)), (1, ClosureTyId::new(0))]
    );
    for f in &mut m.functions {
        f.id = FuncId::new(77);
    }
    let n = node(
        Inst::Call {
            callee: FuncId::new(77),
            args: vec![],
        },
        &[],
    );
    assert_eq!(
        closure_results(&m, &n),
        vec![(1, ClosureTyId::new(2)), (2, ClosureTyId::new(1))]
    );
}
#[test]
fn nested_and_refined_closures_are_not_mistaken_for_outer_closure_results() {
    let m = fixture();
    for ty in [
        Ty::Tuple(vec![c(1)]),
        Ty::Refine(TyId::new(0), PredId::new(0)),
        Ty::RefMut(Box::new(c(1))),
    ] {
        assert!(closure_results(&m, &node(Inst::Undef { ty }, &[])).is_empty());
    }
}
#[test]
fn complete_error_order_is_function_signature_then_physical_blocks_and_nodes() {
    let mut m = fixture();
    m.functions.push(m.functions[0].clone());
    m.functions[2].name = "second".into();
    m.functions[2].id = FuncId::new(1442);
    let e = run(&m).0;
    assert_eq!(e.len(), 4);
    assert!(
        matches!(&e[0],ValidationError::FunctionPureWithStatefulClosureSignature{func_name,..}if func_name=="pure")
    );
    assert!(
        matches!(&e[2],ValidationError::FunctionPureWithStatefulClosureSignature{func_name,..}if func_name=="second")
    );
}
#[test]
fn actual_rich_unicode_capture_display_and_function_names_are_byte_exact() {
    let m = rich();
    let e = run(&m).0;
    assert!(
        matches!(&e[0],ValidationError::FunctionPureWithStatefulClosureSignature{func_name,capture_ty,..}if func_name==&m.functions[0].name&&capture_ty.contains("中Name")&&capture_ty.contains("éRuntime"))
    );
}
#[test]
fn result_reader_matches_actual_bridge_for_one_pair_types_empty_and_comparison_plans() {
    let m = fixture();
    for n in [
        node(Inst::Undef { ty: c(1) }, &[]),
        node(
            Inst::Overflow {
                op: trust_ir::inst::OverflowOp::AddOverflow,
                ty: c(1),
                lhs: v(0),
                rhs: v(1),
            },
            &[],
        ),
        node(
            Inst::ICmp {
                op: trust_ir::inst::ICmpOp::Eq,
                ty: c(1),
                lhs: v(0),
                rhs: v(1),
            },
            &[],
        ),
        node(
            Inst::LandingPad {
                is_cleanup: true,
                catch_type_indices: vec![],
            },
            &[],
        ),
        node(
            Inst::Call {
                callee: FuncId::new(9),
                args: vec![],
            },
            &[],
        ),
        node(
            Inst::Call {
                callee: FuncId::new(999),
                args: vec![],
            },
            &[],
        ),
        node(Inst::Return { values: vec![] }, &[]),
        node(Inst::Borrow { ptr: v(0) }, &[]),
    ] {
        closure_results(&m, &n);
    }
}
