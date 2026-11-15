// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
#[test]
fn normal_edges_emit_count_before_all_zipped_type_errors_even_when_count_is_wrong() {
    let errors = parity(&fixture(), None);
    assert_eq!(errors.len(), 3);
    assert!(matches!(
        errors[0],
        ValidationError::BranchArgCountMismatch {
            expected: 3,
            actual: 2,
            ..
        }
    ));
    assert!(matches!(
        errors[1],
        ValidationError::BranchArgTypeMismatch { arg_index: 0, .. }
    ));
    assert!(matches!(
        errors[2],
        ValidationError::BranchArgTypeMismatch { arg_index: 1, .. }
    ));
    let f = function(
        Inst::Br {
            target: b(1),
            args: vec![v(0), v(1)],
        },
        vec![Ty::I32],
    );
    assert_eq!(parity(&f, None).len(), 2);
}
#[test]
fn conditional_then_else_and_parallel_edge_diagnostics_keep_source_order_and_duplicates() {
    let mut f = function(
        Inst::CondBr {
            cond: v(0),
            then_target: b(1),
            then_args: vec![v(0)],
            else_target: b(1),
            else_args: vec![v(0)],
        },
        vec![Ty::I32],
    );
    let errors = parity(&f, None);
    assert_eq!(errors.len(), 2);
    assert_eq!(errors[0], errors[1]);
    let mut other = Block::new(b(2));
    other.params.push((v(300), Ty::Bool));
    f.blocks.push(other);
    if let Inst::CondBr { else_target, .. } = &mut f.blocks[0].body[0].inst {
        *else_target = b(2);
    }
    let errors = parity(&f, None);
    assert!(matches!(
        errors[0],
        ValidationError::BranchArgTypeMismatch { target: 1, .. }
    ));
    assert!(matches!(
        errors[1],
        ValidationError::BranchArgTypeMismatch { target: 2, .. }
    ));
}
#[test]
fn switch_default_diagnostics_precede_case_diagnostics_without_rotating_or_losing_edges() {
    let f = function(
        Inst::Switch {
            value: v(0),
            default: b(1),
            default_args: vec![],
            exhaustive_enum_unreachable: false,
            cases: vec![
                trust_ir::inst::SwitchCase {
                    value: trust_ir::Constant::Int(0),
                    target: b(1),
                    args: vec![v(0)],
                },
                trust_ir::inst::SwitchCase {
                    value: trust_ir::Constant::Int(1),
                    target: b(1),
                    args: vec![v(0)],
                },
            ],
        },
        vec![Ty::I32],
    );
    let errors = parity(&f, None);
    assert_eq!(errors.len(), 3);
    assert!(matches!(
        errors[0],
        ValidationError::BranchArgCountMismatch { actual: 0, .. }
    ));
    assert!(matches!(
        errors[1],
        ValidationError::BranchArgTypeMismatch { .. }
    ));
    assert_eq!(errors[1], errors[2]);
}
#[test]
fn all_four_invokes_check_normal_types_then_only_unwind_parameter_count() {
    for family in 0..4 {
        let normal_dest = b(1);
        let unwind_dest = b(2);
        let normal_args = vec![v(0)];
        let term = match family {
            0 => Inst::Invoke {
                callee: FuncId::new(7),
                args: vec![],
                normal_dest,
                normal_args,
                unwind_dest,
            },
            1 => Inst::InvokeIndirect {
                callee: v(2),
                sig: FuncTyId::new(0),
                args: vec![],
                calling_conv: CallingConv::C,
                normal_dest,
                normal_args,
                unwind_dest,
            },
            2 => Inst::DropInvoke {
                ty: Ty::U32,
                ptr: v(2),
                normal_dest,
                normal_args,
                unwind_dest,
            },
            _ => Inst::AssertInvoke {
                cond: v(0),
                kind: trust_ir::AssertKind::NullPtr,
                site: trust_ir::PanicSite {
                    entry: FuncId::new(7),
                    location: trust_ir::PanicLocation::Value(v(2)),
                },
                normal_dest,
                normal_args,
                unwind_dest,
            },
        };
        let mut f = function(term, vec![Ty::I32]);
        let mut pad = Block::new(b(2));
        pad.params.push((v(200), Ty::Bool));
        pad.body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        f.blocks.push(pad);
        let errors = parity(&f, None);
        assert_eq!(errors.len(), 2);
        assert!(matches!(
            errors[0],
            ValidationError::BranchArgTypeMismatch { target: 1, .. }
        ));
        assert!(matches!(
            errors[1],
            ValidationError::BranchArgCountMismatch {
                target: 2,
                actual: 0,
                ..
            }
        ));
    }
}
#[test]
fn last_duplicate_target_and_value_definitions_match_both_original_last_write_maps() {
    let mut f = function(
        Inst::Br {
            target: b(1),
            args: vec![v(0)],
        },
        vec![Ty::I32, Ty::Bool],
    );
    let mut last = Block::new(b(1));
    last.params = vec![(v(0), Ty::I32)];
    last.body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    f.blocks.push(last);
    assert!(parity(&f, None).is_empty());
    f.blocks.last_mut().unwrap().params.clear();
    assert!(matches!(
        parity(&f, None)[0],
        ValidationError::BranchArgCountMismatch {
            expected: 0,
            actual: 1,
            ..
        }
    ));
}
#[test]
fn absent_targets_unknown_argument_types_and_nonterminating_tails_add_no_type_errors() {
    let mut f = function(
        Inst::Br {
            target: b(99),
            args: vec![v(99)],
        },
        vec![Ty::I32],
    );
    assert!(parity(&f, None).is_empty());
    f.blocks[0].body[0] = InstrNode::new(Inst::Br {
        target: b(1),
        args: vec![v(99)],
    });
    assert!(parity(&f, None).is_empty());
    f.blocks[0].body.push(InstrNode::new(Inst::NullPtr));
    assert!(parity(&f, None).is_empty());
    f.blocks.clear();
    assert!(parity(&f, None).is_empty());
    assert!(parity(&f, Some(&Module::new("empty component"))).is_empty());
}
#[test]
fn only_outer_refinement_mismatches_defer_and_nested_refinement_differences_still_report() {
    let refined = Ty::Refine(TyId::new(0), PredId::new(1));
    let mut f = function(
        Inst::Br {
            target: b(1),
            args: vec![v(0)],
        },
        vec![Ty::I32],
    );
    f.blocks[0].params[0].1 = refined.clone();
    assert!(parity(&f, None).is_empty());
    f.blocks[0].params[0].1 = Ty::Tuple(vec![refined]);
    f.blocks[1].params[0].1 = Ty::Tuple(vec![Ty::I32]);
    assert_eq!(parity(&f, None).len(), 1);
}
#[test]
fn module_call_returns_are_checked_and_unknown_callees_keep_the_original_exemption() {
    let (f, module) = call_fixture(true);
    assert!(parity(&f, None).is_empty());
    assert_eq!(parity(&f, Some(&module)).len(), 1);
    let (f, module) = call_fixture(false);
    assert!(parity(&f, Some(&module)).is_empty());
}
#[test]
fn multi_result_zip_preserves_unknown_extra_results_in_both_contexts() {
    let mut f = function(
        Inst::Br {
            target: b(1),
            args: vec![v(7), v(8), v(9)],
        },
        vec![Ty::I32, Ty::U32, Ty::Bool],
    );
    f.blocks[0].body.insert(
        0,
        InstrNode::new(Inst::Overflow {
            op: trust_ir::OverflowOp::AddOverflow,
            ty: Ty::U32,
            lhs: v(0),
            rhs: v(0),
        })
        .with_results([v(7), v(8), v(9)]),
    );
    assert_eq!(parity(&f, None).len(), 2);
    assert_eq!(parity(&f, Some(&Module::new("multi result"))).len(), 2);
}
#[test]
fn fat_borrow_results_are_corrected_before_standalone_and_module_branch_type_checks() {
    let mut f = function(
        Inst::Br {
            target: b(1),
            args: vec![v(3)],
        },
        vec![Ty::Ptr],
    );
    f.blocks[0].params[0].1 = Ty::FatPtr(FatPtrKind::Str);
    f.blocks[0].body.insert(
        0,
        InstrNode::new(Inst::Borrow { ptr: v(0) }).with_result(v(3)),
    );
    assert_eq!(parity(&f, None).len(), 1);
    assert_eq!(parity(&f, Some(&Module::new("borrow branch"))).len(), 1);
}
#[test]
fn actual_observed_type_spelling_keeps_full_nested_and_malformed_unicode_handle_diagnostics() {
    let a = Ty::Handle(Box::new(HandleTy {
        name: "raw'\"λ\n".repeat(20),
        runtime: "runtime\0".repeat(20),
    }));
    let e = Ty::Tuple(vec![a.clone(), Ty::U32]);
    let a = Ty::Tuple(vec![a, Ty::I32]);
    let mut f = function(
        Inst::Br {
            target: b(1),
            args: vec![v(0)],
        },
        vec![e],
    );
    f.blocks[0].params[0].1 = a;
    assert_eq!(parity(&f, None).len(), 1);
}
