// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
fn indirect(callee: u32, sig: u32, args: &[u32]) -> Inst {
    Inst::CallIndirect {
        callee: v(callee),
        sig: FuncTyId::new(sig),
        args: args.iter().copied().map(v).collect(),
        calling_conv: CallingConv::C,
    }
}
#[test]
fn scalar_only_instruction_keeps_original_empty_rule_output() {
    let (m, f) = fixture();
    assert!(
        check(
            &m,
            &f,
            Inst::Copy {
                ty: Ty::Bool,
                operand: v(0)
            }
        )
        .is_empty()
    );
}
#[test]
fn exact_handle_dialect_and_mixed_copy_and_select_transport_is_preserved() {
    let (m, f) = fixture();
    for (ty, id) in [(handle(), 1), (dialect(), 2), (mixed(), 3)] {
        assert!(
            check(
                &m,
                &f,
                Inst::Copy {
                    ty: ty.clone(),
                    operand: v(id)
                }
            )
            .is_empty()
        );
        assert!(
            check(
                &m,
                &f,
                Inst::Select {
                    ty,
                    cond: v(0),
                    then_val: v(id),
                    else_val: v(id)
                }
            )
            .is_empty()
        );
    }
}
#[test]
fn handle_precedence_is_preserved_when_both_families_refuse() {
    let (m, f) = fixture();
    let out = check(&m, &f, Inst::Undef { ty: mixed() });
    assert!(matches!(
        &out[..],
        [ValidationError::InvalidHandleUse { .. }]
    ));
}
#[test]
fn aggregate_handle_success_still_passes_mandatory_dialect_intersection() {
    let (m, f) = fixture();
    let out = check(
        &m,
        &f,
        Inst::MakeAggregate {
            ty: mixed(),
            variant: None,
            fields: vec![v(1), v(2)],
        },
    );
    assert!(matches!(
        &out[..],
        [ValidationError::InvalidDialectType { .. }]
    ));
}
#[test]
fn generic_and_specific_aggregate_handle_failures_keep_complete_original_details() {
    let (m, f) = fixture();
    let out = check(
        &m,
        &f,
        Inst::MakeAggregate {
            ty: Ty::Tuple(vec![handle()]),
            variant: None,
            fields: vec![v(0)],
        },
    );
    assert!(
        matches!(&out[..],[ValidationError::InvalidHandleUse{detail,..}] if detail.contains("lane 0"))
    );
    let out = check(&m, &f, Inst::Undef { ty: handle() });
    assert!(
        matches!(&out[..],[ValidationError::InvalidHandleUse{detail,..}] if detail.starts_with("`Undef`"))
    );
}
#[test]
fn every_exact_select_operand_and_boolean_condition_remain_required() {
    let (m, f) = fixture();
    for (cond, then_val, else_val) in [(1, 1, 1), (0, 0, 1), (0, 1, 0)] {
        assert!(matches!(
            &check(
                &m,
                &f,
                Inst::Select {
                    ty: handle(),
                    cond: v(cond),
                    then_val: v(then_val),
                    else_val: v(else_val)
                }
            )[..],
            [ValidationError::InvalidHandleUse { .. }]
        ));
    }
}
#[test]
fn handle_indirect_calls_require_exact_func_identity_even_for_transport_only() {
    let (m, f) = fixture();
    assert!(check(&m, &f, indirect(5, 1, &[1])).is_empty());
    for (callee, sig) in [(4, 1), (4, 4), (5, 4), (8, 1)] {
        assert!(matches!(
            &check(&m, &f, indirect(callee, sig, &[1]))[..],
            [ValidationError::InvalidHandleUse { .. }]
        ));
    }
}
#[test]
fn dialect_pointerlike_calls_transport_arguments_but_never_originate_returns() {
    let (m, f) = fixture();
    assert!(check(&m, &f, indirect(4, 3, &[2])).is_empty());
    assert!(check(&m, &f, indirect(7, 2, &[2])).is_empty());
    for sig in [2, 99] {
        let out = check(&m, &f, indirect(4, sig, &[2]));
        assert!(
            matches!(&out[..],[ValidationError::InvalidDialectType{detail,..}] if detail.contains("cannot originate"))
        );
    }
}
#[test]
fn indirect_callee_pointer_shape_and_dialect_containment_are_checked() {
    let (m, mut f) = fixture();
    for ty in [Ty::Bool, Ty::Ref(Box::new(dialect()))] {
        f.blocks[0].params.push((v(30), ty));
        let out = check(&m, &f, indirect(30, 3, &[2]));
        assert!(matches!(
            &out[..],
            [ValidationError::InvalidDialectType { .. }]
        ));
        f.blocks[0].params.pop();
    }
}
#[test]
fn all_indirect_opcode_routes_preserve_original_exact_handle_and_dialect_rules() {
    let (m, f) = fixture();
    for inst in [
        Inst::CallIndirectCannotUnwind {
            callee: v(4),
            sig: FuncTyId::new(1),
            args: vec![v(1)],
            calling_conv: CallingConv::C,
        },
        Inst::InvokeIndirect {
            callee: v(4),
            sig: FuncTyId::new(1),
            args: vec![v(1)],
            calling_conv: CallingConv::C,
            normal_dest: BlockId::new(2),
            normal_args: vec![],
            unwind_dest: BlockId::new(3),
        },
    ] {
        assert!(matches!(
            &check(&m, &f, inst)[..],
            [ValidationError::InvalidHandleUse { .. }]
        ));
    }
}
#[test]
fn semantic_call_branch_return_transport_stays_separate_from_full_signature_and_edge_validation() {
    let (m, f) = fixture();
    for inst in [
        Inst::Call {
            callee: FuncId::new(999),
            args: vec![v(1), v(2)],
        },
        Inst::CallCannotUnwind {
            callee: FuncId::new(999),
            args: vec![v(1), v(2)],
        },
        Inst::Return {
            values: vec![v(1), v(2)],
        },
        Inst::Br {
            target: BlockId::new(99),
            args: vec![v(1), v(2)],
        },
    ] {
        assert!(check(&m, &f, inst).is_empty());
    }
}
#[test]
fn conditional_branch_and_switch_selectors_cannot_be_nominal_values() {
    let (m, f) = fixture();
    for value in [1, 2, 3] {
        let out = check(
            &m,
            &f,
            Inst::CondBr {
                cond: v(value),
                then_target: BlockId::new(2),
                then_args: vec![],
                else_target: BlockId::new(3),
                else_args: vec![],
            },
        );
        assert!(!out.is_empty());
        let out = check(
            &m,
            &f,
            Inst::Switch {
                value: v(value),
                default: BlockId::new(2),
                default_args: vec![],
                cases: vec![],
                exhaustive_enum_unreachable: false,
            },
        );
        assert!(!out.is_empty());
    }
}
#[test]
fn actual_sealed_access_success_and_missing_analysis_reason_are_preserved() {
    let (m, f) = fixture();
    let node = &f.blocks[0].body[2];
    assert!(
        run(&m, &f, node, (f.entry, 2), false, true, "L")
            .0
            .is_empty()
    );
    let out = run(&m, &f, node, (f.entry, 2), false, false, "L").0;
    assert!(
        matches!(&out[..],[ValidationError::InvalidHandleUse{detail,..}] if detail.contains("not a sealed handle slot"))
    );
}
#[test]
fn dialect_operations_accept_dialect_only_and_cannot_bypass_handle_origin_rule() {
    let (m, f) = fixture();
    let mut op = trust_ir::dialect::DialectInst::new("ns", "op");
    op.operands = vec![v(2)];
    assert!(check(&m, &f, Inst::DialectOp(Box::new(op.clone()))).is_empty());
    op.operands.push(v(1));
    assert!(matches!(
        &check(&m, &f, Inst::DialectOp(Box::new(op)))[..],
        [ValidationError::InvalidHandleUse { .. }]
    ));
}
#[test]
fn every_actual_result_and_operand_is_noted_after_inline_family_bits_are_already_true() {
    let (m, f) = fixture();
    let short = InstrNode::new(Inst::Return {
        values: vec![v(1), v(2)],
    });
    let mut long = short.clone();
    long.results = vec![v(1), v(2), v(1), v(99)];
    let (a, oa, ba, ea) = run(&m, &f, &short, (f.entry, 3), false, false, "L");
    let (b, ob, bb, eb) = run(&m, &f, &long, (f.entry, 3), false, false, "L");
    assert_eq!(a, b);
    assert!(eb - bb > ea - ba);
    assert!(
        ob.events[bb..eb].iter().map(|e| e.work).sum::<usize>()
            > oa.events[ba..ea].iter().map(|e| e.work).sum::<usize>()
    );
    let mut only_result = InstrNode::new(Inst::Undef { ty: Ty::Bool });
    only_result.results = vec![v(1)];
    assert!(matches!(
        &run(&m, &f, &only_result, (f.entry, 3), false, false, "L").0[..],
        [ValidationError::InvalidHandleUse { .. }]
    ));
}
#[test]
fn full_raw_location_and_last_definition_map_are_preserved_without_normalization() {
    let (m, mut f) = fixture();
    let location = "λ\0尾\n".repeat(2000);
    let node = InstrNode::new(Inst::Undef { ty: handle() });
    let out = run(&m, &f, &node, (f.entry, 3), false, false, &location).0;
    assert!(
        matches!(&out[..],[ValidationError::InvalidHandleUse{location:actual,..}] if actual==&location)
    );
    f.blocks[0]
        .body
        .push(InstrNode::new(Inst::Undef { ty: Ty::Bool }).with_result(v(1)));
    assert!(check(&m, &f, Inst::Return { values: vec![v(1)] }).is_empty());
}
