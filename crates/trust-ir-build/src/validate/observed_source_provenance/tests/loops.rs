// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn original_dominated_backedge_self_edge_and_unreachable_self_test_are_preserved() {
    let original = module();
    assert!(parity(&original.functions[0], Some(&original)).is_empty());
    for reachable in [false, true] {
        let mut module = original.clone();
        module.functions[0].blocks[1].body = vec![branch(1, &[2, 3])];
        if !reachable {
            module.functions[0].blocks[0].body = vec![branch(3, &[])];
        }
        seal(&mut module, rows());
        // The ordinary predicate admits latch.id==header even when unreachable.
        // This constituent must not silently strengthen that separate CFG rule.
        assert!(parity(&module.functions[0], Some(&module)).is_empty());
    }
    let mut bypass = original.clone();
    bypass.functions[0].blocks[0].body = vec![node(Inst::CondBr {
        cond: v(1),
        then_target: BlockId::new(1),
        then_args: vec![v(0), v(0)],
        else_target: BlockId::new(2),
        else_args: vec![v(0)],
    })];
    seal(&mut bypass, rows());
    assert_eq!(
        details(&parity(&bypass.functions[0], Some(&bypass))),
        vec!["bb1 is not a reachable natural-loop header with a dominated backedge"]
    );
}
#[test]
fn missing_entry_dangling_targets_and_nonterminal_tail_keep_fail_closed_cfg_answers() {
    let original = module();
    for case in 0..3 {
        let mut module = original.clone();
        match case {
            0 => module.functions[0].entry = BlockId::new(999),
            1 => module.functions[0].blocks[0].body = vec![branch(999, &[])],
            2 => module.functions[0].blocks[2].body.push(node(Inst::Const {
                ty: Ty::U32,
                value: Constant::Int(0),
            })),
            _ => unreachable!(),
        }
        seal(&mut module, rows());
        let errors = parity(&module.functions[0], Some(&module));
        assert_eq!(
            details(&errors)[0],
            "bb1 is not a reachable natural-loop header with a dominated backedge"
        );
        assert_eq!(errors.len(), if case == 0 { 2 } else { 1 });
        if case == 0 {
            assert_eq!(
                details(&errors)[1],
                "binding \"arg\" names missing function parameter 0"
            );
        }
    }
}
#[test]
fn switch_default_and_cases_and_all_four_invoke_normal_and_unwind_edges_count() {
    let panic = PanicSite {
        entry: FuncId::new(99),
        location: PanicLocation::Value(v(1)),
    };
    let mut instructions = vec![];
    for (normal, unwind) in [(1, 3), (3, 1)] {
        instructions.extend([
            Inst::Invoke {
                callee: FuncId::new(99),
                args: vec![],
                normal_dest: BlockId::new(normal),
                normal_args: vec![],
                unwind_dest: BlockId::new(unwind),
            },
            Inst::InvokeIndirect {
                callee: v(1),
                sig: FuncTyId::new(0),
                args: vec![],
                calling_conv: trust_ir::CallingConv::C,
                normal_dest: BlockId::new(normal),
                normal_args: vec![],
                unwind_dest: BlockId::new(unwind),
            },
            Inst::AssertInvoke {
                cond: v(1),
                kind: AssertKind::DivByZero,
                site: panic,
                normal_dest: BlockId::new(normal),
                normal_args: vec![],
                unwind_dest: BlockId::new(unwind),
            },
            Inst::DropInvoke {
                ty: Ty::U32,
                ptr: v(4),
                normal_dest: BlockId::new(normal),
                normal_args: vec![],
                unwind_dest: BlockId::new(unwind),
            },
        ]);
    }
    for (default, target) in [(1, 3), (3, 1)] {
        instructions.push(Inst::Switch {
            value: v(4),
            default: BlockId::new(default),
            default_args: vec![],
            exhaustive_enum_unreachable: false,
            cases: vec![SwitchCase {
                value: Constant::Int(0),
                target: BlockId::new(target),
                args: vec![],
            }],
        });
    }
    assert_eq!(instructions.len(), 10);
    for instruction in instructions {
        let mut module = module();
        module.functions[0].blocks[2].body = vec![node(instruction)];
        seal(&mut module, rows());
        assert!(parity(&module.functions[0], Some(&module)).is_empty());
    }
}
#[test]
fn first_physical_duplicate_entry_and_header_supply_parameter_counts() {
    let mut module = module();
    module.functions[0].blocks[1].body = vec![branch(1, &[2, 3])];
    module.functions[0].blocks[0].params.clear();
    let mut later = Block::new(BlockId::new(0));
    later.params.push((v(90), Ty::U32));
    later.body.push(node(Inst::Return { values: vec![] }));
    module.functions[0].blocks.push(later);
    seal(&mut module, rows());
    assert_eq!(
        details(&parity(&module.functions[0], Some(&module))),
        vec!["binding \"arg\" names missing function parameter 0"]
    );
    let mut module = super::module();
    module.functions[0].blocks[1].params.clear();
    module.functions[0].blocks[1].body = vec![node(Inst::Return { values: vec![] })];
    let mut later = Block::new(BlockId::new(1));
    later.params.push((v(91), Ty::U32));
    later.body.push(branch(1, &[91]));
    module.functions[0].blocks.push(later);
    seal(&mut module, rows());
    assert_eq!(
        details(&parity(&module.functions[0], Some(&module))),
        vec!["binding \"iter\" names missing bb1 loop parameter 0"]
    );
}
#[test]
fn row_ids_hir_headers_and_missing_header_checks_keep_order_and_skip_bad_binding_payloads() {
    let mut module = module();
    let mut source = rows().remove(0);
    source.source_loop_id = 7;
    source.hir_local_id = 42;
    source.header = BlockId::new(999);
    source.bindings = vec![binding(
        " \t",
        100,
        SourcePlace::FunctionParameter { index: u32::MAX },
    )];
    let mut second = source.clone();
    second.source_loop_id = 8;
    seal(&mut module, vec![source, second]);
    assert_eq!(
        details(&parity(&module.functions[0], Some(&module))),
        vec![
            "source-loop row 0 has id 7, expected dense ordered id 0",
            "source loop 7 names missing header bb999",
            "source-loop row 1 has id 8, expected dense ordered id 1",
            "source loop HIR local id 42 is duplicated",
            "TrustIR loop header bb999 is claimed by more than one source loop",
            "source loop 8 names missing header bb999",
        ]
    );
}
