// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn empty_and_unrelated_instruction_paths_add_no_drop_diagnostics() {
    assert!(run(&Module::new("empty")).0.is_empty());
    assert!(
        run(&module(vec![
            Inst::Return { values: vec![] },
            Inst::Unreachable
        ]))
        .0
        .is_empty()
    );
}
#[test]
fn outer_refinement_has_priority_for_drop_and_dropinvoke_without_reading_its_base() {
    for invoke in [false, true] {
        let ty = Ty::Refine(TyId::new(u32::MAX), PredId::new(u32::MAX));
        let m = module(vec![drop_inst(ty.clone(), invoke)]);
        let (out, before, _) = run(&m);
        assert_eq!(out, vec![error("dropλ\0", 7, &type_reason(&ty, true))]);
        let mut other = m;
        other.types = vec![Ty::Error; 1000];
        let (_, after, _) = run(&other);
        assert_eq!(before.events, after.events);
    }
}
#[test]
fn documented_trivial_scalar_pointer_vector_tuple_and_array_spellings_are_refused() {
    for ty in [
        Ty::Unit,
        Ty::Bool,
        Ty::Char,
        Ty::Ptr,
        Ty::Ref(Box::new(Ty::Error)),
        Ty::Vector(Box::new(Ty::Error), 7),
        Ty::Func(FuncTyId::new(99)),
        Ty::Tuple(vec![]),
        Ty::Array(TyId::new(u32::MAX), 0),
    ] {
        for invoke in [false, true] {
            let out = run(&module(vec![drop_inst(ty.clone(), invoke)])).0;
            assert_eq!(out, vec![error("dropλ\0", 7, &type_reason(&ty, false))]);
        }
    }
}
#[test]
fn nontrivial_and_unresolved_drop_types_are_left_to_other_original_rules() {
    for ty in [
        Ty::Error,
        Ty::Struct(StructId::new(3)),
        Ty::Rc(Box::new(Ty::Unit)),
        Ty::handle("runtime", "owned"),
        Ty::Tuple(vec![Ty::U8, Ty::Error]),
        Ty::Array(TyId::new(99), 1),
    ] {
        for invoke in [false, true] {
            assert!(
                run(&module(vec![drop_inst(ty.clone(), invoke)]))
                    .0
                    .is_empty()
            );
        }
    }
    let ty = Ty::Struct(StructId::new(3));
    let mut m = module(vec![
        drop_inst(ty.clone(), false),
        drop_inst(ty.clone(), true),
    ]);
    register(&mut m, 7, ty);
    assert!(run(&m).0.is_empty());
}
#[test]
fn array_zero_dangling_cycles_and_completed_diamonds_keep_the_actual_predicate_answer() {
    let cases = [
        (Ty::Array(TyId::new(u32::MAX), 0), vec![], true),
        (Ty::Array(TyId::new(0), 1), vec![], false),
        (
            Ty::Array(TyId::new(0), 1),
            vec![Ty::Array(TyId::new(0), 1)],
            false,
        ),
        (
            Ty::Array(TyId::new(0), 1),
            vec![Ty::Array(TyId::new(1), 1), Ty::Array(TyId::new(0), 1)],
            false,
        ),
        (
            Ty::Tuple(vec![Ty::Array(TyId::new(0), 1), Ty::Array(TyId::new(0), 2)]),
            vec![Ty::U8],
            true,
        ),
    ];
    for (ty, types, refused) in cases {
        let mut m = module(vec![drop_inst(ty, false)]);
        m.types = types;
        assert_eq!(run(&m).0.len(), usize::from(refused));
    }
}
#[test]
fn all_six_registered_direct_call_and_panic_forms_have_exact_original_reasons() {
    for kind in 0..6 {
        let mut m = module(vec![direct(7, kind)]);
        register(&mut m, 7, Ty::Struct(StructId::new(3)));
        let what = match kind {
            0..=2 => "call",
            3 => "seq_map element call",
            _ => "panic-site entry",
        };
        assert_eq!(
            run(&m).0,
            vec![error("dropλ\0", 7, &direct_reason(7, what))]
        );
    }
}
#[test]
fn indirect_dynamic_dispatch_unsited_asserts_and_unregistered_targets_remain_allowed() {
    let mut m = module(vec![
        Inst::CallIndirect {
            callee: v(7),
            sig: FuncTyId::new(0),
            args: vec![],
            calling_conv: CallingConv::C,
        },
        Inst::CallIndirectCannotUnwind {
            callee: v(7),
            sig: FuncTyId::new(0),
            args: vec![],
            calling_conv: CallingConv::C,
        },
        Inst::InvokeIndirect {
            callee: v(7),
            sig: FuncTyId::new(0),
            args: vec![],
            calling_conv: CallingConv::C,
            normal_dest: BlockId::new(8),
            normal_args: vec![],
            unwind_dest: BlockId::new(9),
        },
        Inst::Assert {
            cond: v(1),
            kind: AssertKind::NullPtr,
            site: None,
        },
        direct(8, 0),
    ]);
    register(&mut m, 7, Ty::Error);
    assert!(run(&m).0.is_empty());
}
#[test]
fn duplicate_or_invalid_glue_keys_preserve_only_registered_function_membership() {
    let mut m = module(vec![direct(7, 0), direct(8, 1), direct(9, 2)]);
    register(&mut m, 7, Ty::Error);
    register(&mut m, 8, Ty::Error);
    register(&mut m, 7, Ty::Unit);
    let (out, before, _) = run(&m);
    assert_eq!(
        out,
        vec![
            error("dropλ\0", 7, &direct_reason(7, "call")),
            error("dropλ\0", 7, &direct_reason(8, "call"))
        ]
    );
    for row in &mut m.drop_glue {
        row.ty = Ty::Tuple(vec![Ty::Error; 1000]);
    }
    let (_, after, _) = run(&m);
    assert_eq!(before.events, after.events);
}
#[test]
fn physical_function_block_and_node_order_preserves_duplicate_ids_and_raw_names() {
    let mut m = module(vec![drop_inst(Ty::Unit, false), drop_inst(Ty::Bool, true)]);
    let mut second = m.functions[0].clone();
    second.name = "second尾".into();
    second.blocks[0].id = BlockId::new(u32::MAX);
    second.blocks[0].body = vec![InstrNode::new(direct(7, 0))];
    m.functions.push(second);
    register(&mut m, 7, Ty::Error);
    assert_eq!(
        run(&m).0,
        vec![
            error("dropλ\0", 7, &type_reason(&Ty::Unit, false)),
            error("dropλ\0", 7, &type_reason(&Ty::Bool, false)),
            error("second尾", u32::MAX, &direct_reason(7, "call"))
        ]
    );
}
#[test]
fn complete_unicode_function_type_and_full_u32_glue_text_reach_diagnostics() {
    let ty = Ty::Tuple(vec![Ty::U8; 600]);
    let mut m = module(vec![drop_inst(ty.clone(), false), direct(u32::MAX, 0)]);
    let name = "λ\0尾".repeat(1000) + "FUNCTIONTAIL";
    m.functions[0].name = name.clone();
    register(&mut m, u32::MAX, Ty::Error);
    assert_eq!(
        run(&m).0,
        vec![
            error(&name, 7, &type_reason(&ty, false)),
            error(&name, 7, &direct_reason(u32::MAX, "call"))
        ]
    );
}
