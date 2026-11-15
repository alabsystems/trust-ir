// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

#[test]
fn every_original_module_surface_is_exact_with_globals_before_drop_and_no_align_error() {
    let locations = [
        "type ty.0",
        "functy.0 param 0",
        "functy.0 return 0",
        "global 'G'",
        "drop_glue row 0",
        "struct @S field 'sf'",
        "record @R field 'rf'",
        "enum @E variant 'V' field 0",
        "closurety.0 capture 0",
    ];
    let mut expected = vec![];
    for location in locations {
        expected.push(module_error(location, ZERO));
        expected.push(module_error(location, LANE));
    }
    assert_eq!(module_parity(&fixture()), expected);
}

#[test]
fn physical_table_parameter_return_drop_and_capture_positions_keep_decimal_text() {
    let mut module = fixture();
    module.types.splice(0..0, vec![Ty::Bool; 12]);
    module.func_types[0].params.splice(0..0, vec![Ty::Bool; 12]);
    module.func_types[0]
        .returns
        .splice(0..0, vec![Ty::Bool; 13]);
    module.func_types.splice(
        0..0,
        vec![
            FuncTy {
                params: vec![],
                returns: vec![],
                abi: None,
                is_vararg: false
            };
            11
        ],
    );
    module.drop_glue.splice(
        0..0,
        (0..11).map(|i| DropGlueEntry {
            glue: FuncId::new(i),
            ty: Ty::Bool,
        }),
    );
    module.closure_types[0]
        .captures
        .splice(0..0, vec![Ty::Bool; 12]);
    module.closure_types.splice(
        0..0,
        vec![
            ClosureTy {
                func: FuncTyId::new(0),
                captures: vec![]
            };
            11
        ],
    );
    let errors = module_parity(&module);
    assert_eq!(errors[0], module_error("type ty.12", ZERO));
    assert_eq!(errors[2], module_error("functy.11 param 12", ZERO));
    assert_eq!(errors[4], module_error("functy.11 return 13", ZERO));
    assert_eq!(errors[8], module_error("drop_glue row 11", ZERO));
    assert_eq!(errors[16], module_error("closurety.11 capture 12", ZERO));
}

#[test]
fn all_three_outer_reasons_precede_invalid_element_recursion_and_keep_block_identity() {
    let ty = Ty::Vector(Box::new(bad()), 0);
    assert_eq!(
        type_parity(&ty, u32::MAX),
        vec![
            block_error(u32::MAX, "<0 x <0 x ptr>>", ZERO),
            block_error(u32::MAX, "<0 x <0 x ptr>>", NESTED),
            block_error(u32::MAX, "<0 x <0 x ptr>>", LANE),
            block_error(u32::MAX, "<0 x ptr>", ZERO),
            block_error(u32::MAX, "<0 x ptr>", LANE),
        ]
    );
}

#[test]
fn exact_twelve_lane_types_accept_positive_counts_and_zero_emits_only_first_reason() {
    for element in [
        Ty::Bool,
        Ty::I8,
        Ty::I16,
        Ty::I32,
        Ty::I64,
        Ty::U8,
        Ty::U16,
        Ty::U32,
        Ty::U64,
        Ty::F16,
        Ty::F32,
        Ty::F64,
    ] {
        for lanes in [1, u32::MAX] {
            assert!(type_parity(&Ty::Vector(Box::new(element.clone()), lanes), 3).is_empty());
        }
        let ty = Ty::Vector(Box::new(element), 0);
        assert_eq!(
            type_parity(&ty, 3),
            vec![block_error(3, &ty.to_string(), ZERO)]
        );
    }
}

#[test]
fn size_char_128_refinement_pointer_and_other_nonlanes_remain_invalid() {
    for element in [
        Ty::I128,
        Ty::U128,
        Ty::Isize,
        Ty::Usize,
        Ty::Char,
        Ty::Ptr,
        Ty::Unit,
        Ty::Never,
        Ty::Error,
        Ty::Ref(Box::new(Ty::I32)),
        Ty::Refine(TyId::new(0), PredId::new(0)),
        Ty::Array(TyId::new(0), 4),
        Ty::Set(TyId::new(0), SetRepr::Boxed),
        Ty::Tuple(vec![]),
    ] {
        let ty = Ty::Vector(Box::new(element), 1);
        assert_eq!(
            type_parity(&ty, 4),
            vec![block_error(4, &ty.to_string(), LANE)]
        );
    }
}

#[test]
fn tuple_and_five_reference_wrappers_recurse_lazily_without_short_circuiting() {
    let ty = Ty::Tuple(vec![
        Ty::Ref(Box::new(bad())),
        Ty::RefMut(Box::new(bad())),
        Ty::PtrConst(Box::new(bad())),
        Ty::PtrMut(Box::new(bad())),
        Ty::Rc(Box::new(bad())),
        Ty::Tuple(vec![bad(), bad()]),
        Ty::Vector(Box::new(Ty::Tuple(vec![bad(), bad()])), 1),
    ]);
    assert_eq!(type_parity(&ty, 8).len(), 19);
}

#[test]
fn nominal_ids_and_function_instruction_attribute_surfaces_are_not_followed_by_module_pass() {
    let mut module = Module::new("excluded");
    module.types = vec![
        Ty::Array(TyId::new(0), 4),
        Ty::Set(TyId::new(0), SetRepr::Boxed),
        Ty::Sequence(TyId::new(0)),
        Ty::Refine(TyId::new(0), PredId::new(0)),
        Ty::Struct(StructId::new(0)),
        Ty::Record(RecordId::new(0)),
        Ty::Enum(EnumId::new(0)),
        Ty::Closure(ClosureTyId::new(0)),
        Ty::Func(FuncTyId::new(0)),
    ];
    let mut f = Function::new(FuncId::new(0), "ignored", FuncTyId::new(0), BlockId::new(0));
    let mut b = Block::new(BlockId::new(0));
    b.params.push((ValueId::new(0), bad()));
    let mut op = trust_ir::dialect::DialectInst::new("vector", "ignored");
    op.result_tys.push(bad());
    op.attrs.push(trust_ir::dialect::AttrEntry {
        name: "ignored".into(),
        value: trust_ir::dialect::AttrValue::Ty(bad()),
    });
    b.body = vec![
        InstrNode::new(Inst::Undef { ty: bad() }),
        InstrNode::new(Inst::DialectOp(Box::new(op))),
    ];
    f.blocks.push(b);
    module.functions.push(f);
    assert!(module_parity(&module).is_empty());
}

#[test]
fn raw_long_names_and_handle_dialect_type_display_match_original_diagnostics() {
    let name = "λ'\n\0🦀".repeat(700);
    let mut module = fixture();
    module.globals[0].name = name.clone();
    module.structs[0].name = name.clone();
    module.structs[0].fields[0].name = name.clone();
    module.records[0].name = name.clone();
    module.records[0].fields[0].name = name.clone();
    module.enums[0].name = name.clone();
    module.enums[0].variants[0].name = name;
    module_parity(&module);
    for element in [
        Ty::Handle(Box::new(HandleTy::new(
            "'\"\\\n\u{300}λ".repeat(300),
            "runtime\0",
        ))),
        Ty::Dialect(Box::new(trust_ir::DialectTy::new(
            "λ\n".repeat(700),
            "raw'\0",
            u32::MAX,
        ))),
    ] {
        let ty = Ty::Vector(Box::new(element), u32::MAX);
        assert_eq!(
            type_parity(&ty, 3),
            vec![block_error(3, &ty.to_string(), LANE)]
        );
    }
}

#[test]
fn wide_duplicate_vectors_and_deep_borrowed_input_do_not_hide_later_reports() {
    let ty = Ty::Tuple(vec![bad(); 1024]);
    assert_eq!(type_parity(&ty, 2).len(), 2048);
    let mut ty = bad();
    for _ in 0..50_000 {
        ty = Ty::Ref(Box::new(ty));
    }
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_vector_type_observed(&ty, 2, &mut session, site()).unwrap(),
        vec![
            block_error(2, "<0 x ptr>", ZERO),
            block_error(2, "<0 x ptr>", LANE)
        ]
    );
    // Fixture input disposal is caller-owned, outside this constituent.
    while let Ty::Ref(child) = ty {
        ty = *child;
    }
}
