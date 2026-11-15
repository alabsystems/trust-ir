// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

#[test]
fn every_original_surface_preserves_full_cardinality_order_and_exact_diagnostics() {
    let mut expected = vec![
        poison("type ty.0"),
        poison("type ty.0"),
        poison("functy.0 param 0"),
        poison("functy.0 return 0"),
        poison("functy.0 return 0"),
        poison("drop_glue row 0"),
        poison("global 'G'"),
        poison("global 'G'"),
        ValidationError::GlobalAlignInvalid {
            global: "G".into(),
            align: 3,
        },
        poison("struct @S field 'sf'"),
        poison("record @R field 'rf'"),
        poison("enum @E variant 'V' field 0"),
        poison("enum @E variant 'V' field 0"),
        poison("closurety.0 capture 0"),
        poison("function 'F' bb42 param %99"),
    ];
    expected.extend(vec![poison("function 'F' bb42 instruction 0 (cast)"); 3]);
    expected.push(poison("function 'F' bb42 instruction 1 (dialect)"));
    expected.extend(vec![
        poison(
            "function 'F' bb42 instruction 1 (dialect) attr 'at'"
        );
        2
    ]);
    assert_eq!(expected.len(), 21);
    assert_eq!(parity(&fixture()), expected);
}

#[test]
fn all_seven_recursive_containers_visit_every_error_after_an_earlier_hit() {
    let mut module = Module::new("containers");
    module.types = vec![
        Ty::Error,
        Ty::Vector(Box::new(Ty::Error), 0),
        Ty::Ref(Box::new(Ty::Error)),
        Ty::RefMut(Box::new(Ty::Error)),
        Ty::PtrConst(Box::new(Ty::Error)),
        Ty::PtrMut(Box::new(Ty::Error)),
        Ty::Rc(Box::new(Ty::Error)),
        Ty::Tuple(vec![
            Ty::Error,
            Ty::Tuple(vec![Ty::Error; 2]),
            Ty::Bool,
            Ty::Error,
        ]),
    ];
    let errors = parity(&module);
    assert_eq!(errors.len(), 11);
    assert_eq!(&errors[7..], &vec![poison("type ty.7"); 4]);
}

#[test]
fn table_ids_refinements_and_non_type_metadata_do_not_add_occurrences() {
    let mut module = Module::new("excluded");
    module.types = vec![
        Ty::Error,
        Ty::Array(TyId::new(0), 100),
        Ty::Set(TyId::new(0), SetRepr::Boxed),
        Ty::Sequence(TyId::new(0)),
        Ty::Refine(TyId::new(0), PredId::new(0)),
        Ty::Struct(StructId::new(0)),
        Ty::Record(RecordId::new(0)),
        Ty::Enum(EnumId::new(0)),
        Ty::Closure(ClosureTyId::new(0)),
        Ty::Func(FuncTyId::new(0)),
    ];
    let mut dialect = trust_ir::dialect::DialectInst::new("error", "error");
    dialect.attrs = vec![
        trust_ir::dialect::AttrEntry {
            name: "error".into(),
            value: trust_ir::dialect::AttrValue::Str("error".repeat(1000)),
        },
        trust_ir::dialect::AttrEntry {
            name: "error".into(),
            value: trust_ir::dialect::AttrValue::Bytes(vec![0; 1000]),
        },
    ];
    module.functions.push(function(
        "error",
        vec![],
        vec![
            Inst::Const {
                ty: Ty::U8,
                value: Constant::SymbolAddr {
                    symbol: "error".into(),
                    addend: 0,
                },
            },
            Inst::DialectOp(Box::new(dialect)),
        ],
    ));
    assert_eq!(parity(&module), vec![poison("type ty.0")]);
}

#[test]
fn actual_inline_pairs_drop_frames_and_top_level_attribute_types_keep_separate_order() {
    let mut module = Module::new("inline");
    let mut dialect = trust_ir::dialect::DialectInst::new("inline", "types");
    dialect.result_tys = vec![Ty::Error; 2];
    dialect.attrs = vec![
        trust_ir::dialect::AttrEntry {
            name: "skip".into(),
            value: trust_ir::dialect::AttrValue::Bool(true),
        },
        trust_ir::dialect::AttrEntry {
            name: "a".into(),
            value: trust_ir::dialect::AttrValue::Ty(Ty::Error),
        },
        trust_ir::dialect::AttrEntry {
            name: "a".into(),
            value: trust_ir::dialect::AttrValue::Ty(Ty::Tuple(vec![Ty::Error; 2])),
        },
    ];
    module.functions.push(function(
        "inline",
        vec![],
        vec![
            Inst::PtrFromParts {
                ptr_ty: Ty::Error,
                metadata_ty: Ty::Error,
                data: ValueId::new(0),
                metadata: ValueId::new(1),
            },
            Inst::Drop {
                ty: Ty::Error,
                ptr: ValueId::new(0),
            },
            Inst::OpenFrame {
                def: BindingFrameDef::new(
                    BindingFrameId::new(0),
                    "ignored",
                    vec![
                        BindingSlot::new("first", Ty::Error),
                        BindingSlot::new("second", Ty::Error),
                    ],
                ),
            },
            Inst::DialectOp(Box::new(dialect)),
        ],
    ));
    let errors = parity(&module);
    assert_eq!(errors.len(), 10);
    assert_eq!(
        errors[0],
        poison("function 'inline' bb42 instruction 0 (ptr_from_parts)")
    );
    assert_eq!(
        errors[9],
        poison("function 'inline' bb42 instruction 3 (dialect) attr 'a'")
    );
}

#[test]
fn global_alignment_boundary_and_error_occurrences_keep_original_interleaving() {
    let mut module = Module::new("align");
    for (i, align) in [
        None,
        Some(0),
        Some(1),
        Some(2),
        Some(3),
        Some(4),
        Some(u32::MAX),
        Some(1 << 31),
    ]
    .into_iter()
    .enumerate()
    {
        module
            .globals
            .push(global(&i.to_string(), Ty::Error, align));
    }
    let errors = parity(&module);
    assert_eq!(errors.len(), 11);
    assert_eq!(
        errors[2],
        ValidationError::GlobalAlignInvalid {
            global: "1".into(),
            align: 0
        }
    );
    assert_eq!(
        errors[6],
        ValidationError::GlobalAlignInvalid {
            global: "4".into(),
            align: 3
        }
    );
    assert_eq!(
        errors[9],
        ValidationError::GlobalAlignInvalid {
            global: "6".into(),
            align: u32::MAX
        }
    );
}

#[test]
fn raw_names_utf8_and_value_id_positions_are_copied_verbatim() {
    let name = "λ'\n\0🦀".repeat(700);
    let mut module = Module::new("names");
    module.globals.push(global(&name, Ty::Error, Some(0)));
    let mut f = function(
        &name,
        vec![(ValueId::new(u32::MAX), Ty::Error)],
        vec![Inst::Undef { ty: Ty::Error }],
    );
    f.blocks[0].id = BlockId::new(u32::MAX);
    module.functions.push(f);
    let errors = parity(&module);
    assert_eq!(errors[0], poison(&format!("global '{name}'")));
    assert_eq!(
        errors[1],
        ValidationError::GlobalAlignInvalid {
            global: name.clone(),
            align: 0
        }
    );
    assert_eq!(
        errors[2],
        poison(&format!(
            "function '{name}' bb{} param %{}",
            u32::MAX,
            u32::MAX
        ))
    );
}

#[test]
fn wide_error_lists_are_not_short_circuited_and_deep_input_is_only_borrowed() {
    let mut module = Module::new("wide");
    module.types.push(Ty::Tuple(vec![Ty::Error; 1024]));
    assert_eq!(parity(&module), vec![poison("type ty.0"); 1024]);
    let mut ty = Ty::Error;
    for _ in 0..50_000 {
        ty = Ty::Ref(Box::new(ty));
    }
    module.types.clear();
    module.types.push(ty);
    assert_eq!(observed(&module).0, vec![poison("type ty.0")]);
    let mut ty = module.types.pop().unwrap();
    // Caller-owned fixture disposal, not claimed as subject retirement.
    while let Ty::Ref(child) = ty {
        ty = *child;
    }
}

#[test]
fn empty_and_bodyless_surfaces_do_not_invent_diagnostics_or_id_traversal() {
    let mut module = Module::new("empty");
    module.functions.push(Function::new(
        FuncId::new(0),
        "declaration",
        FuncTyId::new(u32::MAX),
        BlockId::new(u32::MAX),
    ));
    assert!(parity(&module).is_empty());
}
