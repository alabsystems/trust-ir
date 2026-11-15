// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! WS3.14 (F-056) part (a): niche enum layouts with an UNINHABITED variant.
//!
//! rustc lays out `enum E { A(char), B(!), C }` in 4 bytes: `A` is the untagged
//! variant (its `char` payload carries the niche), `C` takes the first invalid
//! `char` value `0x110000`, and `B` — which has no value — gets NO encoding at
//! all (`niche_variants = 2..=2`). The niche-coverage rule used to demand that
//! the interval plus the untagged variant cover EVERY variant, so the producer
//! had to decline the descriptor and fall back to the canonical tagged layout,
//! which is not rustc's.
//!
//! The rule is now: every INHABITED variant is the untagged variant or lies in
//! the niche interval. It is checked independently at three sites — the
//! validator, `shape`, and the interpreter — and each is tested separately
//! below, so a change that fixes only one of them fails here. Constructing an
//! uninhabited variant is refused by name (`UninhabitedVariantConstructed`), and
//! the interpreter refuses to decode a byte image that names one.
//!
//! Part (b) (`EnumTagRepr::{I128, U128}`) is a binary-version batch and is
//! deferred to its reserved version (WS8.5); its row stays a GAP ratchet here.

use trust_ir::inst::Inst;
use trust_ir::interpret::{InterpretValue, InterpretValueKind, Interpreter};
use trust_ir::node::InstrNode;
use trust_ir::ty::{
    EnumDef, EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr, EnumVariant, FieldDef, StructDef,
    StructRepr,
};
use trust_ir::value::{BlockId, EnumId, FuncId, StructId, ValueId};
use trust_ir::{
    Block, Constant, FuncTy, Function, Global, LayoutError, Linkage, Module, Ty, Visibility,
};
use trust_ir_build::validate::ValidationError;
use trust_ir_build::validate_module;

const E: EnumId = EnumId::new(0);
/// The first invalid `char` value: rustc's `niche_start` for a `char` lane.
const CHAR_NICHE: u128 = 0x11_0000;

fn v(i: u32) -> ValueId {
    ValueId::new(i)
}

fn variant(name: &str, fields: Vec<Ty>) -> EnumVariant {
    EnumVariant {
        name: name.into(),
        fields,
        field_names: Vec::new(),
    }
}

/// `enum E { A(char), B(<b_field>), C }` with rustc's niche descriptor for the
/// `B(!)` case: untagged `A`, niche interval `2..=2` (only `C`), `B` in
/// neither place.
fn e_def(b_field: Ty) -> EnumDef {
    let mut def = EnumDef::new(
        E,
        "E",
        vec![
            variant("A", vec![Ty::Char]),
            variant("B", vec![b_field]),
            variant("C", vec![]),
        ],
    );
    def.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Niche {
            untagged_variant: 0,
            niche_variants_start: 2,
            niche_variants_end: 2,
            niche_start: CHAR_NICHE,
            niche_offset: 0,
            niche_ty: EnumTagRepr::U32,
        },
        size: 4,
        align: 4,
        variant_field_offsets: vec![vec![0], vec![0], vec![]],
    });
    def
}

fn module_with(def: EnumDef) -> Module {
    let mut module = Module::new("ws3_14");
    module.add_enum(def);
    module
}

/// `fn f() -> E { let p = alloca E; *(p as *u32) = raw; *p }` — the
/// interpreter's decode direction, on a raw lane value.
fn decode_fn(module: &mut Module, raw: i128) -> FuncId {
    let id = FuncId::new(module.functions.len() as u32);
    let sig = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::Enum(E)],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(id, format!("decode_{raw:x}"), sig, BlockId::new(0));
    let mut blk = Block::new(BlockId::new(0));
    blk.body.push(
        InstrNode::new(Inst::Alloca {
            ty: Ty::U32,
            count: None,
            align: Some(4),
        })
        .with_result(v(0)),
    );
    blk.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U32,
            value: Constant::Int(raw),
        })
        .with_result(v(1)),
    );
    blk.body.push(InstrNode::new(Inst::Store {
        ty: Ty::U32,
        ptr: v(0),
        value: v(1),
        volatile: false,
        align: Some(4),
    }));
    blk.body.push(
        InstrNode::new(Inst::Load {
            ty: Ty::Enum(E),
            ptr: v(0),
            volatile: false,
            align: Some(4),
        })
        .with_result(v(2)),
    );
    blk.body
        .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
    f.blocks.push(blk);
    module
        .try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    id
}

/// `fn f() -> u32 { let p = alloca E; *p = <const>; *(p as *u32) }` — the
/// interpreter's encode direction, from an enum constant.
fn encode_fn(module: &mut Module, name: &str, value: Constant) -> FuncId {
    let id = FuncId::new(module.functions.len() as u32);
    let sig = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::U32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(id, name, sig, BlockId::new(0));
    let mut blk = Block::new(BlockId::new(0));
    blk.body.push(
        InstrNode::new(Inst::Alloca {
            ty: Ty::Enum(E),
            count: None,
            align: Some(4),
        })
        .with_result(v(0)),
    );
    blk.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::Enum(E),
            value,
        })
        .with_result(v(1)),
    );
    blk.body.push(InstrNode::new(Inst::Store {
        ty: Ty::Enum(E),
        ptr: v(0),
        value: v(1),
        volatile: false,
        align: Some(4),
    }));
    blk.body.push(
        InstrNode::new(Inst::Load {
            ty: Ty::U32,
            ptr: v(0),
            volatile: false,
            align: Some(4),
        })
        .with_result(v(2)),
    );
    blk.body
        .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
    f.blocks.push(blk);
    module
        .try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    id
}

fn layout_errors(errors: &[ValidationError]) -> Vec<String> {
    errors
        .iter()
        .map(ToString::to_string)
        .filter(|message| message.contains("layout"))
        .collect()
}

fn enum_value(module: &Module, func: FuncId) -> Vec<InterpretValue> {
    let out = Interpreter::with_module(module)
        .execute_func(func, [])
        .expect("executes");
    let InterpretValueKind::Aggregate(elems) = &out.returns[0].kind else {
        panic!("an enum value is an aggregate, got {:?}", out.returns[0]);
    };
    elems.clone()
}

// ─────────────────────────── the ported GAP row ───────────────────────────

/// Row `producer-rust-thir/enum-niche-uninhabited-variant`, now CLOSED: rustc's
/// niche descriptor for an enum with an uninhabited variant is accepted by the
/// validator, has a `shape` layout of rustc's size, and executes in the
/// interpreter — so the producer no longer has to decline it.
#[test]
fn producer_rust_thir_enum_niche_uninhabited_variant() {
    let mut module = module_with(e_def(Ty::Never));
    let c = decode_fn(&mut module, CHAR_NICHE as i128);
    assert_eq!(validate_module(&module), Vec::new());
    let shape = module.enum_layout_shape(E).expect("shape layout");
    assert_eq!((shape.size_bits, shape.align_bits), (32, 32));
    let elems = enum_value(&module, c);
    assert_eq!(elems[0].as_int().unwrap().as_unsigned(), 2, "decodes to C");
}

// ─────────────────────── positive: the three sites ───────────────────────

/// Site 1, the validator: the descriptor validates, with no layout error.
#[test]
fn validator_accepts_niche_descriptor_leaving_uninhabited_variant_unencoded() {
    let module = module_with(e_def(Ty::Never));
    assert_eq!(validate_module(&module), Vec::new());
}

/// Site 2, `shape`: the descriptor's size and alignment are the enum's layout
/// (rustc: `size_of::<E>() == 4`), through both layout queries.
#[test]
fn shape_lays_out_niche_descriptor_leaving_uninhabited_variant_unencoded() {
    let module = module_with(e_def(Ty::Never));
    let shape = module.enum_layout_shape(E).expect("enum layout");
    assert_eq!((shape.size_bits, shape.align_bits), (32, 32));
    assert!(shape.descriptor.is_some());
    let ty_shape = module.ty_layout_shape(&Ty::Enum(E)).expect("ty layout");
    assert_eq!(ty_shape.size_bytes(), Some(4));
}

/// Site 3, the interpreter: both directions of the byte funnel agree with
/// rustc's image — `C` is `0x110000`, `A('x')` is the char itself.
#[test]
fn interpreter_encodes_and_decodes_niche_enum_with_uninhabited_variant() {
    let mut module = module_with(e_def(Ty::Never));
    let c = decode_fn(&mut module, CHAR_NICHE as i128);
    let a = decode_fn(&mut module, 'x' as i128);
    let store_c = encode_fn(
        &mut module,
        "store_c",
        Constant::Aggregate(vec![Constant::Int(2)]),
    );
    let store_a = encode_fn(
        &mut module,
        "store_a",
        Constant::Aggregate(vec![Constant::Int(0), Constant::Int('x' as i128)]),
    );
    assert_eq!(validate_module(&module), Vec::new());

    let elems = enum_value(&module, c);
    assert_eq!(elems.len(), 1);
    assert_eq!(elems[0].as_int().unwrap().as_unsigned(), 2);
    let elems = enum_value(&module, a);
    assert_eq!(elems.len(), 2);
    assert_eq!(elems[0].as_int().unwrap().as_unsigned(), 0);
    assert_eq!(elems[1].as_int().unwrap().as_unsigned(), 'x' as u128);

    let interp = Interpreter::with_module(&module);
    let raw = |f| {
        interp.execute_func(f, []).expect("executes").returns[0]
            .as_int()
            .unwrap()
            .as_unsigned()
    };
    assert_eq!(raw(store_c), CHAR_NICHE);
    assert_eq!(raw(store_a), 'x' as u128);
}

// ─────────────────── negative twin: `B` inhabited (`B(u8)`) ───────────────────

/// The same descriptor with `B(u8)` leaves an INHABITED variant unencoded, and
/// each of the three sites still refuses it — with its own named reason.
#[test]
fn validator_refuses_niche_descriptor_leaving_inhabited_variant_unencoded() {
    let module = module_with(e_def(Ty::U8));
    let errors = layout_errors(&validate_module(&module));
    assert_eq!(errors.len(), 1, "{errors:#?}");
    assert!(
        errors[0].contains("cover every inhabited variant")
            && errors[0].contains(
                "inhabited variant 1 (B) is neither untagged 0 nor in niche interval 2..=2"
            ),
        "{}",
        errors[0]
    );
}

#[test]
fn shape_refuses_niche_descriptor_leaving_inhabited_variant_unencoded() {
    let module = module_with(e_def(Ty::U8));
    assert_eq!(
        module.enum_layout_shape(E).map(|shape| shape.size_bits),
        Err(LayoutError::EnumLayoutUnavailable(E))
    );
}

#[test]
fn interpreter_refuses_niche_descriptor_leaving_inhabited_variant_unencoded() {
    let mut module = module_with(e_def(Ty::U8));
    let c = decode_fn(&mut module, CHAR_NICHE as i128);
    let error = Interpreter::with_module(&module)
        .execute_func(c, [])
        .expect_err("an incoherent niche layout is refused");
    assert!(
        error.to_string().contains("incoherent niche encoding"),
        "{error}"
    );
}

/// A variant that is inhabited only THROUGH a nominal type is still judged:
/// `B(S)` with `struct S { x: u8 }` leaves an inhabited variant unencoded,
/// `B(S)` with `struct S { x: u8, n: ! }` does not. This is the validator's
/// coverage verdict; `shape` and the interpreter give no struct holding `!` a
/// byte layout at all (a struct field has no `!` rule), so for them the second
/// module stays refused — fail closed, for a reason other than coverage.
#[test]
fn uninhabitedness_is_read_through_a_struct_field() {
    for never_field in [false, true] {
        let mut fields = vec![FieldDef {
            name: "x".into(),
            ty: Ty::U8,
            offset: Some(0),
        }];
        if never_field {
            fields.push(FieldDef {
                name: "n".into(),
                ty: Ty::Never,
                offset: Some(1),
            });
        }
        let mut module = module_with(e_def(Ty::Struct(StructId::new(0))));
        module.add_struct(StructDef {
            id: StructId::new(0),
            name: "S".into(),
            fields,
            size: Some(1),
            align: Some(1),
            repr: StructRepr::Rust,
            origin: None,
        });
        let coverage_error = validate_module(&module)
            .iter()
            .any(|e| e.to_string().contains("cover every inhabited variant"));
        assert_eq!(coverage_error, !never_field, "never_field={never_field}");
        assert_eq!(
            module.variant_is_uninhabited(&module.enums[0].variants[1]),
            never_field
        );
    }
}

/// An uninhabited variant that still has a SIZED field — rustc's `B(u8, !)`,
/// which is not "absent" in rustc's sense but has no value — is exempt from
/// coverage too, at all three sites; its inhabited twin `B(u8, u8)` is refused
/// at all three.
#[test]
fn uninhabited_variant_with_a_sized_field_is_exempt_at_all_three_sites() {
    for (second, accepted) in [(Ty::Never, true), (Ty::U8, false)] {
        let mut def = e_def(Ty::U8);
        def.variants[1].fields.push(second.clone());
        if let Some(layout) = &mut def.layout {
            layout.variant_field_offsets[1] = vec![0, 1];
        }
        let mut module = module_with(def);
        let c = decode_fn(&mut module, CHAR_NICHE as i128);
        let coverage_error = validate_module(&module)
            .iter()
            .any(|e| e.to_string().contains("cover every inhabited variant"));
        assert_eq!(coverage_error, !accepted, "validator, second={second:?}");
        if accepted {
            assert_eq!(validate_module(&module), Vec::new());
        }
        assert_eq!(
            module.enum_layout_shape(E).is_ok(),
            accepted,
            "shape, second={second:?}"
        );
        assert_eq!(
            Interpreter::with_module(&module)
                .execute_func(c, [])
                .is_ok(),
            accepted,
            "interpreter, second={second:?}"
        );
    }
}

// ───────────────── mutation: constructing / decoding `B` ─────────────────

/// Constructing `B` through an `Inst::Const` aggregate is refused by name, and
/// the interpreter refuses the same construction on an unvalidated module.
#[test]
fn const_construction_of_uninhabited_variant_is_refused() {
    let mut module = module_with(e_def(Ty::Never));
    let store_b = encode_fn(
        &mut module,
        "store_b",
        Constant::Aggregate(vec![Constant::Int(1), Constant::Int(0)]),
    );
    let errors = validate_module(&module);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::UninhabitedVariantConstructed { enum_name, variant: 1, variant_name, location }
                if enum_name == "E" && variant_name == "B" && location.contains("store_b")
        )),
        "{errors:#?}"
    );
    let error = Interpreter::with_module(&module)
        .execute_func(store_b, [])
        .expect_err("the interpreter refuses to construct an uninhabited variant");
    assert!(
        error.to_string().contains("variant 1 is uninhabited"),
        "{error}"
    );
}

fn enum_global(initializer: Constant) -> Global {
    Global {
        name: "G".into(),
        ty: Ty::Enum(E),
        mutable: false,
        initializer: Some(initializer),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Visibility::Default,
        retained: false,
    }
}

/// A global initializer is the other constant funnel; it is refused the same way.
#[test]
fn global_initializer_constructing_uninhabited_variant_is_refused() {
    let mut module = module_with(e_def(Ty::Never));
    module.globals.push(enum_global(Constant::Aggregate(vec![
        Constant::Int(1),
        Constant::Int(0),
    ])));
    let errors = validate_module(&module);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::UninhabitedVariantConstructed { variant: 1, location, .. }
                if location.contains("global 'G'")
        )),
        "{errors:#?}"
    );
    // The twin: constructing an inhabited variant of the same enum is fine.
    let mut module = module_with(e_def(Ty::Never));
    module
        .globals
        .push(enum_global(Constant::Aggregate(vec![Constant::Int(2)])));
    assert_eq!(validate_module(&module), Vec::new());
}

/// rustc places an uninhabited variant INSIDE the niche interval when it sits
/// between two variants that need one (`enum G { A(char), C, B(!), D }` has
/// `niche_variants = 1..=3`). The layout is accepted; a byte image whose niche
/// value names `B` (`0x110001`) is an invalid value, refused on Load.
#[test]
fn interpreter_refuses_niche_image_naming_uninhabited_variant() {
    let mut def = EnumDef::new(
        E,
        "G",
        vec![
            variant("A", vec![Ty::Char]),
            variant("C", vec![]),
            variant("B", vec![Ty::Never]),
            variant("D", vec![]),
        ],
    );
    def.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Niche {
            untagged_variant: 0,
            niche_variants_start: 1,
            niche_variants_end: 3,
            niche_start: CHAR_NICHE,
            niche_offset: 0,
            niche_ty: EnumTagRepr::U32,
        },
        size: 4,
        align: 4,
        variant_field_offsets: vec![vec![0], vec![], vec![0], vec![]],
    });
    let mut module = module_with(def);
    let c = decode_fn(&mut module, CHAR_NICHE as i128);
    let b = decode_fn(&mut module, CHAR_NICHE as i128 + 1);
    let d = decode_fn(&mut module, CHAR_NICHE as i128 + 2);
    assert_eq!(validate_module(&module), Vec::new());
    assert!(module.enum_layout_shape(E).is_ok());
    assert_eq!(enum_value(&module, c)[0].as_int().unwrap().as_unsigned(), 1);
    assert_eq!(enum_value(&module, d)[0].as_int().unwrap().as_unsigned(), 3);
    let error = Interpreter::with_module(&module)
        .execute_func(b, [])
        .expect_err("a niche value naming an uninhabited variant is invalid");
    assert!(
        error.to_string().contains("Load: enum")
            && error.to_string().contains("variant 2 is uninhabited"),
        "{error}"
    );
}

/// The direct-tag twin: `enum H { A(u32), B(!) }` with its tag after the
/// payload. A tag byte equal to `B`'s discriminant is refused on Load; `A`'s
/// is not.
#[test]
fn interpreter_refuses_direct_tag_naming_uninhabited_variant() {
    let mut def = EnumDef::new(
        E,
        "H",
        vec![variant("A", vec![Ty::U32]), variant("B", vec![Ty::Never])],
    );
    def.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Direct { tag_offset: 4 },
        size: 8,
        align: 4,
        variant_field_offsets: vec![vec![0], vec![0]],
    });
    let mut module = module_with(def);
    let sig = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::Enum(E)],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut build = |id: u32, tag: i128| {
        let mut f = Function::new(FuncId::new(id), format!("h{tag}"), sig, BlockId::new(0));
        let mut blk = Block::new(BlockId::new(0));
        blk.body.push(
            InstrNode::new(Inst::Alloca {
                ty: Ty::U64,
                count: None,
                align: Some(8),
            })
            .with_result(v(0)),
        );
        blk.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::U64,
                // Payload 7 in bytes 0..4, tag in byte 4.
                value: Constant::Int((tag << 32) | 7),
            })
            .with_result(v(1)),
        );
        blk.body.push(InstrNode::new(Inst::Store {
            ty: Ty::U64,
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: Some(8),
        }));
        blk.body.push(
            InstrNode::new(Inst::Load {
                ty: Ty::Enum(E),
                ptr: v(0),
                volatile: false,
                align: Some(4),
            })
            .with_result(v(2)),
        );
        blk.body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        f.blocks.push(blk);
        module
            .try_add_function(f)
            .expect("Module::try_add_function: test fixture");
    };
    build(0, 0);
    build(1, 1);
    assert_eq!(validate_module(&module), Vec::new());
    let elems = enum_value(&module, FuncId::new(0));
    assert_eq!(elems[1].as_int().unwrap().as_unsigned(), 7);
    let error = Interpreter::with_module(&module)
        .execute_func(FuncId::new(1), [])
        .expect_err("a direct tag naming an uninhabited variant is invalid");
    assert!(
        error.to_string().contains("variant 1 is uninhabited"),
        "{error}"
    );
}

// ─────────────── adversarial review: nesting and field spellings ───────────────

const OPT: EnumId = EnumId::new(1);

/// `Option<E>` over rustc's `E`: `None` takes the NEXT invalid `char`,
/// `0x110001` — rustc's `size_of::<Option<E>>() == 4`.
fn option_of_e_module() -> Module {
    let mut module = module_with(e_def(Ty::Never));
    let mut opt = EnumDef::new(
        OPT,
        "Option<E>",
        vec![variant("None", vec![]), variant("Some", vec![Ty::Enum(E)])],
    );
    opt.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Niche {
            untagged_variant: 1,
            niche_variants_start: 0,
            niche_variants_end: 0,
            niche_start: CHAR_NICHE + 1,
            niche_offset: 0,
            niche_ty: EnumTagRepr::U32,
        },
        size: 4,
        align: 4,
        variant_field_offsets: vec![vec![], vec![0]],
    });
    module.add_enum(opt);
    module
}

/// `decode_fn`, loading the lane as `Option<E>` instead of `E`.
fn decode_option_fn(module: &mut Module, raw: i128) -> FuncId {
    let id = decode_fn(module, raw);
    let sig = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::Enum(OPT)],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let func = module
        .functions
        .iter_mut()
        .find(|func| func.id == id)
        .expect("just added");
    func.ty = sig;
    for node in &mut func.blocks[0].body {
        if let Inst::Load { ty, .. } = &mut node.inst {
            *ty = Ty::Enum(OPT);
        }
    }
    id
}

/// The legitimate module a producer emits once it stops declining: rustc's `E`
/// NESTED in `Option<E>` (the finding's own test idea). The inner descriptor is
/// consumed through the outer one at all three sites — the validator accepts,
/// `shape` sizes it at rustc's 4 bytes, and the interpreter decodes `None`,
/// `Some(C)` and `Some(A('x'))` from their rustc images.
#[test]
fn option_of_niche_enum_with_uninhabited_variant_is_accepted_at_all_three_sites() {
    let mut module = option_of_e_module();
    let none = decode_option_fn(&mut module, CHAR_NICHE as i128 + 1);
    let some_c = decode_option_fn(&mut module, CHAR_NICHE as i128);
    let some_a = decode_option_fn(&mut module, 'x' as i128);
    assert_eq!(validate_module(&module), Vec::new());
    let shape = module.enum_layout_shape(OPT).expect("Option<E> layout");
    assert_eq!((shape.size_bits, shape.align_bits), (32, 32));

    let tag = |value: &InterpretValue| value.as_int().unwrap().as_unsigned();
    let elems = enum_value(&module, none);
    assert_eq!((elems.len(), tag(&elems[0])), (1, 0), "None");
    let elems = enum_value(&module, some_c);
    let InterpretValueKind::Aggregate(inner) = &elems[1].kind else {
        panic!("Some carries an E: {elems:?}");
    };
    assert_eq!((tag(&elems[0]), tag(&inner[0])), (1, 2), "Some(C)");
    let elems = enum_value(&module, some_a);
    let InterpretValueKind::Aggregate(inner) = &elems[1].kind else {
        panic!("Some carries an E: {elems:?}");
    };
    assert_eq!(
        (tag(&elems[0]), tag(&inner[0]), tag(&inner[1])),
        (1, 0, 'x' as u128),
        "Some(A('x'))"
    );
}

/// Constructing the uninhabited variant NESTED inside another enum constant
/// (`Some(B(..))`) is refused by name too — the construction check is part of
/// the typed constant walk, not a top-level-only test.
#[test]
fn nested_construction_of_uninhabited_variant_is_refused() {
    let mut module = option_of_e_module();
    let mut global = enum_global(Constant::Aggregate(vec![
        Constant::Int(1),
        Constant::Aggregate(vec![Constant::Int(1), Constant::Int(0)]),
    ]));
    global.ty = Ty::Enum(OPT);
    module.globals.push(global);
    let errors = validate_module(&module);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::UninhabitedVariantConstructed { enum_name, variant: 1, .. }
                if enum_name == "E"
        )),
        "{errors:#?}"
    );
}

/// A pointer to `!` HAS values (rustc: `&!` is inhabited for layout), and so
/// does `[!; 0]`: `B(&!)` / `B([!; 0])` leave an inhabited variant unencoded,
/// so the exemption must NOT fire for them.
#[test]
fn pointer_to_never_and_empty_never_array_are_not_exempt() {
    let mut types = Module::new("types");
    let never = types
        .add_type(Ty::Never)
        .expect("Module::add_type: test fixture");
    for field in [Ty::Ref(Box::new(Ty::Never)), Ty::Array(never, 0)] {
        let mut module = module_with(e_def(field.clone()));
        module.types = types.types.clone();
        assert!(!module.variant_is_uninhabited(&module.enums[0].variants[1]));
        let errors = layout_errors(&validate_module(&module));
        assert!(
            errors.iter().any(|e| e.contains(
                "inhabited variant 1 (B) is neither untagged 0 nor in niche interval 2..=2"
            )),
            "{field:?}: {errors:#?}"
        );
        assert!(module.enum_layout_shape(E).is_err(), "{field:?}");
    }
}

/// Only a DIRECT `!` field has a descriptor layout (size 0, align 1). An
/// uninhabited variant spelled through `[!; 2]` is exempt from coverage, but
/// that field has no alignment, and `shape` and the interpreter both refuse the
/// enum — so the validator refuses it too, by name, instead of accepting a
/// layout no consumer can compute (the three sites disagreed before this).
#[test]
fn alignment_free_non_never_field_is_refused_at_all_three_sites() {
    let mut module = module_with(e_def(Ty::U8));
    let never = module
        .add_type(Ty::Never)
        .expect("Module::add_type: test fixture");
    module.enums[0].variants[1].fields = vec![Ty::Array(never, 2)];
    let c = decode_fn(&mut module, CHAR_NICHE as i128);
    assert!(module.variant_is_uninhabited(&module.enums[0].variants[1]));
    let errors = layout_errors(&validate_module(&module));
    assert_eq!(errors.len(), 1, "{errors:#?}");
    assert!(
        errors[0].contains("variant 1 field 0 to have a byte alignment")
            && errors[0].contains("has no alignment"),
        "{}",
        errors[0]
    );
    assert_eq!(
        module.enum_layout_shape(E).map(|shape| shape.size_bits),
        Err(LayoutError::EnumLayoutUnavailable(E))
    );
    assert!(
        Interpreter::with_module(&module)
            .execute_func(c, [])
            .is_err()
    );
    // Mutation control: the direct `!` spelling of the same variant is accepted.
    let module = module_with(e_def(Ty::Never));
    assert_eq!(validate_module(&module), Vec::new());
}

/// The interpreter's ENCODE direction refuses an uninhabited variant however
/// the in-register value was reached — a route that never passes through the
/// `Const` refusal. `Store` must not write an image for it.
///
/// Two routes are pinned. (1) Overwriting the tag of an `A` value with `B`'s
/// discriminant (`InsertField` at field 0): since WS2.2 the interpreter refuses
/// that re-tag itself as undefined behaviour ("insert_field cannot rewrite an
/// enum discriminant"), so the forged value never reaches `Store` — asserted
/// here so the route stays closed. (2) A forged `B` value handed in as an
/// ENTRY ARGUMENT (the call boundary checks the value's type, not which
/// variant it names), which does reach `Store` and must be refused there.
#[test]
fn interpreter_store_refuses_a_forged_uninhabited_variant_value() {
    let mut module = module_with(e_def(Ty::Never));
    let sig = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::Enum(E)],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    // f0: `forge_b` — the (now closed) InsertField re-tag route.
    let mut f = Function::new(FuncId::new(0), "forge_b", sig, BlockId::new(0));
    let mut blk = Block::new(BlockId::new(0));
    blk.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::Enum(E),
            value: Constant::Aggregate(vec![Constant::Int(0), Constant::Int('x' as i128)]),
        })
        .with_result(v(0)),
    );
    blk.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U8,
            value: Constant::Int(1),
        })
        .with_result(v(1)),
    );
    blk.body.push(
        InstrNode::new(Inst::InsertField {
            ty: Ty::Enum(E),
            aggregate: v(0),
            field: 0,
            value: v(1),
        })
        .with_result(v(2)),
    );
    blk.body
        .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
    f.blocks.push(blk);
    module
        .try_add_function(f)
        .expect("Module::try_add_function: test fixture");

    // f1: `make_a` — an honest `A('x')`, the seed the forged value is cut from.
    let mut f = Function::new(FuncId::new(1), "make_a", sig, BlockId::new(0));
    let mut blk = Block::new(BlockId::new(0));
    blk.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::Enum(E),
            value: Constant::Aggregate(vec![Constant::Int(0), Constant::Int('x' as i128)]),
        })
        .with_result(v(0)),
    );
    blk.body
        .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
    f.blocks.push(blk);
    module
        .try_add_function(f)
        .expect("Module::try_add_function: test fixture");

    // f2: `store_e(e: E)` — writes its argument's image to a fresh slot.
    let store_sig = module
        .add_func_type(FuncTy {
            params: vec![Ty::Enum(E)],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(2), "store_e", store_sig, BlockId::new(0));
    let mut blk = Block::new(BlockId::new(0));
    blk.params.push((v(0), Ty::Enum(E)));
    blk.body.push(
        InstrNode::new(Inst::Alloca {
            ty: Ty::Enum(E),
            count: None,
            align: Some(4),
        })
        .with_result(v(1)),
    );
    blk.body.push(InstrNode::new(Inst::Store {
        ty: Ty::Enum(E),
        ptr: v(1),
        value: v(0),
        volatile: false,
        align: Some(4),
    }));
    blk.body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    f.blocks.push(blk);
    module
        .try_add_function(f)
        .expect("Module::try_add_function: test fixture");

    let interpreter = Interpreter::with_module(&module);

    // Route (1): the re-tag is refused before any image exists.
    let error = interpreter
        .execute_func(FuncId::new(0), [])
        .expect_err("the InsertField re-tag of an A value is refused");
    assert!(
        error
            .to_string()
            .contains("insert_field cannot rewrite an enum discriminant"),
        "{error}"
    );

    // Route (2): a forged `B` value reaches `Store` as an argument.
    let seed = interpreter
        .execute_func(FuncId::new(1), [])
        .expect("make_a executes")
        .returns
        .remove(0);
    // Control: the honest `A` value stores.
    interpreter
        .execute_func(FuncId::new(2), [seed.clone()])
        .expect("Store of an honest A value succeeds");
    let InterpretValueKind::Aggregate(mut lanes) = seed.kind.clone() else {
        panic!("an enum value is an aggregate, got {seed:?}");
    };
    lanes[0] = InterpretValue::int(lanes[0].ty.clone(), 1).expect("tag lane is an integer");
    let forged = InterpretValue {
        ty: seed.ty.clone(),
        kind: InterpretValueKind::Aggregate(lanes),
    };
    let error = interpreter
        .execute_func(FuncId::new(2), [forged])
        .expect_err("Store of a forged uninhabited-variant value is refused");
    assert!(
        error.to_string().contains("Store: enum")
            && error.to_string().contains("variant 1 is uninhabited"),
        "{error}"
    );
}

// ─────────────────────────── the predicate ───────────────────────────

#[test]
fn ty_is_uninhabited_is_sound_and_cycle_guarded() {
    let mut module = Module::new("predicate");
    let never = module
        .add_type(Ty::Never)
        .expect("Module::add_type: test fixture");
    // struct S0 { n: ! }, struct S1 { s: S1 } (a by-value cycle), struct S2 { p: *const ! }
    for (id, name, ty) in [
        (0, "S0", Ty::Never),
        (1, "S1", Ty::Struct(StructId::new(1))),
        (2, "S2", Ty::PtrConst(Box::new(Ty::Never))),
    ] {
        module.add_struct(StructDef {
            id: StructId::new(id),
            name: name.into(),
            fields: vec![FieldDef {
                name: "f".into(),
                ty,
                offset: None,
            }],
            size: None,
            align: None,
            repr: StructRepr::Rust,
            origin: None,
        });
    }
    // enum Void {}, enum AllVoid { X(S0), Y(S0) }, enum Some_ { X(S0), Y }
    module.add_enum(EnumDef::new(EnumId::new(0), "Void", vec![]));
    module.add_enum(EnumDef::new(
        EnumId::new(1),
        "AllVoid",
        vec![
            variant("X", vec![Ty::Struct(StructId::new(0))]),
            variant("Y", vec![Ty::Struct(StructId::new(0))]),
        ],
    ));
    module.add_enum(EnumDef::new(
        EnumId::new(2),
        "Inhabited",
        vec![
            variant("X", vec![Ty::Struct(StructId::new(0))]),
            variant("Y", vec![]),
        ],
    ));

    let s = |i| Ty::Struct(StructId::new(i));
    for (ty, expected) in [
        (Ty::Never, true),
        (Ty::Unit, false),
        (Ty::U8, false),
        (Ty::Tuple(vec![Ty::U8, Ty::Never]), true),
        (Ty::Tuple(vec![s(0), s(0)]), true),
        (Ty::Array(never, 0), false),
        (Ty::Array(never, 3), true),
        (Ty::Ref(Box::new(Ty::Never)), false),
        (Ty::PtrConst(Box::new(Ty::Never)), false),
        (s(0), true),
        (s(1), false), // cycle: conservatively inhabited
        (s(2), false),
        (s(9), false), // unresolvable: conservatively inhabited
        (Ty::Enum(EnumId::new(0)), true),
        (Ty::Enum(EnumId::new(1)), true),
        (Ty::Enum(EnumId::new(2)), false),
    ] {
        assert_eq!(module.ty_is_uninhabited(&ty), expected, "{ty:?}");
    }
    assert!(module.variant_is_uninhabited(&variant("B", vec![Ty::U8, s(0)])));
    assert!(!module.variant_is_uninhabited(&variant("B", vec![Ty::U8])));
    assert!(!module.variant_is_uninhabited(&variant("C", vec![])));
}

// ──────────── part (b) — deferred wire batch, still a GAP ratchet ────────────

/// Row `producer-rust-thir/enum-repr-128`: STILL A GAP. `EnumTagRepr` has no
/// 128-bit member (part (b) of WS3.14 is a binary-version batch, deferred to its
/// reserved version under WS8.5), so a discriminant beyond the 64-bit tag cap has
/// no canonical tag and the def is refused. This row asserts the CURRENT outcome
/// exactly; the increment that adds `EnumTagRepr::{I128, U128}` flips it.
#[test]
fn producer_rust_thir_enum_repr_128() {
    let def = EnumDef::new(E, "Big", vec![variant("A", vec![]), variant("B", vec![])])
        .with_discriminants(vec![Some(0), Some(1i128 << 64)]);
    assert_eq!(def.canonical_tag_repr(), None);
    let module = module_with(def);
    let errors: Vec<String> = validate_module(&module)
        .iter()
        .map(ToString::to_string)
        .collect();
    assert_eq!(errors.len(), 1, "{errors:#?}");
    assert!(errors[0].contains("no canonical tag"), "{}", errors[0]);
}
