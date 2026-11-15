// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// WS2.17 REVIEW (F-037): the v25 `Char` constant range rule is checked on
// EVERY leaf of a constant, not only on its top-level declared type.
//
// Lowering-target subset v4 admits `Ty::Char` into the proven subset, and
// structural condition 6 admits exactly two ORIGINS for a `Char`: a
// range-validated `Const`, and `Cast ZExt` of a `U8`. The first of those is
// a claim ABOUT THE VALIDATOR — so if the validator only range-checks a
// `Char` that is the WHOLE constant, the condition is circumventable by
// writing the surrogate one level down:
//
//     const (char, i32) = (0xD800, 0)   ; then `extractfield 0`
//
// Before this review that module validated with zero errors AND was reported
// in-subset, i.e. the subset accepted a module carrying an invalid `char`.
// The check now lives on the typed constant walk's per-node funnel
// (`trust_ir_build::validate::constant_values::check_node`), which is the
// same funnel the v24 canonical-integer-spelling rule already used.
//
// Twin structure: each negative is ONE mutation (the scalar value) from a
// positive that carries no char-range refusal, and the controls pin that the
// rule neither over-refuses a non-`char` carrier nor lost its original
// top-level spelling.

use trust_ir::value::{EnumId, FuncId, StructId};
use trust_ir::{
    Block, Constant, EnumDef, EnumVariant, FieldDef, FuncTy, Function, Module, StructDef, Ty,
};
use trust_ir::{inst::Inst, node::InstrNode, value::BlockId, value::ValueId};
use trust_ir_build::validate_module;

/// The first surrogate: representable in `Char`'s 32-bit carrier, NOT a
/// Unicode scalar value.
const SURROGATE: i128 = 0xD800;
/// The last code point — the in-range boundary the rule must keep.
const MAX_SCALAR: i128 = 0x10FFFF;

/// Wrap one constant in `fn f() { const <ty> = <value>; return }` so the only
/// thing under test is the constant.
fn with_const(mut module: Module, ty: Ty, value: Constant) -> Module {
    let ft = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = Function::new(FuncId::new(0), "f", ft, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block
        .body
        .push(InstrNode::new(Inst::Const { ty, value }).with_result(ValueId::new(0)));
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    func.blocks.push(block);
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    module
}

fn char_range_refusals(module: &Module) -> Vec<String> {
    validate_module(module)
        .iter()
        .map(|e| e.to_string())
        .filter(|e| e.contains("Unicode scalar value"))
        .collect()
}

fn assert_refused(module: &Module, what: &str) {
    let refusals = char_range_refusals(module);
    assert!(
        !refusals.is_empty(),
        "{what} must be refused by the char range rule; validator said: {:?}",
        validate_module(module)
            .iter()
            .map(|e| e.to_string())
            .collect::<Vec<_>>()
    );
    assert!(
        refusals.iter().any(|e| e.contains("char constant 55296")),
        "{what}: the refusal must NAME the offending scalar: {refusals:?}"
    );
}

/// The over-refusal control: this shape carries NO char-range refusal.
/// (Deliberately narrower than "validates clean" so an unrelated layout rule
/// on the carrier type cannot masquerade as this rule firing.)
fn assert_no_char_refusal(module: &Module, what: &str) {
    assert!(
        char_range_refusals(module).is_empty(),
        "{what} must not be refused by the char range rule: {:?}",
        char_range_refusals(module)
    );
}

/// Regression guard for the MOVE: the original top-level spelling is still
/// refused, and its in-range twin still validates with ZERO errors.
#[test]
fn a_top_level_char_constant_keeps_its_range_rule() {
    assert_refused(
        &with_const(Module::new("top_bad"), Ty::Char, Constant::Int(SURROGATE)),
        "const char = 0xD800",
    );
    let ok = with_const(Module::new("top_ok"), Ty::Char, Constant::Int(MAX_SCALAR));
    assert!(
        validate_module(&ok).is_empty(),
        "const char = 0x10FFFF (the last code point) must validate clean: {:?}",
        validate_module(&ok)
            .iter()
            .map(|e| e.to_string())
            .collect::<Vec<_>>()
    );
}

/// THE HOLE, inline spelling: a surrogate one level down, inside a tuple.
#[test]
fn a_surrogate_nested_in_a_tuple_constant_is_refused() {
    let ty = || Ty::Tuple(vec![Ty::Char, Ty::I32]);
    assert_no_char_refusal(
        &with_const(
            Module::new("tuple_ok"),
            ty(),
            Constant::Aggregate(vec![Constant::Int(65), Constant::Int(0)]),
        ),
        "const (char, i32) = ('A', 0)",
    );
    assert_refused(
        &with_const(
            Module::new("tuple_bad"),
            ty(),
            Constant::Aggregate(vec![Constant::Int(SURROGATE), Constant::Int(0)]),
        ),
        "const (char, i32) = (0xD800, 0)",
    );
}

/// THE HOLE, named-table spelling: the leaf type comes from the struct field
/// table, which no inline type surface names.
#[test]
fn a_surrogate_nested_in_a_struct_constant_is_refused() {
    let build = |name: &str, scalar: i128| {
        let mut module = Module::new(name);
        let sid = module.add_struct(StructDef {
            id: StructId::new(0),
            name: "S".into(),
            fields: vec![FieldDef {
                name: "c".into(),
                ty: Ty::Char,
                offset: None,
            }],
            size: None,
            align: None,
            repr: Default::default(),
            origin: None,
        });
        with_const(
            module,
            Ty::Struct(sid),
            Constant::Aggregate(vec![Constant::Int(scalar)]),
        )
    };
    assert_no_char_refusal(&build("struct_ok", 65), "const S { c: 'A' }");
    assert_refused(&build("struct_bad", SURROGATE), "const S { c: 0xD800 }");
}

/// THE HOLE, interned-element spelling: an array's element type lives in the
/// module type table.
#[test]
fn a_surrogate_nested_in_an_array_constant_is_refused() {
    let build = |name: &str, scalar: i128| {
        let mut module = Module::new(name);
        let elem = module
            .add_type(Ty::Char)
            .expect("Module::add_type: test fixture");
        with_const(
            module,
            Ty::Array(elem, 2),
            Constant::Array(vec![Constant::Int(65), Constant::Int(scalar)]),
        )
    };
    assert_no_char_refusal(&build("array_ok", 66), "const [char; 2] = ['A', 'B']");
    assert_refused(
        &build("array_bad", SURROGATE),
        "const [char; 2] = ['A', 0xD800]",
    );
}

/// THE HOLE, variant-table spelling — and the one where the walk's first
/// constant element is the DISCRIMINANT, not a field, so a rule keyed on
/// position rather than on the resolved leaf type would look at the wrong
/// element.
#[test]
fn a_surrogate_nested_in_an_enum_payload_constant_is_refused() {
    let build = |name: &str, scalar: i128| {
        let mut module = Module::new(name);
        let eid = module.add_enum(
            EnumDef::new(
                EnumId::new(0),
                "E",
                vec![EnumVariant {
                    name: "C".into(),
                    fields: vec![Ty::Char],
                    field_names: Vec::new(),
                }],
            )
            .with_discriminants(vec![Some(0)]),
        );
        with_const(
            module,
            Ty::Enum(eid),
            Constant::Aggregate(vec![Constant::Int(0), Constant::Int(scalar)]),
        )
    };
    assert_no_char_refusal(&build("enum_ok", 65), "const E::C('A')");
    assert_refused(&build("enum_bad", SURROGATE), "const E::C(0xD800)");
}

/// MUTATION CONTROL — the rule is keyed on `Ty::Char`, not on the VALUE.
/// The same bit pattern at `u32` is an ordinary integer and must stay legal,
/// or the rule would refuse every program that computes with `0xD800`.
#[test]
fn the_same_scalar_at_a_non_char_type_is_untouched() {
    assert_no_char_refusal(
        &with_const(Module::new("u32_ok"), Ty::U32, Constant::Int(SURROGATE)),
        "const u32 = 0xD800",
    );
    assert_no_char_refusal(
        &with_const(
            Module::new("tuple_u32_ok"),
            Ty::Tuple(vec![Ty::U32, Ty::I32]),
            Constant::Aggregate(vec![Constant::Int(SURROGATE), Constant::Int(0)]),
        ),
        "const (u32, i32) = (0xD800, 0)",
    );
}
