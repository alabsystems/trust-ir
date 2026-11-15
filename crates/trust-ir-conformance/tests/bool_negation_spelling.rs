// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Roadmap WS2.21 (F-033, trust-ir half): scalar Bool negation has ONE
// spelling (docs/SPEC_RATIFICATIONS.md §3.2). Boolean negation is the Bool
// connective `bxor %b, true`; `not` is the BITWISE complement, defined only on
// integers, integer vectors and bool vectors, and `not bool` is refused by its
// own name, `ValidationError::UnOpNotOnScalarBool`, whose text names the
// spelling a producer must emit.
//
// Proof-program row ported here, named after it:
//   * `a.format.unop_not_bool` (Part A, analyze.py; specimens
//     `parta/attrib/bool_not_{xor,unop}.trust_ir` of the archived 2026-09-17
//     proof program): `a_format_unop_not_bool_*`. Re-labelled PASS "ratified
//     single spelling": the bxor specimen validates and runs to the native 3,
//     and the `not` specimen is refused by name.
// The Part B ratchet `b6.bool.scalar_not_rejected` flips GAP -> PASS in
// `two_language/b6_data_carriers.rs`; `a.lean.bool_connective` flips only when
// the producer respell (WS5.13, a `~/trust` companion) lands.
//
// Every fixture meant to validate is also RUN: the validator and the
// normative interpreter agree on each spelling.

use trust_ir::Module;
use trust_ir::constant::Constant;
use trust_ir::inst::{BinOp, UnOp};
use trust_ir::interpret::{InterpretValue, InterpretValueKind, Interpreter};
use trust_ir::parser::parse_module;
use trust_ir::ty::Ty;
use trust_ir_build::{ModuleBuilder, ValidationError, validate_module};

/// The Part A attribution module: Lean `def neg (b : Bool) : Bool := not b`
/// beside `conj`/`disj` as the from-source compiler emits them; `program` =
/// `neg(false) + 2*conj(true,true) + 4*disj(false,false)`, whose native value
/// is 3. `neg` is the instruction defining `%2` in `@neg`.
fn parta_specimen(neg: &str) -> String {
    format!(
        r#"; TrustIr text format v1
module "parta-bool-not"

functy.0 = (bool) -> (bool)

functy.1 = (bool, bool) -> (bool)

functy.2 = () -> (u64)

rustcc fn @neg(functy.0) {{
    ; #producer: clean
bb0(%0: bool):
    %1 = const bool true
{neg}
    ret %2
}}

rustcc fn @conj(functy.1) {{
    ; #producer: clean
bb0(%0: bool, %1: bool):
    %2 = and bool %0, %1
    ret %2
}}

rustcc fn @disj(functy.1) {{
    ; #producer: clean
bb0(%0: bool, %1: bool):
    %2 = or bool %0, %1
    ret %2
}}

rustcc fn @program(functy.2) {{
bb0:
    %0 = const bool false
    %1 = const bool true
    %2 = call @func.0(%0)
    %3 = call @func.1(%1, %1)
    %4 = call @func.2(%0, %0)
    %5 = zext bool %2 to u64
    %6 = zext bool %3 to u64
    %7 = zext bool %4 to u64
    %8 = const u64 2
    %9 = mul u64 %6, %8
    %10 = const u64 4
    %11 = mul u64 %7, %10
    %12 = add u64 %5, %9
    %13 = add u64 %12, %11
    ret %13
}}
"#
    )
}

fn run(module: &Module, entry: &str, args: Vec<InterpretValue>) -> Vec<InterpretValue> {
    let id = module
        .function_by_name(entry)
        .unwrap_or_else(|| panic!("no function @{entry}"))
        .id;
    Interpreter::with_module(module)
        .execute_func(id, args)
        .unwrap_or_else(|e| panic!("@{entry} must execute: {e}"))
        .returns
}

fn is_the_named_refusal(errors: &[ValidationError]) -> bool {
    matches!(errors, [ValidationError::UnOpNotOnScalarBool { block: 0 }])
        && errors[0]
            .to_string()
            .contains("boolean negation is `bxor %b, true`; `not` is bitwise")
}

/// `fn neg(b: bool) -> bool` spelled with `negate`.
fn build_neg(
    negate: impl FnOnce(
        &mut trust_ir_build::FunctionBuilder<'_>,
        trust_ir::ValueId,
    ) -> trust_ir::ValueId,
) -> Module {
    let mut mb = ModuleBuilder::new("bool_negation");
    let ft = mb.add_func_type(vec![Ty::Bool], vec![Ty::Bool]);
    let mut fb = mb.function("neg", ft);
    let entry = fb.create_block();
    let b = fb.add_block_param(entry, Ty::Bool);
    fb.switch_to_block(entry);
    let out = negate(&mut fb, b);
    fb.ret(vec![out]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn a_format_unop_not_bool_bxor_specimen_validates_and_runs_to_native() {
    let module = parse_module(&parta_specimen("    %2 = bxor bool %0, %1"))
        .expect("the bxor specimen parses");
    assert_eq!(validate_module(&module), []);
    let out = run(&module, "program", vec![]);
    assert_eq!(out.len(), 1);
    assert_eq!(
        out[0].as_int().map(|i| i.as_unsigned()),
        Some(3),
        "program = neg(false) + 2*conj(true,true) + 4*disj(false,false) == native 3"
    );
}

#[test]
fn a_format_unop_not_bool_not_specimen_is_refused_by_name() {
    let module =
        parse_module(&parta_specimen("    %2 = not bool %0")).expect("the not specimen parses");
    let errors = validate_module(&module);
    assert!(is_the_named_refusal(&errors), "{errors:?}");
    // Never the generic integer refusal it was before WS2.21.
    assert!(
        !errors
            .iter()
            .any(|e| matches!(e, ValidationError::BinOpRequiresInteger { .. })),
        "{errors:?}"
    );
}

#[test]
fn bxor_true_is_boolean_negation_and_validates() {
    let module = build_neg(|fb, b| {
        let t = fb.const_value(Ty::Bool, Constant::Bool(true));
        fb.binop(BinOp::BXor, Ty::Bool, b, t)
    });
    assert_eq!(validate_module(&module), []);
    for input in [false, true] {
        let out = run(&module, "neg", vec![InterpretValue::bool(input)]);
        assert_eq!(out.len(), 1);
        assert_eq!(out[0].as_bool(), Some(!input), "neg({input})");
    }
}

/// The ratified spelling survives text: the printer writes `bxor` and the
/// parser reads it back to the same module (before WS2.21 the parser refused
/// `band`/`bor`/`bxor` as "unknown instruction", so the one spelling of
/// boolean negation could be built but not written as text).
#[test]
fn bxor_true_round_trips_through_text() {
    let module = build_neg(|fb, b| {
        let t = fb.const_value(Ty::Bool, Constant::Bool(true));
        fb.binop(BinOp::BXor, Ty::Bool, b, t)
    });
    let text = module.to_string();
    assert!(text.contains("bxor bool"), "{text}");
    let reparsed = parse_module(&text).expect("the printed bxor module parses");
    assert_eq!(reparsed.to_string(), text);
    assert_eq!(validate_module(&reparsed), []);
}

/// All three Bool connectives parse from text: the Part A module with
/// `conj`/`disj` respelled `band`/`bor` validates and still computes 3.
#[test]
fn bool_connectives_parse_from_text() {
    let text = parta_specimen("    %2 = bxor bool %0, %1")
        .replace("= and bool", "= band bool")
        .replace("= or bool", "= bor bool");
    assert!(
        text.contains("band bool") && text.contains("bor bool"),
        "{text}"
    );
    let module = parse_module(&text).expect("band/bor/bxor parse");
    assert_eq!(validate_module(&module), []);
    let out = run(&module, "program", vec![]);
    assert_eq!(out[0].as_int().map(|i| i.as_unsigned()), Some(3));
}

#[test]
fn not_on_scalar_bool_is_refused_as_unop_not_on_scalar_bool() {
    let module = build_neg(|fb, b| fb.unop(UnOp::Not, Ty::Bool, b));
    let errors = validate_module(&module);
    assert!(is_the_named_refusal(&errors), "{errors:?}");
}

/// Mutation control: the rule keys on SCALAR `Bool` only. `not` on a bool
/// vector and on an integer is unchanged (validates and runs), and on a float
/// it is still the generic integer refusal.
#[test]
fn not_on_bool_vector_and_integers_is_unchanged() {
    let v4bool = Ty::Vector(Box::new(Ty::Bool), 4);
    let mut mb = ModuleBuilder::new("bool_vector_not");
    let ft = mb.add_func_type(vec![], vec![v4bool.clone(), Ty::U8]);
    let mut fb = mb.function("flip", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let lanes = fb.const_value(
        v4bool.clone(),
        Constant::v4_bool_mask([false, true, false, true]),
    );
    let flipped = fb.unop(UnOp::Not, v4bool, lanes);
    let byte = fb.const_value(Ty::U8, Constant::Int(0b1010_0101));
    let inverted = fb.unop(UnOp::Not, Ty::U8, byte);
    fb.ret(vec![flipped, inverted]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(validate_module(&module), []);
    let out = run(&module, "flip", vec![]);
    let lanes: Vec<bool> = match &out[0].kind {
        InterpretValueKind::Vector(lanes) => lanes
            .iter()
            .map(|lane| lane.as_bool().expect("bool lane"))
            .collect(),
        other => panic!("expected a bool vector, got {other:?}"),
    };
    assert_eq!(lanes, [true, false, true, false]);
    assert_eq!(out[1].as_int().map(|i| i.as_unsigned()), Some(0b0101_1010));

    let mut mb = ModuleBuilder::new("float_not");
    let ft = mb.add_func_type(vec![Ty::F32], vec![Ty::F32]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::F32);
    fb.switch_to_block(entry);
    let r = fb.unop(UnOp::Not, Ty::F32, x);
    fb.ret(vec![r]);
    fb.build();
    let errors = validate_module(&mb.build().expect("ModuleBuilder::build: test fixture"));
    assert!(
        matches!(errors.as_slice(), [ValidationError::BinOpRequiresInteger { op, ty, .. }] if op == "not" && ty == "f32"),
        "{errors:?}"
    );
}

/// Review (adversarial, the new text surface): the parser now reads
/// `band`/`bor`/`bxor`, so it must read them AS the Bool connectives and never
/// fold them onto the overloaded integer `and`/`or`/`xor`. At an integer type
/// a connective is `BinOpRequiresBool` — built, and again after a text round
/// trip — while the overloaded spelling at the same type validates. Were the
/// parser to map `bxor` to `Xor`, the reparsed integer module would validate.
#[test]
fn bool_connectives_read_from_text_stay_bool_only() {
    for op in [BinOp::BAnd, BinOp::BOr, BinOp::BXor] {
        let module = |op: BinOp| {
            let mut mb = ModuleBuilder::new("integer_connective");
            let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
            let mut fb = mb.function("f", ft);
            let entry = fb.create_block();
            let a = fb.add_block_param(entry, Ty::I32);
            let b = fb.add_block_param(entry, Ty::I32);
            fb.switch_to_block(entry);
            let r = fb.binop(op, Ty::I32, a, b);
            fb.ret(vec![r]);
            fb.build();
            mb.build().expect("ModuleBuilder::build: test fixture")
        };
        let built = module(op);
        let reparsed = parse_module(&built.to_string()).expect("the connective parses");
        assert_eq!(reparsed.to_string(), built.to_string());
        for m in [&built, &reparsed] {
            let errors = validate_module(m);
            assert!(
                matches!(errors.as_slice(), [ValidationError::BinOpRequiresBool { op: name, ty, .. }]
                    if *name == op.to_string() && ty == "i32"),
                "{op:?}: {errors:?}"
            );
        }
        let overloaded = match op {
            BinOp::BAnd => BinOp::And,
            BinOp::BOr => BinOp::Or,
            _ => BinOp::Xor,
        };
        assert_eq!(validate_module(&module(overloaded)), [], "{overloaded:?}");
    }
}

/// Review (adversarial, mutation control on the text surface): `not` on a
/// bool VECTOR is printed, parsed back to the same module and still
/// validates; only scalar `Bool` is refused, and the refusal survives text.
#[test]
fn not_on_bool_vector_round_trips_and_scalar_refusal_survives_text() {
    let v4bool = Ty::Vector(Box::new(Ty::Bool), 4);
    let vector = {
        let mut mb = ModuleBuilder::new("bool_vector_not_text");
        let ft = mb.add_func_type(vec![v4bool.clone()], vec![v4bool.clone()]);
        let mut fb = mb.function("flip", ft);
        let entry = fb.create_block();
        let lanes = fb.add_block_param(entry, v4bool.clone());
        fb.switch_to_block(entry);
        let flipped = fb.unop(UnOp::Not, v4bool, lanes);
        fb.ret(vec![flipped]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let reparsed = parse_module(&vector.to_string()).expect("vector not parses");
    assert_eq!(reparsed.to_string(), vector.to_string());
    assert_eq!(validate_module(&reparsed), []);

    let scalar = build_neg(|fb, b| fb.unop(UnOp::Not, Ty::Bool, b));
    let reparsed = parse_module(&scalar.to_string()).expect("scalar not parses");
    let errors = validate_module(&reparsed);
    assert!(is_the_named_refusal(&errors), "{errors:?}");
}
