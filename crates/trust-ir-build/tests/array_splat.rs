// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// ══════════════════════════════════════════════════════════════════════════
// v50 — the constant-size uniform array: `Constant::Splat` / `Inst::ArraySplat`.
// ══════════════════════════════════════════════════════════════════════════
//
// The owner's principle: compiler memory and time scale with the size of the
// program TEXT, never with values in it. "N copies of v" is one element and one
// length, so every consumer here must cost O(1) in N. This battery pins that at
// u64-scale lengths (2^32 .. 2^40 elements, up to 4 TiB of declared bytes),
// where any O(N) path would run for hours or exhaust the host:
//
//   * validator — `ArraySplat` is checked in constant time (the type resolves
//     to `Array(e, n)`, the operand has type `e`, `n` is compared, never
//     walked); every ill-shaped form is refused by name (`InvalidArraySplat`,
//     `OperandTypeMismatch`), and the SPEC_RATIFICATIONS §3.1 one-spelling rule
//     is VALIDATED in both directions (`NonCanonicalUniformArray`): a constant
//     list of two or more equal elements (`Constant::Array` /
//     `Constant::Aggregate` at an array type, raw `Constant::Bytes`) must be a
//     `Splat`, and a `Splat` of zero or one element the list; a
//     `MakeAggregate` whose lanes are all one register (one lane included)
//     must be an `ArraySplat`, and an `ArraySplat` of zero copies the constant
//     `array[ ]`. The builder's `uniform_array` picks the canonical spelling,
//     every one of which has a binary encoding;
//   * reference interpreter — a splat is one uniform node: `ExtractElement`
//     and `InsertElement` are O(height); a splat stored to a 4 GiB `Alloca`
//     is one repeating run of a SPARSE allocation, reads back element-wise and
//     as a whole value, and survives a `MemCopy`; a `MemSet` of 4 GiB is one
//     run; a splat / BSS global of 4 GiB is one run; a nested splat of 4 TiB
//     loads back as a nested splat.

use trust_ir::constant::Constant;
use trust_ir::inst::Inst;
use trust_ir::interpret::{
    ArrayValue, InterpretOptions, InterpretValue, InterpretValueKind, Interpreter,
};
use trust_ir::value::GlobalId;
use trust_ir::{Global, Linkage, Module, Ty, TyId};
use trust_ir_build::{ModuleBuilder, ValidationError, validate_module, wire_identity_blocker};

const HUGE: u64 = 1 << 40;
const FOUR_GIB_OF_U8: u64 = 1 << 32;
const FOUR_GIB_OF_U32: u64 = 1 << 30;

fn run(module: &Module, entry: &str, args: Vec<InterpretValue>) -> Vec<InterpretValue> {
    let func = module.function_by_name(entry).expect("entry exists");
    Interpreter::with_module(module)
        .with_options(InterpretOptions {
            fuel: 10_000,
            max_call_depth: 64,
            ..InterpretOptions::default()
        })
        .execute_func(func.id, args)
        .unwrap_or_else(|error| panic!("@{entry} must execute: {error}"))
        .returns
}

fn int(ty: Ty, value: i128) -> InterpretValue {
    InterpretValue::int(ty, value).expect("integer value")
}

fn global(name: &str, ty: Ty, initializer: Option<Constant>) -> Global {
    Global {
        name: name.into(),
        ty,
        mutable: false,
        initializer,
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    }
}

fn non_canonical(errors: &[ValidationError]) -> usize {
    errors
        .iter()
        .filter(|error| matches!(error, ValidationError::NonCanonicalUniformArray { .. }))
        .count()
}

// ───────────────────────────── validator ─────────────────────────────

/// `fill(x) = [x; 2^40]`, `pick(i) = splat[ -3; 2^40 ][i]`,
/// `poke(x, i) = [x; 2^40] with [i] = 1, then read [i] and [i + 1]`.
fn register_module() -> Module {
    let mut mb = ModuleBuilder::new("array_splat_registers");
    let i64_id = mb.add_type(Ty::I64);
    let big = Ty::Array(i64_id, HUGE);

    let ft = mb.add_func_type(vec![Ty::I64], vec![big.clone()]);
    {
        let mut fb = mb.function("fill", ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let array = fb.uniform_array(big.clone(), x);
        fb.ret(vec![array]);
        fb.build();
    }

    let ft = mb.add_func_type(vec![Ty::U64], vec![Ty::I64]);
    {
        let mut fb = mb.function("pick", ft);
        let entry = fb.create_block();
        let index = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        let array = fb.const_value(big.clone(), Constant::splat(Constant::Int(-3), HUGE));
        let element = fb.extract_element(Ty::I64, array, index);
        fb.ret(vec![element]);
        fb.build();
    }

    let ft = mb.add_func_type(vec![Ty::I64, Ty::U64], vec![Ty::I64, Ty::I64, Ty::I64]);
    {
        let mut fb = mb.function("poke", ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I64);
        let index = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        let array = fb.uniform_array(big.clone(), x);
        let one = fb.iconst(Ty::I64, 1);
        let written = fb.insert_element(big.clone(), array, index, one);
        let at = fb.extract_element(Ty::I64, written, index);
        let step = fb.iconst(Ty::U64, 1);
        let next_index = fb.add(Ty::U64, index, step);
        let next = fb.extract_element(Ty::I64, written, next_index);
        // The INPUT array is unchanged: SSA keeps it alive beside the update.
        let before = fb.extract_element(Ty::I64, array, index);
        fb.ret(vec![at, next, before]);
        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn array_splat_validates_in_constant_time_at_u64_scale() {
    let m = register_module();
    assert_eq!(validate_module(&m), []);
    assert!(matches!(
        m.function_by_name("fill").unwrap().blocks[0].body[0].inst,
        Inst::ArraySplat { .. }
    ));
}

#[test]
fn ill_shaped_array_splats_are_refused_by_name() {
    let mut mb = ModuleBuilder::new("array_splat_refusals");
    let i64_id = mb.add_type(Ty::I64);
    let ft = mb.add_func_type(vec![Ty::I64, Ty::Bool], vec![]);
    {
        let mut fb = mb.function("bad", ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I64);
        let flag = fb.add_block_param(entry, Ty::Bool);
        fb.switch_to_block(entry);
        // Not an array type.
        fb.array_splat(Ty::I64, x);
        // A dangling element type.
        fb.array_splat(Ty::Array(TyId::new(99), 4), x);
        // An operand of the wrong type (EXACT, as InsertElement's value).
        fb.array_splat(Ty::Array(i64_id, 4), flag);
        fb.ret(vec![]);
        fb.build();
    }
    let errors = validate_module(&mb.build().expect("ModuleBuilder::build: test fixture"));
    let invalid = |needle: &str| {
        errors.iter().any(|error| {
            matches!(error, ValidationError::InvalidArraySplat { reason, .. } if reason.contains(needle))
        })
    };
    assert!(invalid("not an array type"), "{errors:?}");
    assert!(invalid("undefined element type"), "{errors:?}");
    assert!(
        errors.iter().any(|error| matches!(
            error,
            ValidationError::OperandTypeMismatch { op, role, .. }
            if op == "array_splat" && role == "value"
        )),
        "{errors:?}"
    );
}

/// A nest of refused lists names each level's element by value (a scalar) or
/// by its shape label (a composite), never by printing the subtree: the
/// refusal text stays proportional to one level, not to the nest.
#[test]
fn a_nest_of_uniform_lists_is_refused_level_by_level_in_short_messages() {
    let mut m = Module::new("nested_lists");
    let i64_id = m.add_type(Ty::I64).expect("Module::add_type: test fixture");
    let row = m
        .add_type(Ty::Array(i64_id, 2))
        .expect("Module::add_type: test fixture");
    let plane = m
        .add_type(Ty::Array(row, 2))
        .expect("Module::add_type: test fixture");
    let row_value = || Constant::Array(vec![Constant::Int(0); 2]);
    let plane_value = || Constant::Array(vec![row_value(), row_value()]);
    let cube = Constant::Array(vec![plane_value(), plane_value()]);
    m.globals
        .push(global("CUBE", Ty::Array(plane, 2), Some(cube)));
    let errors = validate_module(&m);
    // Four rows, two planes and the cube are each uniform.
    assert_eq!(non_canonical(&errors), 7, "{errors:?}");
    for error in &errors {
        let ValidationError::NonCanonicalUniformArray { spelling, .. } = error else {
            panic!("{error:?}");
        };
        assert!(spelling.len() < 96, "{spelling}");
        assert!(!spelling.contains("[ 0, 0 ]"), "{spelling}");
    }
}

/// §3.1 in the register direction: `ArraySplat` is the one register spelling
/// of `[v; n]` for every `n >= 1` — one copy included — and the empty array is
/// the constant `array[ ]`. A `MakeAggregate` whose lanes are all ONE register
/// (one lane included) is the splat's non-canonical spelling; distinct lanes
/// stay a list, and zero lanes are the §3 producer rule, not validated.
#[test]
fn the_register_one_spelling_rule_is_validated_both_ways() {
    for (n, expected) in [(0u64, 1usize), (1, 0), (2, 0), (HUGE, 0)] {
        let mut mb = ModuleBuilder::new("raw_splat");
        let i64_id = mb.add_type(Ty::I64);
        let ft = mb.add_func_type(vec![Ty::I64], vec![Ty::Array(i64_id, n)]);
        {
            let mut fb = mb.function("raw", ft);
            let entry = fb.create_block();
            let x = fb.add_block_param(entry, Ty::I64);
            fb.switch_to_block(entry);
            let array = fb.array_splat(Ty::Array(i64_id, n), x);
            fb.ret(vec![array]);
            fb.build();
        }
        let errors = validate_module(&mb.build().expect("ModuleBuilder::build: test fixture"));
        assert_eq!(non_canonical(&errors), expected, "n = {n}: {errors:?}");
        assert_eq!(errors.len(), expected, "n = {n}: {errors:?}");
    }

    let mut mb = ModuleBuilder::new("repeated_lane");
    let i64_id = mb.add_type(Ty::I64);
    let one = Ty::Array(i64_id, 1);
    let three = Ty::Array(i64_id, 3);
    let empty = Ty::Array(i64_id, 0);
    let ft = mb.add_func_type(
        vec![Ty::I64, Ty::I64],
        vec![one.clone(), three.clone(), three.clone(), empty.clone()],
    );
    {
        let mut fb = mb.function("lanes", ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I64);
        let y = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let single = fb.make_aggregate(one.clone(), vec![x]);
        let same = fb.make_aggregate(three.clone(), vec![x, x, x]);
        let mixed = fb.make_aggregate(three.clone(), vec![x, y, x]);
        let none = fb.make_aggregate(empty.clone(), Vec::new());
        fb.ret(vec![single, same, mixed, none]);
        fb.build();
    }
    let errors = validate_module(&mb.build().expect("ModuleBuilder::build: test fixture"));
    assert_eq!(
        non_canonical(&errors),
        2,
        "the one-lane and the repeated-lane lists: {errors:?}"
    );
    assert_eq!(errors.len(), 2, "{errors:?}");
}

/// Every spelling `uniform_array` emits — `const array[ ]` for zero copies,
/// `array_splat` for one or more — validates, has a binary encoding (so a
/// stable digest) and executes. Review finding 2026-09-23: under the first
/// version of §3.1, `[v; 0]` and `[v; 1]` were `make_aggregate`, which had no
/// wire tag before the INST batch (v51), so a module holding `[f(); 1]` lost
/// its binary form and its digest.
#[test]
fn uniform_array_spells_every_length_encodably() {
    for n in [0u64, 1, 2, HUGE] {
        let mut mb = ModuleBuilder::new("uniform_array_lengths");
        let i64_id = mb.add_type(Ty::I64);
        let ty = Ty::Array(i64_id, n);
        let ft = mb.add_func_type(vec![Ty::I64], vec![ty.clone()]);
        {
            let mut fb = mb.function("fill", ft);
            let entry = fb.create_block();
            let x = fb.add_block_param(entry, Ty::I64);
            fb.switch_to_block(entry);
            let array = fb.uniform_array(ty.clone(), x);
            fb.ret(vec![array]);
            fb.build();
        }
        let m = mb.build().expect("ModuleBuilder::build: test fixture");
        assert_eq!(validate_module(&m), [], "n = {n}");
        let first = &m.functions[0].blocks[0].body[0].inst;
        if n == 0 {
            assert!(
                matches!(first, Inst::Const { value: Constant::Array(values), .. } if values.is_empty()),
                "{first:?}"
            );
        } else {
            assert!(matches!(first, Inst::ArraySplat { .. }), "{first:?}");
        }
        assert_eq!(
            wire_identity_blocker(&m),
            None,
            "n = {n}: has a wire encoding"
        );
        let _ = m.stable_digest();
        let out = run(&m, "fill", vec![int(Ty::I64, 5)]);
        let InterpretValueKind::Array(array) = &out[0].kind else {
            panic!("an array value: {:?}", out[0]);
        };
        assert_eq!(array.len(), n);
        if n > 0 {
            assert_eq!(array.get(n - 1), Some(&int(Ty::I64, 5)));
        }
    }
}

/// §3 in the constant direction, decided by one bottom-up pass over the
/// constant as written.
#[test]
fn the_constant_one_spelling_rule_is_validated_both_ways() {
    let cases: Vec<(&str, Ty, Constant, usize)> = {
        let mut m = Module::new("types");
        let i64_id = m.add_type(Ty::I64).expect("Module::add_type: test fixture");
        let u8_id = m.add_type(Ty::U8).expect("Module::add_type: test fixture");
        let row_id = m
            .add_type(Ty::Array(i64_id, 2))
            .expect("Module::add_type: test fixture");
        let byte_row_id = m
            .add_type(Ty::Array(u8_id, 2))
            .expect("Module::add_type: test fixture");
        vec![
            (
                "an equal list",
                Ty::Array(i64_id, 3),
                Constant::Array(vec![Constant::Int(4); 3]),
                1,
            ),
            (
                "an equal legacy aggregate at an array type",
                Ty::Array(i64_id, 2),
                Constant::Aggregate(vec![Constant::Int(4); 2]),
                1,
            ),
            (
                "raw equal bytes",
                Ty::Array(u8_id, 4),
                Constant::bytes(vec![9u8; 4]),
                1,
            ),
            (
                "a list of equal rows (each row distinct inside)",
                Ty::Array(row_id, 2),
                Constant::Array(vec![
                    Constant::Array(vec![Constant::Int(1), Constant::Int(2)]),
                    Constant::Array(vec![Constant::Int(1), Constant::Int(2)]),
                ]),
                1,
            ),
            (
                "a list of equal splats",
                Ty::Array(row_id, 2),
                Constant::Array(vec![
                    Constant::splat(Constant::Int(0), 2),
                    Constant::splat(Constant::Int(0), 2),
                ]),
                1,
            ),
            (
                "the two list spellings of one row (siblings share a type)",
                Ty::Array(row_id, 2),
                Constant::Array(vec![
                    Constant::Array(vec![Constant::Int(1), Constant::Int(2)]),
                    Constant::Aggregate(vec![Constant::Int(1), Constant::Int(2)]),
                ]),
                1,
            ),
            (
                "raw bytes and the list of the same bytes",
                Ty::Array(byte_row_id, 2),
                Constant::Array(vec![
                    Constant::bytes(vec![1u8, 2]),
                    Constant::Array(vec![Constant::Int(1), Constant::Int(2)]),
                ]),
                1,
            ),
            (
                "a splat of one element",
                Ty::Array(i64_id, 1),
                Constant::Splat {
                    elem: Box::new(Constant::Int(4)),
                    len: 1,
                },
                1,
            ),
            // Controls: canonical spellings.
            (
                "a splat",
                Ty::Array(i64_id, HUGE),
                Constant::splat(Constant::Int(4), HUGE),
                0,
            ),
            (
                "a distinct list",
                Ty::Array(i64_id, 3),
                Constant::Array(vec![Constant::Int(4), Constant::Int(4), Constant::Int(5)]),
                0,
            ),
            (
                "a one-element list",
                Ty::Array(i64_id, 1),
                Constant::Array(vec![Constant::Int(4)]),
                0,
            ),
            (
                "utf8 bytes keep their string claim",
                Ty::Array(u8_id, 2),
                Constant::str_bytes("aa"),
                0,
            ),
            (
                "a string row is not the list of its bytes",
                Ty::Array(byte_row_id, 2),
                Constant::Array(vec![
                    Constant::str_bytes("ab"),
                    Constant::Array(vec![Constant::Int(97), Constant::Int(98)]),
                ]),
                0,
            ),
        ]
    };
    for (what, ty, constant, expected) in cases {
        let mut m = Module::new("constant_spelling");
        m.add_type(Ty::I64).expect("Module::add_type: test fixture");
        m.add_type(Ty::U8).expect("Module::add_type: test fixture");
        let i64_id = TyId::new(0);
        m.add_type(Ty::Array(i64_id, 2))
            .expect("Module::add_type: test fixture");
        m.add_type(Ty::Array(TyId::new(1), 2))
            .expect("Module::add_type: test fixture");
        m.globals.push(global("G", ty, Some(constant)));
        let errors = validate_module(&m);
        assert_eq!(non_canonical(&errors), expected, "{what}: {errors:?}");
        assert_eq!(
            errors.len(),
            expected,
            "{what}: nothing else is refused: {errors:?}"
        );
    }
}

/// The default target validates and executes every case. Qualifying this same
/// target with `--features binary` additionally decodes and executes its exact
/// encoded module; no codec claim is made for the default-only run.
fn run_constructed_array(mut mb: ModuleBuilder, ty: Ty, constant: Constant) -> InterpretValue {
    mb.add_global(global("G", ty.clone(), Some(constant.clone())));
    let ft = mb.add_func_type(vec![], vec![ty.clone()]);
    {
        let mut fb = mb.function("constructed", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let value = fb.const_value(ty, constant);
        fb.ret(vec![value]);
        fb.build();
    }
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(validate_module(&module), []);
    assert_eq!(wire_identity_blocker(&module), None);
    let digest = module.stable_digest();
    assert_eq!(module.stable_digest(), digest);
    let mut values = run(&module, "constructed", vec![]);
    assert_eq!(values.len(), 1);
    #[cfg(feature = "binary")]
    {
        let bytes =
            trust_ir::binary::serialize_module(&module).expect("serialize_module: test fixture");
        assert!(
            bytes.len() < 16 * 1024,
            "stored fixture size, not logical array length"
        );
        let decoded =
            trust_ir::binary::deserialize_module(&bytes).expect("constructor module decodes");
        assert_eq!(decoded, module);
        assert_eq!(
            trust_ir::binary::serialize_module(&decoded).expect("serialize_module: test fixture"),
            bytes
        );
        assert_eq!(decoded.stable_digest(), digest);
        assert_eq!(validate_module(&decoded), []);
        assert_eq!(run(&decoded, "constructed", vec![]), values);
    }
    values.remove(0)
}

#[test]
fn array_constructor_canonicalizes_mixed_row_spellings_and_executes() {
    let row = || vec![Constant::Int(1), Constant::Int(2)];
    for (name, left, right, expected) in [
        (
            "array_aggregate",
            Constant::Array(row()),
            Constant::Aggregate(row()),
            vec![1, 2],
        ),
        (
            "aggregate_array",
            Constant::Aggregate(row()),
            Constant::Array(row()),
            vec![1, 2],
        ),
        (
            "bytes_array",
            Constant::bytes(vec![1, 2]),
            Constant::Array(row()),
            vec![1, 2],
        ),
        (
            "array_bytes",
            Constant::Array(row()),
            Constant::bytes(vec![1, 2]),
            vec![1, 2],
        ),
        (
            "empty_array_aggregate",
            Constant::Array(vec![]),
            Constant::Aggregate(vec![]),
            vec![],
        ),
        (
            "empty_bytes_array",
            Constant::bytes(vec![]),
            Constant::Array(vec![]),
            vec![],
        ),
    ] {
        assert_ne!(left, right, "the global structural Eq must not change");
        let elems = vec![left.clone(), right];
        assert!(
            !Constant::is_uniform_list(&elems),
            "distinct structural spellings"
        );
        let legacy = Constant::Array(elems.clone());
        assert!(legacy.uniform_element_lists().contains(&legacy));
        let constructed = Constant::array(elems);
        assert_eq!(constructed, Constant::splat(left, 2));
        let mut mb = ModuleBuilder::new(name);
        let byte = mb.add_type(Ty::U8);
        let row_ty = Ty::Array(byte, expected.len() as u64);
        let row_id = mb.add_type(row_ty);
        let value = run_constructed_array(mb, Ty::Array(row_id, 2), constructed);
        let InterpretValueKind::Array(rows) = &value.kind else {
            panic!("array result");
        };
        assert_eq!(rows.len(), 2);
        for index in 0..2 {
            let InterpretValueKind::Array(row) = &rows.get(index).unwrap().kind else {
                panic!("row result");
            };
            assert_eq!(row.len(), expected.len() as u64);
            for (index, value) in expected.iter().enumerate() {
                assert_eq!(row.get(index as u64), Some(&int(Ty::U8, *value)));
            }
        }
    }
}

#[test]
fn array_constructor_preserves_unequal_rows_and_utf8_claims() {
    for (name, left, right, expected) in [
        (
            "unequal",
            Constant::Array(vec![Constant::Int(1), Constant::Int(2)]),
            Constant::Aggregate(vec![Constant::Int(1), Constant::Int(3)]),
            [[1, 2], [1, 3]],
        ),
        (
            "utf8_raw",
            Constant::str_bytes("ab"),
            Constant::bytes(b"ab".to_vec()),
            [[97, 98], [97, 98]],
        ),
        (
            "utf8_list",
            Constant::str_bytes("ab"),
            Constant::Array(vec![Constant::Int(97), Constant::Int(98)]),
            [[97, 98], [97, 98]],
        ),
    ] {
        let elems = vec![left, right];
        let expected_constant = Constant::Array(elems.clone());
        let constructed = Constant::array(elems);
        assert_eq!(
            constructed, expected_constant,
            "{name}: preserve exact variant and claim"
        );
        assert!(!constructed.uniform_element_lists().contains(&constructed));
        let mut mb = ModuleBuilder::new(name);
        let byte = mb.add_type(Ty::U8);
        let row_id = mb.add_type(Ty::Array(byte, 2));
        let value = run_constructed_array(mb, Ty::Array(row_id, 2), constructed);
        let InterpretValueKind::Array(rows) = &value.kind else {
            panic!("array result");
        };
        assert_eq!(rows.len(), 2);
        for (index, expected) in expected.iter().enumerate() {
            let InterpretValueKind::Array(row) = &rows.get(index as u64).unwrap().kind else {
                panic!("row result");
            };
            assert_eq!(row.len(), 2);
            for (index, value) in expected.iter().enumerate() {
                assert_eq!(row.get(index as u64), Some(&int(Ty::U8, *value)));
            }
        }
    }
}

#[test]
fn array_constructor_preserves_float_bits_in_scalar_and_composite_paths() {
    let nan_a = 0x7ff8_0000_0000_0011;
    let nan_b = 0x7ff8_0000_0000_0012;
    for (left, right, uniform) in [
        (0, 0, true),
        (0, 1u64 << 63, false),
        (nan_a, nan_a, true),
        (nan_a, nan_b, false),
    ] {
        for nested in [false, true] {
            let mut mb = ModuleBuilder::new("float_identity");
            let float = mb.add_type(Ty::F64);
            let elems = if nested {
                vec![
                    Constant::Array(vec![Constant::Float(f64::from_bits(left))]),
                    Constant::Aggregate(vec![Constant::Float(f64::from_bits(right))]),
                ]
            } else {
                vec![
                    Constant::Float(f64::from_bits(left)),
                    Constant::Float(f64::from_bits(right)),
                ]
            };
            let elem_ty = if nested {
                mb.add_type(Ty::Array(float, 1))
            } else {
                float
            };
            let constructed = Constant::array(elems);
            assert_eq!(matches!(constructed, Constant::Splat { .. }), uniform);
            let value = run_constructed_array(mb, Ty::Array(elem_ty, 2), constructed);
            let InterpretValueKind::Array(values) = &value.kind else {
                panic!("array result");
            };
            assert_eq!(values.len(), 2);
            for (index, bits) in [left, right].into_iter().enumerate() {
                let mut scalar = values.get(index as u64).unwrap();
                if nested {
                    let InterpretValueKind::Array(row) = &scalar.kind else {
                        panic!("float row");
                    };
                    assert_eq!(row.len(), 1);
                    scalar = row.get(0).unwrap();
                }
                assert_eq!(scalar.kind, InterpretValueKind::FloatBits(bits));
            }
        }
    }
}

#[test]
fn array_constructor_classifies_huge_nested_splats_without_expansion() {
    for (last, uniform) in [(2, true), (3, false)] {
        let elems = vec![
            Constant::splat(
                Constant::Array(vec![Constant::Int(1), Constant::Int(2)]),
                HUGE,
            ),
            Constant::splat(
                Constant::Aggregate(vec![Constant::Int(1), Constant::Int(last)]),
                HUGE,
            ),
        ];
        let constructed = Constant::array(elems);
        assert_eq!(matches!(constructed, Constant::Splat { .. }), uniform);
        let mut stored_nodes = 0;
        constructed.visit_constants(|_| stored_nodes += 1);
        assert_eq!(stored_nodes, if uniform { 5 } else { 9 });
        let mut mb = ModuleBuilder::new("huge_nested_constructor");
        let byte = mb.add_type(Ty::U8);
        let pair = mb.add_type(Ty::Array(byte, 2));
        let row = mb.add_type(Ty::Array(pair, HUGE));
        let value = run_constructed_array(mb, Ty::Array(row, 2), constructed);
        let InterpretValueKind::Array(rows) = &value.kind else {
            panic!("array result");
        };
        assert_eq!(rows.len(), 2);
        for (index, expected_last) in [2, last].into_iter().enumerate() {
            let InterpretValueKind::Array(row) = &rows.get(index as u64).unwrap().kind else {
                panic!("huge row");
            };
            assert_eq!(row.len(), HUGE);
            for index in [0, HUGE - 1] {
                let InterpretValueKind::Array(pair) = &row.get(index).unwrap().kind else {
                    panic!("pair");
                };
                assert_eq!(pair.len(), 2);
                assert_eq!(pair.get(0), Some(&int(Ty::U8, 1)));
                assert_eq!(pair.get(1), Some(&int(Ty::U8, expected_last)));
            }
        }
    }
}

#[test]
fn legacy_array_aggregate_matches_array_in_constants_memory_and_globals() {
    for values in [vec![], vec![7], vec![1, 2, 3]] {
        let mut outcomes = Vec::new();
        for aggregate in [false, true] {
            let mut mb = ModuleBuilder::new("legacy_array_execution");
            let byte = mb.add_type(Ty::U8);
            let ty = Ty::Array(byte, values.len() as u64);
            let elems = values.iter().map(|value| Constant::Int(*value)).collect();
            let constant = if aggregate {
                Constant::Aggregate(elems)
            } else {
                Constant::Array(elems)
            };
            mb.add_global(global("G", ty.clone(), Some(constant.clone())));
            let ft = mb.add_func_type(vec![], vec![ty.clone(), ty.clone(), ty.clone()]);
            {
                let mut fb = mb.function("legacy", ft);
                let entry = fb.create_block();
                fb.switch_to_block(entry);
                let value = fb.const_value(ty.clone(), constant);
                let slot = fb.alloca(ty.clone());
                fb.store(ty.clone(), slot, value);
                let loaded = fb.load(ty.clone(), slot);
                let global = fb.global_addr(GlobalId::new(0));
                let global_loaded = fb.load(ty, global);
                fb.ret(vec![value, loaded, global_loaded]);
                fb.build();
            }
            let module = mb.build().expect("ModuleBuilder::build: test fixture");
            assert_eq!(validate_module(&module), []);
            let result = run(&module, "legacy", vec![]);
            assert_eq!(result.len(), 3);
            for value in &result {
                let InterpretValueKind::Array(array) = &value.kind else {
                    panic!("array result");
                };
                assert_eq!(array.len(), values.len() as u64);
                for (index, value) in values.iter().enumerate() {
                    assert_eq!(array.get(index as u64), Some(&int(Ty::U8, *value)));
                }
            }
            #[cfg(feature = "binary")]
            {
                let bytes = trust_ir::binary::serialize_module(&module)
                    .expect("serialize_module: test fixture");
                let decoded =
                    trust_ir::binary::deserialize_module(&bytes).expect("legacy module decodes");
                assert_eq!(decoded, module);
                assert_eq!(validate_module(&decoded), []);
                assert_eq!(run(&decoded, "legacy", vec![]), result);
            }
            outcomes.push(result);
        }
        assert_eq!(
            outcomes[0], outcomes[1],
            "both stored spellings have identical array semantics"
        );
    }
}

#[test]
fn legacy_array_spellings_reject_wrong_length_type_and_uninit() {
    for aggregate in [false, true] {
        for case in ["length", "element", "uninit", "nested", "not_array"] {
            let mut mb = ModuleBuilder::new("invalid_legacy_array");
            let byte = mb.add_type(Ty::U8);
            let row = mb.add_type(Ty::Array(byte, 2));
            let (ty, elems) = match case {
                "length" => (Ty::Array(byte, 2), vec![Constant::Int(1)]),
                "element" => (
                    Ty::Array(byte, 2),
                    vec![Constant::Int(1), Constant::Bool(true)],
                ),
                "uninit" => (Ty::Array(byte, 2), vec![Constant::Int(1), Constant::Uninit]),
                "nested" => (
                    Ty::Array(row, 2),
                    vec![
                        Constant::Array(vec![Constant::Int(1), Constant::Int(2)]),
                        Constant::Aggregate(vec![Constant::Int(1), Constant::Bool(true)]),
                    ],
                ),
                "not_array" => (Ty::U8, vec![Constant::Int(1), Constant::Int(2)]),
                _ => unreachable!(),
            };
            let constant = if aggregate {
                Constant::Aggregate(elems)
            } else {
                Constant::Array(elems)
            };
            let ft = mb.add_func_type(vec![], vec![ty.clone()]);
            {
                let mut fb = mb.function("invalid", ft);
                let entry = fb.create_block();
                fb.switch_to_block(entry);
                let value = fb.const_value(ty, constant);
                fb.ret(vec![value]);
                fb.build();
            }
            let module = mb.build().expect("ModuleBuilder::build: test fixture");
            let errors = validate_module(&module);
            assert!(
                !errors.is_empty(),
                "{case}, aggregate={aggregate}: invalid shape must be refused"
            );
            assert_eq!(
                non_canonical(&errors),
                0,
                "{case}: refusal is not the uniform-spelling rule"
            );
            let function = module.function_by_name("invalid").unwrap();
            let error = Interpreter::with_module(&module)
                .execute_func(function.id, vec![])
                .expect_err("unvalidated ill-typed arrays must still fail closed");
            assert_eq!(
                error.code,
                trust_ir::InterpretErrorCode::TypeError,
                "{case}, aggregate={aggregate}: {error}"
            );
        }
    }
}

#[test]
fn a_splat_is_typed_by_its_one_element_and_its_length() {
    let mut m = Module::new("splat_typing");
    let i64_id = m.add_type(Ty::I64).expect("Module::add_type: test fixture");
    m.globals.push(global(
        "WRONG_LENGTH",
        Ty::Array(i64_id, HUGE),
        Some(Constant::splat(Constant::Int(0), HUGE - 1)),
    ));
    m.globals.push(global(
        "WRONG_ELEMENT",
        Ty::Array(i64_id, HUGE),
        Some(Constant::splat(Constant::Bool(true), HUGE)),
    ));
    let errors = validate_module(&m);
    let mismatches = errors
        .iter()
        .filter(|error| matches!(error, ValidationError::ConstTypeMismatch { .. }))
        .count();
    assert_eq!(mismatches, 2, "{errors:?}");
}

// ───────────────────────────── interpreter ─────────────────────────────

#[test]
fn register_splats_extract_and_insert_at_u64_scale() {
    let m = register_module();
    let filled = run(&m, "fill", vec![int(Ty::I64, 5)]);
    let InterpretValueKind::Array(array) = &filled[0].kind else {
        panic!("expected an array value, got {:?}", filled[0].kind);
    };
    assert_eq!(array.len(), HUGE);
    assert_eq!(array.get(HUGE - 1), Some(&int(Ty::I64, 5)));
    assert_eq!(array, &ArrayValue::splat(int(Ty::I64, 5), HUGE));

    assert_eq!(
        run(&m, "pick", vec![int(Ty::U64, (HUGE - 1) as i128)]),
        vec![int(Ty::I64, -3)]
    );

    assert_eq!(
        run(
            &m,
            "poke",
            vec![int(Ty::I64, 5), int(Ty::U64, (HUGE / 3) as i128)]
        ),
        vec![int(Ty::I64, 1), int(Ty::I64, 5), int(Ty::I64, 5)]
    );
}

/// A splat stored to a 4 GiB `Alloca` is one repeating run of a sparse
/// allocation: element loads, a single-element store and a whole-value load
/// all cost O(runs), never the 2^30 elements.
#[test]
fn a_splat_stored_to_a_four_gib_alloca_round_trips() {
    let mut mb = ModuleBuilder::new("splat_memory");
    let u32_id = mb.add_type(Ty::U32);
    let big = Ty::Array(u32_id, FOUR_GIB_OF_U32);
    let ft = mb.add_func_type(
        vec![Ty::U32, Ty::U64],
        vec![Ty::U32, Ty::U32, Ty::U32, Ty::U32],
    );
    {
        let mut fb = mb.function("round_trip", ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::U32);
        let index = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        let slot = fb.alloca(big.clone());
        let array = fb.uniform_array(big.clone(), x);
        fb.store(big.clone(), slot, array);
        let last_index = fb.iconst(Ty::U64, (FOUR_GIB_OF_U32 - 1) as i128);
        let last_ptr = fb.gep(Ty::U32, slot, vec![last_index]);
        let last = fb.load(Ty::U32, last_ptr);
        let nine = fb.iconst(Ty::U32, 9);
        let poked = fb.gep(Ty::U32, slot, vec![index]);
        fb.store(Ty::U32, poked, nine);
        let whole = fb.load(big.clone(), slot);
        let at = fb.extract_element(Ty::U32, whole, index);
        let one = fb.iconst(Ty::U64, 1);
        let after_index = fb.add(Ty::U64, index, one);
        let after = fb.extract_element(Ty::U32, whole, after_index);
        let first_index = fb.iconst(Ty::U64, 0);
        let first = fb.extract_element(Ty::U32, whole, first_index);
        fb.ret(vec![last, at, after, first]);
        fb.build();
    }
    let m = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(validate_module(&m), []);
    assert_eq!(
        run(
            &m,
            "round_trip",
            vec![int(Ty::U32, 7), int(Ty::U64, 123_456_789)]
        ),
        vec![
            int(Ty::U32, 7),
            int(Ty::U32, 9),
            int(Ty::U32, 7),
            int(Ty::U32, 7)
        ]
    );
}

/// A 4 GiB `MemSet` is one run, a 4 GiB `MemCopy` moves runs, and memory
/// written at one element width reads back at another.
#[test]
fn four_gib_memset_and_memcopy_are_runs() {
    let mut mb = ModuleBuilder::new("bulk_memory");
    let u8_id = mb.add_type(Ty::U8);
    let u32_id = mb.add_type(Ty::U32);
    let bytes = Ty::Array(u8_id, FOUR_GIB_OF_U8);
    let words = Ty::Array(u32_id, FOUR_GIB_OF_U32);
    let ft = mb.add_func_type(vec![], vec![Ty::U8, Ty::U32]);
    {
        let mut fb = mb.function("bulk", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let a = fb.alloca(bytes.clone());
        let b = fb.alloca(bytes.clone());
        let fill = fb.iconst(Ty::U8, 5);
        let count = fb.iconst(Ty::U64, FOUR_GIB_OF_U8 as i128);
        fb.memset(a, fill, count);
        fb.memcopy(b, a, count, false);
        let as_bytes = fb.load(bytes.clone(), b);
        let last_index = fb.iconst(Ty::U64, (FOUR_GIB_OF_U8 - 1) as i128);
        let last = fb.extract_element(Ty::U8, as_bytes, last_index);
        let as_words = fb.load(words.clone(), b);
        let word_index = fb.iconst(Ty::U64, (FOUR_GIB_OF_U32 - 1) as i128);
        let word = fb.extract_element(Ty::U32, as_words, word_index);
        fb.ret(vec![last, word]);
        fb.build();
    }
    let m = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(validate_module(&m), []);
    assert_eq!(
        run(&m, "bulk", vec![]),
        vec![int(Ty::U8, 5), int(Ty::U32, 0x0505_0505)]
    );
}

/// A splat initializer of 4 GiB, a zero-filled (BSS) global of 4 GiB, and a
/// nested splat of 4 TiB — each one run — read back element-wise and as
/// whole values.
#[test]
fn huge_splat_and_bss_globals_are_one_run() {
    let mut mb = ModuleBuilder::new("splat_globals");
    let u8_id = mb.add_type(Ty::U8);
    let i32_id = mb.add_type(Ty::I32);
    let row_id = mb.add_type(Ty::Array(i32_id, 1 << 20));
    let bytes = Ty::Array(u8_id, FOUR_GIB_OF_U8);
    let grid = Ty::Array(row_id, 1 << 20);
    mb.add_global(global(
        "THREES",
        bytes.clone(),
        Some(Constant::splat(Constant::Int(3), FOUR_GIB_OF_U8)),
    ));
    mb.add_global(global("BSS", bytes.clone(), None));
    mb.add_global(global(
        "GRID",
        grid.clone(),
        Some(Constant::splat(
            Constant::splat(Constant::Int(7), 1 << 20),
            1 << 20,
        )),
    ));
    let row = Ty::Array(i32_id, 1 << 20);
    let ft = mb.add_func_type(vec![], vec![Ty::U8, Ty::U8, Ty::I32]);
    {
        let mut fb = mb.function("globals", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let threes = fb.global_addr(GlobalId::new(0));
        let bss = fb.global_addr(GlobalId::new(1));
        let grid_ptr = fb.global_addr(GlobalId::new(2));
        let last_index = fb.iconst(Ty::U64, (FOUR_GIB_OF_U8 - 1) as i128);
        let three_ptr = fb.gep(Ty::U8, threes, vec![last_index]);
        let three = fb.load(Ty::U8, three_ptr);
        let zero_ptr = fb.gep(Ty::U8, bss, vec![last_index]);
        let zero = fb.load(Ty::U8, zero_ptr);
        let whole = fb.load(grid.clone(), grid_ptr);
        let row_index = fb.iconst(Ty::U64, (1 << 20) - 1);
        let last_row = fb.extract_element(row.clone(), whole, row_index);
        let seven = fb.extract_element(Ty::I32, last_row, row_index);
        fb.ret(vec![three, zero, seven]);
        fb.build();
    }
    let m = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(validate_module(&m), []);
    assert_eq!(
        run(&m, "globals", vec![]),
        vec![int(Ty::U8, 3), int(Ty::U8, 0), int(Ty::I32, 7)]
    );
}

#[test]
fn a_poison_element_and_a_non_array_type_fail_closed() {
    let mut mb = ModuleBuilder::new("fail_closed");
    let i64_id = mb.add_type(Ty::I64);
    let ft = mb.add_func_type(vec![], vec![Ty::Array(i64_id, 2)]);
    {
        let mut fb = mb.function("poison", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let poison = fb.undef(Ty::I64);
        let array = fb.array_splat(Ty::Array(i64_id, 2), poison);
        fb.ret(vec![array]);
        fb.build();
    }
    let m = mb.build().expect("ModuleBuilder::build: test fixture");
    let func = m.function_by_name("poison").unwrap();
    let error = Interpreter::with_module(&m)
        .execute_func(func.id, Vec::new())
        .expect_err("embedding poison inspects it");
    assert_eq!(error.code.as_str(), "undefined_behavior");
}
