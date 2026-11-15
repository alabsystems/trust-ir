// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// ══════════════════════════════════════════════════════════════════════════
// The tensor region (PKG-U13d): `Inst::TensorGather` and `Inst::TensorScatter`
// in the validator, the reference interpreter, SemR's executable oracle, the
// WS1.8 site table and the codegen gate (docs/SPEC_RATIFICATIONS.md §26).
// ══════════════════════════════════════════════════════════════════════════
//
// What this battery pins:
//
//   * gathers from rank-1 and rank-2 data at coordinate tensors of rank 0, 1
//     and 2, and scatters into rank-1 and rank-2 tensors from sources of rank
//     0, 1 and 2, with coordinate elements signed, unsigned, `isize` and
//     `usize` (each coordinate tensor its own), are accepted on the module and
//     the standalone path;
//   * every static rule is refused by its own variant (`InvalidTensorGather`
//     G1..G3, `InvalidTensorScatter` S1..S3) with a reason that names the
//     rule;
//   * the interpreter computes what a hand-written loop nest computes, in one
//     fuel unit per instruction, empty coordinate tensors (zero result
//     elements) and an empty source (`init` unchanged) included;
//   * a coordinate named by several source positions holds the row-major-last
//     of them, in rank 1 and rank 2;
//   * a coordinate outside its axis (at the extent, negative, past a zero
//     extent) and each extents mismatch is undefined behaviour by its
//     normative message, never a validator refusal, in the reference
//     interpreter AND in SemR's `semr_eval` run on the module's binary image,
//     which also returns the interpreter's tensors on the in-range runs (the
//     SemR half SKIPS only when no `lake` exists and `TRUST_IR_REQUIRE_LEAN`
//     is not `1`);
//   * the WS1.8 site table admits a `BoundsCheck` row sited on either
//     instruction, refuses `ArithmeticSafety`, `MemorySafety` and
//     `PanicFreedom` rows there (`ObligationSiteKindMismatch`), and an
//     `InBounds` claim on the instruction binds to the `BoundsCheck` row sited
//     on it (only the kernel authority is then missing);
//   * the default codegen gate refuses each instruction by name
//     (`UnlowerableForCodegen`): a tensor has no machine layout.

use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process::Command;

use trust_ir::proof::{
    ObligationKind, ObligationSite, ProofAnnotation, ProofObligation, ProofStatus,
};
use trust_ir::{
    ArrayValue, BlockId, FuncId, InterpretErrorCode, InterpretOutcome, InterpretResult,
    InterpretValue, InterpretValueKind, Interpreter, Module, Ty, ValueId,
};
use trust_ir_build::validate::obligation_kind_admits_site_instruction;
use trust_ir_build::{
    FunctionBuilder, ModuleBuilder, ValidationError, validate_function, validate_module,
    validate_module_for_codegen,
};

fn tensor(elem: Ty, rank: u32) -> Ty {
    Ty::Tensor(Box::new(elem), rank)
}

fn gate() -> trust_ir::BodyGate {
    trust_ir::BodyGate::Gated {
        authority: "tensor-gather-scatter".into(),
        evidence: None,
    }
}

/// The normative undefined-behaviour messages (§26), which SemR spells byte
/// for byte.
const GATHER_EXTENTS: &str = "tensor gather: coordinate tensors have different extents";
const GATHER_OUTSIDE: &str = "tensor gather: a coordinate is outside its axis";
const SCATTER_EXTENTS: &str = "tensor scatter: coordinate tensor extents differ from the source's";
const SCATTER_OUTSIDE: &str = "tensor scatter: a coordinate is outside its axis";

/// What emits a case's one instruction from the function's parameters.
type Emit = Box<dyn Fn(&mut FunctionBuilder<'_>, &[ValueId]) -> ValueId>;

/// One function `fn {name}(params..) -> result`, its body one instruction
/// `body` emits from the parameters.
struct Case {
    name: &'static str,
    params: Vec<Ty>,
    result: Ty,
    body: Emit,
}

fn case(
    name: &'static str,
    params: Vec<Ty>,
    result: Ty,
    body: impl Fn(&mut FunctionBuilder<'_>, &[ValueId]) -> ValueId + 'static,
) -> Case {
    Case {
        name,
        params,
        result,
        body: Box::new(body),
    }
}

fn module_of(name: &str, cases: &[Case]) -> Module {
    let mut mb = ModuleBuilder::new(name);
    for c in cases {
        let ft = mb.add_func_type(c.params.clone(), vec![c.result.clone()]);
        let mut fb = mb.function(c.name, ft);
        let entry = fb.create_block();
        let params: Vec<ValueId> = c
            .params
            .iter()
            .map(|ty| fb.add_block_param(entry, ty.clone()))
            .collect();
        fb.switch_to_block(entry);
        let out = (c.body)(&mut fb, &params);
        fb.ret(vec![out]);
        fb.set_body_gate(gate());
        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// `fn name(data, coords..) -> result { tensor_gather result %data coords
/// [%coords..] }`.
fn gather_case(name: &'static str, data: Ty, coords: Vec<Ty>, result: Ty) -> Case {
    let mut params = vec![data];
    params.extend(coords);
    let ty = result.clone();
    case(name, params, result, move |fb, p| {
        fb.tensor_gather(ty.clone(), p[0], p[1..].to_vec())
    })
}

/// `fn name(init, src, coords..) -> result { tensor_scatter result %init,
/// %src coords [%coords..] }`.
fn scatter_case(name: &'static str, init: Ty, src: Ty, coords: Vec<Ty>, result: Ty) -> Case {
    let mut params = vec![init, src];
    params.extend(coords);
    let ty = result.clone();
    case(name, params, result, move |fb, p| {
        fb.tensor_scatter(ty.clone(), p[0], p[1], p[2..].to_vec())
    })
}

// ───────────────────────────── the cases ─────────────────────────────

fn accepted_cases() -> Vec<Case> {
    vec![
        // Rank-1 data at a rank-1 signed coordinate tensor.
        gather_case(
            "gather_rows",
            tensor(Ty::I32, 1),
            vec![tensor(Ty::I32, 1)],
            tensor(Ty::I32, 1),
        ),
        // A rank-0 (`u8`) coordinate tensor: a rank-0 result.
        gather_case(
            "gather_scalar",
            tensor(Ty::I32, 1),
            vec![tensor(Ty::U8, 0)],
            tensor(Ty::I32, 0),
        ),
        // Rank-1 data at a rank-2 (`i8`) coordinate tensor.
        gather_case(
            "gather_tile",
            tensor(Ty::U8, 1),
            vec![tensor(Ty::I8, 2)],
            tensor(Ty::U8, 2),
        ),
        // Rank-2 data at rank-2 coordinate tensors of two element types.
        gather_case(
            "gather_matrix",
            tensor(Ty::I64, 2),
            vec![tensor(Ty::Usize, 2), tensor(Ty::I16, 2)],
            tensor(Ty::I64, 2),
        ),
        // Rank-2 data at rank-1 `isize` and `u64` coordinate tensors.
        gather_case(
            "gather_pairs",
            tensor(Ty::U16, 2),
            vec![tensor(Ty::Isize, 1), tensor(Ty::U64, 1)],
            tensor(Ty::U16, 1),
        ),
        // A rank-1 source into rank-1 `init` at `usize` coordinates.
        scatter_case(
            "scatter_row",
            tensor(Ty::I32, 1),
            tensor(Ty::I32, 1),
            vec![tensor(Ty::Usize, 1)],
            tensor(Ty::I32, 1),
        ),
        // A rank-0 source at a rank-0 `i8` coordinate tensor: one write.
        scatter_case(
            "scatter_scalar",
            tensor(Ty::I32, 1),
            tensor(Ty::I32, 0),
            vec![tensor(Ty::I8, 0)],
            tensor(Ty::I32, 1),
        ),
        // A rank-2 source into rank-2 `init` at `u32` and `isize` coordinates.
        scatter_case(
            "scatter_matrix",
            tensor(Ty::I64, 2),
            tensor(Ty::I64, 2),
            vec![tensor(Ty::U32, 2), tensor(Ty::Isize, 2)],
            tensor(Ty::I64, 2),
        ),
        // A rank-1 source into rank-2 `init` at `i64` and `usize` coordinates.
        scatter_case(
            "scatter_pairs",
            tensor(Ty::U8, 2),
            tensor(Ty::U8, 1),
            vec![tensor(Ty::I64, 1), tensor(Ty::Usize, 1)],
            tensor(Ty::U8, 2),
        ),
    ]
}

fn accepted() -> Module {
    module_of("tensor_gather_scatter_accepted", &accepted_cases())
}

#[test]
fn gathers_and_scatters_validate_on_both_paths() {
    let m = accepted();
    assert_eq!(validate_module(&m), []);
    for func in &m.functions {
        assert_eq!(
            validate_function(func),
            [],
            "{}: the standalone path agrees",
            func.name
        );
    }
}

// ───────────────────────────── static rules ─────────────────────────────

/// The refusals of a one-case module on both validation paths: every error
/// is `variant`'s or `beside` admits it, and one names `rule`.
fn assert_rule_beside(
    c: Case,
    is_variant: fn(&ValidationError) -> Option<&str>,
    rule: &str,
    beside: fn(&ValidationError) -> bool,
) {
    let name = c.name;
    let m = module_of("tensor_gather_scatter_refused", &[c]);
    for errors in [validate_module(&m), validate_function(&m.functions[0])] {
        assert!(!errors.is_empty(), "{name}: accepted");
        let reasons: Vec<&str> = errors.iter().filter_map(is_variant).collect();
        assert!(
            errors.iter().all(|e| is_variant(e).is_some() || beside(e)),
            "{name}: only the instruction's own variant expected, got {errors:?}"
        );
        assert!(
            reasons.iter().any(|reason| reason.starts_with(rule)),
            "{name}: no refusal names {rule:?}: {errors:?}"
        );
    }
}

/// [`assert_rule_beside`] with nothing beside the instruction's own variant.
fn assert_rule(c: Case, is_variant: fn(&ValidationError) -> Option<&str>, rule: &str) {
    assert_rule_beside(c, is_variant, rule, |_| false);
}

/// A tensor type whose element is not an integer is refused at its type
/// occurrence too (`InvalidTensorType`, PKG-U13a), beside the instruction's
/// own rule.
fn non_integer_tensor_type(e: &ValidationError) -> bool {
    matches!(e, ValidationError::InvalidTensorType { .. })
}

fn gather_reason(e: &ValidationError) -> Option<&str> {
    match e {
        ValidationError::InvalidTensorGather { reason, .. } => Some(reason),
        _ => None,
    }
}

fn scatter_reason(e: &ValidationError) -> Option<&str> {
    match e {
        ValidationError::InvalidTensorScatter { reason, .. } => Some(reason),
        _ => None,
    }
}

#[test]
fn the_gather_rules_are_each_refused_by_name() {
    let row = |elem: Ty| tensor(elem, 1);
    // G1: the data's element differs from the result's; the data is not a
    // tensor; the result is not a tensor.
    assert_rule(
        gather_case("g1_elem", row(Ty::I64), vec![row(Ty::Usize)], row(Ty::I32)),
        gather_reason,
        "rule G1",
    );
    assert_rule(
        gather_case("g1_data", Ty::I32, vec![row(Ty::Usize)], row(Ty::I32)),
        gather_reason,
        "rule G1",
    );
    assert_rule(
        gather_case("g1_result", row(Ty::I32), vec![row(Ty::Usize)], Ty::I32),
        gather_reason,
        "rule G1",
    );
    // G2: rank-0 data; no coordinate operand; too few and too many.
    assert_rule(
        gather_case(
            "g2_rank0",
            tensor(Ty::I32, 0),
            vec![row(Ty::Usize)],
            row(Ty::I32),
        ),
        gather_reason,
        "rule G2",
    );
    assert_rule(
        gather_case("g2_none", row(Ty::I32), vec![], row(Ty::I32)),
        gather_reason,
        "rule G2",
    );
    assert_rule(
        gather_case(
            "g2_few",
            tensor(Ty::I32, 2),
            vec![row(Ty::Usize)],
            row(Ty::I32),
        ),
        gather_reason,
        "rule G2",
    );
    assert_rule(
        gather_case(
            "g2_many",
            row(Ty::I32),
            vec![row(Ty::Usize), row(Ty::Usize)],
            row(Ty::I32),
        ),
        gather_reason,
        "rule G2",
    );
    // G3: a coordinate tensor of the wrong rank (the second, past a good
    // first); a scalar coordinate.
    assert_rule(
        gather_case(
            "g3_rank",
            tensor(Ty::I32, 2),
            vec![row(Ty::Usize), tensor(Ty::Usize, 2)],
            row(Ty::I32),
        ),
        gather_reason,
        "rule G3",
    );
    assert_rule(
        gather_case("g3_scalar", row(Ty::I32), vec![Ty::Usize], row(Ty::I32)),
        gather_reason,
        "rule G3",
    );
    // G3: a `Bool` and an `f32` coordinate element. Their tensor types are
    // refused at the type occurrence as well.
    for (name, elem) in [("g3_bool", Ty::Bool), ("g3_float", Ty::F32)] {
        assert_rule_beside(
            gather_case(name, row(Ty::I32), vec![row(elem)], row(Ty::I32)),
            gather_reason,
            "rule G3",
            non_integer_tensor_type,
        );
    }
}

#[test]
fn the_scatter_rules_are_each_refused_by_name() {
    let row = |elem: Ty| tensor(elem, 1);
    // S1: `init` of another rank and of another element than the result;
    // the source's element differs; the source is not a tensor; the result
    // is not a tensor, and not an integer tensor.
    assert_rule(
        scatter_case(
            "s1_init_rank",
            tensor(Ty::I32, 2),
            row(Ty::I32),
            vec![row(Ty::Usize)],
            row(Ty::I32),
        ),
        scatter_reason,
        "rule S1",
    );
    assert_rule(
        scatter_case(
            "s1_init_elem",
            row(Ty::I64),
            row(Ty::I32),
            vec![row(Ty::Usize)],
            row(Ty::I32),
        ),
        scatter_reason,
        "rule S1",
    );
    assert_rule(
        scatter_case(
            "s1_src_elem",
            row(Ty::I32),
            row(Ty::U32),
            vec![row(Ty::Usize)],
            row(Ty::I32),
        ),
        scatter_reason,
        "rule S1",
    );
    assert_rule(
        scatter_case(
            "s1_src_scalar",
            row(Ty::I32),
            Ty::I32,
            vec![row(Ty::Usize)],
            row(Ty::I32),
        ),
        scatter_reason,
        "rule S1",
    );
    assert_rule(
        scatter_case(
            "s1_result",
            Ty::I32,
            row(Ty::I32),
            vec![row(Ty::Usize)],
            Ty::I32,
        ),
        scatter_reason,
        "rule S1",
    );
    assert_rule_beside(
        scatter_case(
            "s1_result_bool",
            row(Ty::Bool),
            row(Ty::Bool),
            vec![row(Ty::Usize)],
            row(Ty::Bool),
        ),
        scatter_reason,
        "rule S1",
        non_integer_tensor_type,
    );
    // S2: a rank-0 result; too few and too many coordinate operands.
    assert_rule(
        scatter_case(
            "s2_rank0",
            tensor(Ty::I32, 0),
            row(Ty::I32),
            vec![],
            tensor(Ty::I32, 0),
        ),
        scatter_reason,
        "rule S2",
    );
    assert_rule(
        scatter_case(
            "s2_few",
            tensor(Ty::I32, 2),
            row(Ty::I32),
            vec![row(Ty::Usize)],
            tensor(Ty::I32, 2),
        ),
        scatter_reason,
        "rule S2",
    );
    assert_rule(
        scatter_case(
            "s2_many",
            row(Ty::I32),
            row(Ty::I32),
            vec![row(Ty::Usize), row(Ty::Usize)],
            row(Ty::I32),
        ),
        scatter_reason,
        "rule S2",
    );
    // S3: a coordinate tensor of the result's rank, not the source's; a
    // scalar coordinate; a `Bool` coordinate element.
    assert_rule(
        scatter_case(
            "s3_rank",
            tensor(Ty::I32, 2),
            row(Ty::I32),
            vec![row(Ty::Usize), tensor(Ty::Usize, 2)],
            tensor(Ty::I32, 2),
        ),
        scatter_reason,
        "rule S3",
    );
    assert_rule(
        scatter_case(
            "s3_scalar",
            row(Ty::I32),
            row(Ty::I32),
            vec![Ty::Usize],
            row(Ty::I32),
        ),
        scatter_reason,
        "rule S3",
    );
    assert_rule_beside(
        scatter_case(
            "s3_bool",
            row(Ty::I32),
            row(Ty::I32),
            vec![row(Ty::Bool)],
            row(Ty::I32),
        ),
        scatter_reason,
        "rule S3",
        non_integer_tensor_type,
    );
}

// ───────────────────────────── the interpreter ─────────────────────────────

fn int(ty: &Ty, value: i128) -> InterpretValue {
    InterpretValue::int(ty.clone(), value).expect("integer value")
}

/// A tensor of `elem` with extents `dims` and the row-major `values`.
fn value(elem: &Ty, dims: &[u64], values: &[i128]) -> InterpretValue {
    InterpretValue {
        ty: tensor(elem.clone(), dims.len() as u32),
        kind: InterpretValueKind::Tensor {
            dims: dims.to_vec(),
            elems: ArrayValue::from_vec(values.iter().map(|&x| int(elem, x)).collect()),
        },
    }
}

fn func_id(m: &Module, name: &str) -> FuncId {
    m.functions
        .iter()
        .find(|f| f.name == name)
        .unwrap_or_else(|| panic!("no function {name}"))
        .id
}

fn run(m: &Module, name: &str, args: Vec<InterpretValue>) -> InterpretResult<InterpretOutcome> {
    Interpreter::with_module(m).execute_func(func_id(m, name), args)
}

/// The returned tensor's extents and elements (each the integer its type
/// denotes).
fn unpack(outcome: &InterpretOutcome) -> (Vec<u64>, Vec<i128>) {
    let [result] = outcome.returns.as_slice() else {
        panic!("one return, got {:?}", outcome.returns);
    };
    let InterpretValueKind::Tensor { dims, elems } = &result.kind else {
        panic!("a tensor result, got {result:?}");
    };
    let values = elems
        .iter()
        .map(|element| {
            let carried = element.as_int().expect("integer element");
            if carried.signed {
                carried.as_signed()
            } else {
                carried.as_unsigned() as i128
            }
        })
        .collect();
    (dims.clone(), values)
}

/// Run `name` and return its result, holding the fuel to one unit for the
/// instruction and one for the return.
fn computes(m: &Module, name: &str, args: Vec<InterpretValue>) -> (Vec<u64>, Vec<i128>) {
    let outcome = run(m, name, args).unwrap_or_else(|e| panic!("{name}: {e:?}"));
    assert_eq!(outcome.steps, 2, "{name}: one fuel unit per instruction");
    unpack(&outcome)
}

fn ub(m: &Module, name: &str, args: Vec<InterpretValue>, message: &str) {
    let error = run(m, name, args).expect_err(name);
    assert_eq!(
        (error.code, error.message.as_str()),
        (InterpretErrorCode::UndefinedBehavior, message),
        "{name}"
    );
}

/// The row-major offset, in a tensor of extents `dims`, of the coordinate
/// the coordinate tensors `coords` hold at position `p` (each element the
/// integer its type denotes), asserted inside every axis.
fn hand_offset(dims: &[u64], coords: &[&[i128]], p: usize) -> usize {
    assert_eq!(dims.len(), coords.len(), "one coordinate tensor per axis");
    let mut offset = 0usize;
    for (&extent, coord) in dims.iter().zip(coords) {
        let c = coord[p];
        assert!(
            (0..i128::from(extent)).contains(&c),
            "the hand loop reads in range: {c} in {extent}"
        );
        offset = offset * extent as usize + c as usize;
    }
    offset
}

/// A gather by a hand-written loop: for every row-major position `p` of the
/// coordinate tensors (extents `coord_dims`), `data`'s element at
/// `(coords[0][p], ..)`.
fn hand_gather(
    data_dims: &[u64],
    data: &[i128],
    coord_dims: &[u64],
    coords: &[&[i128]],
) -> (Vec<u64>, Vec<i128>) {
    let count: u64 = coord_dims.iter().product();
    let elems = (0..count as usize)
        .map(|p| data[hand_offset(data_dims, coords, p)])
        .collect();
    (coord_dims.to_vec(), elems)
}

/// A scatter by a hand-written loop: a copy of `init`, then for every
/// source position `p` in row-major order, `src[p]` written at `(coords[0][p],
/// ..)`.
fn hand_scatter(
    init_dims: &[u64],
    init: &[i128],
    src: &[i128],
    coords: &[&[i128]],
) -> (Vec<u64>, Vec<i128>) {
    let mut out = init.to_vec();
    for (p, &x) in src.iter().enumerate() {
        out[hand_offset(init_dims, coords, p)] = x;
    }
    (init_dims.to_vec(), out)
}

const DATA: [i128; 5] = [10, -20, 30, -40, 50];

/// A `[3, 4]` `i64` matrix, row-major.
fn matrix() -> Vec<i128> {
    (0..12).map(|k| k * 7 - 30).collect()
}

#[test]
fn gathers_match_a_hand_loop() {
    let m = accepted();
    // Rank-1 data, a rank-1 signed coordinate tensor, one coordinate twice.
    let at = [4, 0, 0, 2];
    assert_eq!(
        computes(
            &m,
            "gather_rows",
            vec![value(&Ty::I32, &[5], &DATA), value(&Ty::I32, &[4], &at)],
        ),
        hand_gather(&[5], &DATA, &[4], &[&at])
    );
    // A rank-0 coordinate tensor: a rank-0 result, one element.
    assert_eq!(
        computes(
            &m,
            "gather_scalar",
            vec![value(&Ty::I32, &[5], &DATA), value(&Ty::U8, &[], &[3])],
        ),
        (vec![], vec![-40])
    );
    assert_eq!(hand_gather(&[5], &DATA, &[], &[&[3]]), (vec![], vec![-40]));
    // A rank-2 `i8` coordinate tensor into rank-1 data.
    let bytes = [200, 7, 255];
    let tile = [2, 0, 1, 2];
    assert_eq!(
        computes(
            &m,
            "gather_tile",
            vec![value(&Ty::U8, &[3], &bytes), value(&Ty::I8, &[2, 2], &tile)],
        ),
        hand_gather(&[3], &bytes, &[2, 2], &[&tile])
    );
    // Rank-2 data at rank-2 `usize` and `i16` coordinate tensors.
    let x = matrix();
    let rows = [0, 1, 2, 2, 2, 0];
    let cols = [3, 0, 1, 2, 3, 0];
    assert_eq!(
        computes(
            &m,
            "gather_matrix",
            vec![
                value(&Ty::I64, &[3, 4], &x),
                value(&Ty::Usize, &[2, 3], &rows),
                value(&Ty::I16, &[2, 3], &cols),
            ],
        ),
        hand_gather(&[3, 4], &x, &[2, 3], &[&rows, &cols])
    );
    // Rank-2 data at rank-1 `isize` and `u64` coordinate tensors.
    let y = [1, 65535, 300, 0, 42, 7];
    let rows = [1, 0, 1, 1];
    let cols = [2, 2, 0, 2];
    assert_eq!(
        computes(
            &m,
            "gather_pairs",
            vec![
                value(&Ty::U16, &[2, 3], &y),
                value(&Ty::Isize, &[4], &rows),
                value(&Ty::U64, &[4], &cols),
            ],
        ),
        hand_gather(&[2, 3], &y, &[4], &[&rows, &cols])
    );
    // Empty coordinate tensors: zero result elements, from any data, an
    // empty one included, and at rank 2.
    for data in [value(&Ty::I32, &[5], &DATA), value(&Ty::I32, &[0], &[])] {
        assert_eq!(
            computes(&m, "gather_rows", vec![data, value(&Ty::I32, &[0], &[])]),
            (vec![0], vec![])
        );
    }
    assert_eq!(
        computes(
            &m,
            "gather_matrix",
            vec![
                value(&Ty::I64, &[3, 4], &x),
                value(&Ty::Usize, &[0, 3], &[]),
                value(&Ty::I16, &[0, 3], &[]),
            ],
        ),
        (vec![0, 3], vec![])
    );
}

#[test]
fn scatters_match_a_hand_loop() {
    let m = accepted();
    let init = [1, 2, 3, 4, 5];
    // Rank 1, unique `usize` coordinates.
    let src = [-7, 8, -9];
    let at = [4, 0, 2];
    assert_eq!(
        computes(
            &m,
            "scatter_row",
            vec![
                value(&Ty::I32, &[5], &init),
                value(&Ty::I32, &[3], &src),
                value(&Ty::Usize, &[3], &at),
            ],
        ),
        hand_scatter(&[5], &init, &src, &[&at])
    );
    // A rank-0 source at a rank-0 `i8` coordinate: one write.
    assert_eq!(
        computes(
            &m,
            "scatter_scalar",
            vec![
                value(&Ty::I32, &[5], &init),
                value(&Ty::I32, &[], &[77]),
                value(&Ty::I8, &[], &[1]),
            ],
        ),
        (vec![5], vec![1, 77, 3, 4, 5])
    );
    // Rank 2 at rank-2 `u32` and `isize` coordinate tensors.
    let grid: Vec<i128> = (0..9).map(|k| k * 11 - 40).collect();
    let src = [100, -200, 300, i128::from(i64::MIN)];
    let rows = [2, 0, 1, 2];
    let cols = [0, 2, 1, 1];
    assert_eq!(
        computes(
            &m,
            "scatter_matrix",
            vec![
                value(&Ty::I64, &[3, 3], &grid),
                value(&Ty::I64, &[2, 2], &src),
                value(&Ty::U32, &[2, 2], &rows),
                value(&Ty::Isize, &[2, 2], &cols),
            ],
        ),
        hand_scatter(&[3, 3], &grid, &src, &[&rows, &cols])
    );
    // A rank-1 source into rank-2 `init` at `i64` and `usize` coordinates.
    let bytes = [9, 8, 7, 6, 5, 4];
    let src = [255, 1, 128];
    let rows = [1, 0, 1];
    let cols = [0, 2, 2];
    assert_eq!(
        computes(
            &m,
            "scatter_pairs",
            vec![
                value(&Ty::U8, &[2, 3], &bytes),
                value(&Ty::U8, &[3], &src),
                value(&Ty::I64, &[3], &rows),
                value(&Ty::Usize, &[3], &cols),
            ],
        ),
        hand_scatter(&[2, 3], &bytes, &src, &[&rows, &cols])
    );
    // An empty source leaves `init` unchanged, at rank 1 and rank 2, and
    // into an empty `init` too.
    assert_eq!(
        computes(
            &m,
            "scatter_row",
            vec![
                value(&Ty::I32, &[5], &init),
                value(&Ty::I32, &[0], &[]),
                value(&Ty::Usize, &[0], &[]),
            ],
        ),
        (vec![5], init.to_vec())
    );
    assert_eq!(
        computes(
            &m,
            "scatter_row",
            vec![
                value(&Ty::I32, &[0], &[]),
                value(&Ty::I32, &[0], &[]),
                value(&Ty::Usize, &[0], &[]),
            ],
        ),
        (vec![0], vec![])
    );
    assert_eq!(
        computes(
            &m,
            "scatter_matrix",
            vec![
                value(&Ty::I64, &[3, 3], &grid),
                value(&Ty::I64, &[0, 2], &[]),
                value(&Ty::U32, &[0, 2], &[]),
                value(&Ty::Isize, &[0, 2], &[]),
            ],
        ),
        (vec![3, 3], grid.clone())
    );
}

#[test]
fn a_repeated_coordinate_keeps_the_row_major_last_write() {
    let m = accepted();
    let row = |src: &[i128], at: &[i128]| {
        computes(
            &m,
            "scatter_row",
            vec![
                value(&Ty::I32, &[5], &[0; 5]),
                value(&Ty::I32, &[src.len() as u64], src),
                value(&Ty::Usize, &[at.len() as u64], at),
            ],
        )
    };
    // Rank 1: positions 0, 2 and 3 name coordinate 1, position 1 names 3.
    let (src, at) = ([11, 22, 33, 44], [1, 3, 1, 1]);
    assert_eq!(row(&src, &at), (vec![5], vec![0, 44, 0, 22, 0]));
    assert_eq!(row(&src, &at), hand_scatter(&[5], &[0; 5], &src, &[&at]));
    // The same writes in the reverse source order: the other value wins.
    assert_eq!(
        row(&[44, 33, 22, 11], &[1, 1, 3, 1]),
        (vec![5], vec![0, 11, 0, 22, 0])
    );
    // Rank 2 coordinate tensors over a `[2, 2]` source: `(0, 0)` at
    // positions 0, 2 and 3, `(2, 1)` at position 1.
    let src = [5, 6, 7, 8];
    let rows = [0, 2, 0, 0];
    let cols = [0, 1, 0, 0];
    assert_eq!(
        computes(
            &m,
            "scatter_matrix",
            vec![
                value(&Ty::I64, &[3, 3], &[0; 9]),
                value(&Ty::I64, &[2, 2], &src),
                value(&Ty::U32, &[2, 2], &rows),
                value(&Ty::Isize, &[2, 2], &cols),
            ],
        ),
        (vec![3, 3], vec![8, 0, 0, 0, 0, 0, 0, 6, 0])
    );
    // Rank-2 `init` from a rank-1 source: `(1, 2)` at positions 0 and 2.
    assert_eq!(
        computes(
            &m,
            "scatter_pairs",
            vec![
                value(&Ty::U8, &[2, 3], &[0; 6]),
                value(&Ty::U8, &[3], &[10, 20, 30]),
                value(&Ty::I64, &[3], &[1, 0, 1]),
                value(&Ty::Usize, &[3], &[2, 0, 2]),
            ],
        ),
        (vec![2, 3], vec![20, 0, 0, 0, 0, 30])
    );
}

// ───────────────────────── preconditions, both engines ─────────────────────────

/// One run of the accepted module: a function, its arguments, and what both
/// engines must answer.
struct Run {
    name: &'static str,
    args: Vec<InterpretValue>,
    /// `Some(message)`: undefined behaviour by that normative message;
    /// `None`: a tensor, the interpreter's.
    ub: Option<&'static str>,
}

fn ub_run(name: &'static str, args: Vec<InterpretValue>, message: &'static str) -> Run {
    Run {
        name,
        args,
        ub: Some(message),
    }
}

fn ok_run(name: &'static str, args: Vec<InterpretValue>) -> Run {
    Run {
        name,
        args,
        ub: None,
    }
}

/// Every out-of-range coordinate and extents mismatch, each at one site that
/// raises it, then in-range runs (an in-range gather, a scatter with a
/// repeated coordinate) whose tensors SemR must return as the interpreter
/// does.
fn precondition_runs() -> Vec<Run> {
    let data3 = || value(&Ty::I32, &[3], &[1, 2, 3]);
    let pairs = || value(&Ty::U16, &[2, 3], &[1, 2, 3, 4, 5, 6]);
    let x = matrix();
    vec![
        // ---- gather: a coordinate outside its axis ----
        // Equal to the extent.
        ub_run(
            "gather_rows",
            vec![data3(), value(&Ty::I32, &[2], &[1, 3])],
            GATHER_OUTSIDE,
        ),
        // A negative `i8` (`-1`, the residue 255).
        ub_run(
            "gather_tile",
            vec![
                value(&Ty::U8, &[3], &[4, 5, 6]),
                value(&Ty::I8, &[2, 2], &[0, -1, 1, 2]),
            ],
            GATHER_OUTSIDE,
        ),
        // A negative `isize`, on the first axis of two.
        ub_run(
            "gather_pairs",
            vec![
                pairs(),
                value(&Ty::Isize, &[2], &[0, -1]),
                value(&Ty::U64, &[2], &[0, 0]),
            ],
            GATHER_OUTSIDE,
        ),
        // The largest `u64`, on the second axis.
        ub_run(
            "gather_pairs",
            vec![
                pairs(),
                value(&Ty::Isize, &[1], &[1]),
                value(&Ty::U64, &[1], &[i128::from(u64::MAX)]),
            ],
            GATHER_OUTSIDE,
        ),
        // The largest `usize`, at rank 2.
        ub_run(
            "gather_matrix",
            vec![
                value(&Ty::I64, &[3, 4], &x),
                value(&Ty::Usize, &[1, 1], &[i128::from(u64::MAX)]),
                value(&Ty::I16, &[1, 1], &[0]),
            ],
            GATHER_OUTSIDE,
        ),
        // Past a zero extent: no coordinate is inside it.
        ub_run(
            "gather_rows",
            vec![value(&Ty::I32, &[0], &[]), value(&Ty::I32, &[1], &[0])],
            GATHER_OUTSIDE,
        ),
        ub_run(
            "gather_scalar",
            vec![value(&Ty::I32, &[0], &[]), value(&Ty::U8, &[], &[0])],
            GATHER_OUTSIDE,
        ),
        // ---- gather: coordinate tensors of different extents ----
        ub_run(
            "gather_matrix",
            vec![
                value(&Ty::I64, &[3, 4], &x),
                value(&Ty::Usize, &[2, 3], &[0; 6]),
                value(&Ty::I16, &[3, 2], &[0; 6]),
            ],
            GATHER_EXTENTS,
        ),
        ub_run(
            "gather_pairs",
            vec![
                pairs(),
                value(&Ty::Isize, &[2], &[0, 1]),
                value(&Ty::U64, &[3], &[0, 1, 2]),
            ],
            GATHER_EXTENTS,
        ),
        // The extents precondition is decided before the bounds one.
        ub_run(
            "gather_pairs",
            vec![
                pairs(),
                value(&Ty::Isize, &[2], &[-1, 9]),
                value(&Ty::U64, &[1], &[9]),
            ],
            GATHER_EXTENTS,
        ),
        // ---- scatter: a coordinate outside its axis ----
        // Equal to the extent, after an in-range position.
        ub_run(
            "scatter_row",
            vec![
                data3(),
                value(&Ty::I32, &[2], &[7, 8]),
                value(&Ty::Usize, &[2], &[0, 3]),
            ],
            SCATTER_OUTSIDE,
        ),
        // A negative rank-0 `i8`.
        ub_run(
            "scatter_scalar",
            vec![
                data3(),
                value(&Ty::I32, &[], &[5]),
                value(&Ty::I8, &[], &[-1]),
            ],
            SCATTER_OUTSIDE,
        ),
        // A negative `isize`, on the second axis.
        ub_run(
            "scatter_matrix",
            vec![
                value(&Ty::I64, &[3, 3], &[0; 9]),
                value(&Ty::I64, &[1, 1], &[1]),
                value(&Ty::U32, &[1, 1], &[0]),
                value(&Ty::Isize, &[1, 1], &[-1]),
            ],
            SCATTER_OUTSIDE,
        ),
        // Equal to the extent of the first axis of a rank-2 `init`.
        ub_run(
            "scatter_pairs",
            vec![
                value(&Ty::U8, &[2, 3], &[0; 6]),
                value(&Ty::U8, &[2], &[1, 2]),
                value(&Ty::I64, &[2], &[0, 2]),
                value(&Ty::Usize, &[2], &[0, 0]),
            ],
            SCATTER_OUTSIDE,
        ),
        // Past a zero extent of `init`.
        ub_run(
            "scatter_row",
            vec![
                value(&Ty::I32, &[0], &[]),
                value(&Ty::I32, &[1], &[7]),
                value(&Ty::Usize, &[1], &[0]),
            ],
            SCATTER_OUTSIDE,
        ),
        // ---- scatter: coordinate tensors whose extents are not the source's ----
        ub_run(
            "scatter_row",
            vec![
                data3(),
                value(&Ty::I32, &[2], &[7, 8]),
                value(&Ty::Usize, &[3], &[0, 1, 2]),
            ],
            SCATTER_EXTENTS,
        ),
        // The second coordinate tensor only.
        ub_run(
            "scatter_pairs",
            vec![
                value(&Ty::U8, &[2, 3], &[0; 6]),
                value(&Ty::U8, &[2], &[1, 2]),
                value(&Ty::I64, &[2], &[0, 1]),
                value(&Ty::Usize, &[1], &[0]),
            ],
            SCATTER_EXTENTS,
        ),
        // At rank 2, the extents transposed; decided before the bounds.
        ub_run(
            "scatter_matrix",
            vec![
                value(&Ty::I64, &[3, 3], &[0; 9]),
                value(&Ty::I64, &[1, 2], &[1, 2]),
                value(&Ty::U32, &[2, 1], &[9, 9]),
                value(&Ty::Isize, &[1, 2], &[-1, -1]),
            ],
            SCATTER_EXTENTS,
        ),
        // ---- in range: the interpreter's tensors ----
        ok_run(
            "gather_matrix",
            vec![
                value(&Ty::I64, &[3, 4], &x),
                value(&Ty::Usize, &[2, 3], &[0, 1, 2, 2, 2, 0]),
                value(&Ty::I16, &[2, 3], &[3, 0, 1, 2, 3, 0]),
            ],
        ),
        ok_run(
            "gather_tile",
            vec![
                value(&Ty::U8, &[3], &[200, 7, 255]),
                value(&Ty::I8, &[2, 2], &[2, 0, 1, 2]),
            ],
        ),
        ok_run(
            "gather_scalar",
            vec![value(&Ty::I32, &[5], &DATA), value(&Ty::U8, &[], &[4])],
        ),
        ok_run(
            "gather_rows",
            vec![value(&Ty::I32, &[0], &[]), value(&Ty::I32, &[0], &[])],
        ),
        ok_run(
            "scatter_matrix",
            vec![
                value(&Ty::I64, &[3, 3], &[0; 9]),
                value(&Ty::I64, &[2, 2], &[5, 6, 7, 8]),
                value(&Ty::U32, &[2, 2], &[0, 2, 0, 0]),
                value(&Ty::Isize, &[2, 2], &[0, 1, 0, 0]),
            ],
        ),
        ok_run(
            "scatter_row",
            vec![
                value(&Ty::I32, &[5], &[0; 5]),
                value(&Ty::I32, &[4], &[11, 22, 33, 44]),
                value(&Ty::Usize, &[4], &[1, 3, 1, 1]),
            ],
        ),
        ok_run(
            "scatter_pairs",
            vec![
                value(&Ty::U8, &[2, 3], &[0; 6]),
                value(&Ty::U8, &[3], &[10, 20, 30]),
                value(&Ty::I64, &[3], &[1, 0, 1]),
                value(&Ty::Usize, &[3], &[2, 0, 2]),
            ],
        ),
        ok_run(
            "scatter_row",
            vec![
                value(&Ty::I32, &[5], &[1, 2, 3, 4, 5]),
                value(&Ty::I32, &[0], &[]),
                value(&Ty::Usize, &[0], &[]),
            ],
        ),
    ]
}

#[test]
fn out_of_range_coordinates_are_undefined_behaviour_in_both_engines() {
    let m = accepted();
    assert_eq!(
        validate_module(&m),
        [],
        "every precondition is a run-time one"
    );
    let runs = precondition_runs();
    // The reference interpreter: the normative message, or a tensor (which
    // the hand loops above pin).
    let mut wanted = Vec::new();
    for r in &runs {
        match r.ub {
            Some(message) => {
                ub(&m, r.name, r.args.clone(), message);
                wanted.push(SemrVerdict::Ub(message.to_string()));
            }
            None => {
                let outcome =
                    run(&m, r.name, r.args.clone()).unwrap_or_else(|e| panic!("{}: {e:?}", r.name));
                let [result] = outcome.returns.as_slice() else {
                    panic!("{}: one return", r.name);
                };
                wanted.push(semr_spelling(result));
            }
        }
    }
    let ub_runs = runs.iter().filter(|r| r.ub.is_some()).count();
    assert!(
        ub_runs >= 12 && runs.len() > ub_runs,
        "both halves are populated"
    );

    // SemR's executable oracle on the module's binary image.
    let Some(exe) = semr_eval() else {
        return;
    };
    let semr_runs: Vec<(FuncId, &[InterpretValue])> = runs
        .iter()
        .map(|r| (func_id(&m, r.name), r.args.as_slice()))
        .collect();
    let verdicts = run_semr(&exe, &m, &semr_runs);
    let mut agreed = 0;
    for ((r, want), got) in runs.iter().zip(&wanted).zip(&verdicts) {
        assert_eq!(got, want, "SemR on {} {:?}", r.name, r.args);
        agreed += 1;
    }
    assert_eq!(agreed, runs.len());
    // The evidence line goes to the process's stderr directly, past libtest's
    // capture of `eprintln!`, so a passing run prints it.
    writeln!(
        std::io::stderr().lock(),
        "tensor_gather_scatter: SemR's semr_eval agreed with the reference interpreter on \
         {agreed} runs of the module's binary image ({ub_runs} undefined behaviour by the \
         byte-identical normative message, {} tensors)",
        agreed - ub_runs
    )
    .expect("write the evidence line");
}

// ───────────────────────────── SemR's oracle ─────────────────────────────

/// Fuel and call depth for each SemR run (the differential's).
const SEMR_FUEL: u64 = 10_000;
const SEMR_CALL_DEPTH: u64 = 64;

fn semr_package() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../lean/semr")
}

/// The Lake that builds SemR: `TRUST_IR_SEMR_LAKE`, `TRUST_IR_LAKE`, elan's
/// shim, then `PATH` (the order of the other SemR tests).
fn lake() -> Option<PathBuf> {
    if let Some(explicit) = std::env::var_os("TRUST_IR_SEMR_LAKE") {
        return Some(explicit.into());
    }
    if let Some(explicit) = std::env::var_os("TRUST_IR_LAKE") {
        return Some(explicit.into());
    }
    if let Some(home) = std::env::var_os("HOME") {
        let shim = Path::new(&home).join(".elan/bin/lake");
        if shim.is_file() {
            return Some(shim);
        }
    }
    std::env::split_paths(&std::env::var_os("PATH")?)
        .map(|directory| directory.join("lake"))
        .find(|candidate| candidate.is_file())
}

/// Build `semr_eval` with the package's pinned Lean and return its path, or
/// `None` (a `SKIPPED:` line) when no Lake exists and Lean is not required.
fn semr_eval() -> Option<PathBuf> {
    let Some(lake) = lake() else {
        assert_ne!(
            std::env::var("TRUST_IR_REQUIRE_LEAN").as_deref(),
            Ok("1"),
            "TRUST_IR_REQUIRE_LEAN=1 but no lake builds lean/semr"
        );
        writeln!(
            std::io::stderr().lock(),
            "SKIPPED: tensor_gather_scatter's SemR half needs lake (TRUST_IR_LAKE, \
             $HOME/.elan/bin/lake, PATH); the interpreter half ran"
        )
        .expect("write the skip line");
        return None;
    };
    let package = semr_package();
    let mut command = Command::new(&lake);
    command.current_dir(&package).env_remove("SDKROOT");
    if let Some(bin) = lake.parent() {
        let mut path = bin.as_os_str().to_os_string();
        path.push(":");
        path.push(std::env::var_os("PATH").unwrap_or_default());
        command.env("PATH", path);
    }
    let out = command
        .args(["build", "semr_eval"])
        .output()
        .unwrap_or_else(|e| panic!("run {} build semr_eval: {e}", lake.display()));
    assert!(
        out.status.success(),
        "`lake build semr_eval` failed in {}:\n{}{}",
        package.display(),
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    let exe = package.join(".lake/build/bin/semr_eval");
    assert!(
        exe.is_file(),
        "lake reported success but {} is missing",
        exe.display()
    );
    Some(exe)
}

/// A scratch directory unique to this process and call, under the test
/// target's own scratch root (`CARGO_TARGET_TMPDIR`), removed when the guard
/// drops, on a panic too.
struct Scratch(PathBuf);

impl Scratch {
    fn new() -> Self {
        static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
        let call = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!(
            "tensor-gather-scatter-semr-{}-{call}",
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap_or_else(|e| panic!("scratch {}: {e}", dir.display()));
        Scratch(dir)
    }

    fn path(&self, name: &str) -> PathBuf {
        self.0.join(name)
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// SemR's spelling of an integer type (`intTyOfCode` in
/// `lean/semr/SemRRuntimeMain.lean`).
fn semr_int_code(ty: &Ty) -> u32 {
    match ty {
        Ty::I8 => 0,
        Ty::I16 => 1,
        Ty::I32 => 2,
        Ty::I64 => 3,
        Ty::I128 => 4,
        Ty::Isize => 5,
        Ty::U8 => 6,
        Ty::U16 => 7,
        Ty::U32 => 8,
        Ty::U64 => 9,
        Ty::U128 => 10,
        Ty::Usize => 11,
        other => panic!("not an integer element type: {other}"),
    }
}

/// A tensor's element type, extents and row-major residues.
fn tensor_parts(v: &InterpretValue) -> (&Ty, &[u64], Vec<trust_ir::InterpretInt>) {
    let (Ty::Tensor(elem, _), InterpretValueKind::Tensor { dims, elems }) = (&v.ty, &v.kind) else {
        panic!("a tensor value, got {v:?}")
    };
    let ints = elems
        .iter()
        .map(|e| e.as_int().expect("a tensor element is an integer"))
        .collect();
    (&**elem, dims.as_slice(), ints)
}

/// A tensor argument as `semr_eval` reads it: `t<element code>:<element
/// source bits>:<extents>:<residues>` (the differential's `semr_arg`). An
/// empty tensor states its type's reference width.
fn semr_arg(v: &InterpretValue) -> String {
    let (elem, dims, ints) = tensor_parts(v);
    let bits = ints.first().map_or_else(
        || {
            elem.bit_width_with(64)
                .expect("an integer element has a width")
        },
        |i| i.bits,
    );
    assert!(
        ints.iter().all(|i| i.bits == bits),
        "a tensor's elements share one width: {v:?}"
    );
    let dims: Vec<String> = dims.iter().map(u64::to_string).collect();
    let residues: Vec<String> = ints.iter().map(|i| i.raw.to_string()).collect();
    format!(
        "t{}:{bits}:{}:{}",
        semr_int_code(elem),
        dims.join(","),
        residues.join(",")
    )
}

/// One SemR verdict, as these runs read it.
#[derive(Debug, PartialEq, Eq)]
enum SemrVerdict {
    /// `{"ub": message}`.
    Ub(String),
    /// `{"ok": [{"tensor": {"elem", "dims", "elems"}}]}`: one returned tensor
    /// by its element type's code, extents and residues.
    Tensor {
        elem: u64,
        dims: Vec<u64>,
        residues: Vec<u128>,
    },
    /// Anything else, verbatim.
    Other(String),
}

/// The interpreter's returned tensor in [`SemrVerdict::Tensor`]'s spelling.
fn semr_spelling(v: &InterpretValue) -> SemrVerdict {
    let (elem, dims, ints) = tensor_parts(v);
    SemrVerdict::Tensor {
        elem: u64::from(semr_int_code(elem)),
        dims: dims.to_vec(),
        residues: ints.iter().map(|i| i.raw).collect(),
    }
}

fn semr_verdict(line: &str) -> SemrVerdict {
    use serde_json::Value;
    let other = || SemrVerdict::Other(line.to_string());
    let Ok(j) = serde_json::from_str::<Value>(line) else {
        return other();
    };
    if let Some(message) = j.get("ub").and_then(Value::as_str) {
        return SemrVerdict::Ub(message.to_string());
    }
    let Some([returned]) = j.get("ok").and_then(Value::as_array).map(Vec::as_slice) else {
        return other();
    };
    let Some(t) = returned.get("tensor") else {
        return other();
    };
    let dims = t["dims"]
        .as_array()
        .and_then(|ds| ds.iter().map(Value::as_u64).collect::<Option<Vec<u64>>>());
    let residues = t["elems"].as_array().and_then(|xs| {
        xs.iter()
            .map(|x| x.as_str().and_then(|s| s.parse::<u128>().ok()))
            .collect::<Option<Vec<u128>>>()
    });
    match (t["elem"].as_u64(), dims, residues) {
        (Some(elem), Some(dims), Some(residues)) => SemrVerdict::Tensor {
            elem,
            dims,
            residues,
        },
        _ => other(),
    }
}

/// SemR's verdict on each run of `module`, sent to `semr_eval` as the
/// module's binary image plus one line per run (`<fuel> <depth> <function>
/// <args..>`).
fn run_semr(exe: &Path, module: &Module, runs: &[(FuncId, &[InterpretValue])]) -> Vec<SemrVerdict> {
    let blob = trust_ir::binary::serialize_module(module).expect("the module has a wire image");
    let scratch = Scratch::new();
    let blob_path = scratch.path("module.tmbc");
    let runs_path = scratch.path("runs.txt");
    std::fs::write(&blob_path, &blob).expect("write the SemR blob");
    let mut lines = String::new();
    for (func, args) in runs {
        lines.push_str(&format!("{SEMR_FUEL} {SEMR_CALL_DEPTH} {}", func.index()));
        for arg in *args {
            lines.push(' ');
            lines.push_str(&semr_arg(arg));
        }
        lines.push('\n');
    }
    std::fs::write(&runs_path, lines.as_bytes()).expect("write the SemR runs");
    let out = Command::new(exe)
        .arg(&blob_path)
        .arg(&runs_path)
        .output()
        .unwrap_or_else(|e| panic!("cannot run {}: {e}", exe.display()));
    drop(scratch);
    assert!(
        out.status.success(),
        "semr_eval exited with {}:\n{}",
        out.status,
        String::from_utf8_lossy(&out.stderr)
    );
    let text = String::from_utf8_lossy(&out.stdout);
    let verdicts: Vec<SemrVerdict> = text.lines().map(semr_verdict).collect();
    assert_eq!(
        verdicts.len(),
        runs.len(),
        "one SemR verdict per run:\n{text}"
    );
    verdicts
}

// ───────────────────────────── obligations ─────────────────────────────

/// `fn gather(data: tensor<i32, 1>, at: tensor<usize, 1>) -> tensor<i32, 1>`
/// and `fn scatter(init: tensor<i32, 1>, src: tensor<i32, 1>, at:
/// tensor<usize, 1>) -> tensor<i32, 1>`, each body its instruction (node 0)
/// then the return (node 1). Row `i` of `rows` is a `Pending` obligation of
/// its kind sited on node `.2` of function `.1`; `claim` stamps `InBounds`
/// backed by a `ProofRef` to row 0 on that function's instruction.
fn sited_module(rows: &[(ObligationKind, usize, u32)], claim: Option<usize>) -> Module {
    let row = tensor(Ty::I32, 1);
    let at = tensor(Ty::Usize, 1);
    let mut mb = ModuleBuilder::new("tensor_gather_scatter_sites");
    let ids: Vec<_> = rows
        .iter()
        .map(|(kind, _, _)| {
            mb.add_proof_obligation(|id| {
                ProofObligation::new(
                    id,
                    kind.clone(),
                    ProofStatus::Pending,
                    "every coordinate is inside its axis",
                )
            })
            .expect("a fresh obligation id")
        })
        .collect();
    let mut funcs = Vec::new();
    for (index, params) in [
        vec![row.clone(), at.clone()],
        vec![row.clone(), row.clone(), at.clone()],
    ]
    .into_iter()
    .enumerate()
    {
        let ft = mb.add_func_type(params.clone(), vec![row.clone()]);
        let mut fb = mb.function(if index == 0 { "gather" } else { "scatter" }, ft);
        let entry = fb.create_block();
        let p: Vec<ValueId> = params
            .iter()
            .map(|ty| fb.add_block_param(entry, ty.clone()))
            .collect();
        fb.switch_to_block(entry);
        let out = if index == 0 {
            fb.tensor_gather(row.clone(), p[0], vec![p[1]])
        } else {
            fb.tensor_scatter(row.clone(), p[0], p[1], vec![p[2]])
        };
        if claim == Some(index) {
            fb.annotate_last(ProofAnnotation::InBounds)
                .expect("the instruction was just emitted");
            fb.annotate_last(ProofAnnotation::ProofRef(ids[0]))
                .expect("the instruction was just emitted");
        }
        fb.ret(vec![out]);
        fb.set_body_gate(gate());
        funcs.push(fb.build());
    }
    for (id, (_, function, inst_index)) in ids.iter().zip(rows) {
        assert!(mb.set_obligation_site(
            *id,
            ObligationSite::new(funcs[*function], BlockId::new(0), *inst_index)
        ));
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn a_bounds_check_obligation_is_sited_on_either_instruction() {
    use ObligationKind as K;
    // An `InBounds` claim is a claim of the `BoundsCheck` obligation.
    assert_eq!(
        ProofAnnotation::InBounds.obligation_kind(),
        Some(K::BoundsCheck)
    );
    let m = sited_module(&[], None);
    assert_eq!(validate_module(&m), [], "the unannotated baseline");
    for (function, op) in [(0usize, "tensor_gather"), (1, "tensor_scatter")] {
        let inst = &m.functions[function].blocks[0].body[0].inst;
        // The table itself: the bounds row and the unconstrained kinds only.
        assert!(obligation_kind_admits_site_instruction(
            &K::BoundsCheck,
            inst
        ));
        assert!(obligation_kind_admits_site_instruction(
            &K::Postcondition,
            inst
        ));
        for kind in [K::ArithmeticSafety, K::MemorySafety, K::PanicFreedom] {
            assert!(
                !obligation_kind_admits_site_instruction(&kind, inst),
                "{kind:?} at a {op}"
            );
        }
        // A `BoundsCheck` row sited on the instruction validates.
        assert_eq!(
            validate_module(&sited_module(&[(K::BoundsCheck, function, 0)], None)),
            [],
            "a bounds_check row at the {op}"
        );
        // Every other constrained kind is refused there by name.
        for (kind, name) in [
            (K::ArithmeticSafety, "arithmetic_safety"),
            (K::MemorySafety, "memory_safety"),
            (K::PanicFreedom, "panic_freedom"),
        ] {
            assert_eq!(
                validate_module(&sited_module(&[(kind, function, 0)], None)),
                vec![ValidationError::ObligationSiteKindMismatch {
                    obligation: 0,
                    kind: name,
                    op,
                }],
                "a {name} row at the {op}"
            );
        }
        // An `InBounds` claim on the instruction, backed by a `ProofRef` to
        // the kind-matched row sited on it, binds: kind, scope and site all
        // hold, so the only finding left is the missing kernel authority
        // (the row is `Pending`, no certificate is replayed), exactly as for
        // every other `ProofRef`.
        let errors = validate_module(&sited_module(
            &[(K::BoundsCheck, function, 0)],
            Some(function),
        ));
        assert!(
            !errors.is_empty()
                && errors.iter().all(|e| matches!(
                    e,
                    ValidationError::ProofRefUnresolved { missing: false, .. }
                )),
            "the InBounds claim on the {op} binds to its bounds row: {errors:#?}"
        );
        // The controls: the row sited on the other function's instruction is
        // `ProofRefSiteMismatch`; a `MemorySafety` row sited on it is
        // refused by the site table.
        let errors = validate_module(&sited_module(
            &[(K::BoundsCheck, 1 - function, 0)],
            Some(function),
        ));
        assert!(
            errors
                .iter()
                .any(|e| matches!(e, ValidationError::ProofRefSiteMismatch { .. })),
            "a bounds row at another instruction backs nothing at the {op}: {errors:#?}"
        );
        let errors = validate_module(&sited_module(
            &[(K::MemorySafety, function, 0)],
            Some(function),
        ));
        assert!(
            errors.contains(&ValidationError::ObligationSiteKindMismatch {
                obligation: 0,
                kind: "memory_safety",
                op,
            }),
            "a memory_safety row cannot be sited on the {op}: {errors:#?}"
        );
    }
}

// ───────────────────────────── codegen ─────────────────────────────

#[test]
fn the_codegen_gate_refuses_each_instruction_by_name() {
    let m = accepted();
    assert_eq!(validate_module(&m), [], "well-formed TrustIr");
    let refused = validate_module_for_codegen(&m);
    for func in &m.functions {
        let (inst, what) = if func.name.starts_with("gather_") {
            ("TensorGather", "a tensor gather")
        } else {
            ("TensorScatter", "a tensor scatter")
        };
        let detail = format!(
            "{what} has no machine lowering yet (PKG-U13: outside the lowering-target subset)"
        );
        let named = refused
            .iter()
            .filter(|e| {
                matches!(
                    e,
                    ValidationError::UnlowerableForCodegen { name, inst: i, detail: d, .. }
                    if *name == func.name && *i == inst && *d == detail
                )
            })
            .count();
        assert_eq!(named, 1, "{}: refused exactly once: {refused:?}", func.name);
    }
    assert!(
        refused.iter().all(|e| matches!(
            e,
            ValidationError::UnlowerableForCodegen {
                inst: "TensorGather" | "TensorScatter",
                ..
            }
        )),
        "the module is licensed and otherwise lowerable: {refused:?}"
    );
}
