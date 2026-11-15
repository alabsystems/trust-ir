// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// ══════════════════════════════════════════════════════════════════════════
// The tensor region (PKG-U13c): `Inst::TensorMap`, `Inst::TensorReduce` and
// `Inst::TensorView` in the validator, the reference interpreter and the
// codegen gate.
// ══════════════════════════════════════════════════════════════════════════
//
// What this battery pins:
//
//   * an element-wise map (with a scalar operand, a compare and a select, and
//     a widening cast), reductions by every operator over one axis, several
//     axes and an empty extent, and views that transpose, slice, pad,
//     broadcast and reshape are accepted, on the module and the standalone
//     path;
//   * every static rule of the three instructions is refused by its own
//     variant (`InvalidTensorMap` M1..M5, `InvalidTensorReduce` R1..R3,
//     `InvalidTensorView` V1..V6) with a reason that names the rule;
//   * the interpreter computes what a hand-written loop nest computes, in one
//     fuel unit per instruction;
//   * every run-time precondition is undefined behaviour by its normative
//     message (the texts SemR spells byte for byte), never a validator
//     refusal: operand extents that differ, a node's own scalar verdict, a
//     reduction result past `usize`, and each of the view's five;
//   * the default codegen gate refuses each instruction by name
//     (`UnlowerableForCodegen`): a tensor has no machine layout.

use trust_ir::{
    ArrayValue, BinOp, CastOp, ICmpOp, InterpretErrorCode, InterpretOutcome, InterpretResult,
    InterpretValue, InterpretValueKind, Interpreter, Module, TensorIndexExpr, TensorMapNode,
    TensorReduceOp, Ty, UnOp, ValueId,
};
use trust_ir_build::{
    FunctionBuilder, ModuleBuilder, ValidationError, validate_function, validate_module,
    validate_module_for_codegen,
};

type Node = TensorMapNode<trust_ir::NoExt>;
use TensorIndexExpr as E;

fn tensor(elem: Ty, rank: u32) -> Ty {
    Ty::Tensor(Box::new(elem), rank)
}

fn gate() -> trust_ir::BodyGate {
    trust_ir::BodyGate::Gated {
        authority: "tensor-map-reduce-view".into(),
        evidence: None,
    }
}

/// One function `fn {name}(params..) -> result`, its body one instruction
/// `body` emits from the parameters (and any constants it makes).
struct Case {
    name: &'static str,
    params: Vec<Ty>,
    result: Ty,
    body: Box<dyn Fn(&mut FunctionBuilder<'_>, &[ValueId]) -> ValueId>,
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

// ───────────────────────────── the cases ─────────────────────────────

/// `a + b`, element-wise, at `tensor<i32, 2>`.
fn add_case() -> Case {
    case(
        "add",
        vec![tensor(Ty::I32, 2), tensor(Ty::I32, 2)],
        tensor(Ty::I32, 2),
        |fb, p| {
            fb.tensor_map(
                tensor(Ty::I32, 2),
                vec![p[0], p[1]],
                vec![Node::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I32,
                    lhs: 0,
                    rhs: 1,
                }],
            )
        },
    )
}

/// `relu(x) = if x > 0 { x } else { 0 }`: a scalar operand, a compare and a
/// select. Lanes: 0 = `x[i]`, 1 = the scalar 0, 2 = the compare, 3 = the
/// select.
fn relu_case() -> Case {
    case(
        "relu",
        vec![tensor(Ty::I32, 2)],
        tensor(Ty::I32, 2),
        |fb, p| {
            let zero = fb.iconst(Ty::I32, 0);
            fb.tensor_map(
                tensor(Ty::I32, 2),
                vec![p[0], zero],
                vec![
                    Node::ICmp {
                        op: ICmpOp::Sgt,
                        ty: Ty::I32,
                        lhs: 0,
                        rhs: 1,
                    },
                    Node::Select {
                        ty: Ty::I32,
                        cond: 2,
                        then_lane: 0,
                        else_lane: 1,
                    },
                ],
            )
        },
    )
}

/// `(i32) x * 1000 - y`, element-wise from `tensor<i8, 1>` and `tensor<i32,
/// 1>`: a widening cast, then wrapping arithmetic.
fn widen_case() -> Case {
    case(
        "widen",
        vec![tensor(Ty::I8, 1), tensor(Ty::I32, 1)],
        tensor(Ty::I32, 1),
        |fb, p| {
            let k = fb.iconst(Ty::I32, 1000);
            fb.tensor_map(
                tensor(Ty::I32, 1),
                vec![p[0], p[1], k],
                vec![
                    Node::Cast {
                        op: CastOp::SExt,
                        src_ty: Ty::I8,
                        dst_ty: Ty::I32,
                        operand: 0,
                    },
                    Node::BinOp {
                        op: BinOp::Mul,
                        ty: Ty::I32,
                        lhs: 3,
                        rhs: 2,
                    },
                    Node::BinOp {
                        op: BinOp::Sub,
                        ty: Ty::I32,
                        lhs: 4,
                        rhs: 1,
                    },
                ],
            )
        },
    )
}

/// `x / y` (unsigned), element-wise at `tensor<u32, 1>`: a node whose own
/// scalar verdict (division by zero) is the map's.
fn udiv_case() -> Case {
    case(
        "udiv",
        vec![tensor(Ty::U32, 1), tensor(Ty::U32, 1)],
        tensor(Ty::U32, 1),
        |fb, p| {
            fb.tensor_map(
                tensor(Ty::U32, 1),
                vec![p[0], p[1]],
                vec![Node::BinOp {
                    op: BinOp::UDiv,
                    ty: Ty::U32,
                    lhs: 0,
                    rhs: 1,
                }],
            )
        },
    )
}

/// `reduce op` of a `tensor<elem, rank>` over `axes`.
fn reduce_case(
    name: &'static str,
    elem: Ty,
    rank: u32,
    op: TensorReduceOp,
    axes: &'static [u32],
) -> Case {
    let result = tensor(elem.clone(), rank - axes.len() as u32);
    case(
        name,
        vec![tensor(elem, rank)],
        result.clone(),
        move |fb, p| fb.tensor_reduce(result.clone(), p[0], op, axes.to_vec()),
    )
}

/// A view of a `tensor<i32, s>` into `tensor<i32, r>`, with `usize`
/// parameters and an optional `i32` fill (the last parameter).
fn view_case(
    name: &'static str,
    s: u32,
    r: u32,
    params: usize,
    fill: bool,
    exprs: Vec<TensorIndexExpr>,
    shape: Vec<u32>,
    index: Vec<u32>,
) -> Case {
    let mut tys = vec![tensor(Ty::I32, s)];
    tys.extend(std::iter::repeat_n(Ty::Usize, params));
    if fill {
        tys.push(Ty::I32);
    }
    case(name, tys, tensor(Ty::I32, r), move |fb, p| {
        let fill_value = fill.then(|| p[p.len() - 1]);
        fb.tensor_view(
            tensor(Ty::I32, r),
            p[0],
            p[1..=params].to_vec(),
            exprs.clone(),
            shape.clone(),
            index.clone(),
            fill_value,
        )
    })
}

/// `x^T` of an `[m, n]` tensor: shape `[n, m]`, source `[c1, c0]`.
fn transpose_case() -> Case {
    view_case(
        "transpose",
        2,
        2,
        0,
        false,
        vec![E::SrcExtent(1), E::SrcExtent(0), E::Coord(1), E::Coord(0)],
        vec![0, 1],
        vec![2, 3],
    )
}

/// Rows `p .. p + q` of an `[m, n]` tensor: shape `[q, n]`, source `[c0 +
/// p, c1]`.
fn slice_case() -> Case {
    view_case(
        "slice",
        2,
        2,
        2,
        false,
        vec![
            E::Param(1),
            E::SrcExtent(1),
            E::Coord(0),
            E::Param(0),
            E::Add(2, 3),
            E::Coord(1),
        ],
        vec![0, 1],
        vec![4, 5],
    )
}

/// One element of padding on each side of a `[n]` tensor, filled with `f`:
/// shape `[n + 2]`, source `[c0 - 1]`.
fn pad_case() -> Case {
    view_case(
        "pad",
        1,
        1,
        0,
        true,
        vec![
            E::SrcExtent(0),
            E::Lit(2),
            E::Add(0, 1),
            E::Coord(0),
            E::Lit(1),
            E::Sub(3, 4),
        ],
        vec![2],
        vec![5],
    )
}

/// A `[n]` tensor broadcast along a new leading axis of extent `p`: shape
/// `[p, n]`, source `[c1]`.
fn broadcast_case() -> Case {
    view_case(
        "broadcast",
        1,
        2,
        1,
        false,
        vec![E::Param(0), E::SrcExtent(0), E::Coord(1)],
        vec![0, 1],
        vec![2],
    )
}

/// A `[6]` tensor reshaped to `[2, 3]`: source `[c0 * 3 + c1]`; and back,
/// `[2, 3]` to `[6]`: source `[c0 / 3, c0 % 3]` (Euclidean).
fn reshape_cases() -> [Case; 2] {
    [
        view_case(
            "reshape_up",
            1,
            2,
            0,
            false,
            vec![
                E::Lit(2),
                E::Lit(3),
                E::Coord(0),
                E::Mul(2, 1),
                E::Coord(1),
                E::Add(3, 4),
            ],
            vec![0, 1],
            vec![5],
        ),
        view_case(
            "reshape_down",
            2,
            1,
            0,
            false,
            vec![
                E::Lit(6),
                E::Lit(3),
                E::Coord(0),
                E::Div(2, 1),
                E::Rem(2, 1),
            ],
            vec![0],
            vec![3, 4],
        ),
    ]
}

fn accepted_cases() -> Vec<Case> {
    let mut cases = vec![
        add_case(),
        relu_case(),
        widen_case(),
        udiv_case(),
        reduce_case("sum_rows", Ty::I32, 2, TensorReduceOp::Add, &[1]),
        reduce_case("sum_all", Ty::I32, 2, TensorReduceOp::Add, &[0, 1]),
        reduce_case("max_cols", Ty::I64, 3, TensorReduceOp::SMax, &[0, 2]),
        reduce_case("keep_all", Ty::U8, 1, TensorReduceOp::UMin, &[]),
        transpose_case(),
        slice_case(),
        pad_case(),
        broadcast_case(),
    ];
    cases.extend(reshape_cases());
    cases
}

fn accepted() -> Module {
    module_of("tensor_map_reduce_view_accepted", &accepted_cases())
}

// ───────────────────────────── accepted ─────────────────────────────

#[test]
fn maps_reductions_and_views_validate_on_both_paths() {
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

/// The refusals of a one-case module: every error is `variant`'s, and one
/// names `rule`.
fn assert_rule(c: Case, is_variant: fn(&ValidationError) -> Option<&str>, rule: &str) {
    let name = c.name;
    let m = module_of("tensor_map_reduce_view_refused", &[c]);
    for errors in [validate_module(&m), validate_function(&m.functions[0])] {
        assert!(!errors.is_empty(), "{name}: accepted");
        let reasons: Vec<&str> = errors.iter().filter_map(is_variant).collect();
        assert_eq!(
            reasons.len(),
            errors.len(),
            "{name}: only the instruction's own variant expected, got {errors:?}"
        );
        assert!(
            reasons.iter().any(|reason| reason.starts_with(rule)),
            "{name}: no refusal names {rule:?}: {errors:?}"
        );
    }
}

fn map_reason(e: &ValidationError) -> Option<&str> {
    match e {
        ValidationError::InvalidTensorMap { reason, .. } => Some(reason),
        _ => None,
    }
}

fn reduce_reason(e: &ValidationError) -> Option<&str> {
    match e {
        ValidationError::InvalidTensorReduce { reason, .. } => Some(reason),
        _ => None,
    }
}

fn view_reason(e: &ValidationError) -> Option<&str> {
    match e {
        ValidationError::InvalidTensorView { reason, .. } => Some(reason),
        _ => None,
    }
}

/// A map of `params` into `result` with `body`.
fn map_with(name: &'static str, params: Vec<Ty>, result: Ty, body: Vec<Node>) -> Case {
    let ty = result.clone();
    case(name, params, result, move |fb, p| {
        fb.tensor_map(ty.clone(), p.to_vec(), body.clone())
    })
}

fn neg(lane: u32) -> Node {
    Node::UnOp {
        op: UnOp::Neg,
        ty: Ty::I32,
        operand: lane,
    }
}

#[test]
fn the_map_rules_are_each_refused_by_name() {
    let t = || tensor(Ty::I32, 1);
    // M1: the result is not a tensor.
    assert_rule(
        map_with("m1", vec![t()], Ty::I32, vec![neg(0)]),
        map_reason,
        "rule M1",
    );
    // M2: an operand of another rank; no tensor operand at all.
    assert_rule(
        map_with("m2_rank", vec![tensor(Ty::I32, 2)], t(), vec![neg(0)]),
        map_reason,
        "rule M2",
    );
    assert_rule(
        map_with("m2_none", vec![Ty::I32], t(), vec![neg(0)]),
        map_reason,
        "rule M2",
    );
    // M3: an empty body; a node reading itself.
    assert_rule(
        map_with("m3_empty", vec![t()], t(), vec![]),
        map_reason,
        "rule M3",
    );
    assert_rule(
        map_with("m3_self", vec![t()], t(), vec![neg(1)]),
        map_reason,
        "rule M3",
    );
    // M4: a lane of the wrong type; a float operation; a Bool-only
    // connective at an integer; a narrowing `sext`.
    assert_rule(
        map_with("m4_lane", vec![tensor(Ty::I64, 1)], t(), vec![neg(0)]),
        map_reason,
        "rule M4",
    );
    assert_rule(
        map_with(
            "m4_float",
            vec![t()],
            t(),
            vec![Node::BinOp {
                op: BinOp::FAdd,
                ty: Ty::I32,
                lhs: 0,
                rhs: 0,
            }],
        ),
        map_reason,
        "rule M4",
    );
    assert_rule(
        map_with(
            "m4_band",
            vec![t()],
            t(),
            vec![Node::BinOp {
                op: BinOp::BAnd,
                ty: Ty::I32,
                lhs: 0,
                rhs: 0,
            }],
        ),
        map_reason,
        "rule M4",
    );
    assert_rule(
        map_with(
            "m4_sext",
            vec![t()],
            tensor(Ty::I8, 1),
            vec![Node::Cast {
                op: CastOp::SExt,
                src_ty: Ty::I32,
                dst_ty: Ty::I8,
                operand: 0,
            }],
        ),
        map_reason,
        "rule M4",
    );
    // M5: the last node is a Bool, not the element.
    assert_rule(
        map_with(
            "m5",
            vec![t()],
            t(),
            vec![Node::ICmp {
                op: ICmpOp::Eq,
                ty: Ty::I32,
                lhs: 0,
                rhs: 0,
            }],
        ),
        map_reason,
        "rule M5",
    );
}

#[test]
fn the_reduction_rules_are_each_refused_by_name() {
    let with = |name, src: Ty, result: Ty, axes: &'static [u32]| {
        case(name, vec![src], result.clone(), move |fb, p| {
            fb.tensor_reduce(result.clone(), p[0], TensorReduceOp::Add, axes.to_vec())
        })
    };
    assert_rule(
        with("r1_elem", tensor(Ty::I32, 2), tensor(Ty::I64, 1), &[1]),
        reduce_reason,
        "rule R1",
    );
    assert_rule(
        with("r1_scalar", Ty::I32, tensor(Ty::I32, 0), &[]),
        reduce_reason,
        "rule R1",
    );
    assert_rule(
        with("r2_order", tensor(Ty::I32, 3), tensor(Ty::I32, 1), &[2, 0]),
        reduce_reason,
        "rule R2",
    );
    assert_rule(
        with("r2_twice", tensor(Ty::I32, 3), tensor(Ty::I32, 1), &[1, 1]),
        reduce_reason,
        "rule R2",
    );
    assert_rule(
        with("r2_range", tensor(Ty::I32, 2), tensor(Ty::I32, 1), &[2]),
        reduce_reason,
        "rule R2",
    );
    assert_rule(
        with("r3", tensor(Ty::I32, 2), tensor(Ty::I32, 2), &[1]),
        reduce_reason,
        "rule R3",
    );
}

#[test]
fn the_view_rules_are_each_refused_by_name() {
    // V1: element types differ.
    let elem = case(
        "v1",
        vec![tensor(Ty::I64, 1)],
        tensor(Ty::I32, 1),
        |fb, p| {
            fb.tensor_view(
                tensor(Ty::I32, 1),
                p[0],
                vec![],
                vec![E::SrcExtent(0), E::Coord(0)],
                vec![0],
                vec![1],
                None,
            )
        },
    );
    assert_rule(elem, view_reason, "rule V1");
    // V2: a parameter that is not a `usize`.
    let param = case(
        "v2",
        vec![tensor(Ty::I32, 1), Ty::U64],
        tensor(Ty::I32, 1),
        |fb, p| {
            fb.tensor_view(
                tensor(Ty::I32, 1),
                p[0],
                vec![p[1]],
                vec![E::Param(0), E::Coord(0)],
                vec![0],
                vec![1],
                None,
            )
        },
    );
    assert_rule(param, view_reason, "rule V2");
    // V3: a fill of another type.
    let fill = case(
        "v3",
        vec![tensor(Ty::I32, 1), Ty::I64],
        tensor(Ty::I32, 1),
        |fb, p| {
            fb.tensor_view(
                tensor(Ty::I32, 1),
                p[0],
                vec![],
                vec![E::SrcExtent(0), E::Coord(0)],
                vec![0],
                vec![1],
                Some(p[1]),
            )
        },
    );
    assert_rule(fill, view_reason, "rule V3");
    // V4: one index node for a rank-2 source; a reference past the nodes.
    assert_rule(
        view_case(
            "v4_count",
            2,
            1,
            0,
            false,
            vec![E::Lit(1), E::Coord(0)],
            vec![0],
            vec![1],
        ),
        view_reason,
        "rule V4",
    );
    assert_rule(
        view_case(
            "v4_dangling",
            1,
            1,
            0,
            false,
            vec![E::Lit(1), E::Coord(0)],
            vec![0],
            vec![2],
        ),
        view_reason,
        "rule V4",
    );
    // V5: a forward read; a parameter, a source axis and a coordinate out of
    // range.
    for (name, expr) in [
        ("v5_forward", E::Add(1, 1)),
        ("v5_param", E::Param(0)),
        ("v5_src", E::SrcExtent(1)),
        ("v5_coord", E::Coord(1)),
    ] {
        assert_rule(
            view_case(
                name,
                1,
                1,
                0,
                false,
                vec![E::Lit(1), expr, E::Coord(0)],
                vec![0],
                vec![2],
            ),
            view_reason,
            "rule V5",
        );
    }
    // V6: an extent that reads a coordinate.
    assert_rule(
        view_case(
            "v6",
            1,
            1,
            0,
            false,
            vec![E::Coord(0), E::Lit(1), E::Add(0, 1)],
            vec![2],
            vec![0],
        ),
        view_reason,
        "rule V6",
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

fn run(m: &Module, name: &str, args: Vec<InterpretValue>) -> InterpretResult<InterpretOutcome> {
    let func = m
        .functions
        .iter()
        .find(|f| f.name == name)
        .unwrap_or_else(|| panic!("no function {name}"));
    Interpreter::with_module(m).execute_func(func.id, args)
}

/// The returned tensor's extents and elements, and the steps the run took.
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

/// Run `name` and return its result, holding the fuel to one unit per
/// instruction (`instructions`, the return included).
fn computes(
    m: &Module,
    name: &str,
    args: Vec<InterpretValue>,
    instructions: u64,
) -> (Vec<u64>, Vec<i128>) {
    let outcome = run(m, name, args).unwrap_or_else(|e| panic!("{name}: {e:?}"));
    assert_eq!(
        outcome.steps, instructions,
        "{name}: one fuel unit per instruction"
    );
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

/// Rule M4's operation half is one rule, `TensorMapNode::op_refusal`: the
/// validator refuses each body below as rule M4, and the interpreter refuses
/// it as a type error naming the node, before any element is read (over an
/// empty tensor too, and ahead of a division by zero at the first
/// coordinate). Its positive twin, a narrowing `trunc` then a widening
/// `zext`, is admitted by both.
#[test]
fn the_operation_rule_is_one_rule_for_the_validator_and_the_interpreter() {
    let row = |elem: Ty| tensor(elem, 1);
    let band = map_with(
        "band_at_i32",
        vec![row(Ty::I32)],
        row(Ty::I32),
        vec![Node::BinOp {
            op: BinOp::BAnd,
            ty: Ty::I32,
            lhs: 0,
            rhs: 0,
        }],
    );
    let widening_trunc = map_with(
        "widening_trunc",
        vec![row(Ty::I8)],
        row(Ty::I32),
        vec![Node::Cast {
            op: CastOp::Trunc,
            src_ty: Ty::I8,
            dst_ty: Ty::I32,
            operand: 0,
        }],
    );
    let bool_add_before_udiv = map_with(
        "bool_add_before_udiv",
        vec![row(Ty::U32), Ty::U32],
        row(Ty::U32),
        vec![
            Node::BinOp {
                op: BinOp::UDiv,
                ty: Ty::U32,
                lhs: 0,
                rhs: 1,
            },
            Node::ICmp {
                op: ICmpOp::Eq,
                ty: Ty::U32,
                lhs: 0,
                rhs: 0,
            },
            Node::BinOp {
                op: BinOp::Add,
                ty: Ty::Bool,
                lhs: 3,
                rhs: 3,
            },
            Node::Select {
                ty: Ty::U32,
                cond: 4,
                then_lane: 2,
                else_lane: 0,
            },
        ],
    );
    let narrow_then_widen = map_with(
        "narrow_then_widen",
        vec![row(Ty::U16)],
        row(Ty::U16),
        vec![
            Node::Cast {
                op: CastOp::Trunc,
                src_ty: Ty::U16,
                dst_ty: Ty::U8,
                operand: 0,
            },
            Node::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::U8,
                dst_ty: Ty::U16,
                operand: 1,
            },
        ],
    );
    let m = module_of(
        "tensor_map_operation_rule",
        &[
            band,
            widening_trunc,
            bool_add_before_udiv,
            narrow_then_widen,
        ],
    );
    let errors = validate_module(&m);
    for name in ["band_at_i32", "widening_trunc", "bool_add_before_udiv"] {
        let function = m.functions.iter().find(|f| f.name == name).expect(name);
        let refused = validate_function(function);
        assert!(
            refused
                .iter()
                .any(|e| map_reason(e).is_some_and(|r| r.contains("rule M4"))),
            "{name}: {refused:?}"
        );
    }
    let positive = m
        .functions
        .iter()
        .find(|f| f.name == "narrow_then_widen")
        .expect("narrow_then_widen");
    assert!(
        validate_function(positive).is_empty(),
        "narrow_then_widen: {errors:?}"
    );
    for (name, args) in [
        ("band_at_i32", vec![value(&Ty::I32, &[2], &[3, 0])]),
        ("band_at_i32", vec![value(&Ty::I32, &[0], &[])]),
        ("widening_trunc", vec![value(&Ty::I8, &[1], &[-1])]),
        (
            "bool_add_before_udiv",
            vec![value(&Ty::U32, &[1], &[6]), int(&Ty::U32, 0)],
        ),
    ] {
        let error = run(&m, name, args).expect_err(name);
        assert_eq!(
            error.code,
            InterpretErrorCode::TypeError,
            "{name}: {error:?}"
        );
        assert!(
            error.message.contains("tensor map: node "),
            "{name}: {error:?}"
        );
    }
    assert_eq!(
        computes(
            &m,
            "narrow_then_widen",
            vec![value(&Ty::U16, &[2], &[0x1234, 0x00FF])],
            2
        ),
        (vec![2], vec![0x34, 0xFF])
    );
}

const A: [i128; 6] = [5, -7, 0, 12, -1, 3];
const B: [i128; 6] = [-2, 9, 4, i32::MAX as i128, 8, -3];

#[test]
fn maps_match_a_hand_loop() {
    let m = accepted();
    let wrap = |x: i128| i128::from(x as i32);
    let expected: Vec<i128> = A.iter().zip(B).map(|(a, b)| wrap(a + b)).collect();
    assert_eq!(
        computes(
            &m,
            "add",
            vec![value(&Ty::I32, &[2, 3], &A), value(&Ty::I32, &[2, 3], &B)],
            2
        ),
        (vec![2, 3], expected)
    );
    let expected: Vec<i128> = A.iter().map(|&a| a.max(0)).collect();
    // The constant, the map and the return.
    assert_eq!(
        computes(&m, "relu", vec![value(&Ty::I32, &[3, 2], &A)], 3),
        (vec![3, 2], expected)
    );
    let x = [-128i128, -1, 0, 1, 127];
    let y = [7i128, -7, 0, i32::MIN as i128, 3];
    let expected: Vec<i128> = x.iter().zip(y).map(|(x, y)| wrap(x * 1000 - y)).collect();
    assert_eq!(
        computes(
            &m,
            "widen",
            vec![value(&Ty::I8, &[5], &x), value(&Ty::I32, &[5], &y)],
            3
        ),
        (vec![5], expected)
    );
    // An empty map evaluates no node: even a division by zero is not
    // reached.
    assert_eq!(
        computes(
            &m,
            "udiv",
            vec![value(&Ty::U32, &[0], &[]), value(&Ty::U32, &[0], &[])],
            2
        ),
        (vec![0], vec![])
    );
}

/// The row-major reduction of `values` (extents `dims`) over `axes` by `op`
/// at `bits` bits (`signed` for the element's carrier), by a hand loop.
fn hand_reduce(
    dims: &[usize],
    values: &[i128],
    axes: &[usize],
    op: TensorReduceOp,
    bits: u32,
    signed: bool,
) -> (Vec<u64>, Vec<i128>) {
    let modulus = 1i128 << bits;
    let residue = |x: i128| x.rem_euclid(modulus);
    let signed_of = |r: i128| if r >= modulus / 2 { r - modulus } else { r };
    let identity = match op {
        TensorReduceOp::Add | TensorReduceOp::Or | TensorReduceOp::Xor | TensorReduceOp::UMax => 0,
        TensorReduceOp::Mul => 1,
        TensorReduceOp::And | TensorReduceOp::UMin => modulus - 1,
        TensorReduceOp::SMin => modulus / 2 - 1,
        TensorReduceOp::SMax => modulus / 2,
    };
    let kept: Vec<usize> = (0..dims.len()).filter(|a| !axes.contains(a)).collect();
    let out_dims: Vec<usize> = kept.iter().map(|&a| dims[a]).collect();
    let count: usize = out_dims.iter().product();
    let terms: usize = axes.iter().map(|&a| dims[a]).product();
    let decode = |mut flat: usize, ds: &[usize]| -> Vec<usize> {
        let mut idx = vec![0; ds.len()];
        for (slot, d) in idx.iter_mut().zip(ds).rev() {
            *slot = flat % d;
            flat /= d;
        }
        idx
    };
    let mut out = Vec::new();
    for flat in 0..count {
        let o = decode(flat, &out_dims);
        let mut acc = identity;
        for term in 0..terms {
            let t = decode(term, &axes.iter().map(|&a| dims[a]).collect::<Vec<_>>());
            let mut at = vec![0; dims.len()];
            for (k, &a) in kept.iter().enumerate() {
                at[a] = o[k];
            }
            for (k, &a) in axes.iter().enumerate() {
                at[a] = t[k];
            }
            let offset = at.iter().zip(dims).fold(0, |off, (i, d)| off * d + i);
            let x = residue(values[offset]);
            acc = match op {
                TensorReduceOp::Add => residue(acc + x),
                TensorReduceOp::Mul => residue(acc.wrapping_mul(x)),
                TensorReduceOp::And => acc & x,
                TensorReduceOp::Or => acc | x,
                TensorReduceOp::Xor => acc ^ x,
                TensorReduceOp::SMin => {
                    if signed_of(x) < signed_of(acc) {
                        x
                    } else {
                        acc
                    }
                }
                TensorReduceOp::SMax => {
                    if signed_of(x) > signed_of(acc) {
                        x
                    } else {
                        acc
                    }
                }
                TensorReduceOp::UMin => acc.min(x),
                TensorReduceOp::UMax => acc.max(x),
            };
        }
        out.push(if signed { signed_of(acc) } else { acc });
    }
    (out_dims.iter().map(|&d| d as u64).collect(), out)
}

#[test]
fn reductions_by_every_operator_match_a_hand_loop() {
    // A [3, 4] i16 tensor with negatives, and a [2, 3] u8 one.
    let x: Vec<i128> = (0..12).map(|k| (k * 37 % 23) - 11).collect();
    let u: Vec<i128> = vec![200, 3, 255, 0, 17, 128];
    let axes_list: [&'static [u32]; 4] = [&[1], &[0], &[0, 1], &[]];
    for op in TensorReduceOp::ALL {
        for axes in axes_list {
            for (elem, dims, values, bits, signed) in [
                (Ty::I16, [3usize, 4], &x, 16, true),
                (Ty::U8, [2, 3], &u, 8, false),
            ] {
                let m = module_of(
                    "tensor_reduce_hand_loop",
                    &[reduce_case("reduce", elem.clone(), 2, op, axes)],
                );
                assert_eq!(validate_module(&m), [], "{op:?} {axes:?}");
                let arg = value(&elem, &[dims[0] as u64, dims[1] as u64], values);
                let axes_usize: Vec<usize> = axes.iter().map(|&a| a as usize).collect();
                assert_eq!(
                    computes(&m, "reduce", vec![arg], 2),
                    hand_reduce(&dims, values, &axes_usize, op, bits, signed),
                    "{op:?} over {axes:?} at {elem}"
                );
            }
        }
    }
}

#[test]
fn an_empty_reduced_extent_gives_the_identity() {
    let m = accepted();
    // `sum_rows` of a [3, 0] tensor: three empty sums.
    assert_eq!(
        computes(&m, "sum_rows", vec![value(&Ty::I32, &[3, 0], &[])], 2),
        (vec![3], vec![0, 0, 0])
    );
    // `max_cols` (SMax over axes 0 and 2) of a [0, 2, 5] tensor: the signed
    // minimum.
    assert_eq!(
        computes(&m, "max_cols", vec![value(&Ty::I64, &[0, 2, 5], &[])], 2),
        (vec![2], vec![i128::from(i64::MIN); 2])
    );
}

fn usize_value(x: u64) -> InterpretValue {
    int(&Ty::Usize, i128::from(x))
}

#[test]
fn views_match_a_hand_loop() {
    let m = accepted();
    let x: Vec<i128> = (0..12).map(|k| k * 10 - 40).collect();
    // Transpose of [3, 4].
    let mut expected = Vec::new();
    for j in 0..4 {
        for i in 0..3 {
            expected.push(x[i * 4 + j]);
        }
    }
    assert_eq!(
        computes(&m, "transpose", vec![value(&Ty::I32, &[3, 4], &x)], 2),
        (vec![4, 3], expected)
    );
    // Rows 1..3 of [3, 4] (p = 1, q = 2).
    assert_eq!(
        computes(
            &m,
            "slice",
            vec![value(&Ty::I32, &[3, 4], &x), usize_value(1), usize_value(2)],
            2
        ),
        (vec![2, 4], x[4..12].to_vec())
    );
    // Pad [4] with -9 on each side.
    let mut expected = vec![-9];
    expected.extend_from_slice(&x[..4]);
    expected.push(-9);
    assert_eq!(
        computes(
            &m,
            "pad",
            vec![value(&Ty::I32, &[4], &x[..4]), int(&Ty::I32, -9)],
            2
        ),
        (vec![6], expected)
    );
    // Broadcast [3] to [2, 3].
    let mut expected = x[..3].to_vec();
    expected.extend_from_slice(&x[..3]);
    assert_eq!(
        computes(
            &m,
            "broadcast",
            vec![value(&Ty::I32, &[3], &x[..3]), usize_value(2)],
            2
        ),
        (vec![2, 3], expected)
    );
    // Reshape [6] to [2, 3] and [2, 3] to [6]: the same row-major elements.
    assert_eq!(
        computes(&m, "reshape_up", vec![value(&Ty::I32, &[6], &x[..6])], 2),
        (vec![2, 3], x[..6].to_vec())
    );
    assert_eq!(
        computes(
            &m,
            "reshape_down",
            vec![value(&Ty::I32, &[2, 3], &x[..6])],
            2
        ),
        (vec![6], x[..6].to_vec())
    );
    // A broadcast to zero rows reads no source element, even from an empty
    // source.
    assert_eq!(
        computes(
            &m,
            "broadcast",
            vec![value(&Ty::I32, &[0], &[]), usize_value(0)],
            2
        ),
        (vec![0, 0], vec![])
    );
}

// ───────────────────────────── preconditions ─────────────────────────────

#[test]
fn map_preconditions_are_undefined_behaviour_by_message() {
    let m = accepted();
    ub(
        &m,
        "add",
        vec![value(&Ty::I32, &[2, 3], &A), value(&Ty::I32, &[3, 2], &B)],
        "tensor map: operand extents differ",
    );
    // A node's verdict is its scalar instruction's.
    ub(
        &m,
        "udiv",
        vec![
            value(&Ty::U32, &[2], &[6, 7]),
            value(&Ty::U32, &[2], &[3, 0]),
        ],
        "unsigned division by zero",
    );
}

#[test]
fn a_reduction_past_usize_is_undefined_behaviour() {
    // A [2^40, 2^40, 0] source has no element, so it is well formed; its sum
    // over axis 2 would have 2^80 elements.
    let m = module_of(
        "tensor_reduce_too_large",
        &[reduce_case(
            "sum_last",
            Ty::I32,
            3,
            TensorReduceOp::Add,
            &[2],
        )],
    );
    ub(
        &m,
        "sum_last",
        vec![value(&Ty::I32, &[1 << 40, 1 << 40, 0], &[])],
        "tensor reduction: the result has more elements than usize holds",
    );
}

#[test]
fn view_preconditions_are_undefined_behaviour_by_message() {
    let one_node = |name, exprs: Vec<TensorIndexExpr>, shape_node: u32| {
        view_case(name, 1, 1, 0, false, exprs, vec![shape_node], vec![0])
    };
    let big = u64::MAX;
    let m = module_of(
        "tensor_view_preconditions",
        &[
            // Out of range with no fill: [n + 1] from [n].
            view_case(
                "overrun",
                1,
                1,
                0,
                false,
                vec![E::SrcExtent(0), E::Lit(1), E::Add(0, 1), E::Coord(0)],
                vec![2],
                vec![3],
            ),
            // (2^64 - 1)^2 is past 2^127.
            one_node(
                "overflow",
                vec![E::Coord(0), E::Lit(big), E::Mul(1, 1), E::Lit(1)],
                3,
            ),
            // A division by a zero literal.
            one_node(
                "div_zero",
                vec![E::Coord(0), E::Lit(1), E::Lit(0), E::Rem(1, 2)],
                3,
            ),
            // An extent of -1.
            one_node(
                "negative",
                vec![E::Coord(0), E::Lit(0), E::Lit(1), E::Sub(1, 2)],
                3,
            ),
            // An extent of 2^64.
            one_node(
                "wide",
                vec![E::Coord(0), E::Lit(big), E::Lit(1), E::Add(1, 2)],
                3,
            ),
            // [2^32, 2^32]: each extent fits, the count (2^64) does not.
            view_case(
                "count",
                1,
                2,
                0,
                false,
                vec![E::Lit(1 << 32), E::Coord(1)],
                vec![0, 0],
                vec![1],
            ),
        ],
    );
    assert_eq!(
        validate_module(&m),
        [],
        "every precondition is a run-time one"
    );
    let src = || value(&Ty::I32, &[3], &[1, 2, 3]);
    ub(
        &m,
        "overrun",
        vec![src()],
        "tensor view: a source coordinate is out of range",
    );
    ub(
        &m,
        "overflow",
        vec![src()],
        "tensor view: an index expression overflows",
    );
    ub(
        &m,
        "div_zero",
        vec![src()],
        "tensor view: an index expression divides by zero",
    );
    ub(
        &m,
        "negative",
        vec![src()],
        "tensor view: a result extent does not fit usize",
    );
    ub(
        &m,
        "wide",
        vec![src()],
        "tensor view: a result extent does not fit usize",
    );
    ub(
        &m,
        "count",
        vec![src()],
        "tensor view: the result has more elements than usize holds",
    );
}

// ───────────────────────────── codegen ─────────────────────────────

#[test]
fn the_codegen_gate_refuses_each_instruction_by_name() {
    let m = accepted();
    assert_eq!(validate_module(&m), [], "well-formed TrustIr");
    let refused = validate_module_for_codegen(&m);
    for func in &m.functions {
        let (inst, what) = match func.name.as_str() {
            "add" | "relu" | "widen" | "udiv" => ("TensorMap", "a tensor map"),
            "sum_rows" | "sum_all" | "max_cols" | "keep_all" => {
                ("TensorReduce", "a tensor reduction")
            }
            _ => ("TensorView", "a tensor view"),
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
                inst: "TensorMap" | "TensorReduce" | "TensorView",
                ..
            }
        )),
        "the module is licensed and otherwise lowerable: {refused:?}"
    );
}
