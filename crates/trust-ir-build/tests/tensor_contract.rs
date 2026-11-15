// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// ══════════════════════════════════════════════════════════════════════════
// The tensor region (PKG-U13a): `Ty::Tensor` and `Inst::TensorContract` in
// the validator.
// ══════════════════════════════════════════════════════════════════════════
//
// The type fixes only the element type and the rank; each extent is a
// run-time value (shape is a value, not a type). What this battery pins:
//
//   * `InvalidTensorType` at EVERY type occurrence (signature, block
//     parameter, a tuple lane): the element is exactly an integer type, a
//     float refused by name until SemR has a float model (PKG-U15);
//   * the contraction's four static rules, each refused as
//     `InvalidTensorContract` whose reason names the rule: (1) the result and
//     both operands are tensors of one integer element type; (2) every paired
//     axis is below its operand's rank; (3) no axis is paired twice on one
//     side; (4) the result rank is |batch| plus both operands' free axes;
//   * matrix multiply, a batched contraction, a dot product (rank 0) and an
//     outer product (no pairs) are accepted, on the module and the standalone
//     path;
//   * the default codegen gate refuses every contraction by name
//     (`UnlowerableForCodegen`): a tensor has no machine layout.

use trust_ir::{Inst, Module, Ty};
use trust_ir_build::{
    ModuleBuilder, ValidationError, validate_function, validate_module, validate_module_for_codegen,
};

fn tensor(elem: Ty, rank: u32) -> Ty {
    Ty::Tensor(Box::new(elem), rank)
}

fn gate() -> trust_ir::BodyGate {
    trust_ir::BodyGate::Gated {
        authority: "tensor-contract".into(),
        evidence: None,
    }
}

/// One contraction, as its own function `fn {name}(lhs, rhs) -> result`.
struct Contraction {
    name: &'static str,
    lhs: Ty,
    rhs: Ty,
    result: Ty,
    batch: Vec<(u32, u32)>,
    contract: Vec<(u32, u32)>,
}

fn add(mb: &mut ModuleBuilder, c: Contraction) {
    let ft = mb.add_func_type(vec![c.lhs.clone(), c.rhs.clone()], vec![c.result.clone()]);
    let mut fb = mb.function(c.name, ft);
    let entry = fb.create_block();
    let lhs = fb.add_block_param(entry, c.lhs);
    let rhs = fb.add_block_param(entry, c.rhs);
    fb.switch_to_block(entry);
    let out = fb.tensor_contract(c.result, lhs, rhs, c.batch, c.contract);
    fb.ret(vec![out]);
    fb.set_body_gate(gate());
    fb.build();
}

fn module_of(name: &str, contractions: Vec<Contraction>) -> Module {
    let mut mb = ModuleBuilder::new(name);
    for c in contractions {
        add(&mut mb, c);
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// `[m, k] x [k, n] -> [m, n]`: `batch: []`, `contract: [(1, 0)]`.
fn matmul(name: &'static str) -> Contraction {
    Contraction {
        name,
        lhs: tensor(Ty::I32, 2),
        rhs: tensor(Ty::I32, 2),
        result: tensor(Ty::I32, 2),
        batch: vec![],
        contract: vec![(1, 0)],
    }
}

fn accepted() -> Module {
    module_of(
        "tensor_contract_accepted",
        vec![
            matmul("matmul"),
            // `[b, m, k] x [b, k, n] -> [b, m, n]`.
            Contraction {
                name: "batched",
                lhs: tensor(Ty::U8, 3),
                rhs: tensor(Ty::U8, 3),
                result: tensor(Ty::U8, 3),
                batch: vec![(0, 0)],
                contract: vec![(2, 1)],
            },
            // `[k] . [k] -> []`: a scalar (rank-0) tensor.
            Contraction {
                name: "dot",
                lhs: tensor(Ty::I64, 1),
                rhs: tensor(Ty::I64, 1),
                result: tensor(Ty::I64, 0),
                batch: vec![],
                contract: vec![(0, 0)],
            },
            // `[m] x [n] -> [m, n]`: no pairs at all.
            Contraction {
                name: "outer",
                lhs: tensor(Ty::Usize, 1),
                rhs: tensor(Ty::Usize, 1),
                result: tensor(Ty::Usize, 2),
                batch: vec![],
                contract: vec![],
            },
        ],
    )
}

/// Every error is an `InvalidTensorContract`, and one of them names `rule`.
fn assert_rule(errors: &[ValidationError], rule: &str, what: &str) {
    assert!(!errors.is_empty(), "{what}: accepted");
    assert!(
        errors
            .iter()
            .all(|e| matches!(e, ValidationError::InvalidTensorContract { .. })),
        "{what}: only InvalidTensorContract expected, got {errors:?}"
    );
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::InvalidTensorContract { reason, .. } if reason.starts_with(rule)
        )),
        "{what}: no refusal names {rule:?}: {errors:?}"
    );
}

fn refused(c: Contraction) -> Vec<ValidationError> {
    validate_module(&module_of("tensor_contract_refused", vec![c]))
}

// ───────────────────────────── accepted ─────────────────────────────

#[test]
fn matmul_batched_dot_and_outer_contractions_validate() {
    let m = accepted();
    assert_eq!(validate_module(&m), []);
    for func in &m.functions {
        assert!(
            matches!(func.blocks[0].body[0].inst, Inst::TensorContract { .. }),
            "{}: the builder spells the contraction verbatim",
            func.name
        );
        assert_eq!(
            validate_function(func),
            [],
            "{}: the standalone path agrees",
            func.name
        );
    }
}

// ───────────────────────────── static rules ─────────────────────────────

#[test]
fn rule_one_refuses_a_result_that_is_not_a_tensor() {
    let errors = refused(Contraction {
        result: Ty::I32,
        ..matmul("not_a_tensor_result")
    });
    assert_rule(&errors, "rule 1", "a non-tensor result type");
}

#[test]
fn rule_one_refuses_an_operand_that_is_not_a_tensor() {
    let errors = refused(Contraction {
        lhs: Ty::I32,
        ..matmul("not_a_tensor_operand")
    });
    assert_rule(&errors, "rule 1", "a non-tensor lhs");
}

#[test]
fn rule_one_refuses_differing_element_types() {
    let errors = refused(Contraction {
        rhs: tensor(Ty::I64, 2),
        ..matmul("element_mismatch")
    });
    assert_rule(&errors, "rule 1", "lhs i32 against rhs i64");
}

#[test]
fn rule_one_refuses_a_float_contraction_beside_the_type_refusal() {
    let errors = refused(Contraction {
        lhs: tensor(Ty::F32, 2),
        rhs: tensor(Ty::F32, 2),
        result: tensor(Ty::F32, 2),
        ..matmul("float_contraction")
    });
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::InvalidTensorContract { reason, .. } if reason.starts_with("rule 1")
        )),
        "{errors:?}"
    );
    assert!(
        errors
            .iter()
            .any(|e| matches!(e, ValidationError::InvalidTensorType { .. })),
        "{errors:?}"
    );
    assert!(
        errors.iter().all(|e| matches!(
            e,
            ValidationError::InvalidTensorContract { .. }
                | ValidationError::InvalidTensorType { .. }
        )),
        "{errors:?}"
    );
}

#[test]
fn rule_two_refuses_an_axis_past_its_operand_rank() {
    let errors = refused(Contraction {
        contract: vec![(2, 0)],
        ..matmul("lhs_axis_out_of_range")
    });
    assert_rule(&errors, "rule 2", "lhs axis 2 of a rank-2 tensor");
    let errors = refused(Contraction {
        contract: vec![(1, 2)],
        ..matmul("rhs_axis_out_of_range")
    });
    assert_rule(&errors, "rule 2", "rhs axis 2 of a rank-2 tensor");
}

#[test]
fn rule_three_refuses_an_axis_paired_twice_on_one_side() {
    let rank3 = |name| Contraction {
        name,
        lhs: tensor(Ty::I32, 3),
        rhs: tensor(Ty::I32, 3),
        result: tensor(Ty::I32, 3),
        batch: vec![(0, 0)],
        contract: vec![(2, 1)],
    };
    let errors = refused(Contraction {
        contract: vec![(0, 1)],
        ..rank3("lhs_axis_twice")
    });
    assert_rule(&errors, "rule 3", "lhs axis 0 in batch and contract");
    let errors = refused(Contraction {
        contract: vec![(1, 0)],
        ..rank3("rhs_axis_twice")
    });
    assert_rule(&errors, "rule 3", "rhs axis 0 in batch and contract");
}

#[test]
fn rule_four_refuses_a_result_rank_that_is_not_batch_plus_free_axes() {
    let errors = refused(Contraction {
        result: tensor(Ty::I32, 3),
        ..matmul("rank_mismatch")
    });
    assert_rule(&errors, "rule 4", "matmul declared at rank 3");
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::InvalidTensorContract { reason, .. } if reason.contains("is 2")
        )),
        "the refusal states the rank the rule computes: {errors:?}"
    );
    // The standalone path checks the same rule (every type is inline).
    let m = module_of(
        "rank_mismatch_standalone",
        vec![Contraction {
            result: tensor(Ty::I32, 3),
            ..matmul("rank_mismatch")
        }],
    );
    assert_rule(
        &validate_function(&m.functions[0]),
        "rule 4",
        "the standalone path",
    );
}

// ───────────────────────────── the type ─────────────────────────────

/// `fn sink(x: param) -> ()`, a body that ignores `x`.
fn signature_module(param: Ty) -> Module {
    let mut mb = ModuleBuilder::new("tensor_signature");
    let ft = mb.add_func_type(vec![param.clone()], vec![]);
    let mut fb = mb.function("sink", ft);
    let entry = fb.create_block();
    fb.add_block_param(entry, param);
    fb.switch_to_block(entry);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// Every error is an `InvalidTensorType` with exactly `detail`, and the
/// signature's parameter is one of the refused occurrences.
fn assert_type_refused(errors: &[ValidationError], detail: &str) {
    assert!(
        errors.iter().all(|e| matches!(
            e,
            ValidationError::InvalidTensorType { detail: d, .. } if d == detail
        )),
        "only InvalidTensorType {detail:?} expected, got {errors:?}"
    );
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::InvalidTensorType { location, .. } if location == "functy.0 param 0"
        )),
        "the signature occurrence is refused: {errors:?}"
    );
}

#[test]
fn a_float_element_is_refused_by_name_at_a_signature() {
    let errors = validate_module(&signature_module(tensor(Ty::F32, 2)));
    assert_type_refused(
        &errors,
        "tensor element type f32 is a float; float tensors wait on SemR's float model (PKG-U15)",
    );
}

#[test]
fn a_bool_element_is_refused_at_a_signature() {
    let errors = validate_module(&signature_module(tensor(Ty::Bool, 1)));
    assert_type_refused(&errors, "tensor element type bool is not an integer type");
}

#[test]
fn a_refused_element_is_found_inside_a_tuple_lane() {
    let errors = validate_module(&signature_module(Ty::Tuple(vec![
        Ty::I32,
        tensor(Ty::Char, 1),
    ])));
    assert_type_refused(&errors, "tensor element type char is not an integer type");
}

#[test]
fn every_integer_element_is_admitted_at_a_signature() {
    for elem in [
        Ty::I8,
        Ty::I16,
        Ty::I32,
        Ty::I64,
        Ty::I128,
        Ty::Isize,
        Ty::U8,
        Ty::U16,
        Ty::U32,
        Ty::U64,
        Ty::U128,
        Ty::Usize,
    ] {
        let ty = tensor(elem, 0);
        assert_eq!(validate_module(&signature_module(ty.clone())), [], "{ty}");
    }
}

// ───────────────────────────── codegen ─────────────────────────────

#[test]
fn the_codegen_gate_refuses_every_contraction_by_name() {
    let m = accepted();
    assert_eq!(validate_module(&m), [], "well-formed TrustIr");
    let refused = validate_module_for_codegen(&m);
    for func in &m.functions {
        let named = refused
            .iter()
            .filter(|e| {
                matches!(
                    e,
                    ValidationError::UnlowerableForCodegen { name, inst: "TensorContract", detail, .. }
                    if *name == func.name
                        && detail
                            == "a tensor contraction has no machine lowering yet (PKG-U13: \
                                outside the lowering-target subset)"
                )
            })
            .count();
        assert_eq!(named, 1, "{}: refused exactly once: {refused:?}", func.name);
    }
    assert!(
        refused.iter().all(|e| matches!(
            e,
            ValidationError::UnlowerableForCodegen {
                inst: "TensorContract",
                ..
            }
        )),
        "the module is licensed and otherwise lowerable: {refused:?}"
    );
}
