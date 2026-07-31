// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// WS3-M1 seed (Program CK1, designs/2026-07-07 ~"mixed module + specs flow,
// negative-test-first"): ONE trust-ir module legally carries functions from
// BOTH producers (v23 `Function.producer` tags) with cross-producer calls in
// BOTH directions, and a skewed cross-producer call edge is REJECTED with a
// diagnostic that attributes both sides by producer.
//
// The NEGATIVE tests come first in this file, in the spirit of
// negative-test-first: the rejection contract is the acceptance seed, the
// green fixture is what remains once the rejection holds. The byte-golden
// four-format wire pinning of the green fixture lives in the corpus
// (`tests/conformance.rs`, fixture `mixed_producer_module`); the subset gate
// (`tests/lowering_subset.rs`) additionally holds it inside lowering-target
// current lowering-target subset with no exemption.

use trust_ir::inst::Inst;
use trust_ir::{Interpreter, Producer};
use trust_ir_build::validate::ValidationError;

// Fixture generators live in a sibling file and are included directly so
// these tests walk the exact module the byte-golden corpus pins. (dead_code
// allowed: only the mixed-producer builders are used here.)
#[allow(dead_code)]
#[path = "generate.rs"]
mod generate;

// ============================================================
// NEGATIVE: mismatched-FuncTy cross-call is rejected, with
// producer-attributed diagnostics (lands first)
// ============================================================

/// A tRust-produced caller invoking a Clean-produced callee against a stale
/// signature (i64 arg where the callee declares i32) must be rejected, and
/// the diagnostic must name BOTH producers of the broken edge.
#[test]
fn cross_producer_functy_type_mismatch_is_rejected_with_producer_attribution() {
    let module = generate::build_mixed_producer_cross_functy_mismatch();
    let errors = trust_ir_build::validate_module(&module);

    let type_mismatch = errors
        .iter()
        .find(|e| matches!(e, ValidationError::CallArgTypeMismatch { .. }))
        .unwrap_or_else(|| {
            panic!("skewed tRust->Clean call must produce CallArgTypeMismatch, got: {errors:?}")
        });
    let rendered = type_mismatch.to_string();
    assert!(
        rendered.contains("call to clean_double")
            && rendered.contains("expected i32")
            && rendered.contains("got i64"),
        "diagnostic must state the FuncTy skew, got: {rendered}"
    );
    assert!(
        rendered.contains("caller producer: trust") && rendered.contains("callee producer: clean"),
        "diagnostic must attribute BOTH sides of the cross-producer edge \
         (caller producer: trust / callee producer: clean), got: {rendered}"
    );
}

/// The reverse direction: a Clean-produced caller invoking a tRust-produced
/// callee with the wrong arity must be rejected with the same attribution.
#[test]
fn cross_producer_functy_arity_mismatch_is_rejected_with_producer_attribution() {
    let module = generate::build_mixed_producer_cross_functy_mismatch();
    let errors = trust_ir_build::validate_module(&module);

    let count_mismatch = errors
        .iter()
        .find(|e| matches!(e, ValidationError::CallArgCountMismatch { .. }))
        .unwrap_or_else(|| {
            panic!("skewed Clean->tRust call must produce CallArgCountMismatch, got: {errors:?}")
        });
    let rendered = count_mismatch.to_string();
    assert!(
        rendered.contains("call to trust_inc")
            && rendered.contains("has 2 args")
            && rendered.contains("expected 1"),
        "diagnostic must state the arity skew, got: {rendered}"
    );
    assert!(
        rendered.contains("caller producer: clean") && rendered.contains("callee producer: trust"),
        "diagnostic must attribute BOTH sides of the cross-producer edge \
         (caller producer: clean / callee producer: trust), got: {rendered}"
    );
}

// ============================================================
// POSITIVE: the mixed-producer module is legal
// ============================================================

/// WS3-M1 acceptance floor: the mixed-producer module validates with ZERO
/// errors, carries both producer tags, and has cross-producer calls in BOTH
/// directions (TRust caller -> Clean callee AND Clean caller -> TRust callee).
#[test]
fn mixed_producer_module_validates_with_both_call_directions() {
    let module = generate::build_mixed_producer_module();

    // 1. validate_module: 0 errors.
    let errors = trust_ir_build::validate_module(&module);
    assert!(
        errors.is_empty(),
        "mixed-producer module must validate cleanly: {errors:?}"
    );

    // 2. Both producers are present as function tags.
    let producer_of = |name: &str| -> &Producer {
        module
            .functions
            .iter()
            .find(|f| f.name == name)
            .unwrap_or_else(|| panic!("fixture lost function `{name}`"))
            .producer
            .as_ref()
            .unwrap_or_else(|| panic!("function `{name}` lost its producer tag"))
    };
    assert_eq!(producer_of("clean_double"), &Producer::Clean);
    assert_eq!(producer_of("trust_inc"), &Producer::TRust);
    assert_eq!(producer_of("trust_calls_clean"), &Producer::TRust);
    assert_eq!(producer_of("clean_calls_trust"), &Producer::Clean);

    // 3. Cross-producer call edges exist in BOTH directions. Collect every
    //    (caller producer, callee producer) pair over direct calls.
    let mut edges = Vec::new();
    for func in &module.functions {
        for block in &func.blocks {
            for node in &block.body {
                if let Inst::Call { callee, .. } = &node.inst {
                    let callee_func = module
                        .functions
                        .iter()
                        .find(|f| f.id == *callee)
                        .expect("callee resolves");
                    edges.push((
                        func.producer.clone().expect("caller tagged"),
                        callee_func.producer.clone().expect("callee tagged"),
                    ));
                }
            }
        }
    }
    assert!(
        edges.contains(&(Producer::TRust, Producer::Clean)),
        "missing tRust -> Clean call edge; edges: {edges:?}"
    );
    assert!(
        edges.contains(&(Producer::Clean, Producer::TRust)),
        "missing Clean -> tRust call edge; edges: {edges:?}"
    );
}

/// Executable end-to-end: both cross-producer call chains run through the
/// reference interpreter (callee included) and produce the arithmetic the
/// bodies spell out. `trust_calls_clean(20) = 20*2 + 1 = 41`;
/// `clean_calls_trust(20) = (20+1)*2 = 42`.
#[test]
fn mixed_producer_module_executes_both_cross_calls() {
    let module = generate::build_mixed_producer_module();

    let func_id = |name: &str| {
        module
            .functions
            .iter()
            .find(|f| f.name == name)
            .unwrap_or_else(|| panic!("fixture lost function `{name}`"))
            .id
    };
    let run = |name: &str, arg: i128| -> i128 {
        let outcome = Interpreter::with_module(&module)
            .execute_func(
                func_id(name),
                [trust_ir::InterpretValue::int(trust_ir::Ty::I32, arg).expect("i32 arg")],
            )
            .unwrap_or_else(|e| panic!("`{name}` executes: {e}"));
        outcome.returns[0].as_int().expect("i32 result").as_signed()
    };

    assert_eq!(run("trust_calls_clean", 20), 41, "tRust -> Clean chain");
    assert_eq!(run("clean_calls_trust", 20), 42, "Clean -> tRust chain");
}
