// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// ══════════════════════════════════════════════════════════════════════════
// WS3.17 (F-051) — element READ and WRITE on a `Ty::Sequence` value.
// ══════════════════════════════════════════════════════════════════════════
//
// The hole: `Ty::supports_element_ops()` answered vector-or-array, so
// `check_extract_element_operands` refused EVERY `ExtractElement` over a
// `Ty::Sequence` with `InvalidVectorElementOp { reason: "operand must be
// vector or array" }` — while the reference interpreter executed exactly that
// read (`interpret.rs` `eval_extract_element` accepts Vector | Array |
// Sequence | Aggregate) and `lowering-target-subset.md` lists `Sequence` as an
// in-subset type. A Clean `List`/`Array` carrier could therefore be built,
// transported and MAPPED (`SeqMapAddK` / `SeqMapNot` / `SeqMap`) but never
// indexed or folded inside a well-formed module. The Lean model was the third
// disagreeing engine: `getElement` had no `.sequence` arm, so it TYPE-ERRORED
// where the Rust engine returned the element.
//
// The rule this pins (all three engines now agree):
//
//   * `ExtractElement` over `Sequence(t)` validates; the declared RESULT type
//     must be exactly the module's `t` (`InvalidVectorElementOp`, "result type
//     must match sequence element type"), decided by the consumption rule when
//     either side is a `Ty::Refine`;
//   * `InsertElement` over `Sequence(t)` validates; its result type is the
//     sequence (the pre-existing rule) and the INSERTED value must be `t`;
//   * an ARRAY's element ops get the same exact-type rule (review finding:
//     the arms used to claim an array's element type was "checked elsewhere",
//     and nothing did — see the review section at the end of this file);
//   * the index must be an UNSIGNED integer. A vector or array carries its
//     element count in its type, so a negative constant index is refused by
//     the static range check; a sequence's length is a property of the VALUE,
//     so the index type is the only place non-negativity can be stated. A
//     negative constant index is refused too, for the same reason;
//   * an index PAST THE END is run-time undefined behaviour, exactly as for a
//     dynamic array index — the reference interpreter answers
//     `UndefinedBehavior "element {i} is out of bounds"`;
//   * `Ty::Sequence` still has NO machine layout, so the element ops are
//     verification-level only: `codegen_lowerability_errors` names them
//     (`UnlowerableForCodegen`) instead of leaving a backend to fail on the
//     layout query late and in another repo.
//
// DECIDE (roadmap WS3.17, recommended option adopted): `Sequence` stays
// verification-level. A borrowed string crosses the language boundary as
// `FatPtr(Str)` and an owned Clean `String` as a pinned runtime handle row —
// never as a `Sequence`. Making `Sequence` a machine type was rejected: it has
// no layout to give.
//
// DEFERRED to the wire lane: `Inst::SeqLen { seq } -> Usize` (WS3.17 (b)) is a
// new `Inst` variant and therefore a new binary version; it lands with the
// coordinated Rust+Lean+obligation triple under a reserved version. The Lean
// half that needs no instruction is already proved:
// `seqMapAddKList_length` / `seqMapNotList_length` (Semantics/Aggregate.lean).
//
// The ported GAP ratchet is `b6.sequence.no_validated_element_read` from the
// 2026-09-17 two-language proof program: there it asserted the hole was
// PRESENT; here it asserts it is CLOSED.

use trust_ir::constant::Constant;
use trust_ir::inst::Inst;
use trust_ir::interpret::{InterpretOptions, InterpretValue, InterpretValueKind, Interpreter};
use trust_ir::ty::Ty;
use trust_ir::value::TyId;
use trust_ir::{Module, Pred, Producer};
use trust_ir_build::validate::codegen_lowerability_errors;
use trust_ir_build::{ModuleBuilder, ValidationError, validate_module};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn render(errors: &[ValidationError]) -> String {
    errors
        .iter()
        .map(|e| e.to_string())
        .collect::<Vec<_>>()
        .join(" | ")
}

fn assert_clean(module: &Module, what: &str) {
    let errors = validate_module(module);
    assert!(
        errors.is_empty(),
        "{what} must validate clean, got {} error(s): {}",
        errors.len(),
        render(&errors)
    );
}

/// Exactly one error, an `InvalidVectorElementOp` on `want_op` whose reason
/// contains `fragment`.
fn assert_one_element_refusal(
    errors: &[ValidationError],
    what: &str,
    want_op: &str,
    fragment: &str,
) {
    assert_eq!(
        errors.len(),
        1,
        "{what}: expected exactly one error, got {}: {}",
        errors.len(),
        render(errors)
    );
    match &errors[0] {
        ValidationError::InvalidVectorElementOp { op, reason, .. } => {
            assert_eq!(op, want_op, "{what}: op");
            assert!(
                reason.contains(fragment),
                "{what}: expected {fragment:?} in the reason, got {reason:?}"
            );
        }
        other => panic!("{what}: wrong refusal kind: {other:?}"),
    }
}

fn run_nullary(module: &Module, entry: &str) -> Result<Vec<InterpretValue>, String> {
    let func = module
        .function_by_name(entry)
        .ok_or_else(|| format!("no function named @{entry}"))?;
    Interpreter::with_module(module)
        .with_options(InterpretOptions {
            fuel: 50_000_000,
            max_call_depth: 4096,
            ..InterpretOptions::default()
        })
        .execute_func(func.id, Vec::new())
        .map(|outcome| outcome.returns)
        .map_err(|e| format!("{:?}: {e}", e.code))
}

fn run_u(module: &Module, entry: &str) -> Result<u128, String> {
    let returns = run_nullary(module, entry)?;
    returns
        .first()
        .and_then(InterpretValue::as_int)
        .map(|i| i.as_unsigned())
        .ok_or_else(|| format!("not a scalar: {returns:?}"))
}

fn sequence_elements(module: &Module, entry: &str) -> Result<Vec<u128>, String> {
    let returns = run_nullary(module, entry)?;
    match returns.first().map(|v| &v.kind) {
        Some(InterpretValueKind::Sequence(items)) => items
            .iter()
            .map(|i| {
                i.as_int()
                    .map(|i| i.as_unsigned())
                    .ok_or_else(|| format!("non-scalar element: {i:?}"))
            })
            .collect(),
        _ => Err(format!("not a sequence: {returns:?}")),
    }
}

/// How the index operand of the element op is spelled.
#[derive(Clone, Copy)]
enum Index {
    /// The admitted spelling: an unsigned integer.
    U64(u128),
    /// A SIGNED integer — refused on a sequence (the roadmap's rule), still
    /// admitted on an array, where the static range check bounds it.
    I64(i128),
    /// Not an integer at all.
    F32,
}

/// `fn program() -> {result_ty}` reading element `index` of the three-element
/// `seq<u8> [1, 5, 15]` (or of `[u8; 3]` when `sequence` is false).
fn build_read(sequence: bool, index: Index, result_ty: Ty) -> Module {
    let mut mb = ModuleBuilder::new("ws317_read");
    let u8_id = mb.add_type(Ty::U8);
    let nullary = mb.add_func_type(vec![], vec![result_ty.clone()]);
    let mut fb = mb.function("program", nullary);
    fb.set_producer(Producer::Clean);
    let e = fb.create_block();
    fb.switch_to_block(e);
    let items = vec![Constant::Int(1), Constant::Int(5), Constant::Int(15)];
    let seq = if sequence {
        fb.const_value(Ty::Sequence(u8_id), Constant::Sequence(items))
    } else {
        fb.const_value(Ty::Array(u8_id, 3), Constant::Array(items))
    };
    let idx = match index {
        Index::U64(v) => fb.uconst(Ty::U64, v),
        Index::I64(v) => fb.iconst(Ty::I64, v),
        Index::F32 => fb.const_value(Ty::F32, Constant::Float(1.0)),
    };
    let el = fb.extract_element(result_ty, seq, idx);
    fb.ret(vec![el]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// `fn program() -> seq<u8>` writing `value_ty`-typed `7` into element `index`
/// of `seq<u8> [1, 5, 15]`.
fn build_write(index: Index, value_ty: Ty) -> Module {
    let mut mb = ModuleBuilder::new("ws317_write");
    let u8_id = mb.add_type(Ty::U8);
    let seq_ty = Ty::Sequence(u8_id);
    let nullary = mb.add_func_type(vec![], vec![seq_ty.clone()]);
    let mut fb = mb.function("program", nullary);
    fb.set_producer(Producer::Clean);
    let e = fb.create_block();
    fb.switch_to_block(e);
    let seq = fb.const_value(
        seq_ty.clone(),
        Constant::Sequence(vec![Constant::Int(1), Constant::Int(5), Constant::Int(15)]),
    );
    let idx = match index {
        Index::U64(v) => fb.uconst(Ty::U64, v),
        Index::I64(v) => fb.iconst(Ty::I64, v),
        Index::F32 => fb.const_value(Ty::F32, Constant::Float(1.0)),
    };
    let seven = fb.uconst(value_ty, 7);
    let out = fb.insert_element(seq_ty, seq, idx, seven);
    fb.ret(vec![out]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

// ---------------------------------------------------------------------------
// The ported ratchet row
// ---------------------------------------------------------------------------

/// `b6.sequence.no_validated_element_read`, ported as a PASS: the read that
/// the interpreter always executed now validates, with the array baseline
/// unchanged beside it.
#[test]
fn b6_sequence_no_validated_element_read_is_closed() {
    let seq = build_read(true, Index::U64(1), Ty::U8);
    let array = build_read(false, Index::U64(1), Ty::U8);
    assert_clean(&seq, "extract_element over seq<u8>");
    assert_clean(&array, "the array baseline");
    assert_eq!(run_u(&seq, "program"), Ok(5), "the sequence read runs");
    assert_eq!(run_u(&array, "program"), Ok(5), "the array baseline runs");
}

// ---------------------------------------------------------------------------
// Positive
// ---------------------------------------------------------------------------

#[test]
fn a_sequence_write_validates_and_runs() {
    let m = build_write(Index::U64(1), Ty::U8);
    assert_clean(&m, "insert_element into seq<u8>");
    assert_eq!(
        sequence_elements(&m, "program"),
        Ok(vec![1, 7, 15]),
        "the write yields a SEQUENCE with element 1 replaced"
    );
}

/// A refined element type is decided by the consumption rule, not by type
/// equality — the same treatment a vector lane gets. Both directions:
/// reading the bare `u8` out of `seq<{u8 | nonzero}>` is admitted (the carried
/// fact is stronger than the demand), and reading `{u8 | nonzero}` out of a
/// bare `seq<u8>` is refused by the REFINEMENT rule, never by the plain
/// element-type check.
#[test]
fn a_refined_sequence_element_is_decided_by_the_consumption_rule() {
    // `refined_carrier`: the sequence's element type is `{u8 | nonzero}`;
    // otherwise the READ demands it.
    let build = |refined_carrier: bool| {
        let mut mb = ModuleBuilder::new("ws317_refined");
        let nonzero = mb.intern_pred(Pred::NonZero).expect("pred");
        let refined = mb.refine_ty(Ty::U8, nonzero);
        let refined_id = mb.add_type(refined.clone());
        let u8_id = mb.add_type(Ty::U8);
        let (elem_id, demanded) = if refined_carrier {
            (refined_id, Ty::U8)
        } else {
            (u8_id, refined)
        };
        // The carrier is a PARAMETER: a `Constant::Sequence` cannot be typed
        // at a refined element (the constant rule refuses it), and the
        // question here is the read, not the constant.
        let sig = mb.add_func_type(vec![Ty::Sequence(elem_id)], vec![demanded.clone()]);
        let mut fb = mb.function("program", sig);
        fb.set_producer(Producer::Clean);
        let e = fb.create_block();
        let seq = fb.add_block_param(e, Ty::Sequence(elem_id));
        fb.switch_to_block(e);
        let idx = fb.uconst(Ty::U64, 1);
        let el = fb.extract_element(demanded, seq, idx);
        fb.ret(vec![el]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let plain_mismatch = |e: &ValidationError| {
        matches!(
            e,
            ValidationError::InvalidVectorElementOp { reason, .. }
                if reason.contains("must match sequence element type")
        )
    };

    let weakening = validate_module(&build(true));
    assert!(
        !weakening.iter().any(plain_mismatch),
        "a refinement-involving position must not raise a plain element-type \
         mismatch (the consumption rule decides it): {}",
        render(&weakening)
    );
    assert!(
        weakening.is_empty(),
        "reading the base type out of a refined carrier is admitted: {}",
        render(&weakening)
    );

    let strengthening = validate_module(&build(false));
    assert!(
        !strengthening.iter().any(plain_mismatch),
        "the plain check must stay out of a refinement decision: {}",
        render(&strengthening)
    );
    assert!(
        strengthening.iter().any(|e| matches!(
            e,
            ValidationError::RefinementNotImplied { location, .. }
                if location.contains("extract_element")
        )),
        "reading a refinement the carrier does not establish must be refused by \
         the refinement rule: {}",
        render(&strengthening)
    );
}

// ---------------------------------------------------------------------------
// Negative twins — each refused for its own named reason
// ---------------------------------------------------------------------------

#[test]
fn a_non_integer_index_is_refused() {
    let errors = validate_module(&build_read(true, Index::F32, Ty::U8));
    assert_one_element_refusal(
        &errors,
        "extract_element at an f32 index",
        "extract_element",
        "index must be integer, got f32",
    );
}

#[test]
fn a_signed_index_is_refused_on_a_sequence() {
    let errors = validate_module(&build_read(true, Index::I64(1), Ty::U8));
    assert_one_element_refusal(
        &errors,
        "extract_element at an i64 index",
        "extract_element",
        "a sequence index must be an unsigned integer",
    );
}

#[test]
fn a_result_type_that_is_not_the_element_type_is_refused() {
    let errors = validate_module(&build_read(true, Index::U64(1), Ty::U16));
    assert_one_element_refusal(
        &errors,
        "extract_element u16 over seq<u8>",
        "extract_element",
        "result type must match sequence element type u8, got u16",
    );
}

#[test]
fn an_inserted_value_that_is_not_the_element_type_is_refused() {
    let errors = validate_module(&build_write(Index::U64(1), Ty::U16));
    assert_one_element_refusal(
        &errors,
        "insert_element u16 into seq<u8>",
        "insert_element",
        "inserted value must match sequence element type u8, got u16",
    );
}

#[test]
fn a_negative_constant_index_is_refused_on_a_sequence() {
    // The index type is signed AND the constant is negative: both rules fire,
    // and neither is the array's static range check (a sequence has no range).
    let errors = validate_module(&build_read(true, Index::I64(-1), Ty::U8));
    assert_eq!(
        errors.len(),
        2,
        "expected the signedness and the negativity refusals: {}",
        render(&errors)
    );
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::InvalidVectorElementOp { reason, .. }
                if reason.contains("constant element index -1 is negative")
        )),
        "the negative constant index must be named: {}",
        render(&errors)
    );
}

/// A sequence whose element `TyId` is not in the module's type table is
/// REFUSED, not silently admitted: with no resolvable element type there is
/// nothing to check the read against.
#[test]
fn a_dangling_sequence_element_type_is_refused() {
    let mut m = build_read(true, Index::U64(1), Ty::U8);
    let dangling = TyId::new(u32::try_from(m.types.len()).expect("small type table") + 7);
    for func in &mut m.functions {
        for block in &mut func.blocks {
            for node in &mut block.body {
                match &mut node.inst {
                    Inst::Const { ty, .. } | Inst::ExtractElement { array: _, ty, .. } => {
                        if let Ty::Sequence(elem) = ty {
                            *elem = dangling;
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    let errors = validate_module(&m);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::InvalidVectorElementOp { op, reason, .. }
                if op == "extract_element"
                    && reason.contains("is not in the module type table")
        )),
        "a dangling element type must be refused by name: {}",
        render(&errors)
    );
}

// ---------------------------------------------------------------------------
// Mutation controls
// ---------------------------------------------------------------------------

/// The refusal for a genuinely unsupported operand is unchanged — widening to
/// sequences did not widen to every value.
#[test]
fn mutation_control_a_scalar_operand_is_still_refused() {
    let mut mb = ModuleBuilder::new("ws317_scalar_operand");
    let nullary = mb.add_func_type(vec![], vec![Ty::U8]);
    let mut fb = mb.function("program", nullary);
    fb.set_producer(Producer::Clean);
    let e = fb.create_block();
    fb.switch_to_block(e);
    let scalar = fb.uconst(Ty::U8, 3);
    let idx = fb.uconst(Ty::U64, 0);
    let el = fb.extract_element(Ty::U8, scalar, idx);
    fb.ret(vec![el]);
    fb.build();
    let errors = validate_module(&mb.build().expect("ModuleBuilder::build: test fixture"));
    assert_one_element_refusal(
        &errors,
        "extract_element over a u8",
        "extract_element",
        "operand must be vector, array or sequence, got u8",
    );
}

/// The ARRAY rules are untouched: a signed index is still fine there (the
/// static range check bounds it), and a constant past the end is still the
/// lane-range refusal, not the sequence's negativity rule.
#[test]
fn mutation_control_the_array_index_rules_are_unchanged() {
    assert_clean(
        &build_read(false, Index::I64(1), Ty::U8),
        "an i64 index into [u8; 3]",
    );
    let errors = validate_module(&build_read(false, Index::U64(3), Ty::U8));
    assert_one_element_refusal(
        &errors,
        "extract_element at array index 3 of 3",
        "extract_element",
        "constant lane index 3 is out of range for 3 lanes",
    );
}

/// Past the end of a SEQUENCE is not a static error — it is run-time UB, the
/// same verdict a dynamic array index gets.
#[test]
fn mutation_control_an_out_of_range_sequence_index_is_run_time_ub() {
    let m = build_read(true, Index::U64(3), Ty::U8);
    assert_clean(&m, "extract_element at sequence index 3");
    let outcome = run_u(&m, "program");
    assert!(
        outcome
            .as_ref()
            .is_err_and(|e| e.contains("UndefinedBehavior") && e.contains("out of bounds")),
        "expected run-time UB, got {outcome:?}"
    );
}

/// The give-back loop instructions and the element read compose: element `i`
/// of a `SeqMapAddK` result is element `i` of the input plus `k`. This is the
/// interpreter half of the Lean `seqMapAddKList_length` lemma (a map preserves
/// length, so the read is defined exactly where the input's is).
#[test]
fn mutation_control_an_element_read_of_a_mapped_sequence_is_the_mapped_element() {
    for (index, want) in [(0u128, 1 + 3), (1, 5 + 3), (2, 15 + 3)] {
        let mut m = build_read(true, Index::U64(index), Ty::U8);
        let seq_ty = {
            let u8_id = TyId::new(0);
            Ty::Sequence(u8_id)
        };
        // Insert `SeqMapAddK k=3` between the constant and the read.
        let func = m
            .functions
            .iter_mut()
            .find(|f| f.name == "program")
            .expect("program");
        let block = &mut func.blocks[0];
        let seq_value = block.body[0].results[0];
        let mapped = trust_ir::value::ValueId::new(
            block
                .body
                .iter()
                .flat_map(|n| n.results.iter().map(|v| v.index()))
                .max()
                .expect("some results")
                + 1,
        );
        let mut node = trust_ir::node::InstrNode::new(Inst::SeqMapAddK {
            ty: seq_ty,
            seq: seq_value,
            k: 3,
        });
        node.results = vec![mapped];
        block.body.insert(1, node);
        let read = block
            .body
            .iter_mut()
            .find_map(|n| match &mut n.inst {
                Inst::ExtractElement { array, .. } => Some(array),
                _ => None,
            })
            .expect("the element read");
        *read = mapped;
        assert_clean(&m, "extract_element over a SeqMapAddK result");
        assert_eq!(
            run_u(&m, "program"),
            Ok(want),
            "element {index} of the mapped sequence"
        );
    }
}

// ---------------------------------------------------------------------------
// Codegen: admitted for verification, refused for lowering
// ---------------------------------------------------------------------------

#[test]
fn a_sequence_element_op_is_refused_for_codegen() {
    for (module, inst) in [
        (build_read(true, Index::U64(1), Ty::U8), "ExtractElement"),
        (build_write(Index::U64(1), Ty::U8), "InsertElement"),
    ] {
        assert_clean(&module, "the sequence element op");
        let errors = codegen_lowerability_errors(&module);
        assert_eq!(
            errors.len(),
            1,
            "expected exactly one lowerability refusal, got: {}",
            render(&errors)
        );
        match &errors[0] {
            ValidationError::UnlowerableForCodegen {
                name,
                inst: got,
                detail,
                ..
            } => {
                assert_eq!(name, "program");
                assert_eq!(*got, inst);
                assert!(
                    detail.contains("Ty::Sequence") && detail.contains("no machine layout"),
                    "the refusal must name the missing layout: {detail}"
                );
            }
            other => panic!("wrong refusal kind: {other:?}"),
        }
    }
}

/// Mutation control for the codegen half: the ARRAY spelling of the same body
/// is lowerable, so the refusal is about the carrier, not about element ops.
#[test]
fn mutation_control_an_array_element_op_is_lowerable() {
    let m = build_read(false, Index::U64(1), Ty::U8);
    assert!(
        codegen_lowerability_errors(&m).is_empty(),
        "the array spelling must stay lowerable: {}",
        render(&codegen_lowerability_errors(&m))
    );
}

// ---------------------------------------------------------------------------
// Review: adversarial inputs (WS3.17 review pass)
// ---------------------------------------------------------------------------

/// `fn program() -> [u8; 3]` writing `value_ty`-typed `7` into element 1 of
/// `[u8; 3] [1, 5, 15]` — the ARRAY twin of `build_write`.
fn build_array_write(value_ty: Ty) -> Module {
    let mut mb = ModuleBuilder::new("ws317_array_write");
    let u8_id = mb.add_type(Ty::U8);
    let arr_ty = Ty::Array(u8_id, 3);
    let nullary = mb.add_func_type(vec![], vec![arr_ty.clone()]);
    let mut fb = mb.function("program", nullary);
    fb.set_producer(Producer::Clean);
    let e = fb.create_block();
    fb.switch_to_block(e);
    let arr = fb.const_value(
        arr_ty.clone(),
        Constant::Array(vec![Constant::Int(1), Constant::Int(5), Constant::Int(15)]),
    );
    let idx = fb.uconst(Ty::U64, 1);
    let seven = fb.uconst(value_ty, 7);
    let out = fb.insert_element(arr_ty, arr, idx, seven);
    fb.ret(vec![out]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// A FALSE CLAIM the review found accepted: the element-op arms said an
/// array's element type was "checked elsewhere by the module-level type
/// table", but the only module-level consumer engages when a `Refine` is
/// involved, so `u16` out of `[u8; 3]` — and `u16` into it — validated CLEAN
/// and was caught only by the interpreter's run-time type check (a backend
/// would have addressed the element at the wrong width). The array now gets
/// the sequence's exact-type rule, by name.
#[test]
fn review_an_array_element_type_mismatch_is_refused() {
    let read = validate_module(&build_read(false, Index::U64(1), Ty::U16));
    assert_one_element_refusal(
        &read,
        "extract_element u16 over [u8; 3]",
        "extract_element",
        "result type must match array element type u8, got u16",
    );
    let write = validate_module(&build_array_write(Ty::U16));
    assert_one_element_refusal(
        &write,
        "insert_element u16 into [u8; 3]",
        "insert_element",
        "inserted value must match array element type u8, got u16",
    );
    // Control: the exact element type is admitted and runs, on both sides.
    assert_clean(&build_array_write(Ty::U8), "insert_element u8 into [u8; 3]");
    let returns = run_nullary(&build_array_write(Ty::U8), "program").expect("runs");
    match returns.first().map(|v| &v.kind) {
        Some(InterpretValueKind::Array(items)) => {
            let got: Vec<u128> = items
                .iter()
                .map(|i| i.as_int().expect("scalar").as_unsigned())
                .collect();
            assert_eq!(got, vec![1, 7, 15]);
        }
        other => panic!("expected an array, got {other:?}"),
    }
}

/// The refinement exemption is not a bypass: demanding `{u8 | nonzero}` out
/// of `seq<u16>` is a REPRESENTATION mismatch, and the consumption rule (not
/// the plain check) refuses it by name.
#[test]
fn review_a_refined_demand_over_the_wrong_base_is_refused() {
    let mut mb = ModuleBuilder::new("ws317_refined_wrong_base");
    let nonzero = mb.intern_pred(Pred::NonZero).expect("pred");
    let refined = mb.refine_ty(Ty::U8, nonzero);
    let u16_id = mb.add_type(Ty::U16);
    let sig = mb.add_func_type(vec![Ty::Sequence(u16_id)], vec![refined.clone()]);
    let mut fb = mb.function("program", sig);
    fb.set_producer(Producer::Clean);
    let e = fb.create_block();
    let seq = fb.add_block_param(e, Ty::Sequence(u16_id));
    fb.switch_to_block(e);
    let idx = fb.uconst(Ty::U64, 1);
    let el = fb.extract_element(refined, seq, idx);
    fb.ret(vec![el]);
    fb.build();
    let errors = validate_module(&mb.build().expect("ModuleBuilder::build: test fixture"));
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::RefinementTypeInvalid { location, detail }
                if location.contains("extract_element")
                    && detail.contains("representation u16 does not match the required representation u8")
        )),
        "the representation mismatch must be named: {}",
        render(&errors)
    );
    assert!(
        !errors.iter().any(|e| matches!(
            e,
            ValidationError::InvalidVectorElementOp { reason, .. }
                if reason.contains("must match sequence element type")
        )),
        "the plain check must not double-report a refinement decision: {}",
        render(&errors)
    );
}

/// The WRITE side of the consumption rule: a bare `u8` into
/// `seq<{u8 | nonzero}>` drops the carrier's fact and is refused
/// (`RefinementNotImplied`); a `{u8 | nonzero}` into a bare `seq<u8>` only
/// weakens and is admitted.
#[test]
fn review_a_refined_carrier_refuses_a_bare_write_and_admits_a_refined_one() {
    let build = |refined_carrier: bool| {
        let mut mb = ModuleBuilder::new("ws317_refined_write");
        let nonzero = mb.intern_pred(Pred::NonZero).expect("pred");
        let refined = mb.refine_ty(Ty::U8, nonzero);
        let refined_id = mb.add_type(refined.clone());
        let u8_id = mb.add_type(Ty::U8);
        let (elem_id, value_ty) = if refined_carrier {
            (refined_id, Ty::U8)
        } else {
            (u8_id, refined)
        };
        let seq_ty = Ty::Sequence(elem_id);
        let sig = mb.add_func_type(vec![seq_ty.clone(), value_ty.clone()], vec![seq_ty.clone()]);
        let mut fb = mb.function("program", sig);
        fb.set_producer(Producer::Clean);
        let e = fb.create_block();
        let seq = fb.add_block_param(e, seq_ty.clone());
        let val = fb.add_block_param(e, value_ty);
        fb.switch_to_block(e);
        let idx = fb.uconst(Ty::U64, 1);
        let out = fb.insert_element(seq_ty, seq, idx, val);
        fb.ret(vec![out]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let strengthening_dropped = validate_module(&build(true));
    assert!(
        strengthening_dropped.iter().any(|e| matches!(
            e,
            ValidationError::RefinementNotImplied { location, .. }
                if location.contains("insert_element")
        )),
        "writing a bare u8 into seq<{{u8 | nonzero}}> must be refused by the \
         refinement rule: {}",
        render(&strengthening_dropped)
    );
    assert_clean(&build(false), "writing {u8 | nonzero} into seq<u8>");
}

/// A sequence that arrives as a PARAMETER (no constant to type-check): the
/// standalone function pass claims nothing about the element type (it has no
/// type table), the module pass refuses the wrong result type, and the codegen
/// layer refuses the carrier by name.
#[test]
fn review_a_sequence_parameter_is_decided_by_the_module_pass() {
    let mut mb = ModuleBuilder::new("ws317_param");
    let u8_id = mb.add_type(Ty::U8);
    let seq_ty = Ty::Sequence(u8_id);
    let sig = mb.add_func_type(vec![seq_ty.clone()], vec![Ty::U16]);
    let mut fb = mb.function("program", sig);
    fb.set_producer(Producer::Clean);
    let e = fb.create_block();
    let seq = fb.add_block_param(e, seq_ty);
    fb.switch_to_block(e);
    let idx = fb.uconst(Ty::U64, 1);
    let el = fb.extract_element(Ty::U16, seq, idx);
    fb.ret(vec![el]);
    fb.build();
    let m = mb.build().expect("ModuleBuilder::build: test fixture");
    let standalone = trust_ir_build::validate_function(&m.functions[0]);
    assert!(
        !standalone
            .iter()
            .any(|e| matches!(e, ValidationError::InvalidVectorElementOp { .. })),
        "the standalone pass has no type table and must claim nothing: {}",
        render(&standalone)
    );
    let module = validate_module(&m);
    assert_one_element_refusal(
        &module,
        "extract_element u16 over a seq<u8> parameter",
        "extract_element",
        "result type must match sequence element type u8, got u16",
    );
    let codegen = codegen_lowerability_errors(&m);
    assert!(
        codegen.iter().any(|e| matches!(
            e,
            ValidationError::UnlowerableForCodegen { inst: "ExtractElement", detail, .. }
                if detail.contains("Ty::Sequence")
        )),
        "a parameter-carried sequence read is refused for codegen: {}",
        render(&codegen)
    );
}

/// Nested carriers: a read out of `seq<seq<u8>>` is checked against the exact
/// inner sequence type (a different inner `TyId` is refused), a well-typed
/// two-level read runs, and BOTH reads are refused for codegen.
#[test]
fn review_a_nested_sequence_read_is_exact() {
    let build = |inner_as_declared: bool| {
        let mut mb = ModuleBuilder::new("ws317_nested");
        let u8_id = mb.add_type(Ty::U8);
        let u16_id = mb.add_type(Ty::U16);
        let inner = Ty::Sequence(u8_id);
        let inner_id = mb.add_type(inner.clone());
        let outer = Ty::Sequence(inner_id);
        let declared_inner = if inner_as_declared {
            inner.clone()
        } else {
            Ty::Sequence(u16_id)
        };
        let sig = mb.add_func_type(vec![], vec![Ty::U8]);
        let mut fb = mb.function("program", sig);
        fb.set_producer(Producer::Clean);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let seq = fb.const_value(
            outer,
            Constant::Sequence(vec![
                Constant::Sequence(vec![Constant::Int(1), Constant::Int(2)]),
                Constant::Sequence(vec![Constant::Int(3), Constant::Int(4)]),
            ]),
        );
        let i1 = fb.uconst(Ty::U64, 1);
        let i0 = fb.uconst(Ty::U64, 0);
        let row = fb.extract_element(declared_inner, seq, i1);
        let el = fb.extract_element(Ty::U8, row, i0);
        fb.ret(vec![el]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let good = build(true);
    assert_clean(&good, "a two-level sequence read");
    assert_eq!(run_u(&good, "program"), Ok(3), "row 1, element 0");
    let codegen = codegen_lowerability_errors(&good);
    assert_eq!(
        codegen.len(),
        2,
        "both reads are refused for codegen: {}",
        render(&codegen)
    );

    let wrong_inner = validate_module(&build(false));
    assert!(
        wrong_inner.iter().any(|e| matches!(
            e,
            ValidationError::InvalidVectorElementOp { op, reason, .. }
                if op == "extract_element"
                    && reason.contains("result type must match sequence element type seq<")
        )),
        "declaring the wrong inner sequence type must be refused: {}",
        render(&wrong_inner)
    );
}

/// Index spellings: `usize` is unsigned and admitted (and runs); `bool` is
/// not an integer and is refused; a `u128` past the address space validates
/// (unsigned, no static length) and is run-time UB, never a silent wrap.
#[test]
fn review_index_spellings() {
    let build = |index: &str| {
        let mut mb = ModuleBuilder::new("ws317_index_spellings");
        let u8_id = mb.add_type(Ty::U8);
        let sig = mb.add_func_type(vec![], vec![Ty::U8]);
        let mut fb = mb.function("program", sig);
        fb.set_producer(Producer::Clean);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let seq = fb.const_value(
            Ty::Sequence(u8_id),
            Constant::Sequence(vec![Constant::Int(1), Constant::Int(5)]),
        );
        let idx = match index {
            "usize" => fb.uconst(Ty::Usize, 1),
            "bool" => fb.const_value(Ty::Bool, Constant::Bool(true)),
            "u128" => fb.uconst(Ty::U128, u128::from(u64::MAX) + 5),
            other => panic!("unknown spelling {other}"),
        };
        let el = fb.extract_element(Ty::U8, seq, idx);
        fb.ret(vec![el]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let usize_index = build("usize");
    assert_clean(&usize_index, "a usize index");
    assert_eq!(run_u(&usize_index, "program"), Ok(5));

    assert_one_element_refusal(
        &validate_module(&build("bool")),
        "a bool index",
        "extract_element",
        "index must be integer, got bool",
    );

    let huge = build("u128");
    assert_clean(&huge, "a u128 index past the address space");
    let outcome = run_u(&huge, "program");
    assert!(
        outcome
            .as_ref()
            .is_err_and(|e| e.contains("UndefinedBehavior")),
        "an index that does not fit usize is run-time UB: {outcome:?}"
    );
}

/// The WRITE side of the index rules: a signed index is refused on a sequence
/// write exactly as on a read, and a write past the end is run-time UB.
#[test]
fn review_a_write_index_follows_the_read_rules() {
    assert_one_element_refusal(
        &validate_module(&build_write(Index::I64(1), Ty::U8)),
        "insert_element at an i64 index",
        "insert_element",
        "a sequence index must be an unsigned integer",
    );
    let past_the_end = build_write(Index::U64(3), Ty::U8);
    assert_clean(&past_the_end, "insert_element at sequence index 3 of 3");
    let outcome = sequence_elements(&past_the_end, "program");
    assert!(
        outcome
            .as_ref()
            .is_err_and(|e| e.contains("UndefinedBehavior") && e.contains("out of bounds")),
        "expected run-time UB, got {outcome:?}"
    );
}
