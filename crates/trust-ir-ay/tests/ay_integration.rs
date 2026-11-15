// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// End-to-end ay integration tests: build TrustIr programs with the builder API,
// encode to ay, and verify proof obligations.

#![allow(clippy::disallowed_methods)] // a test drives ay directly; a panic here is a test failure (r11 item 5, crates/trust-ir-ay/clippy.toml)

use ay::Sort;
use trust_ir::inst::*;
use trust_ir::proof::{ProofAnnotation, ProofStatus};
use trust_ir::ty::Ty;
use trust_ir::value::ProofId;
use trust_ir_ay::{
    MemoryModel, ProofOperands, VerificationResult, create_bv_solver, create_fp_solver,
    encode_binop, encode_overflow_check, ty_to_sort, verify_and_certify, verify_proof_obligation,
};
use trust_ir_build::ModuleBuilder;

// ============================================================================
// Test 1: Arithmetic program — verify NoOverflow via ay
// ============================================================================

/// Build an arithmetic program with the builder API, then verify that
/// constant addition (1 + 1) does not overflow via ay.
///
/// This is the core end-to-end test: builder constructs TrustIr,
/// trust-ir-ay verifies a proof obligation against it.
#[test]
fn arithmetic_program_no_overflow_verified_for_constants() {
    // --- Step 1: Build TrustIr program using builder API ---
    let mut mb = ModuleBuilder::new("arith_test");
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("safe_add", ft);

    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::I32);
    let b_param = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);

    // Emit add with NoOverflow proof annotation
    let sum = fb.binop_proven(
        BinOp::Add,
        Ty::I32,
        a,
        b_param,
        vec![ProofAnnotation::NoOverflow],
    );
    fb.ret(vec![sum]);
    fb.build();

    let module = mb.build().expect("ModuleBuilder::build: test fixture");

    // Verify the TrustIr was built correctly
    assert_eq!(module.functions.len(), 1);
    assert_eq!(module.functions[0].name, "safe_add");
    let block = &module.functions[0].blocks[0];
    assert!(block.body[0].has_proof(&ProofAnnotation::NoOverflow));

    // --- Step 2: Verify with ay using constant operands ---
    // Use the types from the TrustIr program
    let operand_ty = Ty::I32;
    let sort = ty_to_sort(&operand_ty).unwrap();

    let mut solver = create_bv_solver().unwrap();
    // Concrete: 1 + 1 cannot overflow
    let lhs = solver.bv_const(1, 32);
    let rhs = solver.bv_const(1, 32);

    let operands = ProofOperands::for_annotation(&ProofAnnotation::NoOverflow, &[lhs, rhs], 32)
        .unwrap()
        .with_overflow_op(OverflowOp::AddOverflow)
        .with_signedness(true);
    let result = verify_and_certify(
        &mut solver,
        &ProofAnnotation::NoOverflow,
        &operands,
        ProofId::new(0),
    )
    .unwrap();

    // Constant 1 + 1 should be verified (no overflow possible)
    assert!(result.is_proved_by_solver());
    assert_eq!(result.status(), ProofStatus::Pending);

    let cert = result.into_certificate();
    assert_eq!(cert.obligation, ProofId::new(0));
    assert_eq!(cert.prover, "ay");

    // Verify the sort matches what we expect from the TrustIr type
    match sort {
        Sort::BitVec(bv) => assert_eq!(bv.width, 32),
        other => panic!("expected BitVec(32) for I32, got {:?}", other),
    }
}

/// Build an arithmetic program and verify that symbolic (unconstrained) addition
/// CANNOT be proven overflow-free — ay should find a counterexample (Refuted).
#[test]
fn arithmetic_program_no_overflow_refuted_for_symbolic() {
    // --- Build TrustIr ---
    let mut mb = ModuleBuilder::new("arith_symbolic");
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("unchecked_add", ft);

    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::I32);
    let b_param = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);

    let sum = fb.add(Ty::I32, a, b_param);
    fb.ret(vec![sum]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");

    // Verify program structure
    assert_eq!(module.functions[0].name, "unchecked_add");

    // --- Verify with ay: bind the program's own SSA operands through the
    // symbol-binding schema (deterministic `f{func}_v{value}` symbols) ---
    let mut solver = create_bv_solver().unwrap();
    let func_id = module.functions[0].id;

    let operands = ProofOperands::from_values(
        &mut solver,
        &ProofAnnotation::NoOverflow,
        func_id,
        &[(a, Ty::I32), (b_param, Ty::I32)],
    )
    .unwrap()
    .with_overflow_op(OverflowOp::AddOverflow)
    .with_signedness(true);
    let result = verify_and_certify(
        &mut solver,
        &ProofAnnotation::NoOverflow,
        &operands,
        ProofId::new(1),
    )
    .unwrap();

    // Symbolic: ay should find values that overflow => Refuted
    assert_eq!(result.status(), ProofStatus::Failed);
    let cert = result.into_certificate();
    assert_eq!(cert.obligation, ProofId::new(1));
}

// ============================================================================
// Test 2: Memory program — verify InBounds via ay
// ============================================================================

/// Build a memory program with the builder API (alloca + store + load),
/// then verify InBounds via ay for a known-safe access.
#[test]
fn memory_program_inbounds_verified() {
    // --- Build TrustIr program ---
    let mut mb = ModuleBuilder::new("mem_test");
    let ft = mb.add_func_type(vec![], vec![Ty::I32]);
    let mut fb = mb.function("safe_mem", ft);

    let entry = fb.create_block();
    fb.switch_to_block(entry);

    // alloca: allocate space for an i32
    let ptr = fb.alloca(Ty::I32);
    // store 42 into the allocation
    let val = fb.iconst(Ty::I32, 42);
    fb.store_proven(
        Ty::I32,
        ptr,
        val,
        vec![ProofAnnotation::InBounds, ProofAnnotation::NotNull],
    );
    // load it back
    let loaded = fb.load_proven(
        Ty::I32,
        ptr,
        vec![ProofAnnotation::InBounds, ProofAnnotation::NotNull],
    );
    fb.ret(vec![loaded]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");

    // Verify proof annotations exist on the instructions
    let block = &module.functions[0].blocks[0];
    // body: alloca, iconst, store, load, ret
    assert!(block.body[2].has_proof(&ProofAnnotation::InBounds)); // store
    assert!(block.body[2].has_proof(&ProofAnnotation::NotNull)); // store
    assert!(block.body[3].has_proof(&ProofAnnotation::InBounds)); // load
    assert!(block.body[3].has_proof(&ProofAnnotation::NotNull)); // load

    // --- Verify InBounds with ay ---
    // Simulate: index=0, length=1 (single-element allocation, accessing element 0)
    let mut solver = create_bv_solver().unwrap();
    let index = solver.bv_const(0, 32);
    let length = solver.bv_const(1, 32);

    let operands =
        ProofOperands::for_annotation(&ProofAnnotation::InBounds, &[index, length], 32).unwrap();
    let result = verify_and_certify(
        &mut solver,
        &ProofAnnotation::InBounds,
        &operands,
        ProofId::new(10),
    )
    .unwrap();

    assert!(result.is_proved_by_solver());
    assert_eq!(result.status(), ProofStatus::Pending);
    let cert = result.into_certificate();
    assert_eq!(cert.obligation, ProofId::new(10));
    assert_eq!(cert.prover, "ay");
}

/// Build a memory program and verify NotNull for an alloca'd pointer.
/// Alloca always returns non-null, so this should be verified.
#[test]
fn memory_program_not_null_verified_for_alloca() {
    // --- Build TrustIr ---
    let mut mb = ModuleBuilder::new("notnull_test");
    let ft = mb.add_func_type(vec![], vec![Ty::I32]);
    let mut fb = mb.function("alloca_load", ft);

    let entry = fb.create_block();
    fb.switch_to_block(entry);

    let ptr = fb.alloca(Ty::I32);
    let val = fb.iconst(Ty::I32, 0);
    fb.store(Ty::I32, ptr, val);
    let loaded = fb.load_proven(Ty::I32, ptr, vec![ProofAnnotation::NotNull]);
    fb.ret(vec![loaded]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");

    assert_eq!(module.functions[0].name, "alloca_load");

    // --- Verify NotNull with ay using MemoryModel ---
    let mut solver = create_fp_solver().unwrap();
    let mut mem = MemoryModel::new(&mut solver, "mem").expect("the adapter encodes");

    // Alloca returns a non-null address
    let addr = mem.encode_alloca(&mut solver, 4).unwrap();

    // Verify NotNull: the alloca'd address should be non-null
    let operands = ProofOperands::for_annotation(&ProofAnnotation::NotNull, &[addr], 64).unwrap();
    let result = verify_and_certify(
        &mut solver,
        &ProofAnnotation::NotNull,
        &operands,
        ProofId::new(20),
    )
    .unwrap();

    assert!(result.is_proved_by_solver());
    assert_eq!(result.status(), ProofStatus::Pending);
}

/// Build a memory program with GEP and verify InBounds for the computed pointer.
#[test]
fn memory_program_gep_inbounds() {
    // --- Build TrustIr ---
    let mut mb = ModuleBuilder::new("gep_test");
    let ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I32]);
    let mut fb = mb.function("array_access", ft);

    let entry = fb.create_block();
    let base = fb.add_block_param(entry, Ty::Ptr);
    fb.switch_to_block(entry);

    let idx = fb.iconst(Ty::I64, 3);
    let elem_ptr = fb.gep_proven(Ty::I32, base, vec![idx], vec![ProofAnnotation::InBounds]);
    let val = fb.load(Ty::I32, elem_ptr);
    fb.ret(vec![val]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");

    // Verify InBounds annotation on GEP
    let block = &module.functions[0].blocks[0];
    // body: iconst, gep, load, ret
    assert!(block.body[1].has_proof(&ProofAnnotation::InBounds));

    // --- Verify with ay: index=3, array_length=10 => in bounds ---
    let mut solver = create_bv_solver().unwrap();
    let index = solver.bv_const(3, 32);
    let length = solver.bv_const(10, 32);

    let operands =
        ProofOperands::for_annotation(&ProofAnnotation::InBounds, &[index, length], 32).unwrap();
    let cond = verify_proof_obligation(&mut solver, &ProofAnnotation::InBounds, &operands).unwrap();

    assert!(cond.check(&mut solver).expect("the condition checks"));
}

// ============================================================================
// Test 3: Deliberate bug — verify ay finds counterexample (Refuted)
// ============================================================================

/// Build a program with a deliberate bug: divide by a value that could be zero.
/// Verify that ay finds a counterexample (Refuted) when the divisor is symbolic.
#[test]
fn deliberate_bug_div_by_zero_refuted() {
    // --- Build TrustIr with a bug: no check before division ---
    let mut mb = ModuleBuilder::new("bug_test");
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("buggy_div", ft);

    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::I32);
    let b_param = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);

    // Bug: divide without checking if b_param is zero
    let result = fb.sdiv(Ty::I32, a, b_param);
    fb.ret(vec![result]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");

    assert_eq!(module.functions[0].name, "buggy_div");

    // --- Verify DivNonZero with ay: the divisor is the program's own
    // `b_param`, bound through the symbol-binding schema ---
    let mut solver = create_bv_solver().unwrap();
    let func_id = module.functions[0].id;

    let operands = ProofOperands::from_values(
        &mut solver,
        &ProofAnnotation::DivNonZero,
        func_id,
        &[(b_param, Ty::I32)],
    )
    .unwrap();
    let result = verify_and_certify(
        &mut solver,
        &ProofAnnotation::DivNonZero,
        &operands,
        ProofId::new(100),
    )
    .unwrap();

    // ay should find that divisor CAN be zero => Refuted
    assert_eq!(result.status(), ProofStatus::Failed);
    let cert = result.into_certificate();
    assert_eq!(cert.obligation, ProofId::new(100));
    assert_eq!(cert.prover, "ay");
}

/// Build a program with a deliberate out-of-bounds access.
/// Verify that ay finds a counterexample when index >= length.
#[test]
fn deliberate_bug_out_of_bounds_refuted() {
    // --- Build TrustIr ---
    let mut mb = ModuleBuilder::new("oob_bug");
    let ft = mb.add_func_type(vec![Ty::Ptr, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("buggy_access", ft);

    let entry = fb.create_block();
    let ptr = fb.add_block_param(entry, Ty::Ptr);
    let _idx = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);

    // Bug: no bounds check, index could be >= array length
    let val = fb.load(Ty::I32, ptr);
    fb.ret(vec![val]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");

    assert_eq!(module.functions[0].name, "buggy_access");

    // --- Verify InBounds with ay: symbolic index, array of length 10 ---
    let mut solver = create_bv_solver().unwrap();
    let sort = ty_to_sort(&Ty::I32).unwrap();
    let index = solver.declare_const("index", sort);
    let length = solver.bv_const(10, 32);

    let operands =
        ProofOperands::for_annotation(&ProofAnnotation::InBounds, &[index, length], 32).unwrap();
    let result = verify_and_certify(
        &mut solver,
        &ProofAnnotation::InBounds,
        &operands,
        ProofId::new(101),
    )
    .unwrap();

    // ay should find an index >= 10 => Refuted
    assert_eq!(result.status(), ProofStatus::Failed);
}

/// Build a program with a deliberate null pointer dereference.
/// Verify ay finds the null counterexample.
#[test]
fn deliberate_bug_null_pointer_refuted() {
    // --- Build TrustIr ---
    let mut mb = ModuleBuilder::new("null_bug");
    let ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I32]);
    let mut fb = mb.function("buggy_deref", ft);

    let entry = fb.create_block();
    let ptr = fb.add_block_param(entry, Ty::Ptr);
    fb.switch_to_block(entry);

    // Bug: no null check, ptr could be null
    let val = fb.load(Ty::I32, ptr);
    fb.ret(vec![val]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");

    assert_eq!(module.functions[0].name, "buggy_deref");

    // --- Verify NotNull with ay: the program's own `ptr` param, bound
    // through the symbol-binding schema ---
    let mut solver = create_bv_solver().unwrap();
    let func_id = module.functions[0].id;

    let operands = ProofOperands::from_values(
        &mut solver,
        &ProofAnnotation::NotNull,
        func_id,
        &[(ptr, Ty::Ptr)],
    )
    .unwrap();
    let result = verify_and_certify(
        &mut solver,
        &ProofAnnotation::NotNull,
        &operands,
        ProofId::new(102),
    )
    .unwrap();

    // ay should find ptr=0 => Refuted
    assert_eq!(result.status(), ProofStatus::Failed);
}

/// Build a shift operation with an out-of-range shift amount.
/// Verify ay finds the bug when shift amount is unconstrained.
#[test]
fn deliberate_bug_shift_out_of_range_refuted() {
    // --- Build TrustIr ---
    let mut mb = ModuleBuilder::new("shift_bug");
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("buggy_shl", ft);

    let entry = fb.create_block();
    let val = fb.add_block_param(entry, Ty::I32);
    let shift = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);

    // Bug: no check that shift < 32
    let result = fb.binop(BinOp::Shl, Ty::I32, val, shift);
    fb.ret(vec![result]);
    fb.build();
    let _module = mb.build().expect("ModuleBuilder::build: test fixture");

    // --- Verify ShiftInRange ---
    let mut solver = create_bv_solver().unwrap();
    let sort = ty_to_sort(&Ty::I32).unwrap();
    let shift_amount = solver.declare_const("shift_amount", sort);
    let bit_width = solver.bv_const(32, 32);

    let operands = ProofOperands::for_annotation(
        &ProofAnnotation::ShiftInRange,
        &[shift_amount, bit_width],
        32,
    )
    .unwrap();
    let result = verify_and_certify(
        &mut solver,
        &ProofAnnotation::ShiftInRange,
        &operands,
        ProofId::new(103),
    )
    .unwrap();

    // ay should find shift_amount >= 32 => Refuted
    assert_eq!(result.status(), ProofStatus::Failed);
}

// ============================================================================
// Test 4: verify_and_certify returns non-authoritative evidence records
// ============================================================================

/// End-to-end: build a safe program, check its proof annotations via ay, and
/// collect structurally well-formed evidence records. Their empty `SmtProof`
/// payloads are deliberately non-authoritative.
#[test]
fn verify_and_certify_returns_non_authoritative_evidence_records() {
    // --- Build a safe TrustIr program with multiple proof annotations ---
    let mut mb = ModuleBuilder::new("cert_test");
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("fully_safe_add", ft);

    fb.add_function_proof(ProofAnnotation::Pure);
    fb.add_function_proof(ProofAnnotation::NoPanic);

    let entry = fb.create_block();
    let _a = fb.add_block_param(entry, Ty::I32);
    let _b = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);

    // Use small constants that obviously cannot overflow
    let c1 = fb.iconst(Ty::I32, 10);
    let c2 = fb.iconst(Ty::I32, 20);
    let sum = fb.binop_proven(
        BinOp::Add,
        Ty::I32,
        c1,
        c2,
        vec![ProofAnnotation::NoOverflow, ProofAnnotation::Commutative],
    );
    fb.ret(vec![sum]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");

    // Verify function-level proofs
    let func = &module.functions[0];
    assert!(func.has_proof(&ProofAnnotation::Pure));
    assert!(func.has_proof(&ProofAnnotation::NoPanic));

    // --- Verify multiple proof obligations via ay ---

    // Certificate 1: NoOverflow for 10 + 20
    let mut solver1 = create_bv_solver().unwrap();
    let lhs1 = solver1.bv_const(10, 32);
    let rhs1 = solver1.bv_const(20, 32);
    let ops1 = ProofOperands::for_annotation(&ProofAnnotation::NoOverflow, &[lhs1, rhs1], 32)
        .unwrap()
        .with_overflow_op(OverflowOp::AddOverflow)
        .with_signedness(true);
    let result1 = verify_and_certify(
        &mut solver1,
        &ProofAnnotation::NoOverflow,
        &ops1,
        ProofId::new(0),
    )
    .unwrap();
    assert!(result1.is_proved_by_solver());
    assert_eq!(result1.status(), ProofStatus::Pending);
    let cert1 = result1.into_certificate();
    assert_eq!(cert1.obligation, ProofId::new(0));
    assert_eq!(cert1.prover, "ay");
    // The empty SmtProof record preserves the solver result but cannot replay.
    assert!(matches!(
        cert1.evidence,
        trust_ir::ProofEvidence::SmtProof(_)
    ));

    // Certificate 2: DivNonZero for constant divisor 20
    let mut solver2 = create_bv_solver().unwrap();
    let divisor = solver2.bv_const(20, 32);
    let ops2 = ProofOperands::for_annotation(&ProofAnnotation::DivNonZero, &[divisor], 32).unwrap();
    let result2 = verify_and_certify(
        &mut solver2,
        &ProofAnnotation::DivNonZero,
        &ops2,
        ProofId::new(1),
    )
    .unwrap();
    assert!(result2.is_proved_by_solver());
    assert_eq!(result2.status(), ProofStatus::Pending);
    let cert2 = result2.into_certificate();
    assert_eq!(cert2.obligation, ProofId::new(1));
    assert_eq!(cert2.prover, "ay");

    // Certificate 3: InBounds for index=0, length=5
    let mut solver3 = create_bv_solver().unwrap();
    let idx = solver3.bv_const(0, 32);
    let len = solver3.bv_const(5, 32);
    let ops3 = ProofOperands::for_annotation(&ProofAnnotation::InBounds, &[idx, len], 32).unwrap();
    let result3 = verify_and_certify(
        &mut solver3,
        &ProofAnnotation::InBounds,
        &ops3,
        ProofId::new(2),
    )
    .unwrap();
    assert!(result3.is_proved_by_solver());
    assert_eq!(result3.status(), ProofStatus::Pending);
    let cert3 = result3.into_certificate();
    assert_eq!(cert3.obligation, ProofId::new(2));
    assert_eq!(cert3.prover, "ay");

    // Certificate 4: NotNull for non-null constant pointer
    let mut solver4 = create_bv_solver().unwrap();
    let ptr = solver4.bv_const(0x1000, 64);
    let ops4 = ProofOperands::for_annotation(&ProofAnnotation::NotNull, &[ptr], 64).unwrap();
    let result4 = verify_and_certify(
        &mut solver4,
        &ProofAnnotation::NotNull,
        &ops4,
        ProofId::new(3),
    )
    .unwrap();
    assert!(result4.is_proved_by_solver());
    assert_eq!(result4.status(), ProofStatus::Pending);
    let cert4 = result4.into_certificate();
    assert_eq!(cert4.obligation, ProofId::new(3));
    assert_eq!(cert4.prover, "ay");

    // All four solver-proved conditions produced evidence records.
    let certs = [cert1, cert2, cert3, cert4];
    for (i, cert) in certs.iter().enumerate() {
        assert_eq!(cert.obligation.index(), i as u32);
        assert_eq!(cert.prover, "ay");
    }
}

/// Verify that VerificationResult variants carry correct status and certificates.
#[test]
fn verification_result_variants_are_correct() {
    // Verified by the solver, but Pending until proof replay is available.
    let mut solver_v = create_bv_solver().unwrap();
    let five = solver_v.bv_const(5, 32);
    let ops_v = ProofOperands::for_annotation(&ProofAnnotation::DivNonZero, &[five], 32).unwrap();
    let result_v = verify_and_certify(
        &mut solver_v,
        &ProofAnnotation::DivNonZero,
        &ops_v,
        ProofId::new(0),
    )
    .unwrap();
    assert!(matches!(result_v, VerificationResult::Verified(_)));
    assert!(result_v.is_proved_by_solver());
    assert_eq!(result_v.status(), ProofStatus::Pending);

    // Refuted (Failed)
    let mut solver_r = create_bv_solver().unwrap();
    let sort = ty_to_sort(&Ty::I32).unwrap();
    let sym = solver_r.declare_const("d", sort);
    let ops_r = ProofOperands::for_annotation(&ProofAnnotation::DivNonZero, &[sym], 32).unwrap();
    let result_r = verify_and_certify(
        &mut solver_r,
        &ProofAnnotation::DivNonZero,
        &ops_r,
        ProofId::new(1),
    )
    .unwrap();
    assert!(matches!(result_r, VerificationResult::Refuted { .. }));
    assert_eq!(result_r.status(), ProofStatus::Failed);
}

// ============================================================================
// Additional integration tests: ay encoding with builder-constructed types
// ============================================================================

/// Build a program using multiple TrustIr types, convert each to ay sort,
/// and verify the sort widths match.
#[test]
fn builder_types_map_to_ay_sorts() {
    let mut mb = ModuleBuilder::new("types_test");
    let ft = mb.add_func_type(
        vec![
            Ty::I8,
            Ty::I16,
            Ty::I32,
            Ty::I64,
            Ty::I128,
            Ty::Ptr,
            Ty::Bool,
        ],
        vec![Ty::I32],
    );
    let mut fb = mb.function("type_zoo", ft);

    let entry = fb.create_block();
    let _v0 = fb.add_block_param(entry, Ty::I8);
    let _v1 = fb.add_block_param(entry, Ty::I16);
    let _v2 = fb.add_block_param(entry, Ty::I32);
    let _v3 = fb.add_block_param(entry, Ty::I64);
    let _v4 = fb.add_block_param(entry, Ty::I128);
    let _v5 = fb.add_block_param(entry, Ty::Ptr);
    let _v6 = fb.add_block_param(entry, Ty::Bool);
    fb.switch_to_block(entry);
    let ret_val = fb.iconst(Ty::I32, 0);
    fb.ret(vec![ret_val]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");

    // Verify each parameter type maps to expected ay sort
    let block = &module.functions[0].blocks[0];
    let expected_widths = [
        (Ty::I8, 8),
        (Ty::I16, 16),
        (Ty::I32, 32),
        (Ty::I64, 64),
        (Ty::I128, 128),
        (Ty::Ptr, 64),
        (Ty::Bool, 1),
    ];
    assert_eq!(block.params.len(), 7);
    for (i, (ty, expected_width)) in expected_widths.iter().enumerate() {
        assert_eq!(block.params[i].1, *ty);
        let sort = ty_to_sort(ty).unwrap();
        match sort {
            Sort::BitVec(bv) => {
                assert_eq!(bv.width, *expected_width, "width mismatch for {:?}", ty)
            }
            other => panic!("expected BitVec for {:?}, got {:?}", ty, other),
        }
    }
}

/// Build an overflow-checking program and verify the ay overflow encoding
/// produces consistent results when paired with the BinOp encoding.
#[test]
fn overflow_check_combined_with_binop_encoding() {
    // --- Build TrustIr: checked_add ---
    let mut mb = ModuleBuilder::new("checked_arith");
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32, Ty::Bool]);
    let mut fb = mb.function("checked_add", ft);

    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::I32);
    let b_param = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);

    let (result, overflow_flag) = fb.overflow(OverflowOp::AddOverflow, Ty::I32, a, b_param);
    fb.ret(vec![result, overflow_flag]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");

    // Verify the overflow instruction was emitted
    let block = &module.functions[0].blocks[0];
    assert!(matches!(
        &block.body[0].inst,
        Inst::Overflow {
            op: OverflowOp::AddOverflow,
            ..
        }
    ));

    // --- Verify with ay: encode the BinOp and overflow check independently ---
    let mut solver = create_bv_solver().unwrap();
    let sort = ty_to_sort(&Ty::I32).unwrap();
    let lhs = solver.declare_const("a", sort.clone());
    let rhs = solver.declare_const("b", sort);

    // Encode the addition (verify construction works)
    let _sum = encode_binop(&mut solver, BinOp::Add, lhs, rhs).unwrap();

    // Encode the overflow check (verify construction works)
    let _safe = encode_overflow_check(&mut solver, OverflowOp::AddOverflow, true, lhs, rhs)
        .expect("the adapter encodes");

    // Verify with concrete constrained values where no overflow occurs.
    let mut solver2 = create_bv_solver().unwrap();
    let a2 = solver2.bv_const(100, 32);
    let b2 = solver2.bv_const(200, 32);
    let safe2 = encode_overflow_check(&mut solver2, OverflowOp::AddOverflow, true, a2, b2)
        .expect("the adapter encodes");
    solver2.assert_term(safe2);
    assert!(solver2.check_sat().is_sat()); // 100 + 200 is safe

    let sum2 = encode_binop(&mut solver2, BinOp::Add, a2, b2).unwrap();
    let expected = solver2.bv_const(300, 32);
    let eq = solver2.eq(sum2, expected);
    solver2.assert_term(eq);
    assert!(solver2.check_sat().is_sat()); // and the result is 300
}

/// Build a program using the memory model (alloca + store + load roundtrip)
/// and verify the loaded value matches the stored value via ay.
#[test]
fn memory_model_store_load_roundtrip() {
    // --- Build TrustIr ---
    let mut mb = ModuleBuilder::new("mem_roundtrip");
    let ft = mb.add_func_type(vec![], vec![Ty::I32]);
    let mut fb = mb.function("store_load", ft);

    let entry = fb.create_block();
    fb.switch_to_block(entry);

    let ptr = fb.alloca(Ty::I32);
    let val = fb.iconst(Ty::I32, 0x42);
    fb.store(Ty::I32, ptr, val);
    let loaded = fb.load(Ty::I32, ptr);
    fb.ret(vec![loaded]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");

    assert_eq!(module.functions[0].name, "store_load");

    // --- Verify with ay MemoryModel ---
    let mut solver = create_fp_solver().unwrap();
    let mut mem = MemoryModel::new(&mut solver, "mem").expect("the adapter encodes");

    // Alloca: get a non-null address
    let addr = mem.encode_alloca(&mut solver, 4).unwrap();

    // Store 0x42 as 4 bytes (little-endian)
    let val = solver.bv_const(0x42, 32);
    mem.encode_store(&mut solver, addr, val, 4).unwrap();

    // Load 4 bytes from same address
    let loaded = mem.encode_load(&mut solver, addr, 4).unwrap();

    // Assert loaded == original value
    let eq = solver.eq(loaded, val);
    solver.assert_term(eq);
    assert!(
        solver.check_sat().is_sat(),
        "store/load roundtrip should be SAT"
    );
}

/// Build the current AY pipeline: TrustIr program with proof claims, AY solver
/// checks, and non-authoritative evidence-record collection into the module.
#[test]
fn full_pipeline_build_verify_certify() {
    // --- Step 1: Build TrustIr ---
    let mut mb = ModuleBuilder::new("full_pipeline");
    let ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I32]);
    let mut fb = mb.function("safe_deref", ft);

    fb.add_function_proof(ProofAnnotation::Pure);

    let entry = fb.create_block();
    let ptr = fb.add_block_param(entry, Ty::Ptr);
    fb.switch_to_block(entry);

    let val = fb.load_proven(
        Ty::I32,
        ptr,
        vec![ProofAnnotation::NotNull, ProofAnnotation::InBounds],
    );
    fb.ret(vec![val]);
    fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");

    // --- Step 2: Check proof conditions with AY ---
    // NotNull: the pointer is a known non-null address (0x1000)
    let mut solver_nn = create_bv_solver().unwrap();
    let ptr_val = solver_nn.bv_const(0x1000, 64);
    let ops_nn = ProofOperands::for_annotation(&ProofAnnotation::NotNull, &[ptr_val], 64).unwrap();
    let result_nn = verify_and_certify(
        &mut solver_nn,
        &ProofAnnotation::NotNull,
        &ops_nn,
        ProofId::new(0),
    )
    .unwrap();
    assert!(result_nn.is_proved_by_solver());
    assert_eq!(result_nn.status(), ProofStatus::Pending);

    // InBounds: index=0, length=1
    let mut solver_ib = create_bv_solver().unwrap();
    let idx = solver_ib.bv_const(0, 32);
    let len = solver_ib.bv_const(1, 32);
    let ops_ib =
        ProofOperands::for_annotation(&ProofAnnotation::InBounds, &[idx, len], 32).unwrap();
    let result_ib = verify_and_certify(
        &mut solver_ib,
        &ProofAnnotation::InBounds,
        &ops_ib,
        ProofId::new(1),
    )
    .unwrap();
    assert!(result_ib.is_proved_by_solver());
    assert_eq!(result_ib.status(), ProofStatus::Pending);

    // --- Step 3: Collect certificates into Module ---
    module.proof_certificates.push(result_nn.into_certificate());
    module.proof_certificates.push(result_ib.into_certificate());

    // --- Step 4: Verify the module carries the evidence records ---
    assert_eq!(module.proof_certificates.len(), 2);
    assert_eq!(module.proof_certificates[0].obligation, ProofId::new(0));
    assert_eq!(module.proof_certificates[0].prover, "ay");
    assert_eq!(module.proof_certificates[1].obligation, ProofId::new(1));
    assert_eq!(module.proof_certificates[1].prover, "ay");

    // The function has the annotations
    let func = &module.functions[0];
    assert!(func.has_proof(&ProofAnnotation::Pure));
    let load_node = &func.blocks[0].body[0];
    assert!(load_node.has_proof(&ProofAnnotation::NotNull));
    assert!(load_node.has_proof(&ProofAnnotation::InBounds));
}

/// Verify that float types from builder programs map to correct ay FP sorts.
#[test]
fn float_types_map_to_ay_fp_sorts() {
    let mut mb = ModuleBuilder::new("fp_test");
    let ft = mb.add_func_type(vec![Ty::F32, Ty::F64], vec![Ty::F64]);
    let mut fb = mb.function("fp_ops", ft);

    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::F32);
    let b_param = fb.add_block_param(entry, Ty::F64);
    fb.switch_to_block(entry);

    let wide = fb.cast(CastOp::FPExt, Ty::F32, Ty::F64, a);
    let sum = fb.fadd(Ty::F64, wide, b_param);
    fb.ret(vec![sum]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");

    assert_eq!(module.functions[0].name, "fp_ops");

    // Verify F32 maps to FloatingPoint(8, 24)
    let f32_sort = ty_to_sort(&Ty::F32).unwrap();
    assert_eq!(f32_sort, Sort::FloatingPoint(8, 24));

    // Verify F64 maps to FloatingPoint(11, 53)
    let f64_sort = ty_to_sort(&Ty::F64).unwrap();
    assert_eq!(f64_sort, Sort::FloatingPoint(11, 53));

    // Verify we can create FP terms and do operations
    let mut solver = create_fp_solver().unwrap();
    let _fa = solver.declare_const("a", f32_sort);
    let fb_val = solver.declare_const("b", f64_sort);
    // Just verify construction doesn't panic
    let _fadd_result = encode_binop(&mut solver, BinOp::FAdd, fb_val, fb_val).unwrap();
}

/// Build a program with constrained addition (both operands in [0, 100]) and
/// confirm that AY supplies strict proof authority for the overflow theorem.
#[test]
fn constrained_addition_has_a_strict_bv_proof() {
    // --- Build TrustIr ---
    let mut mb = ModuleBuilder::new("constrained");
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("bounded_add", ft);

    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::I32);
    let b_param = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);

    let sum = fb.binop_proven(
        BinOp::Add,
        Ty::I32,
        a,
        b_param,
        vec![ProofAnnotation::NoOverflow],
    );
    fb.ret(vec![sum]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");

    assert!(module.functions[0].blocks[0].body[0].has_proof(&ProofAnnotation::NoOverflow));

    // --- Verify with ay: constrain a, b in [0, 100] ---
    let mut solver = create_bv_solver().unwrap();
    let sort = ty_to_sort(&Ty::I32).unwrap();
    let a_sym = solver.declare_const("a", sort.clone());
    let b_sym = solver.declare_const("b", sort);

    // Constrain: 0 <= a <= 100 and 0 <= b <= 100
    let zero = solver.bv_const(0, 32);
    let hundred = solver.bv_const(100, 32);

    let a_ge_0 = solver.bvuge(a_sym, zero);
    solver.assert_term(a_ge_0);
    let a_le_100 = solver.bvule(a_sym, hundred);
    solver.assert_term(a_le_100);
    let b_ge_0 = solver.bvuge(b_sym, zero);
    solver.assert_term(b_ge_0);
    let b_le_100 = solver.bvule(b_sym, hundred);
    solver.assert_term(b_le_100);

    // Now check: can overflow occur?
    let safe = encode_overflow_check(&mut solver, OverflowOp::AddOverflow, true, a_sym, b_sym)
        .expect("the adapter encodes");
    let not_safe = solver.not(safe);
    solver.assert_term(not_safe);

    // The upgraded AY proof boundary strictly checks this mixed BV derivation
    // and publishes the one-shot UNSAT witness. Keep this as a coverage
    // ratchet: Unknown would mean certified capability regressed.
    let result = solver.check_sat();
    assert!(result.is_unsat(), "strictly proved theorem became {result}");
    assert!(result.has_unsat_emission_witness());
}
