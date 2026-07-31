// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Integration tests: build programs using ModuleBuilder, validate, display,
// and verify the output matches expected .trust_ir text format.

use trust_ir::dialect::vector;
use trust_ir::inst::*;
use trust_ir::proof::ProofAnnotation;
use trust_ir::ty::{FieldDef, StructDef, Ty};
use trust_ir::value::{BlockId, FuncId};
use trust_ir::{Constant, Global};
use trust_ir_build::demo::VectorDemoExt;
use trust_ir_build::{ModuleBuilder, validate_function, validate_module};

/// Build a complete add program, display it, and verify output.
#[test]
fn build_display_add_program() {
    let mut mb = ModuleBuilder::new("add_program");
    let ft = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);

    let mut fb = mb.function("add", ft);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::I64);
    let b = fb.add_block_param(entry, Ty::I64);
    fb.switch_to_block(entry);
    let sum = fb.add(Ty::I64, a, b);
    fb.ret(vec![sum]);
    fb.build();

    let module = mb.build();
    let output = format!("{}", module);

    // Verify header
    assert!(output.contains("; TrustIr text format v1"));
    assert!(output.contains("module \"add_program\""));

    // Verify function
    assert!(output.contains("fn @add(functy.0)"));
    assert!(output.contains("bb0(%0: i64, %1: i64):"));
    assert!(output.contains("add i64 %0, %1"));
    assert!(output.contains("ret %2"));
}

/// Build a program with multiple functions and verify all appear in output.
#[test]
fn build_display_multiple_functions() {
    let mut mb = ModuleBuilder::new("multi");

    // fn identity(i32) -> i32
    let ft1 = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    {
        let mut fb = mb.function("identity", ft1);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        fb.ret(vec![x]);
        fb.build();
    }

    // fn noop()
    let ft2 = mb.add_func_type(vec![], vec![]);
    {
        let mut fb = mb.function("noop", ft2);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.ret(vec![]);
        fb.build();
    }

    // fn constant() -> i64
    let ft3 = mb.add_func_type(vec![], vec![Ty::I64]);
    {
        let mut fb = mb.function("constant", ft3);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let val = fb.iconst(Ty::I64, 42);
        fb.ret(vec![val]);
        fb.build();
    }

    let module = mb.build();
    let output = format!("{}", module);

    assert!(output.contains("fn @identity"));
    assert!(output.contains("fn @noop"));
    assert!(output.contains("fn @constant"));
    assert!(output.contains("const i64 42"));
}

/// Build, validate, then display a program.
#[test]
fn build_validate_display_pipeline() {
    let mut mb = ModuleBuilder::new("validated");
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);

    let mut fb = mb.function("double", ft);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);
    let result = fb.add(Ty::I32, x, x);
    fb.ret(vec![result]);
    fb.build();

    let module = mb.build();

    // Validate each function
    for func in &module.functions {
        let errors = validate_function(func);
        assert!(
            errors.is_empty(),
            "validation errors in {}: {:?}",
            func.name,
            errors
        );
    }

    // Display
    let output = format!("{}", module);
    assert!(output.contains("fn @double"));
    assert!(output.contains("add i32 %0, %0"));
}

/// Build a program with structs and verify struct display.
#[test]
fn build_with_structs() {
    let mut mb = ModuleBuilder::new("struct_test");

    let sid = mb.add_struct(StructDef {
        id: trust_ir::StructId::new(0),
        name: "Pair".to_string(),
        fields: vec![
            FieldDef {
                name: "first".to_string(),
                ty: Ty::I32,
                offset: Some(0),
            },
            FieldDef {
                name: "second".to_string(),
                ty: Ty::I64,
                offset: Some(8),
            },
        ],
        size: Some(16),
        align: Some(8),

        repr: Default::default(),
    });

    let ft = mb.add_func_type(vec![Ty::Struct(sid)], vec![Ty::I32]);
    let mut fb = mb.function("get_first", ft);
    let entry = fb.create_block();
    let pair = fb.add_block_param(entry, Ty::Struct(sid));
    fb.switch_to_block(entry);
    let first = fb.extract_field(Ty::I32, pair, 0);
    fb.ret(vec![first]);
    fb.build();

    let module = mb.build();
    let output = format!("{}", module);

    assert!(output.contains("struct @Pair"));
    assert!(output.contains("i32, i64"));
    assert!(output.contains("size=16"));
    assert!(output.contains("align=8"));
    assert!(output.contains("extractfield i32 %0, 0"));
}

/// Build a program with globals.
#[test]
fn build_with_globals() {
    let mut mb = ModuleBuilder::new("global_test");
    mb.add_global(Global {
        name: "counter".to_string(),
        ty: Ty::I64,
        mutable: true,
        initializer: Some(trust_ir::Constant::Int(0)),
        linkage: trust_ir::Linkage::External,
        tls: None,
        align: None,
    });
    mb.add_global(Global {
        name: "PI".to_string(),
        ty: Ty::F64,
        mutable: false,
        initializer: Some(trust_ir::Constant::Float(1.25)),
        linkage: trust_ir::Linkage::External,
        tls: None,
        align: None,
    });

    let module = mb.build();
    assert_eq!(module.globals.len(), 2);
    assert_eq!(module.globals[0].name, "counter");
    assert!(module.globals[0].mutable);
    assert_eq!(module.globals[1].name, "PI");
    assert!(!module.globals[1].mutable);
}

/// Build a complex control-flow program (if-else with merge).
#[test]
fn build_complex_control_flow() {
    let mut mb = ModuleBuilder::new("cfg_test");
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("abs", ft);

    let entry = fb.create_block();
    let then_bb = fb.create_block();
    let else_bb = fb.create_block();
    let merge_bb = fb.create_block();

    let x = fb.add_block_param(entry, Ty::I32);
    let result = fb.add_block_param(merge_bb, Ty::I32);

    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::I32, 0);
    let is_neg = fb.icmp(ICmpOp::Slt, Ty::I32, x, zero);
    fb.condbr(is_neg, then_bb, vec![], else_bb, vec![]);

    fb.switch_to_block(then_bb);
    let neg_x = fb.unop(UnOp::Neg, Ty::I32, x);
    fb.br(merge_bb, vec![neg_x]);

    fb.switch_to_block(else_bb);
    fb.br(merge_bb, vec![x]);

    fb.switch_to_block(merge_bb);
    fb.ret(vec![result]);

    fb.build();

    let module = mb.build();

    // Validate
    for func in &module.functions {
        let errors = validate_function(func);
        assert!(errors.is_empty(), "errors: {:?}", errors);
    }

    let output = format!("{}", module);
    assert!(output.contains("fn @abs"));
    assert!(output.contains("icmp slt"));
    assert!(output.contains("condbr"));
    assert!(output.contains("neg i32"));
}

/// Build a program with proof annotations and verify they appear in display output.
#[test]
fn build_proof_annotated_program() {
    let mut mb = ModuleBuilder::new("proof_test");
    let ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I32]);
    let mut fb = mb.function("safe_deref", ft);

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

    let module = mb.build();

    for func in &module.functions {
        let errors = validate_function(func);
        assert!(errors.is_empty());
    }

    let output = format!("{}", module);
    assert!(output.contains("#proof:"));
    assert!(output.contains("not_null"));
    assert!(output.contains("in_bounds"));
}

/// Build a program with atomics and verify display output.
#[test]
fn build_atomic_program() {
    let mut mb = ModuleBuilder::new("atomic_test");
    let ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I64]);
    let mut fb = mb.function("atomic_read_write", ft);

    let entry = fb.create_block();
    let ptr = fb.add_block_param(entry, Ty::Ptr);
    fb.switch_to_block(entry);

    let old_val = fb.atomic_load(Ty::I64, ptr, Ordering::SeqCst);
    let one = fb.iconst(Ty::I64, 1);
    let new_val = fb.add(Ty::I64, old_val, one);
    fb.atomic_store(Ty::I64, ptr, new_val, Ordering::SeqCst);
    fb.fence(Ordering::SeqCst);
    fb.ret(vec![old_val]);
    fb.build();

    let module = mb.build();

    for func in &module.functions {
        let errors = validate_function(func);
        assert!(errors.is_empty());
    }

    let output = format!("{}", module);
    assert!(output.contains("atomic_load seq_cst i64"));
    assert!(output.contains("atomic_store seq_cst i64"));
    assert!(output.contains("fence seq_cst"));
}

/// Build a program with overflow checking and verify display output.
#[test]
fn build_overflow_checked_program() {
    let mut mb = ModuleBuilder::new("overflow_test");
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("safe_add", ft);

    let entry = fb.create_block();
    let ok_bb = fb.create_block();
    let overflow_bb = fb.create_block();

    let a = fb.add_block_param(entry, Ty::I32);
    let b = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);

    let (result, did_overflow) = fb.overflow(OverflowOp::AddOverflow, Ty::I32, a, b);
    fb.condbr(did_overflow, overflow_bb, vec![], ok_bb, vec![]);

    fb.switch_to_block(ok_bb);
    fb.ret(vec![result]);

    fb.switch_to_block(overflow_bb);
    fb.unreachable();

    fb.build();

    let module = mb.build();

    for func in &module.functions {
        let errors = validate_function(func);
        assert!(errors.is_empty(), "errors: {:?}", errors);
    }

    let output = format!("{}", module);
    assert!(output.contains("add.overflow i32"));
    assert!(output.contains("%2, %3 ="));
    assert!(output.contains("unreachable"));
}

/// Validation catches invalid functions built manually.
#[test]
fn validation_catches_errors() {
    // Build an empty function (no blocks)
    let mut func = trust_ir::Function::new(
        FuncId::new(0),
        "empty",
        trust_ir::value::FuncTyId::new(0),
        BlockId::new(0),
    );
    func.linkage = trust_ir::Linkage::Internal;
    let errors = validate_function(&func);
    assert!(!errors.is_empty());
    assert!(
        errors
            .iter()
            .any(|e| matches!(e, trust_ir_build::validate::ValidationError::EmptyFunction))
    );
}

/// Module Display includes function types correctly.
#[test]
fn display_shows_func_type_reference() {
    let mut mb = ModuleBuilder::new("functy_test");
    let _ft0 = mb.add_func_type(vec![Ty::I32], vec![Ty::I64]);
    let ft1 = mb.add_func_type(vec![Ty::F64, Ty::F64], vec![Ty::F64]);

    let mut fb = mb.function("use_ft1", ft1);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::F64);
    let b = fb.add_block_param(entry, Ty::F64);
    fb.switch_to_block(entry);
    let sum = fb.fadd(Ty::F64, a, b);
    fb.ret(vec![sum]);
    fb.build();

    let module = mb.build();
    let output = format!("{}", module);
    // Function should reference functy.1 (the second func type)
    assert!(output.contains("fn @use_ft1(functy.1)"));
}

// --- NEW INTEGRATION TESTS ---

/// Build a loop: while(true) { x = x + 1 } — branch back to same block.
#[test]
fn build_infinite_loop() {
    let mut mb = ModuleBuilder::new("loop_test");
    let ft = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("infinite_loop", ft);

    let entry = fb.create_block();
    let loop_bb = fb.create_block();

    fb.switch_to_block(entry);
    let init = fb.iconst(Ty::I64, 0);
    fb.br(loop_bb, vec![init]);

    let x = fb.add_block_param(loop_bb, Ty::I64);
    fb.switch_to_block(loop_bb);
    let one = fb.iconst(Ty::I64, 1);
    let next = fb.add(Ty::I64, x, one);
    fb.br(loop_bb, vec![next]); // branch back to self

    fb.build();

    let module = mb.build();
    for func in &module.functions {
        let errors = validate_function(func);
        assert!(errors.is_empty(), "errors: {:?}", errors);
    }

    let output = format!("{}", module);
    assert!(output.contains("fn @infinite_loop"));
    // bb1 should branch to bb1
    assert!(output.contains("br bb1("));
}

/// Build a counted loop: for i in 0..10 { ... }
#[test]
fn build_counted_loop() {
    let mut mb = ModuleBuilder::new("counted_loop");
    let ft = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("sum_to_10", ft);

    let entry = fb.create_block();
    let loop_bb = fb.create_block();
    let exit_bb = fb.create_block();

    // entry: br loop(0, 0)
    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::I64, 0);
    fb.br(loop_bb, vec![zero, zero]);

    // loop(i, acc): if i < 10 then loop(i+1, acc+i) else exit(acc)
    let i = fb.add_block_param(loop_bb, Ty::I64);
    let acc = fb.add_block_param(loop_bb, Ty::I64);
    fb.switch_to_block(loop_bb);
    let limit = fb.iconst(Ty::I64, 10);
    let cond = fb.icmp(ICmpOp::Slt, Ty::I64, i, limit);
    let one = fb.iconst(Ty::I64, 1);
    let next_i = fb.add(Ty::I64, i, one);
    let next_acc = fb.add(Ty::I64, acc, i);
    fb.condbr(cond, loop_bb, vec![next_i, next_acc], exit_bb, vec![acc]);

    // exit(result): return result
    let result = fb.add_block_param(exit_bb, Ty::I64);
    fb.switch_to_block(exit_bb);
    fb.ret(vec![result]);

    fb.build();

    let module = mb.build();
    for func in &module.functions {
        let errors = validate_function(func);
        assert!(errors.is_empty(), "errors: {:?}", errors);
    }

    let output = format!("{}", module);
    assert!(output.contains("fn @sum_to_10"));
    assert!(output.contains("icmp slt i64"));
    // condbr should branch back to loop_bb and to exit_bb
    assert!(output.contains("condbr"));
    assert!(output.contains("bb1(")); // branch back with args
    assert!(output.contains("bb2(")); // branch to exit with args
}

/// Build a switch-based dispatch program.
#[test]
fn build_switch_dispatch() {
    let mut mb = ModuleBuilder::new("switch_test");
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("dispatch", ft);

    let entry = fb.create_block();
    let case_0 = fb.create_block();
    let check_1 = fb.create_block();
    let case_1 = fb.create_block();
    let default_bb = fb.create_block();

    let x = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);

    // Simulate a 3-way switch with condbr chain:
    // entry: if x == 0 -> case_0, else -> check_1
    let zero = fb.iconst(Ty::I32, 0);
    let is_zero = fb.icmp(ICmpOp::Eq, Ty::I32, x, zero);
    fb.condbr(is_zero, case_0, vec![], check_1, vec![]);

    // check_1: if x == 1 -> case_1, else -> default_bb
    fb.switch_to_block(check_1);
    let one = fb.iconst(Ty::I32, 1);
    let is_one = fb.icmp(ICmpOp::Eq, Ty::I32, x, one);
    fb.condbr(is_one, case_1, vec![], default_bb, vec![]);

    fb.switch_to_block(case_0);
    let r0 = fb.iconst(Ty::I32, 100);
    fb.ret(vec![r0]);

    fb.switch_to_block(case_1);
    let r1 = fb.iconst(Ty::I32, 200);
    fb.ret(vec![r1]);

    fb.switch_to_block(default_bb);
    let rd = fb.iconst(Ty::I32, -1);
    fb.ret(vec![rd]);

    fb.build();

    let module = mb.build();
    for func in &module.functions {
        let errors = validate_function(func);
        assert!(errors.is_empty(), "errors: {:?}", errors);
    }

    let output = format!("{}", module);
    assert!(output.contains("fn @dispatch"));
    assert!(output.contains("icmp eq i32"));
    assert!(output.contains("const i32 100"));
    assert!(output.contains("const i32 200"));
}

/// Build a program with multiple cast types and verify display.
#[test]
fn build_program_with_multiple_casts() {
    let mut mb = ModuleBuilder::new("cast_test");
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::F64]);
    let mut fb = mb.function("cast_chain", ft);

    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);

    // i32 -> i64 via sext
    let wide = fb.sext(Ty::I32, Ty::I64, x);
    // i64 -> i32 via trunc
    let narrow = fb.trunc(Ty::I64, Ty::I32, wide);
    // i32 -> i64 via zext
    let unsigned_wide = fb.zext(Ty::I32, Ty::I64, narrow);
    // i64 -> f64 via generic cast (SIToFP)
    let float_val = fb.cast(CastOp::SIToFP, Ty::I64, Ty::F64, unsigned_wide);

    fb.ret(vec![float_val]);
    fb.build();

    let module = mb.build();
    for func in &module.functions {
        let errors = validate_function(func);
        assert!(errors.is_empty(), "errors: {:?}", errors);
    }

    let output = format!("{}", module);
    assert!(output.contains("sext i32 %0 to i64"));
    assert!(output.contains("trunc i64 %1 to i32"));
    assert!(output.contains("zext i32 %2 to i64"));
    assert!(output.contains("sitofp i64 %3 to f64"));
}

/// Build a program with struct + proof annotations and verify combined display.
#[test]
fn build_struct_with_proof_annotations() {
    let mut mb = ModuleBuilder::new("struct_proof_test");

    let sid = mb.add_struct(StructDef {
        id: trust_ir::StructId::new(0),
        name: "SafeBox".to_string(),
        fields: vec![
            FieldDef {
                name: "ptr".to_string(),
                ty: Ty::Ptr,
                offset: Some(0),
            },
            FieldDef {
                name: "len".to_string(),
                ty: Ty::I64,
                offset: Some(8),
            },
        ],
        size: Some(16),
        align: Some(8),

        repr: Default::default(),
    });

    let ft = mb.add_func_type(vec![Ty::Struct(sid)], vec![Ty::I32]);
    let mut fb = mb.function("safe_read", ft);

    let entry = fb.create_block();
    let sbox = fb.add_block_param(entry, Ty::Struct(sid));
    fb.switch_to_block(entry);

    // Extract the pointer field
    let ptr = fb.extract_field(Ty::Ptr, sbox, 0);
    // Load with proof annotations
    let val = fb.load_proven(
        Ty::I32,
        ptr,
        vec![
            ProofAnnotation::NotNull,
            ProofAnnotation::InBounds,
            ProofAnnotation::ValidBorrow,
        ],
    );
    fb.ret(vec![val]);
    fb.build();

    let module = mb.build();
    for func in &module.functions {
        let errors = validate_function(func);
        assert!(errors.is_empty(), "errors: {:?}", errors);
    }

    let output = format!("{}", module);
    assert!(output.contains("struct @SafeBox"));
    assert!(output.contains("extractfield ptr %0, 0"));
    assert!(output.contains("#proof: not_null, in_bounds, valid_borrow"));
}

/// Build a program using all builder constant methods.
#[test]
fn build_all_constant_types() {
    let mut mb = ModuleBuilder::new("const_test");
    let ft = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("constants", ft);

    let entry = fb.create_block();
    fb.switch_to_block(entry);

    let _i = fb.iconst(Ty::I64, 42);
    let _f = fb.fconst(Ty::F64, 1.25);
    let _b = fb.bool_const(true);
    let _n = fb.null_ptr();
    fb.ret(vec![]);
    fb.build();

    let module = mb.build();
    let output = format!("{}", module);

    assert!(output.contains("const i64 42"));
    assert!(output.contains("const f64 1.25"));
    assert!(output.contains("const bool true"));
    assert!(output.contains("null ptr"));
}

/// Builder: copy and select produce correct instructions.
#[test]
fn build_copy_and_select() {
    let mut mb = ModuleBuilder::new("pseudo_test");
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("choose", ft);

    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::I32);
    let b = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);

    let copied = fb.copy(Ty::I32, a);
    let cond = fb.bool_const(true);
    let selected = fb.select(Ty::I32, cond, copied, b);
    fb.ret(vec![selected]);
    fb.build();

    let module = mb.build();
    for func in &module.functions {
        let errors = validate_function(func);
        assert!(errors.is_empty(), "errors: {:?}", errors);
    }

    let output = format!("{}", module);
    assert!(output.contains("copy i32 %0"));
    assert!(output.contains("select i32"));
}

/// Builder/validator: fixed-width vectors use existing typed ops.
#[test]
fn build_fixed_width_integer_vector_ir() {
    let mut mb = ModuleBuilder::new("vector_batch");
    let v4i32 = Ty::Vector(Box::new(Ty::I32), 4);
    let v4bool = Ty::Vector(Box::new(Ty::Bool), 4);
    let ft = mb.add_func_type(
        vec![Ty::Ptr, v4i32.clone(), v4i32.clone()],
        vec![v4i32.clone(), v4bool.clone()],
    );
    let mut fb = mb.function("batch", ft);

    let entry = fb.create_block();
    let ptr = fb.add_block_param(entry, Ty::Ptr);
    let a = fb.add_block_param(entry, v4i32.clone());
    let b = fb.add_block_param(entry, v4i32.clone());
    fb.switch_to_block(entry);

    let loaded = fb.load_aligned(v4i32.clone(), ptr, 16);
    let add = fb.add(v4i32.clone(), a, b);
    let sub = fb.sub(v4i32.clone(), add, loaded);
    let mul = fb.mul(v4i32.clone(), sub, b);
    let and = fb.binop(BinOp::And, v4i32.clone(), mul, a);
    let or = fb.binop(BinOp::Or, v4i32.clone(), and, b);
    let xor = fb.binop(BinOp::Xor, v4i32.clone(), or, loaded);
    let mask = fb.icmp(ICmpOp::Eq, v4i32.clone(), xor, loaded);
    let selected = fb.select(v4i32.clone(), mask, xor, loaded);
    fb.store_aligned(v4i32.clone(), ptr, selected, 16);
    fb.ret(vec![selected, mask]);
    fb.build();

    let module = mb.build();
    let errors = validate_module(&module);
    assert!(errors.is_empty(), "errors: {errors:?}");

    let output = format!("{module}");
    assert!(output.contains("functy.0 = (ptr, <4 x i32>, <4 x i32>) -> (<4 x i32>, <4 x bool>)"));
    assert!(output.contains("load <4 x i32>, ptr %0, align 16"));
    assert!(output.contains("mul <4 x i32>"));
    assert!(output.contains("xor <4 x i32>"));
    assert!(output.contains("icmp eq <4 x i32>"));
    assert!(output.contains("select <4 x i32>"));
    assert!(output.contains("store <4 x i32>"));
}

#[test]
fn build_repeated_lane_pack_helpers_emit_existing_vector_dialect() {
    let mut mb = ModuleBuilder::new("vector_repeated_lane_pack");
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I64], vec![Ty::v4_i32(), Ty::v2_i64()]);
    let mut fb = mb.function("splat", ft);

    let entry = fb.create_block();
    let lane32 = fb.add_block_param(entry, Ty::I32);
    let lane64 = fb.add_block_param(entry, Ty::I64);
    fb.switch_to_block(entry);

    let v4 = fb
        .v4_i32_splat_lane(lane32)
        .expect("v4 splat uses repeated pack_lanes operands");
    let v2 = fb
        .v2_i64_splat_lane(lane64)
        .expect("v2 splat uses repeated pack_lanes operands");
    fb.ret(vec![v4, v2]);
    fb.build();

    let module = mb.build();
    let errors = validate_module(&module);
    assert!(errors.is_empty(), "errors: {errors:?}");

    let block = &module.functions[0].blocks[0];
    match &block.body[0].inst {
        Inst::DialectOp(op) => {
            assert!(vector::is_pack_lanes_op(op));
            assert_eq!(op.operands, vec![lane32, lane32, lane32, lane32]);
            assert_eq!(op.result_tys, vec![Ty::v4_i32()]);
        }
        other => panic!("expected v4 pack_lanes dialect op, got {other:?}"),
    }
    match &block.body[1].inst {
        Inst::DialectOp(op) => {
            assert!(vector::is_pack_lanes_op(op));
            assert_eq!(op.operands, vec![lane64, lane64]);
            assert_eq!(op.result_tys, vec![Ty::v2_i64()]);
        }
        other => panic!("expected v2 pack_lanes dialect op, got {other:?}"),
    }

    let output = format!("{module}");
    assert!(output.contains("%2 = dialect_op vector.pack_lanes(%0, %0, %0, %0) -> <4 x i32>"));
    assert!(output.contains("%3 = dialect_op vector.pack_lanes(%1, %1) -> <2 x i64>"));
}

#[test]
fn build_vector_dialect_helpers_emit_lane_and_mask_ops() {
    let mut mb = ModuleBuilder::new("vector_lane_helpers");
    let ft = mb.add_func_type(
        vec![
            Ty::I32,
            Ty::I32,
            Ty::I32,
            Ty::I32,
            Ty::v4_i32(),
            Ty::I32,
            Ty::v2_i64(),
            Ty::v2_i64(),
            Ty::v8_bool(),
            Ty::v16_bool(),
        ],
        vec![
            Ty::v4_i32(),
            Ty::I32,
            Ty::v4_i32(),
            Ty::I32,
            Ty::I32,
            Ty::I32,
            Ty::I32,
        ],
    );
    let mut fb = mb.function("lanes", ft);

    let entry = fb.create_block();
    let l0 = fb.add_block_param(entry, Ty::I32);
    let l1 = fb.add_block_param(entry, Ty::I32);
    let l2 = fb.add_block_param(entry, Ty::I32);
    let l3 = fb.add_block_param(entry, Ty::I32);
    let vector = fb.add_block_param(entry, Ty::v4_i32());
    let replacement = fb.add_block_param(entry, Ty::I32);
    let v2_a = fb.add_block_param(entry, Ty::v2_i64());
    let v2_b = fb.add_block_param(entry, Ty::v2_i64());
    let v8_mask = fb.add_block_param(entry, Ty::v8_bool());
    let v16_mask = fb.add_block_param(entry, Ty::v16_bool());
    fb.switch_to_block(entry);

    let packed = fb
        .v4_i32_pack_lanes([l0, l1, l2, l3])
        .expect("valid v4 lane pack");
    let extracted = fb
        .v4_i32_extract_lane(packed, 2)
        .expect("valid v4 extract lane");
    let inserted = fb
        .v4_i32_insert_lane(vector, 1, replacement)
        .expect("valid v4 insert lane");
    let mask = fb.v4_i32_icmp_sgt(inserted, packed);
    let bits = fb
        .v4_bool_mask_to_i32_bits(mask)
        .expect("valid v4 mask compaction");
    let v2_mask = fb.v2_i64_icmp_eq(v2_a, v2_b);
    let v2_bits_i32 = fb
        .v2_bool_mask_to_i32_bits(v2_mask)
        .expect("valid v2 i32 mask compaction");
    let v8_bits = fb
        .v8_bool_mask_to_i32_bits(v8_mask)
        .expect("valid v8 i32 mask compaction");
    let v16_bits = fb
        .v16_bool_mask_to_i32_bits(v16_mask)
        .expect("valid v16 i32 mask compaction");
    let err = fb
        .v4_i32_extract_lane(packed, 4)
        .expect_err("builder rejects out-of-range constant lanes");
    assert!(err.contains("lane 4 is out of range"));
    fb.ret(vec![
        packed,
        extracted,
        inserted,
        bits,
        v2_bits_i32,
        v8_bits,
        v16_bits,
    ]);
    fb.build();

    let module = mb.build();
    let errors = validate_module(&module);
    assert!(errors.is_empty(), "errors: {errors:?}");

    #[cfg(feature = "serde")]
    {
        let json = serde_json::to_string_pretty(&module).expect("serialize vector helper module");
        let from_json: trust_ir::Module =
            serde_json::from_str(&json).expect("deserialize vector helper module");
        assert_eq!(from_json, module);
        let errors = validate_module(&from_json);
        assert!(
            errors.is_empty(),
            "JSON vector helper module errors: {errors:?}"
        );

        let msgpack = rmp_serde::to_vec(&module).expect("serialize vector helper module");
        let from_msgpack: trust_ir::Module =
            rmp_serde::from_slice(&msgpack).expect("deserialize vector helper module");
        assert_eq!(from_msgpack, module);
        let errors = validate_module(&from_msgpack);
        assert!(
            errors.is_empty(),
            "MessagePack vector helper module errors: {errors:?}"
        );
    }

    let block = &module.functions[0].blocks[0];
    assert!(matches!(&block.body[0].inst, Inst::DialectOp(op) if vector::is_pack_lanes_op(op)));
    assert!(matches!(&block.body[1].inst, Inst::DialectOp(op) if vector::is_extract_lane_op(op)));
    assert!(matches!(&block.body[2].inst, Inst::DialectOp(op) if vector::is_insert_lane_op(op)));
    assert!(matches!(&block.body[4].inst, Inst::DialectOp(op) if vector::is_mask_to_bits_op(op)));
    assert!(matches!(&block.body[6].inst, Inst::DialectOp(op) if vector::is_mask_to_bits_op(op)));
    assert!(matches!(&block.body[7].inst, Inst::DialectOp(op) if vector::is_mask_to_bits_op(op)));
    assert!(matches!(&block.body[8].inst, Inst::DialectOp(op) if vector::is_mask_to_bits_op(op)));

    let output = format!("{module}");
    assert!(output.contains("%10 = dialect_op vector.pack_lanes(%0, %1, %2, %3) -> <4 x i32>"));
    assert!(output.contains("%11 = dialect_op vector.extract_lane(%10) -> i32"));
    assert!(output.contains("%12 = dialect_op vector.insert_lane(%4, %5) -> <4 x i32>"));
    assert!(output.contains("%14 = dialect_op vector.mask_to_bits(%13) -> i32"));
    assert!(output.contains("%16 = dialect_op vector.mask_to_bits(%15) -> i32"));
    assert!(output.contains("%17 = dialect_op vector.mask_to_bits(%8) -> i32"));
    assert!(output.contains("%18 = dialect_op vector.mask_to_bits(%9) -> i32"));
}

#[test]
fn validate_module_rejects_vector_dialect_operand_types_from_call_results() {
    let mut mb = ModuleBuilder::new("bad_vector_call_lane");
    let callee_ty = mb.add_func_type(vec![], vec![Ty::I64]);
    let callee = {
        let mut fb = mb.function("lane64", callee_ty);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let lane = fb.iconst(Ty::I64, 7);
        fb.ret(vec![lane]);
        fb.build()
    };

    let caller_ty = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("caller", caller_ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let lane32 = fb.iconst(Ty::I32, 1);
    let lane64 = fb.call(callee, vec![]);
    fb.dialect_op(vector::pack_lanes(
        Ty::v4_i32(),
        [lane32, lane64, lane32, lane32],
    ));
    fb.ret(vec![]);
    fb.build();

    let module = mb.build();
    let errors = validate_module(&module);
    assert!(
        errors.iter().any(|error| matches!(
            error,
            trust_ir_build::validate::ValidationError::InvalidVectorDialectOp {
                op,
                reason,
                ..
            } if op == "vector.pack_lanes"
                && reason.contains("lane operand 1")
                && reason.contains("type i64")
                && reason.contains("expected i32")
        )),
        "expected vector dialect operand type rejection, got {errors:?}"
    );
}

#[test]
fn build_chc_x86_v4_i32_canonical_builder_api() {
    let mut mb = ModuleBuilder::new("chc_x86_v4_i32_builder");
    let v4i32 = Ty::v4_i32();
    let v4bool = Ty::v4_bool();
    let ft = mb.add_func_type(
        vec![v4i32.clone(), v4i32.clone()],
        vec![
            v4i32.clone(),
            v4i32.clone(),
            v4bool.clone(),
            v4bool.clone(),
            v4bool.clone(),
            v4bool.clone(),
        ],
    );
    let mut fb = mb.function("lane_packed", ft);

    let entry = fb.create_block();
    let a = fb.add_block_param(entry, v4i32.clone());
    let b = fb.add_block_param(entry, v4i32.clone());
    fb.switch_to_block(entry);

    let all_ones = fb.v4_i32_all_ones_mask_const();
    let zero = fb.v4_i32_zero_mask_const();
    let mask = fb.icmp(ICmpOp::Ne, v4i32.clone(), all_ones, zero);
    let add = fb.v4_i32_add(a, b);
    let sub = fb.v4_i32_sub(add, b);
    let mul = fb.v4_i32_mul(sub, b);
    let selected = fb.v4_i32_mask_select(mask, add, sub);
    let slt = fb.v4_i32_icmp_slt(sub, add);
    let sle = fb.v4_i32_icmp_sle(sub, add);
    let sgt = fb.v4_i32_icmp_sgt(add, sub);
    let sge = fb.v4_i32_icmp_sge(add, sub);
    fb.ret(vec![mul, selected, slt, sle, sgt, sge]);
    fb.build();

    let module = mb.build();
    let errors = validate_module(&module);
    assert!(errors.is_empty(), "errors: {errors:?}");

    let output = format!("{module}");
    assert!(output.contains("functy.0 = (<4 x i32>, <4 x i32>) -> (<4 x i32>, <4 x i32>, <4 x bool>, <4 x bool>, <4 x bool>, <4 x bool>)"));
    assert!(output.contains("%2 = const <4 x i32> vec[ -1, -1, -1, -1 ]"));
    assert!(output.contains("%3 = const <4 x i32> vec[ 0, 0, 0, 0 ]"));
    assert!(output.contains("%4 = icmp ne <4 x i32> %2, %3"));
    assert!(output.contains("%5 = add <4 x i32> %0, %1"));
    assert!(output.contains("%6 = sub <4 x i32> %5, %1"));
    assert!(output.contains("%7 = mul <4 x i32> %6, %1"));
    assert!(output.contains("%8 = select <4 x i32> %4, %5, %6"));
    assert!(output.contains("%9 = icmp slt <4 x i32> %6, %5"));
    assert!(output.contains("%10 = icmp sle <4 x i32> %6, %5"));
    assert!(output.contains("%11 = icmp sgt <4 x i32> %5, %6"));
    assert!(output.contains("%12 = icmp sge <4 x i32> %5, %6"));
}

#[test]
fn build_chc_x86_v2_i64_signed_compare_mask_builder_api() {
    let mut mb = ModuleBuilder::new("chc_x86_v2_i64_builder");
    let v2i64 = Ty::v2_i64();
    let v2bool = Ty::v2_bool();
    let ft = mb.add_func_type(
        vec![v2i64.clone(), v2i64.clone()],
        vec![
            v2i64.clone(),
            v2bool.clone(),
            v2bool.clone(),
            v2bool.clone(),
            v2bool.clone(),
            v2bool.clone(),
            v2bool.clone(),
        ],
    );
    let mut fb = mb.function("lane_packed_i64", ft);

    let entry = fb.create_block();
    let a = fb.add_block_param(entry, v2i64.clone());
    let b = fb.add_block_param(entry, v2i64.clone());
    fb.switch_to_block(entry);

    let all_ones = fb.v2_i64_all_ones_mask_const();
    let zero = fb.v2_i64_zero_mask_const();
    let ne = fb.v2_i64_icmp_ne(all_ones, zero);
    let add = fb.v2_i64_add(a, b);
    let sub = fb.v2_i64_sub(add, b);
    let selected = fb.v2_i64_mask_select(ne, add, sub);
    let eq = fb.v2_i64_icmp_eq(a, b);
    let slt = fb.v2_i64_icmp_slt(sub, add);
    let sle = fb.v2_i64_icmp_sle(sub, add);
    let sgt = fb.v2_i64_icmp_sgt(add, sub);
    let sge = fb.v2_i64_icmp_sge(add, sub);
    fb.ret(vec![selected, eq, ne, slt, sle, sgt, sge]);
    fb.build();

    let module = mb.build();
    let errors = validate_module(&module);
    assert!(errors.is_empty(), "errors: {errors:?}");

    let output = format!("{module}");
    assert!(output.contains("functy.0 = (<2 x i64>, <2 x i64>) -> (<2 x i64>, <2 x bool>, <2 x bool>, <2 x bool>, <2 x bool>, <2 x bool>, <2 x bool>)"));
    assert!(output.contains("%2 = const <2 x i64> vec[ -1, -1 ]"));
    assert!(output.contains("%3 = const <2 x i64> vec[ 0, 0 ]"));
    assert!(output.contains("%4 = icmp ne <2 x i64> %2, %3"));
    assert!(output.contains("%5 = add <2 x i64> %0, %1"));
    assert!(output.contains("%6 = sub <2 x i64> %5, %1"));
    assert!(output.contains("%7 = select <2 x i64> %4, %5, %6"));
    assert!(output.contains("%8 = icmp eq <2 x i64> %0, %1"));
    assert!(output.contains("%9 = icmp slt <2 x i64> %6, %5"));
    assert!(output.contains("%10 = icmp sle <2 x i64> %6, %5"));
    assert!(output.contains("%11 = icmp sgt <2 x i64> %5, %6"));
    assert!(output.contains("%12 = icmp sge <2 x i64> %5, %6"));
}

#[test]
fn validate_rejects_chc_x86_v4_i32_physical_mask_select_condition() {
    let mut mb = ModuleBuilder::new("bad_chc_x86_v4_i32_select");
    let v4i32 = Ty::v4_i32();
    let ft = mb.add_func_type(
        vec![v4i32.clone(), v4i32.clone(), v4i32.clone()],
        vec![v4i32.clone()],
    );
    let mut fb = mb.function("bad_lane_select", ft);

    let entry = fb.create_block();
    let physical_mask = fb.add_block_param(entry, v4i32.clone());
    let then_val = fb.add_block_param(entry, v4i32.clone());
    let else_val = fb.add_block_param(entry, v4i32);
    fb.switch_to_block(entry);

    let selected = fb.v4_i32_mask_select(physical_mask, then_val, else_val);
    fb.ret(vec![selected]);
    fb.build();

    let module = mb.build();
    let errors = validate_module(&module);
    assert!(
        errors.iter().any(|error| matches!(
            error,
            trust_ir_build::validate::ValidationError::SelectConditionTypeMismatch {
                expected,
                actual,
                ..
            } if expected == "<4 x bool>" && actual == "<4 x i32>"
        )),
        "expected physical mask select rejection, got {errors:?}"
    );
}

#[test]
fn validate_rejects_malformed_vector_surfaces() {
    let mut mb = ModuleBuilder::new("bad_vector_surfaces");
    let v4ptr = Ty::Vector(Box::new(Ty::Ptr), 4);
    let v2bool = Ty::Vector(Box::new(Ty::Bool), 2);
    let nested = Ty::Vector(Box::new(Ty::Vector(Box::new(Ty::I32), 4)), 2);

    mb.add_func_type(vec![v4ptr.clone()], vec![Ty::Vector(Box::new(Ty::I32), 0)]);
    mb.add_global(Global {
        name: "BAD_PTRS".to_string(),
        ty: v4ptr,
        mutable: false,
        initializer: None,
        linkage: trust_ir::Linkage::Internal,
        tls: None,
        align: None,
    });
    mb.add_global(Global {
        name: "BAD_MASK".to_string(),
        ty: v2bool,
        mutable: false,
        initializer: Some(Constant::Vector(vec![
            Constant::Bool(true),
            Constant::Int(1),
        ])),
        linkage: trust_ir::Linkage::Internal,
        tls: None,
        align: None,
    });
    mb.add_struct(StructDef {
        id: trust_ir::value::StructId::new(0),
        name: "BadVectorStruct".to_string(),
        fields: vec![FieldDef {
            name: "lanes".to_string(),
            ty: nested,
            offset: None,
        }],
        size: None,
        align: None,

        repr: Default::default(),
    });

    let module = mb.build();
    let errors = validate_module(&module);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            trust_ir_build::validate::ValidationError::InvalidModuleVectorType {
                location,
                reason,
                ..
            } if location == "functy.0 param 0"
                && reason == "lane type must be bool, integer, or float"        )),
        "expected invalid vector function param, got {errors:?}"
    );
    assert!(
        errors.iter().any(|e| matches!(
            e,
            trust_ir_build::validate::ValidationError::InvalidModuleVectorType {
                location,
                reason,
                ..
            } if location == "functy.0 return 0" && reason == "lane count must be nonzero"
        )),
        "expected invalid vector function return, got {errors:?}"
    );
    assert!(
        errors.iter().any(|e| matches!(
            e,
            trust_ir_build::validate::ValidationError::InvalidModuleVectorType { location, .. }
                if location == "global 'BAD_PTRS'"
        )),
        "expected invalid vector global, got {errors:?}"
    );
    assert!(
        errors.iter().any(|e| matches!(
            e,
            trust_ir_build::validate::ValidationError::ConstTypeMismatch { location, expected, actual }
                if location == "global 'BAD_MASK'"
                    && expected == "<2 x bool>"
                    && actual == "vector[2]"
        )),
        "expected invalid vector constant, got {errors:?}"
    );
    assert!(
        errors.iter().any(|e| matches!(
            e,
            trust_ir_build::validate::ValidationError::InvalidModuleVectorType {
                location,
                reason,
                ..
            } if location == "struct @BadVectorStruct field 'lanes'"
                && reason == "nested vector lanes are not supported"
        )),
        "expected invalid vector struct field, got {errors:?}"
    );
}

/// Builder: assume and assert don't produce results.
#[test]
fn build_assume_assert_no_results() {
    let mut mb = ModuleBuilder::new("proof_ops");
    let ft = mb.add_func_type(vec![Ty::Bool], vec![]);
    let mut fb = mb.function("proof_check", ft);

    let entry = fb.create_block();
    let cond = fb.add_block_param(entry, Ty::Bool);
    fb.switch_to_block(entry);

    fb.assume(cond);
    fb.assert(cond);
    fb.ret(vec![]);
    fb.build();

    let module = mb.build();
    let block = &module.functions[0].blocks[0];

    // assume and assert should have no results
    assert!(block.body[0].results.is_empty());
    assert!(block.body[1].results.is_empty());

    let output = format!("{}", module);
    assert!(output.contains("assume %0"));
    assert!(output.contains("assert %0"));
}

/// Builder: unreachable is a valid terminator.
#[test]
fn build_unreachable_terminator() {
    let mut mb = ModuleBuilder::new("unreachable_test");
    let ft = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("trap", ft);

    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.unreachable();
    fb.build();

    let module = mb.build();
    for func in &module.functions {
        let errors = validate_function(func);
        assert!(errors.is_empty(), "errors: {:?}", errors);
    }

    let output = format!("{}", module);
    assert!(output.contains("unreachable"));
}

/// Complete round-trip: build complex program -> display -> verify all elements.
#[test]
fn full_round_trip_complex_program() {
    let mut mb = ModuleBuilder::new("full_program");

    // Add struct
    let sid = mb.add_struct(StructDef {
        id: trust_ir::StructId::new(0),
        name: "Vec2".to_string(),
        fields: vec![
            FieldDef {
                name: "x".to_string(),
                ty: Ty::F64,
                offset: Some(0),
            },
            FieldDef {
                name: "y".to_string(),
                ty: Ty::F64,
                offset: Some(8),
            },
        ],
        size: Some(16),
        align: Some(8),

        repr: Default::default(),
    });

    // Add global
    mb.add_global(Global {
        name: "EPSILON".to_string(),
        ty: Ty::F64,
        mutable: false,
        initializer: Some(trust_ir::Constant::Float(1e-10)),
        linkage: trust_ir::Linkage::External,
        tls: None,
        align: None,
    });

    // Function: dot product
    let ft = mb.add_func_type(vec![Ty::Struct(sid), Ty::Struct(sid)], vec![Ty::F64]);
    let mut fb = mb.function("dot", ft);
    let entry = fb.create_block();

    let a = fb.add_block_param(entry, Ty::Struct(sid));
    let b = fb.add_block_param(entry, Ty::Struct(sid));
    fb.switch_to_block(entry);

    let ax = fb.extract_field(Ty::F64, a, 0);
    let ay = fb.extract_field(Ty::F64, a, 1);
    let bx = fb.extract_field(Ty::F64, b, 0);
    let by = fb.extract_field(Ty::F64, b, 1);

    let px = fb.fmul(Ty::F64, ax, bx);
    let py = fb.fmul(Ty::F64, ay, by);
    let result = fb.fadd(Ty::F64, px, py);

    fb.ret(vec![result]);
    fb.build();

    let module = mb.build();

    // Validate
    for func in &module.functions {
        let errors = validate_function(func);
        assert!(errors.is_empty(), "errors: {:?}", errors);
    }

    // Display and verify all components
    let output = format!("{}", module);

    // Module header
    assert!(output.contains("; TrustIr text format v1"));
    assert!(output.contains("module \"full_program\""));

    // Struct
    assert!(output.contains("struct @Vec2 { f64, f64 } size=16 align=8"));

    // Function
    assert!(output.contains("fn @dot(functy.0)"));
    assert!(output.contains("extractfield f64 %0, 0"));
    assert!(output.contains("extractfield f64 %0, 1"));
    assert!(output.contains("fmul f64"));
    assert!(output.contains("fadd f64"));
}

/// Validation with builder-built function guarantees consistency.
#[test]
fn validate_builder_output_always_valid() {
    // Any function built through the builder API should always validate,
    // as long as every block has a terminator.
    let mut mb = ModuleBuilder::new("valid_guaranteed");

    // Build 5 functions with different patterns
    let ft_void = mb.add_func_type(vec![], vec![]);
    let ft_i32 = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);

    // fn1: single block, return
    {
        let mut fb = mb.function("f1", ft_void);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.ret(vec![]);
        fb.build();
    }

    // fn2: two blocks, branch
    {
        let mut fb = mb.function("f2", ft_i32);
        let entry = fb.create_block();
        let exit = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        fb.br(exit, vec![x]);
        let y = fb.add_block_param(exit, Ty::I32);
        fb.switch_to_block(exit);
        fb.ret(vec![y]);
        fb.build();
    }

    // fn3: unreachable
    {
        let mut fb = mb.function("f3", ft_void);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.unreachable();
        fb.build();
    }

    let module = mb.build();
    for func in &module.functions {
        let errors = validate_function(func);
        assert!(
            errors.is_empty(),
            "function {} has errors: {:?}",
            func.name,
            errors
        );
    }
}

/// Build a function with atomics: load, increment, store, fence.
#[test]
fn build_atomic_increment() {
    let mut mb = ModuleBuilder::new("atomic_inc");
    let ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I64]);
    let mut fb = mb.function("atomic_inc", ft);

    let entry = fb.create_block();
    let ptr = fb.add_block_param(entry, Ty::Ptr);
    fb.switch_to_block(entry);

    let old = fb.atomic_load(Ty::I64, ptr, Ordering::Acquire);
    let one = fb.iconst(Ty::I64, 1);
    let new = fb.add(Ty::I64, old, one);
    fb.atomic_store(Ty::I64, ptr, new, Ordering::Release);
    fb.fence(Ordering::SeqCst);
    fb.ret(vec![old]);
    fb.build();

    let module = mb.build();

    // Validate
    for func in &module.functions {
        let errors = validate_function(func);
        assert!(errors.is_empty());
    }

    // Verify display output
    let output = format!("{}", module);
    assert!(output.contains("atomic_load acquire i64, ptr %0"));
    assert!(output.contains("add i64 %1, %2"));
    assert!(output.contains("atomic_store release i64 %3, ptr %0"));
    assert!(output.contains("fence seq_cst"));
}

/// Build a function using fcmp.
#[test]
fn build_fcmp_program() {
    let mut mb = ModuleBuilder::new("fcmp_test");
    let ft = mb.add_func_type(vec![Ty::F64, Ty::F64], vec![Ty::Bool]);
    let mut fb = mb.function("is_less", ft);

    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::F64);
    let b = fb.add_block_param(entry, Ty::F64);
    fb.switch_to_block(entry);

    let result = fb.fcmp(FCmpOp::OLt, Ty::F64, a, b);
    fb.ret(vec![result]);
    fb.build();

    let module = mb.build();
    for func in &module.functions {
        let errors = validate_function(func);
        assert!(errors.is_empty());
    }

    let output = format!("{}", module);
    assert!(output.contains("fcmp olt f64 %0, %1"));
}

/// Build a function with multiple proof annotation types.
#[test]
fn build_multiple_proof_types() {
    let mut mb = ModuleBuilder::new("multi_proof");
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("safe_div", ft);

    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::I32);
    let b = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);

    // Assert b != 0 (proof: DivNonZero)
    let zero = fb.iconst(Ty::I32, 0);
    let not_zero = fb.icmp(ICmpOp::Ne, Ty::I32, b, zero);
    fb.assert(not_zero);

    // Divide with proof annotation
    let result = fb.sdiv(Ty::I32, a, b);
    fb.ret(vec![result]);
    fb.build();

    let module = mb.build();
    let output = format!("{}", module);
    assert!(output.contains("assert %3"));
    assert!(output.contains("sdiv i32 %0, %1"));
}

// --- Tests for new builder methods (Part of #17, Part of #19) ---

/// Build a program with dealloc (heap free) and verify display.
#[test]
fn build_dealloc_program() {
    let mut mb = ModuleBuilder::new("dealloc_test");
    let ft = mb.add_func_type(vec![Ty::Ptr], vec![]);
    let mut fb = mb.function("free_box", ft);

    let entry = fb.create_block();
    let ptr = fb.add_block_param(entry, Ty::Ptr);
    fb.switch_to_block(entry);

    fb.dealloc(ptr);
    fb.ret(vec![]);
    fb.build();

    let module = mb.build();
    for func in &module.functions {
        let errors = validate_function(func);
        assert!(errors.is_empty(), "errors: {:?}", errors);
    }

    let output = format!("{}", module);
    assert!(output.contains("dealloc %0"));
}

/// Build a program with borrow/borrow_mut/end_borrow and verify display.
#[test]
fn build_borrow_program() {
    let mut mb = ModuleBuilder::new("borrow_test");
    let ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::Ptr]);
    let mut fb = mb.function("borrow_and_release", ft);

    let entry = fb.create_block();
    let ptr = fb.add_block_param(entry, Ty::Ptr);
    fb.switch_to_block(entry);

    let shared = fb.borrow(ptr);
    fb.end_borrow(shared);
    let mutable = fb.borrow_mut(ptr);
    fb.end_borrow(mutable);
    fb.ret(vec![ptr]);
    fb.build();

    let module = mb.build();
    for func in &module.functions {
        let errors = validate_function(func);
        assert!(errors.is_empty(), "errors: {:?}", errors);
    }

    let output = format!("{}", module);
    assert!(output.contains("borrow %0"));
    assert!(output.contains("borrow_mut %0"));
    assert!(output.contains("end_borrow %1"));
    assert!(output.contains("end_borrow %2"));
}

/// Build a program with retain/release/is_unique and verify display.
#[test]
fn build_arc_program() {
    let mut mb = ModuleBuilder::new("arc_test");
    let ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::Bool]);
    let mut fb = mb.function("arc_ops", ft);

    let entry = fb.create_block();
    let ptr = fb.add_block_param(entry, Ty::Ptr);
    fb.switch_to_block(entry);

    fb.retain(ptr);
    let unique = fb.is_unique(ptr);
    fb.release(ptr);
    fb.ret(vec![unique]);
    fb.build();

    let module = mb.build();
    for func in &module.functions {
        let errors = validate_function(func);
        assert!(errors.is_empty(), "errors: {:?}", errors);
    }

    let output = format!("{}", module);
    assert!(output.contains("retain %0"));
    assert!(output.contains("is_unique %0"));
    assert!(output.contains("release %0"));
}

/// Build a program using the switch builder method.
#[test]
fn build_switch_via_builder() {
    let mut mb = ModuleBuilder::new("switch_builder_test");
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("dispatch", ft);

    let entry = fb.create_block();
    let case_0 = fb.create_block();
    let case_1 = fb.create_block();
    let default_bb = fb.create_block();

    let x = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);

    fb.switch(
        x,
        vec![
            SwitchCase {
                value: trust_ir::Constant::Int(0),
                target: case_0,
                args: vec![],
            },
            SwitchCase {
                value: trust_ir::Constant::Int(1),
                target: case_1,
                args: vec![],
            },
        ],
        default_bb,
        vec![],
    );

    fb.switch_to_block(case_0);
    let r0 = fb.iconst(Ty::I32, 100);
    fb.ret(vec![r0]);

    fb.switch_to_block(case_1);
    let r1 = fb.iconst(Ty::I32, 200);
    fb.ret(vec![r1]);

    fb.switch_to_block(default_bb);
    let rd = fb.iconst(Ty::I32, -1);
    fb.ret(vec![rd]);

    fb.build();

    let module = mb.build();
    for func in &module.functions {
        let errors = validate_function(func);
        assert!(errors.is_empty(), "errors: {:?}", errors);
    }

    let output = format!("{}", module);
    assert!(output.contains("switch %0"));
    assert!(output.contains("0: bb1"));
    assert!(output.contains("1: bb2"));
    assert!(output.contains("default: bb3"));
}

/// Build a program using call_indirect builder method.
#[test]
fn build_call_indirect_program() {
    let mut mb = ModuleBuilder::new("call_indirect_test");
    let callee_ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let ft = mb.add_func_type(vec![Ty::Ptr, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("indirect_caller", ft);

    let entry = fb.create_block();
    let fptr = fb.add_block_param(entry, Ty::Ptr);
    let arg = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);

    let result = fb.call_indirect(fptr, callee_ft, vec![arg]);
    fb.ret(vec![result]);
    fb.build();

    let module = mb.build();
    for func in &module.functions {
        let errors = validate_function(func);
        assert!(errors.is_empty(), "errors: {:?}", errors);
    }

    let output = format!("{}", module);
    assert!(output.contains("call_indirect %0(functy.0)(%1)"));
}

/// Build a program using atomic_rmw builder method.
#[test]
fn build_atomic_rmw_program() {
    let mut mb = ModuleBuilder::new("rmw_test");
    let ft = mb.add_func_type(vec![Ty::Ptr, Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function("fetch_add", ft);

    let entry = fb.create_block();
    let ptr = fb.add_block_param(entry, Ty::Ptr);
    let val = fb.add_block_param(entry, Ty::I64);
    fb.switch_to_block(entry);

    let old = fb.atomic_rmw(AtomicRMWOp::Add, Ty::I64, ptr, val, Ordering::AcqRel);
    fb.ret(vec![old]);
    fb.build();

    let module = mb.build();
    for func in &module.functions {
        let errors = validate_function(func);
        assert!(errors.is_empty(), "errors: {:?}", errors);
    }

    let output = format!("{}", module);
    assert!(output.contains("atomicrmw add acq_rel i64 ptr %0, %1"));
}

/// Build a program using cmpxchg builder method.
#[test]
fn build_cmpxchg_program() {
    let mut mb = ModuleBuilder::new("cas_test");
    let ft = mb.add_func_type(vec![Ty::Ptr, Ty::I64, Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function("compare_and_swap", ft);

    let entry = fb.create_block();
    let ok_bb = fb.create_block();
    let fail_bb = fb.create_block();

    let ptr = fb.add_block_param(entry, Ty::Ptr);
    let expected = fb.add_block_param(entry, Ty::I64);
    let desired = fb.add_block_param(entry, Ty::I64);
    fb.switch_to_block(entry);

    let (result, success) = fb.cmpxchg(
        Ty::I64,
        ptr,
        expected,
        desired,
        Ordering::SeqCst,
        Ordering::Acquire,
    );
    fb.condbr(success, ok_bb, vec![], fail_bb, vec![]);

    fb.switch_to_block(ok_bb);
    fb.ret(vec![result]);

    fb.switch_to_block(fail_bb);
    fb.ret(vec![expected]);

    fb.build();

    let module = mb.build();
    for func in &module.functions {
        let errors = validate_function(func);
        assert!(errors.is_empty(), "errors: {:?}", errors);
    }

    let output = format!("{}", module);
    assert!(output.contains("cmpxchg i64 ptr %0, %1, %2 seq_cst acquire"));
}

/// Build a program using extract_element and insert_element builder methods.
#[test]
fn build_extract_insert_element_program() {
    let mut mb = ModuleBuilder::new("element_test");
    let ft = mb.add_func_type(vec![Ty::v4_i32(), Ty::I64, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("vector_swap", ft);

    let entry = fb.create_block();
    let vector = fb.add_block_param(entry, Ty::v4_i32());
    let idx = fb.add_block_param(entry, Ty::I64);
    let new_val = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);

    let old_val = fb.extract_element(Ty::I32, vector, idx);
    let _new_vector = fb.insert_element(Ty::v4_i32(), vector, idx, new_val);
    fb.ret(vec![old_val]);
    fb.build();

    let module = mb.build();
    for func in &module.functions {
        let errors = validate_function(func);
        assert!(errors.is_empty(), "errors: {:?}", errors);
    }

    let output = format!("{}", module);
    assert!(output.contains("extractelement i32 %0, %1"));
    assert!(output.contains("insertelement <4 x i32> %0, %1, %2"));
}

/// Integration: alloc, store, load, dealloc lifecycle.
#[test]
fn build_alloc_store_load_dealloc_lifecycle() {
    let mut mb = ModuleBuilder::new("lifecycle_test");
    let ft = mb.add_func_type(vec![], vec![Ty::I32]);
    let mut fb = mb.function("heap_lifecycle", ft);

    let entry = fb.create_block();
    fb.switch_to_block(entry);

    let ptr = fb.alloca(Ty::I32);
    let val = fb.iconst(Ty::I32, 42);
    fb.store(Ty::I32, ptr, val);
    let loaded = fb.load(Ty::I32, ptr);
    fb.dealloc(ptr);
    fb.ret(vec![loaded]);
    fb.build();

    let module = mb.build();
    for func in &module.functions {
        let errors = validate_function(func);
        assert!(errors.is_empty(), "errors: {:?}", errors);
    }

    let output = format!("{}", module);
    assert!(output.contains("alloca i32"));
    assert!(output.contains("const i32 42"));
    assert!(output.contains("store i32 %1, ptr %0"));
    assert!(output.contains("load i32, ptr %0"));
    assert!(output.contains("dealloc %0"));
}

/// Integration: Swift ARC pattern (retain, use, release).
#[test]
fn build_swift_arc_pattern() {
    let mut mb = ModuleBuilder::new("swift_arc");
    let ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I32]);
    let mut fb = mb.function("use_rc_object", ft);

    let entry = fb.create_block();
    let release_bb = fb.create_block();

    let obj = fb.add_block_param(entry, Ty::Ptr);
    fb.switch_to_block(entry);

    // Retain, use, check uniqueness
    fb.retain(obj);
    let val = fb.load(Ty::I32, obj);
    let is_unique = fb.is_unique(obj);
    fb.condbr(is_unique, release_bb, vec![], release_bb, vec![]);

    // Release in both paths
    fb.switch_to_block(release_bb);
    fb.release(obj);
    fb.ret(vec![val]);

    fb.build();

    let module = mb.build();
    for func in &module.functions {
        let errors = validate_function(func);
        assert!(errors.is_empty(), "errors: {:?}", errors);
    }

    let output = format!("{}", module);
    assert!(output.contains("retain %0"));
    assert!(output.contains("is_unique %0"));
    assert!(output.contains("release %0"));
}

/// Integration: Rust borrow pattern.
#[test]
fn build_rust_borrow_pattern() {
    let mut mb = ModuleBuilder::new("rust_borrow");
    let ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I32]);
    let mut fb = mb.function("borrow_read", ft);

    let entry = fb.create_block();
    let ptr = fb.add_block_param(entry, Ty::Ptr);
    fb.switch_to_block(entry);

    // Borrow, read through borrow, end borrow
    let borrow_ref = fb.borrow(ptr);
    let val = fb.load(Ty::I32, borrow_ref);
    fb.end_borrow(borrow_ref);
    fb.ret(vec![val]);

    fb.build();

    let module = mb.build();
    for func in &module.functions {
        let errors = validate_function(func);
        assert!(errors.is_empty(), "errors: {:?}", errors);
    }

    let output = format!("{}", module);
    assert!(output.contains("borrow %0"));
    assert!(output.contains("load i32, ptr %1"));
    assert!(output.contains("end_borrow %1"));
}

/// audit #5: a builder-emitted `trunc` whose declared widths run the wrong way
/// (narrow -> wide) must be rejected by `validate_module`. End-to-end through
/// the public builder + validate path.
#[test]
fn validate_rejects_trunc_to_wider_type() {
    let mut mb = ModuleBuilder::new("bad_trunc");
    let ft = mb.add_func_type(vec![Ty::I16], vec![Ty::I32]);
    let mut fb = mb.function("widen", ft);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::I16);
    fb.switch_to_block(entry);
    // trunc i16 -> i32 is backwards (truncation must narrow).
    let widened = fb.trunc(Ty::I16, Ty::I32, x);
    fb.ret(vec![widened]);
    fb.build();

    let module = mb.build();
    let errors = validate_module(&module);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            trust_ir_build::validate::ValidationError::CastWidthDirectionInvalid { op, .. }
                if op == "trunc"
        )),
        "expected trunc width-direction rejection, got {errors:?}"
    );
}

/// audit #6: a function whose entry block parameters disagree with its declared
/// signature must be rejected. Built directly (the builder keeps them in sync,
/// so we tamper with the entry block after building).
#[test]
fn validate_rejects_entry_params_disagreeing_with_signature() {
    use trust_ir::value::ValueId;

    let mut mb = ModuleBuilder::new("entry_mismatch");
    // Signature declares (i32) but we will give the entry block an i64 param.
    let ft = mb.add_func_type(vec![Ty::I32], vec![]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    let _p = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);
    fb.ret(vec![]);
    fb.build();

    let mut module = mb.build();
    // Tamper: change the entry param type to i64 so it no longer matches.
    module.functions[0].blocks[0].params = vec![(ValueId::new(0), Ty::I64)];

    let errors = validate_module(&module);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            trust_ir_build::validate::ValidationError::EntryParamsMismatch { .. }
        )),
        "expected entry param mismatch rejection, got {errors:?}"
    );
}
