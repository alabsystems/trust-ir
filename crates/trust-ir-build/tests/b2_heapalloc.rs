// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// B2 (self-hosting blocker): `Inst::HeapAlloc` + `AllocOrigin`.
//
// Heap allocation was previously unrepresentable (only stack `Alloca` existed),
// so the alloc/dealloc pair was broken and Box/Vec/String/malloc could not be
// lowered. These tests exercise: build -> validate -> interpret of a heap
// allocate/store/load/free cycle, double-free detection, and all origins.
//
// Note (deferred, see docs/roadmap/B2-heap-alloc.md): `Dealloc` is still
// permissive about origin (it frees any live region); origin-aware rejection of
// freeing a stack/global region is a tracked follow-up that requires migrating
// existing alloca+dealloc programs.

use trust_ir::inst::AllocOrigin;
use trust_ir::interpret::{InterpretErrorCode, InterpretValue, Interpreter};
use trust_ir::ty::Ty;
use trust_ir_build::{ModuleBuilder, validate_module};

/// heap_alloc -> store -> load -> dealloc validates and executes.
#[test]
fn heap_alloc_store_load_dealloc_executes() {
    let mut mb = ModuleBuilder::new("b2_basic");
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("roundtrip", ft);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);
    let p = fb.heap_alloc(Ty::I32, None, None, AllocOrigin::RustHeap);
    fb.store(Ty::I32, p, x);
    let v = fb.load(Ty::I32, p);
    fb.dealloc(p);
    fb.ret(vec![v]);
    fb.build();
    let module = mb.build();

    assert!(
        validate_module(&module).is_empty(),
        "{:?}",
        validate_module(&module)
    );
    let out = Interpreter::with_module(&module)
        .execute_func(
            module.functions[0].id,
            [InterpretValue::int(Ty::I32, 123).unwrap()],
        )
        .expect("executes");
    assert_eq!(out.returns[0].as_int().unwrap().as_signed(), 123);
}

/// A heap region freed twice is UNDEFINED BEHAVIOR (double-free), ratified in
/// docs/ub-numerics-policy.md §6 and proved against the Lean semantics as
/// `semDealloc_twice_is_ub` (Proofs/MemorySafety.lean, with the
/// `dealloc_twice_ub_code_stable` executable fixture as its twin).
#[test]
fn heap_alloc_double_free_is_detected() {
    let mut mb = ModuleBuilder::new("b2_double_free");
    let ft = mb.add_func_type(vec![], vec![Ty::I32]);
    let mut fb = mb.function("double_free", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let p = fb.heap_alloc(Ty::I32, None, None, AllocOrigin::CMalloc);
    fb.dealloc(p);
    fb.dealloc(p); // second free of the same heap region: runtime UB
    let c = fb.iconst(Ty::I32, 0);
    fb.ret(vec![c]);
    fb.build();
    let module = mb.build();

    assert!(validate_module(&module).is_empty());
    let r = Interpreter::with_module(&module).execute_func(module.functions[0].id, []);
    assert_eq!(
        r.expect_err("double free of a heap region must be a runtime error")
            .code,
        InterpretErrorCode::UndefinedBehavior,
        "double free is UB, not a panic/type error"
    );
}

/// A load through a freed heap region is use-after-free UB
/// (docs/ub-numerics-policy.md §6; Lean twin: `semLoad_after_dealloc_is_ub`
/// and the `load_after_dealloc_ub_code_stable` fixture).
#[test]
fn heap_alloc_use_after_free_is_ub() {
    let mut mb = ModuleBuilder::new("b2_use_after_free");
    let ft = mb.add_func_type(vec![], vec![Ty::I32]);
    let mut fb = mb.function("use_after_free", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let p = fb.heap_alloc(Ty::I32, None, None, AllocOrigin::RustHeap);
    let seven = fb.iconst(Ty::I32, 7);
    fb.store(Ty::I32, p, seven);
    fb.dealloc(p);
    let v = fb.load(Ty::I32, p); // freed region: runtime UB
    fb.ret(vec![v]);
    fb.build();
    let module = mb.build();

    assert!(validate_module(&module).is_empty());
    let r = Interpreter::with_module(&module).execute_func(module.functions[0].id, []);
    assert_eq!(
        r.expect_err("use-after-free must be a runtime error").code,
        InterpretErrorCode::UndefinedBehavior,
    );
}

/// ARC refcount underflow is the ARC double free and is UB: the `Release`
/// that drops the last reference frees the allocation, and a second
/// `Release` (or a `Retain`) on it is rejected
/// (docs/ub-numerics-policy.md §6; Lean twins:
/// `semRelease_after_last_release_is_ub` and the
/// `release_after_last_release_ub_code_stable` /
/// `retain_after_free_ub_code_stable` fixtures).
#[test]
fn arc_release_after_last_release_is_ub() {
    for retain_instead_of_second_release in [false, true] {
        let mut mb = ModuleBuilder::new("b2_arc_underflow");
        let ft = mb.add_func_type(vec![], vec![Ty::I32]);
        let mut fb = mb.function("arc_underflow", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        // A Swift-heap allocation starts with refcount 1 (one owner).
        let p = fb.heap_alloc(Ty::I32, None, None, AllocOrigin::SwiftHeap);
        fb.release(p); // drops the last reference: frees the allocation
        if retain_instead_of_second_release {
            fb.retain(p); // resurrection attempt on a freed allocation: UB
        } else {
            fb.release(p); // refcount underflow (ARC double free): UB
        }
        let c = fb.iconst(Ty::I32, 0);
        fb.ret(vec![c]);
        fb.build();
        let module = mb.build();

        assert!(validate_module(&module).is_empty());
        let r = Interpreter::with_module(&module).execute_func(module.functions[0].id, []);
        assert_eq!(
            r.expect_err("ARC op on a freed allocation must be a runtime error")
                .code,
            InterpretErrorCode::UndefinedBehavior,
            "retain_instead_of_second_release={retain_instead_of_second_release}"
        );
    }
}

/// P1 "Native ARC for Clean": a Clean Perceus RC cell — `heap_alloc
/// clean_heap` starts at refcount 1, `retain` takes it to 2 (`is_unique`
/// false), and two `release`s reach zero and free it. One more `release` is
/// the RC underflow (Perceus double free): UB — byte-for-byte the SwiftHeap
/// discipline (Lean twins: `clean_rc_lifecycle_reaches_zero_stable`,
/// `clean_release_underflow_ub_code_stable`, and the
/// `clean_swift_rc_*_parity_stable` fixtures).
#[test]
fn clean_heap_rc_lifecycle_mirrors_swift_heap() {
    for release_past_zero in [false, true] {
        let mut mb = ModuleBuilder::new("p1_clean_rc");
        let ft = mb.add_func_type(vec![], vec![Ty::Bool]);
        let mut fb = mb.function("clean_rc", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let cell = fb.heap_alloc(Ty::I64, None, None, AllocOrigin::CleanHeap);
        fb.retain(cell); // clean_inc: 1 -> 2
        let uniq = fb.is_unique(cell); // false (two owners)
        fb.release(cell); // clean_dec: 2 -> 1
        fb.release(cell); // clean_dec: 1 -> 0, frees the cell
        if release_past_zero {
            fb.release(cell); // RC underflow (Perceus double free): UB
        }
        fb.ret(vec![uniq]);
        fb.build();
        let module = mb.build();

        assert!(
            validate_module(&module).is_empty(),
            "{:?}",
            validate_module(&module)
        );
        let r = Interpreter::with_module(&module).execute_func(module.functions[0].id, []);
        if release_past_zero {
            assert_eq!(
                r.expect_err("release past refcount zero must be a runtime error")
                    .code,
                InterpretErrorCode::UndefinedBehavior,
                "RC underflow is UB, not a panic/type error"
            );
        } else {
            let out = r.expect("the balanced Clean RC lifecycle executes");
            assert_eq!(
                out.returns[0],
                InterpretValue::bool(false),
                "is_unique after retain must be false (refcount 2)"
            );
        }
    }
}

/// A counted heap allocation (Vec-style: count elements) validates and executes.
#[test]
fn heap_alloc_counted_validates_and_executes() {
    let mut mb = ModuleBuilder::new("b2_counted");
    let ft = mb.add_func_type(vec![], vec![Ty::I32]);
    let mut fb = mb.function("vec4", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let n = fb.iconst(Ty::I64, 4);
    // 4 i32 elements from the Swift heap, then free.
    let p = fb.heap_alloc(Ty::I32, Some(n), Some(4), AllocOrigin::SwiftHeap);
    let seven = fb.iconst(Ty::I32, 7);
    fb.store(Ty::I32, p, seven);
    let v = fb.load(Ty::I32, p);
    fb.dealloc(p);
    fb.ret(vec![v]);
    fb.build();
    let module = mb.build();

    assert!(
        validate_module(&module).is_empty(),
        "{:?}",
        validate_module(&module)
    );
    let out = Interpreter::with_module(&module)
        .execute_func(module.functions[0].id, [])
        .expect("executes");
    assert_eq!(out.returns[0].as_int().unwrap().as_signed(), 7);
}
