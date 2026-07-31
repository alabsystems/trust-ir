// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// B1 (self-hosting blocker): `Inst::GlobalAddr` + `GlobalId`.
//
// Exercises the end-to-end contract that lets trust-ir lower code that
// addresses a module global (a `static`, a `&str` literal's data, or a
// trait-object vtable) — previously inexpressible. Black-box over the public
// API: build -> validate -> interpret, plus the out-of-range rejection.
//
// See docs/roadmap/B1-globaladdr.md.

use trust_ir::interpret::Interpreter;
use trust_ir::ty::Ty;
use trust_ir::value::GlobalId;
use trust_ir::{Constant, Global, Linkage};
use trust_ir_build::{ModuleBuilder, validate_module};

/// A read-only global initialized to 42; `global_addr` + `load` must read it.
#[test]
fn global_addr_loads_initializer() {
    let mut mb = ModuleBuilder::new("b1_load");
    mb.add_global(Global {
        name: "ANSWER".into(),
        ty: Ty::I32,
        mutable: false,
        initializer: Some(Constant::Int(42)),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
    });

    let ft = mb.add_func_type(vec![], vec![Ty::I32]);
    let mut fb = mb.function("read_answer", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let p = fb.global_addr(GlobalId::new(0));
    let v = fb.load(Ty::I32, p);
    fb.ret(vec![v]);
    fb.build();
    let module = mb.build();

    assert!(
        validate_module(&module).is_empty(),
        "in-range GlobalAddr must validate: {:?}",
        validate_module(&module)
    );

    let interp = Interpreter::with_module(&module);
    let out = interp
        .execute_func(module.functions[0].id, [])
        .expect("execution succeeds");
    assert_eq!(out.returns.len(), 1);
    assert_eq!(
        out.returns[0].as_int().expect("int return").as_signed(),
        42,
        "GlobalAddr+Load must observe the global's initializer"
    );
}

/// Two `global_addr` of the same mutable global alias the same storage, so a
/// store through one is observed by a load through the other.
#[test]
fn global_addr_mutable_store_persists_and_aliases() {
    let mut mb = ModuleBuilder::new("b1_store");
    mb.add_global(Global {
        name: "COUNTER".into(),
        ty: Ty::I32,
        mutable: true,
        initializer: Some(Constant::Int(7)),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
    });

    let ft = mb.add_func_type(vec![], vec![Ty::I32]);
    let mut fb = mb.function("bump", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    // store 99 through one address-of, then read back through a fresh one.
    let p1 = fb.global_addr(GlobalId::new(0));
    let ninetynine = fb.iconst(Ty::I32, 99);
    fb.store(Ty::I32, p1, ninetynine);
    let p2 = fb.global_addr(GlobalId::new(0));
    let v = fb.load(Ty::I32, p2);
    fb.ret(vec![v]);
    fb.build();
    let module = mb.build();

    assert!(validate_module(&module).is_empty());

    let interp = Interpreter::with_module(&module);
    let out = interp
        .execute_func(module.functions[0].id, [])
        .expect("execution succeeds");
    assert_eq!(
        out.returns[0].as_int().expect("int return").as_signed(),
        99,
        "store through a mutable global must be observed by a later GlobalAddr+Load"
    );
}

/// A `GlobalAddr` whose id is past the end of `Module::globals` is rejected.
#[test]
fn global_addr_out_of_range_is_rejected() {
    let mut mb = ModuleBuilder::new("b1_oob");
    // No globals added at all -> id 0 is already out of range.
    let ft = mb.add_func_type(vec![], vec![Ty::Ptr]);
    let mut fb = mb.function("dangling", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let p = fb.global_addr(GlobalId::new(0));
    fb.ret(vec![p]);
    fb.build();
    let module = mb.build();

    let errors = validate_module(&module);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            trust_ir_build::validate::ValidationError::GlobalNotFound { .. }
        )),
        "out-of-range GlobalAddr must produce GlobalNotFound, got: {errors:?}"
    );
}
