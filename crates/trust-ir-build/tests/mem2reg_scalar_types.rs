// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use trust_ir::mem2reg::{promote_allocas_function, promote_allocas_module};
use trust_ir::{FuncId, InterpretErrorCode, InterpretValue, Interpreter, Module, Ty};
use trust_ir_build::{ModuleBuilder, validate_module};

fn fixture(allocation: Ty, stored: Ty, loaded: Ty, initialize: bool) -> Module {
    let mut builder = ModuleBuilder::new("scalar-memory-types");
    let signature = builder.add_func_type(vec![], vec![loaded.clone()]);
    let mut function = builder.function("read", signature);
    let entry = function.create_block();
    function.switch_to_block(entry);
    let slot = function.alloca(allocation);
    if initialize {
        let value = function.iconst(stored.clone(), 0x34);
        function.store(stored, slot, value);
    }
    let value = function.load(loaded, slot);
    function.ret(vec![value]);
    function.build();
    builder.build().expect("ModuleBuilder::build: test fixture")
}

fn preserve(mut module: Module) -> Module {
    assert!(
        validate_module(&module).is_empty(),
        "{:?}",
        validate_module(&module)
    );
    let before = module.clone();
    assert_eq!(promote_allocas_function(&mut module.functions[0]), 0);
    promote_allocas_module(&mut module);
    assert_eq!(module, before);
    assert_eq!(module.stable_digest(), before.stable_digest());
    assert!(validate_module(&module).is_empty());
    module
}

#[test]
fn legal_narrow_and_reinterpreted_loads_keep_their_memory_types() {
    for loaded in [Ty::I8, Ty::U8, Ty::U64] {
        let mut module = fixture(Ty::I64, Ty::I64, loaded.clone(), true);
        let value = module.functions[0].blocks[0]
            .body
            .iter_mut()
            .find_map(|node| {
                if let trust_ir::Inst::Const { value, .. } = &mut node.inst {
                    Some(value)
                } else {
                    None
                }
            })
            .unwrap();
        *value = trust_ir::Constant::Int(0x1234);
        let expected = InterpretValue::int(
            loaded.clone(),
            if loaded == Ty::U64 { 0x1234 } else { 0x34 },
        )
        .unwrap();
        let before = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .unwrap();
        assert_eq!(before.returns, vec![expected]);
        let module = preserve(module);
        let after = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .unwrap();
        assert_eq!(after.returns, before.returns);
    }
}

#[test]
fn oversized_accesses_and_uninitialized_bytes_are_not_scalar_values() {
    for (stored, loaded) in [(Ty::I64, Ty::I64), (Ty::I8, Ty::I64)] {
        let module = fixture(Ty::I8, stored, loaded, true);
        let before = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .unwrap_err();
        assert_eq!(before.code, InterpretErrorCode::UndefinedBehavior);
        let module = preserve(module);
        assert_eq!(
            Interpreter::with_module(&module)
                .execute_func(FuncId::new(0), [])
                .unwrap_err(),
            before
        );
    }
    // A partial narrow initialization is not a full-width definition. Preserve
    // the reference model's poison/error outcome, including its original site.
    for initialize in [false, true] {
        let module = fixture(Ty::I64, Ty::I8, Ty::I64, initialize);
        let before = Interpreter::with_module(&module).execute_func(FuncId::new(0), []);
        let module = preserve(module);
        let after = Interpreter::with_module(&module).execute_func(FuncId::new(0), []);
        assert_eq!(format!("{after:?}"), format!("{before:?}"));
    }
}

#[test]
fn same_type_integer_scalars_still_promote_and_execute_identically() {
    for ty in [
        Ty::I8,
        Ty::U8,
        Ty::I16,
        Ty::U16,
        Ty::I32,
        Ty::U32,
        Ty::I64,
        Ty::U64,
        Ty::I128,
        Ty::U128,
    ] {
        let mut module = fixture(ty.clone(), ty.clone(), ty, true);
        assert!(validate_module(&module).is_empty());
        let before = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .unwrap();
        assert_eq!(promote_allocas_function(&mut module.functions[0]), 1);
        assert!(validate_module(&module).is_empty());
        let after = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .unwrap();
        assert_eq!(after.returns, before.returns);
    }
}
