// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ordinary Core consumers: typed code pointers survive memory and byte copies.
//! These are reference-interpreter tests, not native ABI/proof claims.
use trust_ir::constant::Constant;
use trust_ir::interpret::{InterpretErrorCode, Interpreter};
use trust_ir::{Endianness, StructPassingPolicy, TargetInfo};
use trust_ir::{FuncId, Module, Ty};
use trust_ir_build::{ModuleBuilder, validate_module};

fn target(mut module: Module, bytes: u32) -> Module {
    module.target_info = Some(TargetInfo {
        triple: if bytes == 4 {
            "wasm32-unknown-unknown"
        } else {
            "aarch64-apple-darwin"
        }
        .into(),
        pointer_size: bytes,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::Unclassified,
    });
    module
}

fn run(module: &Module, root: FuncId) -> u128 {
    let errors = validate_module(module);
    assert!(errors.is_empty(), "{errors:?}");
    let result = Interpreter::with_module(module)
        .execute_func(root, [])
        .unwrap();
    assert_eq!(result.host_calls, 0);
    result.returns[0].as_int().unwrap().as_unsigned()
}

fn plain(bytes: u32, raw: Option<i128>, copy: bool, wrong_signature: bool) -> (Module, FuncId) {
    let mut m = ModuleBuilder::new("typed_function_memory");
    let signature = m.add_func_type(vec![], vec![Ty::U64]);
    let wrong = m.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let leaf = m.declare_function("leaf", signature);
    let root = m.declare_function("root", signature);
    {
        let mut b = m.define_function(leaf).unwrap();
        let entry = b.create_block();
        b.switch_to_block(entry);
        let answer = b.uconst(Ty::U64, 42);
        b.ret(vec![answer]);
        b.build();
    }
    {
        let mut b = m.define_function(root).unwrap();
        let entry = b.create_block();
        b.switch_to_block(entry);
        let slot = b.alloca(Ty::Func(signature));
        if let Some(raw) = raw {
            let bits = b.iconst(Ty::Usize, raw);
            b.store(Ty::Usize, slot, bits);
        } else {
            let code = b.fn_addr(signature, leaf);
            b.store(Ty::Func(signature), slot, code);
        }
        let slot = if copy {
            let copied = b.alloca(Ty::Func(signature));
            let length = b.uconst(Ty::Usize, u128::from(bytes));
            b.memcopy(copied, slot, length, false);
            copied
        } else {
            slot
        };
        let loaded_signature = if wrong_signature { wrong } else { signature };
        let code = b.load(Ty::Func(loaded_signature), slot);
        let args = if wrong_signature {
            vec![b.uconst(Ty::U64, 0)]
        } else {
            vec![]
        };
        let answer = b.call_indirect(code, loaded_signature, args);
        b.ret(vec![answer]);
        b.build();
    }
    (target(m.build().unwrap(), bytes), root)
}

#[test]
fn typed_function_pointer_store_load_and_memcopy_execute_at_target_width() {
    for bytes in [4, 8] {
        for copy in [false, true] {
            let (module, root) = plain(bytes, None, copy, false);
            assert_eq!(run(&module, root), 42);
        }
    }
}

#[test]
fn typed_function_parameter_and_mixed_environment_tuple_roundtrip() {
    for bytes in [4, 8] {
        let mut m = ModuleBuilder::new("typed_function_environment");
        let callback = m.add_func_type(vec![Ty::Ptr], vec![Ty::U64]);
        let forward_sig = m.add_func_type(vec![Ty::Func(callback), Ty::Ptr], vec![Ty::U64]);
        let root_sig = m.add_func_type(vec![], vec![Ty::U64]);
        let leaf = m.declare_function("leaf", callback);
        let forward = m.declare_function("forward", forward_sig);
        let root = m.declare_function("root", root_sig);
        {
            let mut b = m.define_function(leaf).unwrap();
            let entry = b.create_block();
            let env = b.add_block_param(entry, Ty::Ptr);
            b.switch_to_block(entry);
            let answer = b.load(Ty::U64, env);
            b.ret(vec![answer]);
            b.build();
        }
        {
            let mut b = m.define_function(forward).unwrap();
            let entry = b.create_block();
            let code = b.add_block_param(entry, Ty::Func(callback));
            let env = b.add_block_param(entry, Ty::Ptr);
            b.switch_to_block(entry);
            let pair = Ty::Tuple(vec![Ty::Func(callback), Ty::Ptr]);
            let seed = b.const_value(
                pair.clone(),
                Constant::Aggregate(vec![Constant::FnDef(leaf), Constant::Int(0)]),
            );
            let value = b.insert_field(pair.clone(), seed, 0, code);
            let value = b.insert_field(pair.clone(), value, 1, env);
            let slot = b.alloca(pair.clone());
            b.store(pair.clone(), slot, value);
            let value = b.load(pair, slot);
            let code = b.extract_field(Ty::Func(callback), value, 0);
            let env = b.extract_field(Ty::Ptr, value, 1);
            let answer = b.call_indirect(code, callback, vec![env]);
            b.ret(vec![answer]);
            b.build();
        }
        {
            let mut b = m.define_function(root).unwrap();
            let entry = b.create_block();
            b.switch_to_block(entry);
            let env = b.alloca(Ty::U64);
            let answer = b.uconst(Ty::U64, 73);
            b.store(Ty::U64, env, answer);
            let code = b.fn_addr(callback, leaf);
            let answer = b.call(forward, vec![code, env]);
            b.ret(vec![answer]);
            b.build();
        }
        assert_eq!(run(&target(m.build().unwrap(), bytes), root), 73);
    }
}

#[test]
fn loaded_function_pointer_keeps_indirect_signature_checks() {
    for bytes in [4, 8] {
        let (module, root) = plain(bytes, None, false, true);
        assert!(validate_module(&module).is_empty());
        let error = Interpreter::with_module(&module)
            .execute_func(root, [])
            .unwrap_err();
        assert_eq!(error.code, InterpretErrorCode::SignatureMismatch);
    }
}

#[test]
fn null_and_unregistered_code_addresses_do_not_become_callable() {
    for bytes in [4, 8] {
        for raw in [0, 999_999] {
            let (module, root) = plain(bytes, Some(raw), false, false);
            assert!(validate_module(&module).is_empty());
            let error = Interpreter::with_module(&module)
                .execute_func(root, [])
                .unwrap_err();
            assert_eq!(error.code, InterpretErrorCode::InvalidFunctionPointer);
        }
    }
}

#[test]
fn unvalidated_undefined_function_identity_fails_closed_on_store() {
    let (mut module, root) = plain(8, None, false, false);
    for node in &mut module.function_by_id_mut(root).unwrap().blocks[0].body {
        if let trust_ir::Inst::Const {
            value: Constant::FnDef(target),
            ..
        } = &mut node.inst
        {
            *target = FuncId::new(999_999);
        }
    }
    let error = Interpreter::with_module(&module)
        .execute_func(root, [])
        .unwrap_err();
    assert_eq!(error.code, InterpretErrorCode::InvalidFunctionPointer);
}

#[test]
fn sparse_function_ids_use_module_addresses_not_truncated_ids() {
    for bytes in [4, 8] {
        let (mut module, root) = plain(bytes, None, false, false);
        let sparse = FuncId::new(u32::MAX);
        module.function_by_id_mut(FuncId::new(0)).unwrap().id = sparse;
        for node in &mut module.function_by_id_mut(root).unwrap().blocks[0].body {
            if let trust_ir::Inst::Const {
                value: Constant::FnDef(target),
                ..
            } = &mut node.inst
            {
                *target = sparse;
            }
        }
        assert_eq!(run(&module, root), 42);
    }
}

#[test]
fn data_addresses_cannot_alias_a_large_function_namespace() {
    for bytes in [4, 8] {
        let mut m = ModuleBuilder::new("code_data_namespaces");
        let sig = m.add_func_type(vec![], vec![Ty::U64]);
        let root = m.declare_function("root", sig);
        // Exceed both the historical first data address (1024) and the
        // next allocation (1032), so omitting reservation aliases a function.
        for index in 0..1100 {
            m.declare_function(format!("unused{index}"), sig);
        }
        {
            let mut b = m.define_function(root).unwrap();
            let entry = b.create_block();
            b.switch_to_block(entry);
            let slot = b.alloca(Ty::Func(sig));
            let data = b.alloca(Ty::U64);
            let bits = b.cast(trust_ir::CastOp::PtrToInt, Ty::Ptr, Ty::Usize, data);
            b.store(Ty::Usize, slot, bits);
            let code = b.load(Ty::Func(sig), slot);
            let answer = b.call_indirect(code, sig, vec![]);
            b.ret(vec![answer]);
            b.build();
        }
        let module = target(m.build().unwrap(), bytes);
        assert!(validate_module(&module).is_empty());
        let error = Interpreter::with_module(&module)
            .execute_func(root, [])
            .unwrap_err();
        assert_eq!(error.code, InterpretErrorCode::InvalidFunctionPointer);
    }
}

#[test]
fn unsupported_execution_layouts_remain_refused() {
    for (bytes, endian) in [(2, Endianness::Little), (8, Endianness::Big)] {
        let (mut module, root) = plain(8, None, false, false);
        let target = module.target_info.as_mut().unwrap();
        target.pointer_size = bytes;
        target.endianness = endian;
        let error = Interpreter::with_module(&module)
            .execute_func(root, [])
            .unwrap_err();
        assert_eq!(error.code, InterpretErrorCode::UnsupportedMemory);
    }
}
