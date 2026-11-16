// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// CallIndirect.calling_conv: the indirect-call ABI declaration (a direct Call's
// convention is the callee Function's calling_conv; an indirect call has no
// statically-known callee, so it declares the expected ABI). Round-trips
// through binary; the conformance corpus (inst_control) covers all formats.

#![cfg(feature = "binary")]

use trust_ir::inst::Inst;
use trust_ir::{CallingConv, Ty};
use trust_ir_build::ModuleBuilder;

/// Back-compat: a serde blob produced before `calling_conv` existed (pre-v12)
/// has no such key/element. The field carries `#[serde(default)]`, so it must
/// deserialize to `CallingConv::C` rather than failing with "missing field".
#[cfg(feature = "serde")]
#[test]
fn call_indirect_missing_calling_conv_deserializes_as_c() {
    use trust_ir::value::{FuncTyId, ValueId};
    let inst = Inst::CallIndirect {
        callee: ValueId::new(0),
        sig: FuncTyId::new(0),
        args: vec![ValueId::new(1)],
        calling_conv: CallingConv::Swift,
    };
    // Round-trip to JSON, then strip the key to emulate a legacy blob.
    let mut json = serde_json::to_value(&inst).expect("serialize");
    let removed = json["CallIndirect"]
        .as_object_mut()
        .expect("CallIndirect object")
        .remove("calling_conv");
    assert!(
        removed.is_some(),
        "fixture must have had a calling_conv key"
    );
    let back: Inst =
        serde_json::from_value(json).expect("legacy CallIndirect without calling_conv must parse");
    match back {
        Inst::CallIndirect { calling_conv, .. } => assert_eq!(calling_conv, CallingConv::C),
        other => panic!("expected CallIndirect, got {other:?}"),
    }
}

#[test]
fn call_indirect_cc_round_trips_binary() {
    let mut mb = ModuleBuilder::new("cc");
    // helper signature: (i32) -> i32
    let helper = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let ft = mb.add_func_type(vec![Ty::Ptr, Ty::I32], vec![Ty::I32]);
    {
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        let fptr = fb.add_block_param(entry, Ty::Ptr);
        let x = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        let r = fb.call_indirect_cc(fptr, helper, vec![x], CallingConv::Swift);
        fb.ret(vec![r]);
        fb.build();
    }
    let m = mb.build().expect("ModuleBuilder::build: test fixture");

    // The builder recorded the declared ABI.
    match &m.functions[0].blocks[0].body[0].inst {
        Inst::CallIndirect { calling_conv, .. } => assert_eq!(*calling_conv, CallingConv::Swift),
        other => panic!("expected CallIndirect, got {other:?}"),
    }

    let bytes = trust_ir::binary::serialize_module(&m).expect("serialize_module: test fixture");
    let back = trust_ir::binary::deserialize_module(&bytes).expect("binary round trip");
    match &back.functions[0].blocks[0].body[0].inst {
        Inst::CallIndirect { calling_conv, .. } => assert_eq!(*calling_conv, CallingConv::Swift),
        other => panic!("expected CallIndirect, got {other:?}"),
    }

    // The default builder method keeps the C convention.
    let mut mb2 = ModuleBuilder::new("cc2");
    let helper2 = mb2.add_func_type(vec![], vec![]);
    let ft2 = mb2.add_func_type(vec![Ty::Ptr], vec![]);
    {
        let mut fb = mb2.function("g", ft2);
        let entry = fb.create_block();
        let fptr = fb.add_block_param(entry, Ty::Ptr);
        fb.switch_to_block(entry);
        fb.call_indirect_void(fptr, helper2, vec![]);
        fb.ret(vec![]);
        fb.build();
    }
    let m2 = mb2.build().expect("ModuleBuilder::build: test fixture");
    match &m2.functions[0].blocks[0].body[0].inst {
        Inst::CallIndirect { calling_conv, .. } => assert_eq!(*calling_conv, CallingConv::C),
        other => panic!("expected CallIndirect, got {other:?}"),
    }
}

// These are ordinary reference-interpreter controls. They do not establish
// compiler source binding, native ABI correctness or proof authority.
mod runtime_aggregate_cc {
    use trust_ir::interpret::{InterpretErrorCode, InterpretValueKind, Interpreter};
    use trust_ir::{
        CallingConv, Constant, Endianness, FuncId, FuncTyId, Module, StructPassingPolicy,
        TargetInfo, Ty,
    };
    use trust_ir_build::{ModuleBuilder, validate_module};

    fn fixture(edge: CallingConv) -> (Module, FuncId, FuncId, FuncId, FuncTyId) {
        let mut builder = ModuleBuilder::new("dynamic_aggregate_calling_convention");
        let signature = builder.add_func_type(vec![], vec![Ty::U64]);
        let tuple = Ty::Tuple(vec![Ty::Func(signature)]);
        let maker_signature = builder.add_func_type(vec![], vec![tuple.clone()]);
        let consumer_signature = builder.add_func_type(vec![tuple.clone()], vec![Ty::U64]);
        let leaf7 = builder.declare_function("leaf7", signature);
        let leaf9 = builder.declare_function("leaf9", signature);
        let maker = builder.declare_function("maker", maker_signature);
        let consumer = builder.declare_function("consumer", consumer_signature);
        assert_ne!(leaf7, leaf9);

        for (target, answer) in [(leaf7, 7u128), (leaf9, 9u128)] {
            let mut function = builder.define_function(target).unwrap();
            function.set_calling_conv(CallingConv::Rust);
            let entry = function.create_block();
            function.switch_to_block(entry);
            let value = function.uconst(Ty::U64, answer);
            function.ret(vec![value]);
            function.build();
        }
        {
            let mut function = builder.define_function(maker).unwrap();
            function.set_calling_conv(CallingConv::Rust);
            let entry = function.create_block();
            function.switch_to_block(entry);
            let seed = function.const_value(
                tuple.clone(),
                Constant::Aggregate(vec![Constant::FnDef(leaf7)]),
            );
            let replacement = function.fn_addr(signature, leaf9);
            let updated = function.insert_field(tuple.clone(), seed, 0, replacement);
            function.ret(vec![updated]);
            function.build();
        }
        {
            let mut function = builder.define_function(consumer).unwrap();
            function.set_calling_conv(CallingConv::Rust);
            let entry = function.create_block();
            let argument = function.add_block_param(entry, tuple);
            function.switch_to_block(entry);
            let pointer = function.extract_field(Ty::Func(signature), argument, 0);
            // The target is dynamic in this body: no constant or synthetic
            // argument lets static target recovery stand in for the runtime check.
            let answer = function.call_indirect_cc(pointer, signature, vec![], edge);
            function.ret(vec![answer]);
            function.build();
        }
        let mut module = builder.build().expect("complete test module");
        module.target_info = Some(TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: None,
            struct_passing: StructPassingPolicy::Unclassified,
        });
        (module, maker, consumer, leaf9, signature)
    }

    #[test]
    fn dynamic_tuple_pointer_checks_edge_convention_after_real_field_write_and_return() {
        // Run the matching control first; the unchanged interpreter is expected
        // to fail only the mismatching C-edge assertion below.
        for edge in [CallingConv::Rust, CallingConv::C] {
            let (module, maker, consumer, replacement, signature) = fixture(edge);
            let errors = validate_module(&module);
            assert!(
                errors.is_empty(),
                "the actual module must validate first: {errors:?}"
            );
            let header = module.func_type(signature).unwrap();
            assert!(header.abi.is_none() && !header.is_vararg);
            assert!(header.params.is_empty());
            assert_eq!(header.returns, vec![Ty::U64]);
            assert!(module.functions.iter().all(|function| {
                function.calling_conv == CallingConv::Rust && function.body_gate.is_none()
            }));

            let interpreter = Interpreter::with_module(&module);
            let produced = interpreter
                .execute_func(maker, [])
                .expect("the real maker body must execute");
            assert_eq!(produced.host_calls, 0);
            assert_eq!(produced.returns.len(), 1);
            {
                let value = &produced.returns[0];
                assert_eq!(value.ty, Ty::Tuple(vec![Ty::Func(signature)]));
                let InterpretValueKind::Aggregate(fields) = &value.kind else {
                    panic!("the maker must return its actual aggregate");
                };
                assert_eq!(fields.len(), 1);
                assert_eq!(fields[0].ty, Ty::Func(signature));
                assert_eq!(
                    fields[0].kind,
                    InterpretValueKind::FnDef(replacement),
                    "the returned field must contain leaf9, not the original leaf7 seed",
                );
            }
            // Supply the actual returned tuple, rather than constructing a
            // conveniently typed function-pointer input outside the program.
            let result = interpreter.execute_func(consumer, produced.returns);
            if edge == CallingConv::Rust {
                let outcome = result.expect("the matching Rust edge must call the returned leaf9");
                assert_eq!(outcome.host_calls, 0);
                assert_eq!(outcome.returns.len(), 1);
                assert_eq!(outcome.returns[0].ty, Ty::U64);
                assert_eq!(outcome.returns[0].as_int().unwrap().as_unsigned(), 9);
            } else {
                let error = result.expect_err(
                    "a dynamic C edge must reject the actual Rust target before executing it",
                );
                assert_eq!(error.code, InterpretErrorCode::SignatureMismatch);
            }
        }
    }
}
