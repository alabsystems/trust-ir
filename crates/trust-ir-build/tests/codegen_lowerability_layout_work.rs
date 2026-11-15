// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The codegen-lowerability pass asks ONE layout table every layout question
//! it has (`codegen_lowerability_errors_in`).
//!
//! Every `CallIndirect` / `CallIndirectCannotUnwind` / `InvokeIndirect` over
//! a `Ty::Closure` callee asks whether the closure's frame lays out. The pass
//! asked a fresh table per call, so N calls over a closure capturing an
//! N-deep struct chain laid the chain out N times: 4.7 s at N = 4000 and
//! 19 s at N = 8000 in release (x4 per doubling). These tests hold the pass
//! to the table it is given: the table must have laid the chain out (a pass
//! that asked fresh tables leaves it empty) and done O(N) work in all, first
//! at a size where a quadratic pass still ends, then at 10^5 calls over a
//! 10^5-deep chain on a 256 KiB stack.

use trust_ir::ty::{ClosureTy, FieldDef, StructDef, StructRepr, Ty};
use trust_ir::value::StructId;
use trust_ir::{ClosureLayoutDescriptor, Endianness, Module, TargetInfo};
use trust_ir_build::builder::ModuleBuilder;
use trust_ir_build::{
    ValidationError, codegen_lowerability_errors, codegen_lowerability_errors_in,
};

/// `calls` closure applications in one body, over a closure whose one
/// capture is the top of a `depth`-deep newtype chain over `u64`; its frame
/// declared (and coherent) or not.
fn module(depth: u32, calls: u32, declared: bool) -> Module {
    let mut builder = ModuleBuilder::new("codegen_lowerability_layout_work");
    let apparent = builder.add_func_type(vec![], vec![Ty::U64]);
    let closure = builder.add_closure_type(ClosureTy {
        func: apparent,
        captures: vec![Ty::Struct(StructId::new(depth - 1))],
    });
    let sig = builder.add_func_type(vec![Ty::Closure(closure)], vec![]);
    {
        let mut function = builder.function("apply", sig);
        let entry = function.create_block();
        let callee = function.add_block_param(entry, Ty::Closure(closure));
        function.switch_to_block(entry);
        for _ in 0..calls {
            function.call_indirect(callee, apparent, vec![]);
        }
        function.ret(vec![]);
        function.build();
    }
    let mut module = builder.build().expect("ModuleBuilder::build: test fixture");
    module.target_info = Some(TargetInfo {
        triple: "x86_64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    let newtype = |id: u32, ty: Ty| StructDef {
        id: StructId::new(id),
        name: format!("S{id}"),
        fields: vec![FieldDef {
            name: "f".into(),
            ty,
            offset: Some(0),
        }],
        size: Some(8),
        align: Some(8),
        repr: StructRepr::C,
        origin: None,
    };
    module.structs.push(newtype(0, Ty::U64));
    for k in 1..depth {
        module
            .structs
            .push(newtype(k, Ty::Struct(StructId::new(k - 1))));
    }
    if declared {
        module.closure_layouts.push(ClosureLayoutDescriptor {
            origin: None,
            closure,
            size: 8,
            align: 8,
            capture_offsets: vec![0],
        });
    }
    module
}

fn closure_refusals(errors: &[ValidationError]) -> usize {
    errors
        .iter()
        .filter(|error| {
            matches!(
                error,
                ValidationError::UnlowerableForCodegen {
                    inst: "CallIndirect",
                    ..
                }
            )
        })
        .count()
}

/// One pass over `n` calls and an `n`-deep chain, through one table: the
/// verdict is the one-shot entry's, the table laid the chain out, and its
/// work is linear.
fn one_pass(n: u32, declared: bool) {
    let module = module(n, n, declared);
    let table = module.layout_table();
    let errors = codegen_lowerability_errors_in(&table);
    let stats = table.stats();
    let n = n as usize;
    // A declared, coherent frame lifts the refusal at every call; without
    // one every call is refused.
    let expected = if declared { 0 } else { n };
    assert_eq!(closure_refusals(&errors), expected, "{errors:?}");
    assert_eq!(errors.len(), expected, "{errors:?}");
    // The pass asked THIS table, once per call (a pass asking a fresh table
    // per call leaves it untouched) ...
    assert!(stats.steps >= n as u64, "{n}: {stats:?}");
    if declared {
        // ... and laid the capture chain out in it, once, whatever the
        // number of calls (an undeclared frame is refused before any
        // capture is laid out).
        assert!(stats.nodes >= n && stats.nodes <= n + 8, "{n}: {stats:?}");
    } else {
        assert_eq!(stats.nodes, 0, "{n}: {stats:?}");
    }
    assert!(stats.steps <= 8 * n as u64 + 64, "{n}: {stats:?}");
    assert!(stats.definitions_indexed <= n + 8, "{n}: {stats:?}");
    assert_eq!(codegen_lowerability_errors(&module), errors);
}

#[test]
fn every_closure_call_of_a_pass_shares_one_layout_table() {
    for declared in [true, false] {
        for n in [1, 2, 64, 2000] {
            one_pass(n, declared);
        }
    }
}

#[test]
fn a_hundred_thousand_calls_over_a_hundred_thousand_deep_capture_take_one_layout() {
    let worker = std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            for declared in [true, false] {
                one_pass(100_000, declared);
            }
        })
        .expect("spawn");
    worker.join().expect("no stack overflow, linear work");
}
