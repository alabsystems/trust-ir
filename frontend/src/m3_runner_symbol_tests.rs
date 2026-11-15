// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Structural controls for the actual private harness producers. Real THIR
//! lowering remains covered separately by `tests/m3_runner_symbols.rs`.

use super::*;
use std::collections::HashSet;
use trust_ir::{BinOp, Inst, Ty};
use trust_ir_build::{validate_module, ValidationError};

fn quad_source(mb: &mut ModuleBuilder) -> LoweredInstance {
    let sig = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function("quad__i64", sig);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::I64);
    fb.switch_to_block(entry);
    let twice = fb.add(Ty::I64, x, x);
    let four_times = fb.add(Ty::I64, twice, twice);
    fb.ret(vec![four_times]);
    LoweredInstance {
        func_id: fb.build(),
        name: "quad__i64".into(),
        param_tys: vec![Ty::I64],
        ret_ty: Ty::I64,
    }
}

fn fixture(with_runners: bool) -> (Module, Vec<(FuncId, i128)>) {
    let mut mb = ModuleBuilder::new("runner-symbols");
    let source = quad_source(&mut mb);
    let mut cases = Vec::new();
    if with_runners {
        // Both producer entry points may drive the same unary source. Neither
        // a repeated argument nor a change of entry point grants a shared name.
        for input in [3_i128, -7, 1_000_000, i64::MAX as i128, 3] {
            let want = (input as i64).wrapping_mul(4) as i128;
            cases.push((add_unary_runner(&mut mb, &source, input), want));
            cases.push((add_nary_runner(&mut mb, &source, &[input]), want));
        }
    }
    (mb.build().expect("ModuleBuilder::build: test fixture"), cases)
}

#[test]
fn repeated_unary_and_nary_invocations_have_distinct_symbols_and_actual_call_targets() {
    let (module, cases) = fixture(true);
    let errors = validate_module(&module);
    assert!(errors.is_empty(), "{errors:?}");
    let names: HashSet<_> = module
        .functions
        .iter()
        .map(|function| &function.name)
        .collect();
    assert_eq!(names.len(), module.functions.len());
    assert_eq!(module.functions[0].name, "quad__i64");
    for (runner, want) in cases {
        let function = module
            .functions
            .iter()
            .find(|function| function.id == runner)
            .unwrap();
        assert_eq!(function.name, format!("run_quad__i64__f{}", runner.index()));
        let calls: Vec<_> = function
            .instructions()
            .filter_map(|node| match &node.inst {
                Inst::Call { callee, args } => Some((*callee, args.as_slice())),
                _ => None,
            })
            .collect();
        assert_eq!(calls.len(), 1);
        assert_eq!(calls[0].0, module.functions[0].id);
        assert_eq!(calls[0].1.len(), 1);
        assert_eq!(interp_int(&module, runner).unwrap(), want);
    }
}

#[test]
fn fresh_symbols_are_deterministic_and_leave_the_source_body_and_export_unchanged() {
    let (without, _) = fixture(false);
    let (first, _) = fixture(true);
    let (second, _) = fixture(true);
    assert_eq!(first.functions[0], without.functions[0]);
    assert_eq!(format!("{first}"), format!("{second}"));
    let adds = first.functions[0]
        .instructions()
        .filter(|node| {
            matches!(
                node.inst,
                Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    ..
                }
            )
        })
        .count();
    assert_eq!(adds, 2);
}

#[test]
fn duplicate_symbols_are_still_refused_after_the_harness_naming_repair() {
    let (mut module, _) = fixture(true);
    module.functions[1].name = module.functions[0].name.clone();
    assert!(validate_module(&module).iter().any(|error| matches!(
        error, ValidationError::DuplicateFunctionSymbol { name, .. } if name == "quad__i64"
    )));
}
