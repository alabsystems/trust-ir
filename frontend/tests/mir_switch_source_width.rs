// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Actual MIR switch extraction: host64 Isize and the unchanged U128 chain.
//! Pure unit controls separately retain source32/selector64 typed refusal;
//! this is not a new 32-bit ABI or cross-target executable support claim.

#![feature(rustc_private)]

use std::path::Path;
use trust_ir::{Constant, FuncId, Inst, Module, Ty};

mod support;
use support::{artifact_only_driver_command, trust_toolchain};

fn emit(symbol: &str) -> Module {
    let toolchain = trust_toolchain();
    let corpus =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/switch_source_width_corpus.rs");
    let outpath = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("source_width_{symbol}.tir"));
    let mut command = artifact_only_driver_command(env!("CARGO_BIN_EXE_trust_ir_mir"), &toolchain);
    command
        .arg("--mir-emit-closure")
        .arg(symbol)
        .arg(&outpath)
        .arg("--crate-type=lib")
        .arg(&corpus);
    let output = command.output().expect("spawn the linked Trust MIR driver");
    let mut diagnostic = String::from_utf8_lossy(&output.stdout).into_owned();
    diagnostic.push_str(&String::from_utf8_lossy(&output.stderr));
    // Assert this extraction actually ran before reading its output; a stale
    // artifact cannot turn a failed/missing driver invocation into a pass.
    assert!(
        output.status.success() && diagnostic.contains("EMIT-CLOSURE-OK"),
        "{symbol}: actual lowering failed: {diagnostic}"
    );
    assert!(
        diagnostic.contains("validate_module = 0 error(s)"),
        "{symbol}: actual emitted module failed validation: {diagnostic}"
    );
    let text = std::fs::read_to_string(&outpath).expect("read this successful extraction");
    let module = trust_ir::parser::parse_module(&text).expect("parse the actual module");
    assert!(trust_ir_build::validate_module(&module).is_empty());
    module
}
fn function(module: &Module, symbol: &str) -> FuncId {
    let matches = module
        .functions
        .iter()
        .filter(|function| function.name.ends_with(symbol))
        .collect::<Vec<_>>();
    assert_eq!(matches.len(), 1, "one original function {symbol}");
    matches[0].id
}
fn run(module: &Module, function: FuncId, ty: Ty, value: u128) -> i128 {
    // InterpretValue::int constructs the actual bit pattern at the nominal
    // type; the cast preserves all 128 bits, including U128's top bit.
    let input = trust_ir::interpret::InterpretValue::int(ty, value as i128).unwrap();
    let outcome = trust_ir::interpret::Interpreter::with_module(module)
        .execute_func(function, vec![input])
        .unwrap();
    outcome
        .returns
        .first()
        .and_then(|value| value.as_int())
        .unwrap()
        .as_signed()
}

#[test]
fn actual_host_isize_switch_uses_signed_case_values_and_interprets_every_arm() {
    let module = emit("signed_pointer_match");
    let pointer_bits = module
        .target_info
        .as_ref()
        .expect("actual target pin")
        .pointer_size
        * 8;
    assert_eq!(
        pointer_bits, 64,
        "this real fixture qualifies the existing 64-bit scalar lane; source32/I64 remains refused"
    );
    let id = function(&module, "signed_pointer_match");
    let lowered = module
        .functions
        .iter()
        .find(|function| function.id == id)
        .unwrap();
    let mut cases = lowered
        .instructions()
        .filter_map(|node| match &node.inst {
            Inst::Switch { cases, .. } => Some(cases),
            _ => None,
        })
        .flatten()
        .map(|case| match &case.value {
            Constant::Int(value) => *value,
            other => panic!("the signed selector must keep a signed value, got {other:?}"),
        })
        .collect::<Vec<_>>();
    cases.sort_unstable();
    assert_eq!(cases, [i128::from(i64::MIN), -1, 5]);
    for (value, expected) in [(i64::MIN, 20), (-1, 10), (5, 30), (0, 0), (i64::MAX, 0)] {
        assert_eq!(run(&module, id, Ty::I64, value as u128), expected);
    }
}

#[test]
fn actual_u128_switch_keeps_the_existing_canonical_eq_branch_chain() {
    let module = emit("unsigned_wide_match");
    let id = function(&module, "unsigned_wide_match");
    let lowered = module
        .functions
        .iter()
        .find(|function| function.id == id)
        .unwrap();
    assert!(
        !lowered
            .instructions()
            .any(|node| matches!(node.inst, Inst::Switch { .. })),
        "the existing wide-selector legalization is not replaced"
    );
    for bits in [1_u128 << 127, u128::MAX] {
        assert!(
            lowered.instructions().any(|node| matches!(&node.inst,
            Inst::Const { ty: Ty::U128, value: Constant::U128(value) } if *value == bits)),
            "retain canonical U128 magnitude {bits}"
        );
    }
    for (value, expected) in [
        (u128::MAX, 10),
        (1_u128 << 127, 20),
        (5, 30),
        (0, 0),
        (6, 0),
    ] {
        assert_eq!(run(&module, id, Ty::U128, value), expected);
    }
}
