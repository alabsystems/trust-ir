// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Actual THIR source drives four calls of one generic instance in M4. This
//! focused check does not claim the separately failing M3/multi-root owner
//! symbols are fixed, or replace the full real-lowering acceptance gate.

#![feature(rustc_private)]

use std::path::Path;
use trust_ir::{Inst, Ty};

mod support;
use support::{artifact_only_driver_command, trust_toolchain};

#[test]
fn actual_callchain_repeated_runners_validate_and_keep_the_published_source_exports() {
    let toolchain = trust_toolchain();
    let corpus = Path::new(env!("CARGO_MANIFEST_DIR")).join("m3_corpus.rs");
    let output_path =
        Path::new(env!("CARGO_TARGET_TMPDIR")).join("actual_callchain_runner_symbols.tir");
    let mut command =
        artifact_only_driver_command(env!("CARGO_BIN_EXE_trust_ir_frontend"), &toolchain);
    command
        .arg("--m3")
        .arg("--emit-callchain")
        .arg(&output_path)
        .arg(&corpus);
    let output = command.output().expect("actual THIR driver");
    let mut diagnostic = String::from_utf8_lossy(&output.stdout).into_owned();
    diagnostic.push_str(&String::from_utf8_lossy(&output.stderr));
    assert!(output.status.success(), "{diagnostic}");
    assert!(
        diagnostic.contains("M4 RESULT: ALL MATCH, 0 validate errors"),
        "{diagnostic}"
    );
    for check in [
        "[MATCH] quad::<i64>(3): ir=12 oracle=12",
        "[MATCH] quad::<i64>(-7): ir=-28 oracle=-28",
        "[MATCH] quad::<i64>(1000000): ir=4000000 oracle=4000000",
        "[MATCH] quad::<i64>(9223372036854775807): ir=-4 oracle=-4",
    ] {
        assert!(diagnostic.contains(check), "{diagnostic}");
    }
    assert!(diagnostic.contains("EMIT-CALLCHAIN: wrote"), "{diagnostic}");
    let text = std::fs::read_to_string(&output_path).expect("newly emitted callchain");
    let module = trust_ir::parser::parse_module(&text).expect("lossless callchain text");
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "{errors:?}");
    assert_eq!(module.functions.len(), 2);
    assert_eq!(module.functions[0].name, "quad__i64");
    assert_eq!(module.functions[1].name, "double__i64");
    let calls: Vec<_> = module.functions[0]
        .instructions()
        .filter_map(|node| match node.inst {
            Inst::Call { callee, .. } => Some(callee),
            _ => None,
        })
        .collect();
    assert_eq!(calls, vec![module.functions[1].id; 2]);
    assert!(module.functions[1].instructions().any(|node| matches!(
        node.inst,
        Inst::BinOp {
            op: trust_ir::BinOp::Add,
            ty: Ty::I64,
            ..
        }
    )));
}
