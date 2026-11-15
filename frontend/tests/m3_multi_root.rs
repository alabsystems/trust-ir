// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Production M3 and per-nominal-family M5.7f consumers of typed batching.
//! This does not replace the entire real-lowering acceptance gate or claim
//! native execution, checked source semantics, or general multi-enum lowering.

#![feature(rustc_private)]

use std::path::Path;
mod support;
use support::{artifact_only_driver_command, trust_toolchain};

#[test]
fn actual_multi_root_families_validate_and_preserve_the_legacy_construct_export() {
    let toolchain = trust_toolchain();
    let corpus = Path::new(env!("CARGO_MANIFEST_DIR")).join("m3_corpus.rs");
    let output_path = Path::new(env!("CARGO_TARGET_TMPDIR")).join("actual_batched_construct.tir");
    match std::fs::remove_file(&output_path) {
        Ok(()) => {}
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(error) => panic!(
            "remove prior construct export {}: {error}",
            output_path.display()
        ),
    }
    let mut command =
        artifact_only_driver_command(env!("CARGO_BIN_EXE_trust_ir_frontend"), &toolchain);
    command
        .arg("--m3")
        .arg("--emit-construct")
        .arg(&output_path)
        .arg(&corpus);
    let output = command.output().expect("actual multi-root source driver");
    let mut diagnostic = String::from_utf8_lossy(&output.stdout).into_owned();
    diagnostic.push_str(&String::from_utf8_lossy(&output.stderr));
    assert!(output.status.success(), "{diagnostic}");
    for result in [
        "M3 RESULT: ALL MATCH, 0 validate errors",
        "M4 RESULT: ALL MATCH, 0 validate errors",
        "M5.7f RESULT: ALL MATCH, 0 validate errors",
    ] {
        assert!(diagnostic.contains(result), "{diagnostic}");
    }
    for check in [
        "[MATCH] call_yes() [-> <Yes as Predicate>::pred]: ir=true oracle=true",
        "[MATCH] call_no() [-> <No as Predicate>::pred]: ir=false oracle=false",
        "[MATCH] one_depth() builds Succ(Zero) -> 1: ir=1 oracle=1",
        "[MATCH] two_depth() builds Succ(Succ(Zero)) -> 2: ir=2 oracle=2",
        "[MATCH] nbox_nil_depth() builds niche-encoded Nil -> 0: ir=0 oracle=0",
        "[MATCH] nbox_two_depth() builds untagged Cons(Cons(Nil)) -> 2: ir=2 oracle=2",
    ] {
        assert!(diagnostic.contains(check), "{diagnostic}");
    }
    assert!(diagnostic.contains("EMIT-CONSTRUCT: wrote"), "{diagnostic}");
    let text = std::fs::read_to_string(&output_path).expect("fresh legacy construct export");
    let module = trust_ir::parser::parse_module(&text).expect("lossless construct export");
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "{errors:?}");
    assert!(module
        .functions
        .iter()
        .any(|function| function.name == "two_depth__i64"));
    let folders: Vec<_> = module
        .functions
        .iter()
        .filter(|function| function.name == "count_succ__i64")
        .collect();
    assert_eq!(
        folders.len(),
        1,
        "legacy JIT consumers still have one exact export"
    );
}
