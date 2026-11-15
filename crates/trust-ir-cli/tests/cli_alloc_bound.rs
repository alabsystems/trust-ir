// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `trust-ir validate`'s allocation-size advisory (`trust_ir::alloc_bound`),
//! end to end: it reports on every target, inside or outside the canonical
//! scalar-alignment table, and never changes the exit code.

mod common;

use std::fs;

use tempfile::tempdir;

use common::trust_ir_cmd;

/// One function allocating `count` elements of `u64` on the stack and `u8`
/// on the heap, with an unchecked `u64` count, on `triple`.
fn module(triple: &str, pointer_size: u32) -> String {
    format!(
        "; TrustIr text format v1\n\
         module \"probe\"\n\n\
         target \"{triple}\" {pointer_size} little\n\n\
         functy.0 = (u64) -> ()\n\n\
         fn @f(functy.0) {{\n\
         bb0(%0: u64):\n    \
             %1 = alloca u64, %0\n    \
             %2 = heap_alloc rust_heap u8, %0\n    \
             ret\n\
         }}\n"
    )
}

#[test]
fn the_advisory_reports_on_targets_off_the_alignment_table() {
    let dir = tempdir().expect("tempdir");
    for (triple, pointer_size) in [
        ("x86_64-unknown-linux-gnu", 8),
        ("wasm32-unknown-unknown", 4),
        ("i686-unknown-linux-gnu", 4),
        ("armv7-unknown-linux-gnueabihf", 4),
        ("riscv32imac-unknown-none-elf", 4),
        ("powerpc64le-unknown-linux-gnu", 8),
        ("s390x-unknown-linux-gnu", 8),
    ] {
        let path = dir.path().join(format!("{triple}.trust_ir"));
        fs::write(&path, module(triple, pointer_size)).expect("write");
        let output = trust_ir_cmd()
            .arg("validate")
            .arg(&path)
            .output()
            .expect("run trust-ir validate");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            output.status.success(),
            "{triple}: the advisory never fails validation\nstdout: {stdout}\nstderr: {stderr}"
        );
        assert!(stdout.contains("ok:"), "{triple}: {stdout}");
        let limit = (1u128 << (pointer_size * 8 - 1)) - 1;
        assert!(
            stderr.contains(
                "note: 2 allocations whose size no bound keeps within the target's largest object"
            ),
            "{triple}: {stderr}"
        );
        assert!(
            stderr.contains(&format!("{limit}-byte object limit")),
            "{triple}: {stderr}"
        );
    }
}
