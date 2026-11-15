// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Standing build/axiom/replay checks for canonical Bool cells and all frame components.
//! These are mathematical component checks, not a source or row certificate.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Mutex;

static LEAN_COMPONENT: Mutex<()> = Mutex::new(());

#[path = "semr_bool_memory/toolchain_cache.rs"]
mod toolchain_cache;

fn lake() -> Option<PathBuf> {
    // Both SemR packages pin Lean 4.30; TrustIR semantics pins 4.8.
    if let Some(explicit) = std::env::var_os("TRUST_IR_SEMR_LAKE") {
        return Some(explicit.into());
    }
    if let Some(explicit) = std::env::var_os("TRUST_IR_LAKE") {
        return Some(explicit.into());
    }
    if let Some(home) = std::env::var_os("HOME") {
        let shim = Path::new(&home).join(".elan/bin/lake");
        if shim.is_file() {
            return Some(shim);
        }
    }
    std::env::split_paths(&std::env::var_os("PATH")?)
        .map(|directory| directory.join("lake"))
        .find(|candidate| candidate.is_file())
}

fn command(lake: &Path, package: &Path) -> Command {
    // A direct native Lake cannot dispatch versions like an elan frontend.
    // The cross-version cache test deliberately builds both canonical packages.
    let pin = std::fs::read_to_string(package.join("lean-toolchain"))
        .expect("package declares its Lean toolchain");
    let explicit = match pin.trim() {
        "leanprover/lean4:v4.8.0" => std::env::var_os("TRUST_IR_LAKE"),
        "leanprover/lean4:v4.30.0-rc2" => std::env::var_os("TRUST_IR_SEMR_LAKE"),
        other if std::env::var_os("TRUST_IR_SEMR_LAKE").is_some() => {
            panic!("no explicit native Lake selection for package pin {other}")
        }
        _ => None,
    };
    let explicit = explicit.map(PathBuf::from);
    let lake = explicit.as_deref().unwrap_or(lake);
    let mut command = Command::new(lake);
    command.current_dir(package).env_remove("SDKROOT");
    if let Some(bin) = lake.parent() {
        let mut path = bin.as_os_str().to_os_string();
        path.push(":");
        path.push(std::env::var_os("PATH").unwrap_or_default());
        command.env("PATH", path);
    }
    command
}

#[test]
fn semr_bool_cells_have_checked_canonical_byte_memory_lemmas() {
    check_component(
        "SemRBoolMemory",
        "BoolMemoryAudit.lean",
        "semr-bool-memory audit: ",
        12,
    );
}

#[test]
fn semr_bool_accesses_use_checked_canonical_wrappers() {
    check_component(
        "SemRBoolAccess",
        "BoolAccessAudit.lean",
        "semr-bool-access audit: ",
        19,
    );
}

#[test]
fn semr_bool_alloca_uses_the_canonical_monadic_instruction() {
    check_component(
        "SemRBoolAlloca",
        "BoolAllocaAudit.lean",
        "semr-bool-alloca audit: ",
        17,
    );
}

#[test]
fn semr_private_bool_heap_preserves_global_mapping_and_freshness() {
    check_component(
        "SemRBoolHeap",
        "BoolHeapAudit.lean",
        "semr-bool-heap audit: ",
        27,
    );
}

#[test]
fn semr_private_frame_libraries_have_complete_kernel_replay() {
    check_component(
        "SemRFrameChecks",
        "FrameAudit.lean",
        "semr-frame audit: ",
        199,
    );
}

#[test]
fn semr_frame_audit_refuses_bad_components_and_authority() {
    let _guard = LEAN_COMPONENT
        .lock()
        .expect("previous Lean component check passed");
    let Some(lake) = lake() else {
        assert_ne!(
            std::env::var("TRUST_IR_REQUIRE_LEAN").as_deref(),
            Ok("1"),
            "TRUST_IR_REQUIRE_LEAN=1 but the SemR-memory proof compiler is missing"
        );
        eprintln!("SKIPPED: the SemR-memory refusal controls need lake (Lean)");
        return;
    };
    let script = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../scripts/semr_frame_refusals.py");
    let output = Command::new("python3")
        .arg(script)
        .arg("--lake")
        .arg(lake)
        .output()
        .expect("run standing frame audit refusal controls");
    let log = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        output.status.success(),
        "frame audit refusal controls failed:\n{log}"
    );
    assert!(log.contains("semr-frame refusals: PASS cases=10"), "{log}");
}

fn check_component(module: &str, audit_file: &str, prefix: &str, required_lemmas: usize) {
    let _guard = LEAN_COMPONENT
        .lock()
        .expect("previous Lean component check passed");
    let Some(lake) = lake() else {
        assert_ne!(
            std::env::var("TRUST_IR_REQUIRE_LEAN").as_deref(),
            Ok("1"),
            "TRUST_IR_REQUIRE_LEAN=1 but the SemR-memory proof compiler is missing"
        );
        eprintln!("SKIPPED: the SemR-memory proof component needs lake (Lean)");
        return;
    };
    let package = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../lean/semr-memory");
    let build = command(&lake, &package)
        .args(["build", module])
        .output()
        .expect("run the package's pinned Lean compiler");
    let build_log = format!(
        "{}{}",
        String::from_utf8_lossy(&build.stdout),
        String::from_utf8_lossy(&build.stderr)
    );
    assert!(
        build.status.success(),
        "SemR-memory build failed:\n{build_log}"
    );
    assert!(
        !build_log.contains("declaration uses 'sorry'"),
        "{build_log}"
    );
    let audit = command(&lake, &package)
        .args(["env", "lean", audit_file])
        .output()
        .expect("audit every declared model constant");
    let audit_log = format!(
        "{}{}",
        String::from_utf8_lossy(&audit.stdout),
        String::from_utf8_lossy(&audit.stderr)
    );
    assert!(
        audit.status.success(),
        "SemR-memory audit failed:\n{audit_log}"
    );
    assert!(
        !audit_log.contains("declaration uses 'sorry'"),
        "{audit_log}"
    );
    let records: Vec<_> = audit_log
        .lines()
        .filter_map(|line| line.split_once(prefix).map(|(_, record)| record))
        .collect();
    assert_eq!(
        records.len(),
        1,
        "one complete kernel audit required:\n{audit_log}"
    );
    let fields: BTreeMap<_, _> = records[0]
        .split_whitespace()
        .map(|field| {
            let (key, value) = field.split_once('=').expect("typed audit field");
            (key, value.parse::<usize>().expect("integer audit count"))
        })
        .collect();
    assert_eq!(fields.len(), 4, "complete audit accounting: {fields:?}");
    assert!(fields["declarations"] > 0, "empty audit: {fields:?}");
    assert!(
        fields["theorems"] >= required_lemmas,
        "missing required lemmas: {fields:?}"
    );
    assert_eq!(fields["replayed"], fields["declarations"], "{fields:?}");
    assert_eq!(fields["native-evaluations"], 0, "{fields:?}");
}
