// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for `trust-ir validate`.

mod common;

use std::fs;

use tempfile::tempdir;

use common::{build_diagnostics_module, build_invalid_module, build_valid_module, trust_ir_cmd};

#[test]
fn validate_valid_module_exits_zero() {
    let dir = tempdir().expect("tempdir");
    let path = dir.path().join("ok.tmbc");
    let bytes = trust_ir::binary::serialize_module(&build_valid_module())
        .expect("serialize_module: test fixture");
    fs::write(&path, bytes).expect("write");

    let output = trust_ir_cmd()
        .arg("validate")
        .arg(&path)
        .output()
        .expect("run trust-ir");
    assert!(
        output.status.success(),
        "expected exit 0, got {:?}\nstdout: {}\nstderr: {}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("ok:"),
        "stdout should report ok, got: {stdout}"
    );
}

#[test]
fn validate_invalid_module_exits_nonzero_with_stderr() {
    let dir = tempdir().expect("tempdir");
    let path = dir.path().join("bad.tmbc");
    let bytes = trust_ir::binary::serialize_module(&build_invalid_module())
        .expect("serialize_module: test fixture");
    fs::write(&path, bytes).expect("write");

    let output = trust_ir_cmd()
        .arg("validate")
        .arg(&path)
        .output()
        .expect("run trust-ir");
    assert!(
        !output.status.success(),
        "expected nonzero exit, got success\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("validation failed"),
        "stderr should explain validation failure, got: {stderr}"
    );
    assert!(
        stderr.contains("BlockMissingTerminator") || stderr.contains("EmptyFunction"),
        "stderr should mention the specific validation error, got: {stderr}"
    );
}

#[test]
fn validate_reports_rendered_obligation_diagnostics_without_failing() {
    let dir = tempdir().expect("tempdir");
    let path = dir.path().join("diag.tmbc");
    let bytes = trust_ir::binary::serialize_module(&build_diagnostics_module())
        .expect("serialize_module: test fixture");
    fs::write(&path, bytes).expect("write");

    let output = trust_ir_cmd()
        .arg("validate")
        .arg(&path)
        .output()
        .expect("run trust-ir");
    // Diagnostics are module data being reported, not a validation verdict.
    assert!(
        output.status.success(),
        "diagnostics must not change the exit code\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("obligation diagnostics (2):"),
        "stderr should announce the diagnostics report, got: {stderr}"
    );
    assert!(
        stderr.contains(
            "src/main.rs:12:5: error: could not prove a + b stays in range \
             [counterexample: a=i64::MAX, b=1]"
        ),
        "stderr should render path:line:col: severity: message [detail], got: {stderr}"
    );
    assert!(
        stderr.contains("note: see verifier transcript"),
        "a location-less diagnostic renders without a path prefix, got: {stderr}"
    );
}

#[test]
fn validate_missing_file_exits_nonzero() {
    let output = trust_ir_cmd()
        .arg("validate")
        .arg("/nonexistent/path/to/module.trust_ir")
        .output()
        .expect("run trust-ir");
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("error:"),
        "expected error message, got: {stderr}"
    );
}

#[test]
fn validate_explicit_json_format() {
    let dir = tempdir().expect("tempdir");
    // Intentionally use a non-standard extension so format detection would fail
    // without the --format override.
    let path = dir.path().join("module.weird");
    let bytes = serde_json::to_vec(&build_valid_module()).expect("json");
    fs::write(&path, bytes).expect("write");

    let output = trust_ir_cmd()
        .arg("validate")
        .arg("--format")
        .arg("json")
        .arg(&path)
        .output()
        .expect("run trust-ir");
    assert!(
        output.status.success(),
        "expected exit 0, got {:?}\nstderr: {}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
}

/// Roadmap WS4.1 (F-066), audit row `a.format.text_parser_utf8` (skeptic
/// c09), standing gate 3 (`cli-gate-tests`): `validate --format
/// text` on a module whose `;` comment carried ONE multi-byte character used
/// to exit 101 (an unwinding panic at `parser.rs` `advance`) instead of the
/// documented exit 0 / parse-error exit 2. The ratchet in the 2026-09-17 proof
/// program asserted rc 101; ported here it asserts the CLI contract holds:
/// exit 0 for the well-formed module, exit 2 with `text parse error` for its
/// malformed twin, and never 101 for either.
#[test]
fn validate_text_with_multibyte_comment_never_panics() {
    let dir = tempdir().expect("tempdir");

    // The proof program's exact specimen (parta/attrib/text_utf8_comment.trust_ir):
    // an empty module behind an em-dash comment. Well-formed => exit 0.
    let specimen = dir.path().join("text_utf8_comment.trust_ir");
    fs::write(
        &specimen,
        "; TrustIr text format v1\n; a comment with one multi-byte character: \u{2014}\nmodule \"parta-utf8-comment\"\n",
    )
    .expect("write");

    // Roadmap WS4.1's named case: a `; é` file. Well-formed => exit 0.
    let e_acute = dir.path().join("e_acute_comment.trust_ir");
    fs::write(&e_acute, "; \u{e9}\nmodule \"m\"\n").expect("write");

    // A real module behind an `é` / em dash / emoji comment, with a trailing
    // non-ASCII node comment. Well-formed => exit 0.
    let module_text = build_valid_module().to_string();
    let ok_path = dir.path().join("ok.trust_ir");
    let mut ret_seen = false;
    let ok_text: String = format!("; caf\u{e9} \u{2014} \u{1f600}\n{module_text}")
        .lines()
        .map(|line| {
            if !ret_seen && line.trim_start().starts_with("ret ") {
                ret_seen = true;
                format!("{line} ; \u{e9} \u{2014} \u{1f600}\n")
            } else {
                format!("{line}\n")
            }
        })
        .collect();
    assert!(ret_seen, "fixture has a `ret` line:\n{module_text}");
    fs::write(&ok_path, ok_text).expect("write");

    for path in [&e_acute, &specimen, &ok_path] {
        let output = trust_ir_cmd()
            .arg("validate")
            .arg("--format")
            .arg("text")
            .arg(path)
            .output()
            .expect("run trust-ir");
        assert_ne!(
            output.status.code(),
            Some(101),
            "panic exit on {}",
            path.display()
        );
        assert!(
            output.status.success(),
            "expected exit 0 for {}, got {:?}\nstdout: {}\nstderr: {}",
            path.display(),
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }

    // Close negative twin: the same non-ASCII comment, but the module body is
    // malformed (a `✝` in the symbol position). Exit 2 with a parse error —
    // a refusal, not a crash.
    let bad_path = dir.path().join("bad.trust_ir");
    let bad_text = format!(
        "; caf\u{e9}\n{}",
        module_text.replacen("fn @add(", "fn @add\u{271d}(", 1)
    );
    fs::write(&bad_path, bad_text).expect("write");
    let output = trust_ir_cmd()
        .arg("validate")
        .arg("--format")
        .arg("text")
        .arg(&bad_path)
        .output()
        .expect("run trust-ir");
    assert_eq!(
        output.status.code(),
        Some(2),
        "expected parse-error exit 2, got {:?}\nstderr: {}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("text parse error") && !stderr.contains("panicked"),
        "expected a parse error, got: {stderr}"
    );
}

// ---------------------------------------------------------------------------
// WS4.18 (F-081): repair options under each refusal
// ---------------------------------------------------------------------------

/// The `options:` line the printer must emit for `err`: every option of
/// `ValidationError::repair_options`, joined by `"; "`, indented under the
/// numbered error line.
fn expected_options_line(err: &trust_ir_build::validate::ValidationError) -> String {
    let options = err.repair_options();
    assert!(!options.is_empty(), "fixture variant must carry options");
    format!("      options: {}", options.join("; "))
}

/// The line immediately after the first stderr line that names `needle`.
fn line_after(stderr: &str, needle: &str) -> Option<String> {
    let mut lines = stderr.lines();
    lines.find(|line| line.contains(needle))?;
    lines.next().map(str::to_string)
}

/// Positive: a module with an FFI boundary and no pinned target is refused
/// with `TargetInfoRequired`, and the enumerated ways forward are printed
/// directly under that refusal. The exit code is unchanged by them.
#[test]
fn validate_prints_repair_options_under_a_refusal_that_has_them() {
    let mut mb = trust_ir_build::ModuleBuilder::new("ffi_without_target");
    let ft = mb.add_func_type(vec![trust_ir::ty::Ty::I64], vec![trust_ir::ty::Ty::I64]);
    mb.declare_function("ext", ft);
    let module = mb.build().expect("ModuleBuilder::build: test fixture");

    let dir = tempdir().expect("tempdir");
    let path = dir.path().join("ffi.tmbc");
    fs::write(
        &path,
        trust_ir::binary::serialize_module(&module).expect("serialize_module: test fixture"),
    )
    .expect("write");
    let output = trust_ir_cmd()
        .arg("validate")
        .arg(&path)
        .output()
        .expect("run trust-ir");
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    let stderr = String::from_utf8_lossy(&output.stderr);
    let expected = expected_options_line(
        &trust_ir_build::validate::ValidationError::TargetInfoRequired {
            boundary: String::new(),
        },
    );
    assert_eq!(
        line_after(&stderr, "TargetInfoRequired").as_deref(),
        Some(expected.as_str()),
        "the options line must sit directly under the refusal: {stderr}"
    );
}

/// Negative twin: a refusal whose variant enumerates no options
/// (`EmptyFunction` / `BlockMissingTerminator`) prints no `options:` line at
/// all — an absent list is never rendered as an empty one.
#[test]
fn validate_prints_no_options_line_for_a_refusal_without_options() {
    let dir = tempdir().expect("tempdir");
    let path = dir.path().join("bad.tmbc");
    fs::write(
        &path,
        trust_ir::binary::serialize_module(&build_invalid_module())
            .expect("serialize_module: test fixture"),
    )
    .expect("write");
    let output = trust_ir_cmd()
        .arg("validate")
        .arg(&path)
        .output()
        .expect("run trust-ir");
    assert!(!output.status.success(), "{output:?}");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("validation failed"), "{stderr}");
    assert!(
        !stderr.contains("options:"),
        "no option-bearing refusal here, so no options line: {stderr}"
    );
}

/// The `--link` printer is the same printer: an import row whose dependency
/// was not supplied is `ImportUnavailable`, with its options under it.
#[test]
fn validate_link_prints_repair_options_under_an_unavailable_import() {
    let supplied = build_valid_module();
    let mut ghost = build_valid_module();
    ghost.name = "ghost".into();
    let mut importer = trust_ir::Module::new("importer");
    importer
        .intern_import(
            trust_ir::ModuleImport::new("ghost", ghost.stable_digest())
                .with_producer(trust_ir::Producer::TRust),
        )
        .expect("Module::intern_import: test fixture");

    let dir = tempdir().expect("tempdir");
    let dep_path = dir.path().join("dep.tmbc");
    let root_path = dir.path().join("importer.tmbc");
    fs::write(
        &dep_path,
        trust_ir::binary::serialize_module(&supplied).expect("serialize_module: test fixture"),
    )
    .expect("write dep");
    fs::write(
        &root_path,
        trust_ir::binary::serialize_module(&importer).expect("serialize_module: test fixture"),
    )
    .expect("write root");
    let output = trust_ir_cmd()
        .arg("validate")
        .arg("--link")
        .arg(&dep_path)
        .arg(&root_path)
        .output()
        .expect("run trust-ir");
    assert!(!output.status.success(), "{output:?}");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("linked validation failed"), "{stderr}");
    let expected = expected_options_line(
        &trust_ir_build::validate::ValidationError::ImportUnavailable {
            import: 0,
            name: String::new(),
        },
    );
    assert_eq!(
        line_after(&stderr, "ImportUnavailable").as_deref(),
        Some(expected.as_str()),
        "{stderr}"
    );
    // Adversarial review: a file WAS supplied here, just not the recorded
    // one (the set is keyed by digest, so a wrong file is "unavailable", not
    // a mismatch). "Supply the dependency" alone would send the reader round
    // in a circle; the options must name the wrong-file case and the digest
    // the `link:` line printed.
    assert!(
        expected.contains("already supplied with `--link`")
            && expected.contains("the digest the `link:` line prints"),
        "{expected}"
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains(&format!("digest {}", supplied.stable_digest())),
        "the `link:` line the option points at must exist: {stdout}"
    );
}
