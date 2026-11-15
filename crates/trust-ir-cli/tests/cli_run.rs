// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for `trust-ir run` — the multi-module linker + reference
//! interpreter execution front (the emit-each battery oracle).

mod common;

// The two-language fixtures (roadmap WS4.6 tests): the proof-carrying b4
// cross-crate pair and the b5 `Nat` handle program, shared with the
// conformance crate and `two_language_cli` by path.
#[path = "../../trust-ir-conformance/tests/two_language/b4_fixtures.rs"]
mod b4_fixtures;
#[path = "../../trust-ir-conformance/tests/two_language/b5_fixtures.rs"]
mod b5_fixtures;

use std::fs;
use std::path::Path;

use tempfile::{TempDir, tempdir};

use common::trust_ir_cmd;
use trust_ir::Module;
use trust_ir::proof::{
    ObligationKind, ProofAnnotation, ProofContext, ProofObligation, ProofStatus,
};
use trust_ir::ty::Ty;
use trust_ir::value::ProofId;
use trust_ir_build::ModuleBuilder;

fn write_module(dir: &Path, name: &str, text: &str) {
    fs::write(dir.join(name), text).expect("write module");
}

fn run_dir(dir: &Path) -> std::process::Output {
    trust_ir_cmd()
        .arg("run")
        .arg(dir)
        .output()
        .expect("run trust-ir")
}

#[test]
fn links_declaration_against_definition_across_modules() {
    let dir = tempdir().expect("tempdir");
    // Module A: `program` calls a DECLARED-only @helper.
    write_module(
        dir.path(),
        "a.trust_ir",
        r#"; TrustIr text format v1
module "a"

functy.0 = (i64) -> (i64)

functy.1 = () -> (i64)

fn @helper(functy.0) {
}

fn @program(functy.1) {
bb0:
    %1 = const i64 41
    %2 = call @func.0(%1)
    ret %2
}
"#,
    );
    // Module B: the definition of @helper (adds 1).
    write_module(
        dir.path(),
        "b.trust_ir",
        r#"; TrustIr text format v1
module "b"

functy.0 = (i64) -> (i64)

fn @helper(functy.0) {
bb0(%0: i64):
    %1 = const i64 1
    %2 = add i64 %0, %1
    ret %2
}
"#,
    );

    let out = run_dir(dir.path());
    assert!(
        out.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&out.stdout).trim(), "42");
}

#[test]
fn conflicting_definitions_are_a_link_error() {
    let dir = tempdir().expect("tempdir");
    let def = |value: i64| {
        format!(
            r#"; TrustIr text format v1
module "m{value}"

functy.0 = () -> (i64)

fn @helper(functy.0) {{
bb0:
    %1 = const i64 {value}
    ret %1
}}
"#
        )
    };
    write_module(dir.path(), "a.trust_ir", &def(1));
    write_module(dir.path(), "b.trust_ir", &def(2));
    // A `program` entry so resolution gets past loading.
    write_module(
        dir.path(),
        "c.trust_ir",
        r#"; TrustIr text format v1
module "c"

functy.0 = () -> (i64)

fn @program(functy.0) {
bb0:
    %1 = const i64 0
    ret %1
}
"#,
    );

    let out = run_dir(dir.path());
    assert!(!out.status.success());
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("conflicting definitions of @helper"),
        "stderr: {stderr}"
    );
}

#[test]
fn identical_duplicate_definitions_are_deduped() {
    let dir = tempdir().expect("tempdir");
    let def = r#"; TrustIr text format v1
module "m"

functy.0 = () -> (i64)

fn @helper(functy.0) {
bb0:
    %1 = const i64 5
    ret %1
}
"#;
    write_module(dir.path(), "a.trust_ir", def);
    write_module(dir.path(), "b.trust_ir", def);
    write_module(
        dir.path(),
        "c.trust_ir",
        r#"; TrustIr text format v1
module "c"

functy.0 = () -> (i64)

functy.1 = () -> (i64)

fn @helper(functy.0) {
}

fn @program(functy.1) {
bb0:
    %1 = call @func.0()
    ret %1
}
"#,
    );

    let out = run_dir(dir.path());
    assert!(
        out.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&out.stdout).trim(), "5");
}

#[test]
fn calling_a_bodyless_extern_traps_with_its_name() {
    let dir = tempdir().expect("tempdir");
    write_module(
        dir.path(),
        "t.trust_ir",
        r#"; TrustIr text format v1
module "t"

functy.0 = () -> ()

functy.1 = () -> (i64)

fn @mystery_extern(functy.0) {
}

fn @program(functy.1) {
bb0:
    call @func.0()
    %1 = const i64 7
    ret %1
}
"#,
    );

    let out = run_dir(dir.path());
    assert!(!out.status.success());
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("trap: reached extern builtin stub @mystery_extern"),
        "stderr: {stderr}"
    );
}

#[test]
fn bool_icmp_is_legalized_and_executes() {
    let dir = tempdir().expect("tempdir");
    // `icmp eq bool` is valid format-side but outside the interpreter's
    // integer comparator; `run` legalizes it into selects.
    write_module(
        dir.path(),
        "m.trust_ir",
        r#"; TrustIr text format v1
module "m"

functy.0 = () -> (i64)

fn @program(functy.0) {
bb0:
    %1 = const bool true
    %2 = const bool false
    %3 = icmp eq bool %1, %2
    %4 = const bool true
    %5 = icmp eq bool %4, %4
    %6 = const i64 10
    %7 = const i64 1
    %8 = select i64 %3, %6, %7
    %9 = const i64 100
    %10 = select i64 %5, %9, %7
    %11 = add i64 %8, %10
    ret %11
}
"#,
    );

    let out = run_dir(dir.path());
    assert!(
        out.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    // eq(true,false) = false -> 1; eq(true,true) = true -> 100.
    assert_eq!(String::from_utf8_lossy(&out.stdout).trim(), "101");
}

#[test]
fn rust_alloc_builtin_maps_to_interpreter_heap() {
    let dir = tempdir().expect("tempdir");
    write_module(
        dir.path(),
        "m.trust_ir",
        r#"; TrustIr text format v1
module "m"

functy.0 = (u64, u64) -> (ptr)

functy.1 = (ptr, u64, u64) -> ()

functy.2 = () -> (i64)

fn @_RNvCsoF1AqU8Qvp_7___rustc12___rust_alloc(functy.0) {
}

fn @_RNvCsoF1AqU8Qvp_7___rustc14___rust_dealloc(functy.1) {
}

fn @program(functy.2) {
bb0:
    %1 = const u64 16
    %2 = const u64 8
    %3 = call @func.0(%1, %2)
    %4 = const i64 12345
    store i64 %4, ptr %3
    %5 = load i64, ptr %3
    call @func.1(%3, %1, %2)
    ret %5
}
"#,
    );

    let out = run_dir(dir.path());
    assert!(
        out.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&out.stdout).trim(), "12345");
}

#[test]
fn missing_entry_is_a_user_error() {
    let dir = tempdir().expect("tempdir");
    write_module(
        dir.path(),
        "m.trust_ir",
        r#"; TrustIr text format v1
module "m"

functy.0 = () -> (i64)

fn @not_program(functy.0) {
bb0:
    %1 = const i64 3
    ret %1
}
"#,
    );

    let out = run_dir(dir.path());
    assert!(!out.status.success());
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("no function named @program"),
        "stderr: {stderr}"
    );

    // The same image runs with an explicit --entry.
    let out = trust_ir_cmd()
        .arg("run")
        .arg(dir.path())
        .arg("--entry")
        .arg("not_program")
        .output()
        .expect("run trust-ir");
    assert!(
        out.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&out.stdout).trim(), "3");
}

// ---------------------------------------------------------------------------
// WS4.6: import authentication, proof-claim stripping, two validation passes,
// pinned trusted-runtime entry points stay bodyless
// ---------------------------------------------------------------------------

/// The captured result of one `trust-ir run` over binary modules.
struct RunResult {
    code: Option<i32>,
    stdout: String,
    stderr: String,
}

/// Write `modules` as `.bin` files into a fresh temp dir (kept alive by the
/// returned guard) and run `trust-ir run --format bin <flags> <files..>`.
fn run_modules(modules: &[&Module], flags: &[&str]) -> (TempDir, RunResult) {
    let dir = tempdir().expect("tempdir");
    let mut cmd = trust_ir_cmd();
    cmd.args(["run", "--format", "bin"]).args(flags);
    for (i, module) in modules.iter().enumerate() {
        let path = dir.path().join(format!("{i:02}.bin"));
        fs::write(
            &path,
            trust_ir::binary::serialize_module(module).expect("serialize_module: test fixture"),
        )
        .expect("write module");
        cmd.arg(path);
    }
    let out = cmd.output().expect("run trust-ir");
    let result = RunResult {
        code: out.status.code(),
        stdout: String::from_utf8_lossy(&out.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
    };
    (dir, result)
}

/// F-067 positive: the honest proof-carrying `[dep, root]` pair, whose dep
/// carries kernel-certified `proved` summaries, links, authenticates both
/// import rows, validates as linked AND after lowering, and runs. The image
/// carries no proof claims: the four summaries (two definitions, two
/// declarations) are stripped and counted.
#[test]
fn run_validate_accepts_an_honest_proved_pair_and_strips_its_proof_claims() {
    let dep = b4_fixtures::build_dep(3);
    let (root, _) = b4_fixtures::build_root(&dep, true);
    let (_dir, out) = run_modules(&[&dep, &root], &["--validate"]);
    assert_eq!(out.code, Some(0), "stderr: {}", out.stderr);
    assert_eq!(out.stdout.trim(), "48");
    for line in [
        "imports: 2 row(s) authenticated against the linked inputs by digest",
        "stripped 4 summaries / 0 ProofRefs / 0 call proof contexts (an execution image carries \
         no proof claims; re-earn them with `trust-ir validate --link`)",
        "linked image is well-formed (as linked)",
        "lowered image is well-formed",
    ] {
        assert!(
            out.stderr.contains(line),
            "missing {line:?} in: {}",
            out.stderr
        );
    }
}

/// F-067 "broader" (source row b4.uf10): a SINGLE import-free module with an
/// honest kernel-certified `proved` summary used to fail `run --validate`
/// with `InvalidFunctionSummary`, because the runner dropped its obligations
/// and kept the summary. It now validates and runs.
#[test]
fn b4_uf10_single_import_free_proved_module_runs_under_validate() {
    let dep = b4_fixtures::build_dep(3);
    assert!(dep.imports.is_empty(), "the fixture is import-free");
    let (_dir, out) = run_modules(
        &[&dep],
        &["--validate", "--entry", b4_fixtures::SCALE, "--arg", "2"],
    );
    assert_eq!(out.code, Some(0), "stderr: {}", out.stderr);
    assert_eq!(out.stdout.trim(), "6");
    assert!(
        out.stderr.contains("stripped 2 summaries"),
        "{}",
        out.stderr
    );
    assert!(
        !out.stderr.contains("InvalidFunctionSummary"),
        "{}",
        out.stderr
    );
    assert!(
        !out.stderr.contains("imports:"),
        "no rows, no import line: {}",
        out.stderr
    );
}

/// F-067 negative twin: the root pins the OLD dep digest and is linked with
/// the REBUILT dep (`dep_scale` factor 3 -> 2). The row matches no linked
/// input, so the run is refused by name before anything links or runs.
#[test]
fn run_refuses_an_import_row_whose_digest_matches_no_linked_input() {
    let dep = b4_fixtures::build_dep(3);
    let (root, _) = b4_fixtures::build_root(&dep, true);
    let rebuilt = b4_fixtures::tampered_dep();
    let (_dir, out) = run_modules(&[&rebuilt, &root], &[]);
    assert_eq!(out.code, Some(1), "stderr: {}", out.stderr);
    assert!(out.stdout.is_empty(), "nothing runs: {}", out.stdout);
    let expected = format!(
        r#"import.0 "b4_dep" pins digest {}, which matches no linked input (inputs: b4_dep={}, b4_root={}); link the exact dependency artifact, or pass --unauthenticated-imports (the image then carries no proof claims either way)"#,
        dep.stable_digest(),
        rebuilt.stable_digest(),
        root.stable_digest(),
    );
    assert!(out.stderr.contains(&expected), "stderr: {}", out.stderr);
    assert!(
        !out.stderr.contains("stripped"),
        "refused before linking: {}",
        out.stderr
    );
}

/// The escape hatch: `--unauthenticated-imports` runs the same mismatched
/// pair (the rebuilt dependency's value, 32) and reports every row UNCHECKED —
/// execution only, never agreement.
#[test]
fn unauthenticated_imports_runs_the_mismatched_pair_and_reports_rows_unchecked() {
    let dep = b4_fixtures::build_dep(3);
    let (root, _) = b4_fixtures::build_root(&dep, true);
    let rebuilt = b4_fixtures::tampered_dep();
    let (_dir, out) = run_modules(&[&rebuilt, &root], &["--unauthenticated-imports"]);
    assert_eq!(out.code, Some(0), "stderr: {}", out.stderr);
    assert_eq!(out.stdout.trim(), "32");
    assert!(
        out.stderr
            .contains("imports: 2 row(s) UNCHECKED (execution only; this is not agreement)"),
        "stderr: {}",
        out.stderr
    );
    assert!(!out.stderr.contains("authenticated"), "{}", out.stderr);
}

/// A row whose digest DOES match an input is still checked C4–C6: renaming
/// the recorded dependency (same digest) is refused with the
/// `ImportVerificationError::NameMismatch` text.
#[test]
fn run_refuses_an_import_row_that_matches_by_digest_but_fails_the_name_check() {
    let dep = b4_fixtures::build_dep(3);
    let (mut root, _) = b4_fixtures::build_root(&dep, true);
    for import in &mut root.imports {
        import.name = "b4_dep_renamed".to_string();
    }
    let (_dir, out) = run_modules(&[&dep, &root], &[]);
    assert_eq!(out.code, Some(1), "stderr: {}", out.stderr);
    assert!(out.stdout.is_empty());
    assert!(
        out.stderr.contains(
            r#"import.0 "b4_dep_renamed": import #0: candidate module is named "b4_dep", import records "b4_dep_renamed""#
        ),
        "stderr: {}",
        out.stderr
    );
}

/// C2 is named before "no match": a row recording a non-SHA-256 digest can
/// match no input by construction, so it is refused with the
/// `UnsupportedDigestAlgorithm` text instead.
#[test]
fn run_refuses_an_import_row_whose_digest_is_not_sha256_by_name() {
    let dep = b4_fixtures::build_dep(3);
    let (mut root, _) = b4_fixtures::build_root(&dep, true);
    root.imports[0].digest.algorithm = trust_ir::proof::ProofDigestAlgorithm::TrustIrStableV1;
    let (_dir, out) = run_modules(&[&dep, &root], &[]);
    assert_eq!(out.code, Some(1), "stderr: {}", out.stderr);
    assert!(
        out.stderr.contains(
            "import #0 records a trust_ir-stable-v1 digest; only SHA-256 identifies a module"
        ),
        "stderr: {}",
        out.stderr
    );
    assert!(
        !out.stderr.contains("matches no linked input"),
        "{}",
        out.stderr
    );
}

/// `ProofRef`s (function- and node-level) and call `ProofContext`s name
/// module obligations, which the image does not carry: they are stripped and
/// counted, while claim-style annotations stay. Without the strip, the linked
/// image fails `--validate` (`ProofRefUnresolved`,
/// `ProofContextUnknownObligation`).
#[test]
fn run_strips_proof_refs_and_call_proof_contexts_from_the_image() {
    let mut mb = ModuleBuilder::new("refs");
    let unary = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let nullary = mb.add_func_type(vec![], vec![Ty::U64]);
    let callee = {
        let mut fb = mb.function("callee", unary);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        fb.ret(vec![x]);
        fb.build()
    };
    let program = {
        let mut fb = mb.function("program", nullary);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let five = fb.uconst(Ty::U64, 5);
        let out = fb.call(callee, vec![five]);
        fb.ret(vec![out]);
        fb.build()
    };
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Precondition,
            ProofStatus::Pending,
            "callee precondition",
        )
        .with_function(callee),
    );
    let func = module.function_by_id_mut(program).expect("program");
    func.proofs = vec![
        ProofAnnotation::NoPanic,
        ProofAnnotation::ProofRef(ProofId::new(0)),
    ];
    let call = func.blocks[0]
        .body
        .iter_mut()
        .find(|node| matches!(node.inst, trust_ir::inst::Inst::Call { .. }))
        .expect("the call node");
    call.proofs = vec![
        ProofAnnotation::NoPanic,
        ProofAnnotation::ProofRef(ProofId::new(0)),
    ];
    call.proof_context = Some(ProofContext {
        assumes: vec![],
        establishes: vec![ProofId::new(0)],
    });

    let (_dir, out) = run_modules(&[&module], &["--validate"]);
    assert_eq!(out.code, Some(0), "stderr: {}", out.stderr);
    assert_eq!(out.stdout.trim(), "5");
    assert!(
        out.stderr
            .contains("stripped 0 summaries / 2 ProofRefs / 1 call proof contexts"),
        "stderr: {}",
        out.stderr
    );
    assert!(
        out.stderr
            .contains("linked image is well-formed (as linked)")
    );
}

/// F-083 handle positive: the `Nat` program validates under `run --validate`
/// (as linked and after lowering: the pinned entry points are never stubbed,
/// so `HandleEntryPointDefinedLocally` is not raised), then — with no host
/// model (the default `--host none`) — exits 1 with a named refusal at the
/// first trusted-runtime entry point it reaches: never "trap stub", and never
/// the interpreter's raw `unsupported_call` (WS2.12). Executing it is
/// `--host pinned` (WS2.13 / F-035, below).
#[test]
fn nat_handle_program_validates_then_refuses_by_name_at_a_trusted_runtime_entry() {
    let module = b5_fixtures::nat_program();
    for flags in [&["--validate"][..], &[][..]] {
        let (_dir, out) = run_modules(&[&module], flags);
        assert_eq!(out.code, Some(1), "{flags:?} stderr: {}", out.stderr);
        assert!(out.stdout.is_empty(), "{flags:?}: {}", out.stdout);
        assert!(
            out.stderr.contains(
                "error: reached trusted-runtime entry point @trust_bignum_nat_from_u64 — the \
                 reference interpreter has no host implementation (TRUST.md items 9 and 13; \
                 `run` installs no host model unless `--host pinned` selects the reference \
                 model)"
            ),
            "{flags:?} stderr: {}",
            out.stderr
        );
        // Every pinned entry point the module declares (the whole row: derived,
        // since WS3.2 widened it from five roles) stays bodyless.
        let pinned = trust_ir_build::TRUSTED_HANDLE_RUNTIMES[0]
            .entry_points
            .len();
        assert!(
            out.stderr.contains(&format!(
                "0 trap stub(s), {pinned} trusted-runtime entry point(s)"
            )),
            "{flags:?} stderr: {}",
            out.stderr
        );
        assert!(!out.stderr.contains("trap:"), "{flags:?}: {}", out.stderr);
        assert!(
            !out.stderr.contains("interpreter error:"),
            "{flags:?}: {}",
            out.stderr
        );
        assert!(
            !out.stderr.contains("HandleEntryPointDefinedLocally"),
            "{flags:?}: {}",
            out.stderr
        );
        if flags.contains(&"--validate") {
            assert!(
                out.stderr
                    .contains("linked image is well-formed (as linked)")
            );
            assert!(out.stderr.contains("lowered image is well-formed"));
        }
    }
}

/// WS2.13 (F-035): `--host pinned` installs the reference model of the pinned
/// runtimes, and the same `Nat` program EXECUTES to the native value (1),
/// with and without `--validate`. The run is reported host-assisted, with
/// the interpreter's own count of served calls, and every pinned entry point
/// still stays bodyless (the model serves declarations; it defines nothing).
#[test]
fn nat_handle_program_executes_under_the_pinned_host_model() {
    let module = b5_fixtures::nat_program();
    let pinned = trust_ir_build::TRUSTED_HANDLE_RUNTIMES[0]
        .entry_points
        .len();
    for flags in [
        &["--validate", "--host", "pinned"][..],
        &["--host", "pinned"][..],
    ] {
        let (_dir, out) = run_modules(&[&module], flags);
        assert_eq!(out.code, Some(0), "{flags:?} stderr: {}", out.stderr);
        assert_eq!(out.stdout.trim(), "1", "{flags:?}");
        assert!(
            out.stderr.contains(
                "call(s) served by the pinned reference host model (a trusted model of the \
                 runtime, TRUST.md items 9 and 13; this run is not in-format execution evidence)"
            ),
            "{flags:?} stderr: {}",
            out.stderr
        );
        assert!(
            out.stderr.contains(&format!(
                "0 trap stub(s), {pinned} trusted-runtime entry point(s)"
            )),
            "{flags:?} stderr: {}",
            out.stderr
        );
        if flags.contains(&"--validate") {
            assert!(out.stderr.contains("lowered image is well-formed"));
        }
    }
    // The handle-free analog under the same flag reports NO host-assisted line:
    // the count is the interpreter's, and an in-format run is zero.
    let (_dir, out) = run_modules(&[&b5_fixtures::u64_program()], &["--host", "pinned"]);
    assert_eq!(out.code, Some(0), "stderr: {}", out.stderr);
    assert_eq!(out.stdout.trim(), "1");
    assert!(!out.stderr.contains("host-assisted"), "{}", out.stderr);
}

/// WS2.13 twin: under `--host pinned` a pinned symbol declared with a
/// signature other than the pinned one is NOT served — the run is refused by
/// name, saying so — and `--validate` refuses the module before it runs.
#[test]
fn a_mis_declared_pinned_symbol_is_not_served_by_the_pinned_host_model() {
    let mut mb = ModuleBuilder::new_with_target_info("bad_nat", b5_fixtures::target());
    let sig = mb.add_func_type(vec![Ty::U64], vec![Ty::Ptr]);
    let from = mb.declare_function("trust_bignum_nat_from_u64", sig);
    let nullary = mb.add_func_type(vec![], vec![Ty::Ptr]);
    let mut fb = mb.function("program", nullary);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let k = fb.uconst(Ty::U64, 1);
    let p = fb.call(from, vec![k]);
    fb.ret(vec![p]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let (_dir, out) = run_modules(&[&module], &["--host", "pinned"]);
    assert_eq!(out.code, Some(1), "stderr: {}", out.stderr);
    assert!(out.stdout.is_empty());
    assert!(
        out.stderr.contains(
            "error: reached trusted-runtime entry point @trust_bignum_nat_from_u64, which the \
             pinned reference host model does not serve: its declaration does not carry the \
             exact pinned signature and calling convention"
        ),
        "{}",
        out.stderr
    );
    let (_dir, out) = run_modules(&[&module], &["--host", "pinned", "--validate"]);
    assert_eq!(out.code, Some(1), "stderr: {}", out.stderr);
    assert!(
        out.stderr.contains("HandleEntryPointSignatureMismatch"),
        "{}",
        out.stderr
    );
}

/// WS2.13: the pinned Clean RC triple (`clean_inc` / `clean_dec` /
/// `clean_is_exclusive`) is never stubbed either — a trap stub would DEFINE
/// the pinned symbol and fail the post-lowering validation as this tool's own
/// defect (`RcEntryPointDefinedLocally`, exit 3). It stays bodyless: under
/// `--host none` reaching it is the named refusal; under `--host pinned` the
/// interpreter counts the `HeapAlloc(CleanHeap)` cell itself.
#[test]
fn pinned_rc_entry_points_stay_bodyless_and_execute_under_the_pinned_host() {
    use trust_ir::inst::AllocOrigin;
    let mut mb = ModuleBuilder::new_with_target_info("clean_rc_cli", b5_fixtures::target());
    let pin = trust_ir_build::TRUSTED_RC_RUNTIMES
        .iter()
        .find(|pin| pin.origin == AllocOrigin::CleanHeap)
        .expect("the Clean RC row");
    let mut ids = std::collections::BTreeMap::new();
    for entry in pin.entry_points {
        let ty = mb.add_func_type(entry.params.to_vec(), entry.returns.to_vec());
        ids.insert(entry.role, mb.declare_function(entry.symbol, ty));
    }
    let nullary = mb.add_func_type(vec![], vec![Ty::U8]);
    let mut fb = mb.function("program", nullary);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let cell = fb.heap_alloc(Ty::U64, None, None, AllocOrigin::CleanHeap);
    fb.call_void(ids["retain"], vec![cell]);
    let shared = fb.call(ids["is_unique"], vec![cell]); // 0
    fb.call_void(ids["release"], vec![cell]);
    let unique = fb.call(ids["is_unique"], vec![cell]); // 1
    let two = fb.uconst(Ty::U8, 2);
    let doubled = fb.mul(Ty::U8, unique, two);
    let out = fb.add(Ty::U8, shared, doubled);
    fb.call_void(ids["release"], vec![cell]);
    fb.ret(vec![out]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");

    let (_dir, out) = run_modules(&[&module], &["--validate"]);
    assert_eq!(out.code, Some(1), "stderr: {}", out.stderr);
    assert!(
        out.stderr.contains("lowered image is well-formed"),
        "{}",
        out.stderr
    );
    assert!(
        out.stderr
            .contains("0 trap stub(s), 3 trusted-runtime entry point(s)"),
        "{}",
        out.stderr
    );
    assert!(
        out.stderr
            .contains("error: reached trusted-runtime entry point @clean_inc"),
        "{}",
        out.stderr
    );
    assert!(
        !out.stderr.contains("RcEntryPointDefinedLocally"),
        "{}",
        out.stderr
    );

    let (_dir, out) = run_modules(&[&module], &["--validate", "--host", "pinned"]);
    assert_eq!(out.code, Some(0), "stderr: {}", out.stderr);
    assert_eq!(out.stdout.trim(), "2");
    assert!(
        out.stderr.contains("host-assisted: 5 call(s) served"),
        "{}",
        out.stderr
    );
}

/// WS2.13 review: a pinned entry point NAMED AS THE ENTRY (`--entry
/// trust_bignum_nat_from_u64 --arg 5`) is executed as a host call under
/// `--host pinned` — the bodyless-entry branch of `cmd_run` that the model
/// unlocks — and the returned handle renders OPAQUELY (`handle(#id, ty)`,
/// never a number or an address). Under the default `--host none` the same
/// invocation is the named refusal, and a pinned symbol that is NOT the
/// exact declaration is refused by name even as the entry.
#[test]
fn a_pinned_entry_point_named_as_the_entry_executes_under_the_pinned_host_model() {
    let module = b5_fixtures::nat_program();
    let (_dir, out) = run_modules(
        &[&module],
        &[
            "--host",
            "pinned",
            "--entry",
            "trust_bignum_nat_from_u64",
            "--arg",
            "5",
        ],
    );
    assert_eq!(out.code, Some(0), "stderr: {}", out.stderr);
    assert_eq!(
        out.stdout.trim(),
        "handle(#0, handle<\"Nat\", \"trust_bignum::Nat\">)",
        "stderr: {}",
        out.stderr
    );
    assert!(
        out.stderr.contains("host-assisted: 1 call(s) served"),
        "{}",
        out.stderr
    );

    let (_dir, out) = run_modules(
        &[&module],
        &["--entry", "trust_bignum_nat_from_u64", "--arg", "5"],
    );
    assert_eq!(out.code, Some(1), "stderr: {}", out.stderr);
    assert!(out.stdout.is_empty());
    assert!(
        out.stderr.contains(
            "error: reached trusted-runtime entry point @trust_bignum_nat_from_u64 — the \
             reference interpreter has no host implementation"
        ),
        "{}",
        out.stderr
    );

    // The mis-declared twin as the entry: not served, refused by name.
    let mut mb = ModuleBuilder::new_with_target_info("bad_nat_entry", b5_fixtures::target());
    let sig = mb.add_func_type(vec![Ty::U64], vec![Ty::Ptr]);
    mb.declare_function("trust_bignum_nat_from_u64", sig);
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let (_dir, out) = run_modules(
        &[&module],
        &[
            "--host",
            "pinned",
            "--entry",
            "trust_bignum_nat_from_u64",
            "--arg",
            "5",
        ],
    );
    assert_eq!(out.code, Some(1), "stderr: {}", out.stderr);
    assert!(out.stdout.is_empty());
    assert!(
        out.stderr.contains(
            "error: reached trusted-runtime entry point @trust_bignum_nat_from_u64, which the \
             pinned reference host model does not serve"
        ),
        "{}",
        out.stderr
    );
}

/// Source row b5.uf06: the handle-free twin of the same program (every pinned
/// call replaced by the machine operation) still validates and runs, so the
/// refusal above is about the unhosted runtime and nothing else.
#[test]
fn b5_uf06_handle_free_analog_validates_and_runs() {
    let module = b5_fixtures::u64_program();
    let (_dir, out) = run_modules(&[&module], &["--validate"]);
    assert_eq!(out.code, Some(0), "stderr: {}", out.stderr);
    assert_eq!(out.stdout.trim(), "1");
    assert!(
        out.stderr.contains("0 trusted-runtime entry point(s)"),
        "{}",
        out.stderr
    );
}

// ---------------------------------------------------------------------------
// WS4.6 review: adversarial inputs the increment's own tests did not cover
// ---------------------------------------------------------------------------

/// A module named `name`, pinned to the b4 target and produced by tRust,
/// that defines `export() -> u64` as `import() + add` (or the constant `add`
/// when `import` is `None`), and records `import`'s dependency row.
fn chain_link(name: &str, export: &str, import: Option<(&str, &Module)>, add: u128) -> Module {
    use trust_ir::{ModuleImport, Producer};
    let mut mb = ModuleBuilder::new_with_target_info(name, b4_fixtures::target());
    mb.set_default_producer(Producer::TRust);
    let nullary = mb.add_func_type(vec![], vec![Ty::U64]);
    let callee = import.map(|(symbol, _)| mb.declare_function(symbol, nullary));
    let mut fb = mb.function(export, nullary);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let k = fb.uconst(Ty::U64, add);
    let out = match callee {
        Some(callee) => {
            let far = fb.call(callee, vec![]);
            fb.add(Ty::U64, far, k)
        }
        None => k,
    };
    fb.ret(vec![out]);
    fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    if let Some((_, dep)) = import {
        module
            .intern_import(
                ModuleImport::new(dep.name.clone(), dep.stable_digest())
                    .with_producer(Producer::TRust),
            )
            .expect("Module::intern_import: test fixture");
    }
    module
}

/// Review (adversarial): authentication covers EVERY input's rows, not just
/// the entry module's. `root -> mid -> leaf`: linked whole, both rows
/// authenticate and the chain runs (5 + 1 + 1 = 7). Linked with a REBUILT
/// leaf, the ROOT's row still authenticates, but MID's row matches no input
/// and the run is refused naming mid, before anything runs.
#[test]
fn run_authenticates_every_input_rows_including_a_dependency_of_a_dependency() {
    let leaf = chain_link("leaf", "leaf_k", None, 5);
    let mid = chain_link("mid", "mid_f", Some(("leaf_k", &leaf)), 1);
    let root = chain_link("root", "program", Some(("mid_f", &mid)), 1);

    let (_dir, out) = run_modules(&[&leaf, &mid, &root], &["--validate"]);
    assert_eq!(out.code, Some(0), "stderr: {}", out.stderr);
    assert_eq!(out.stdout.trim(), "7");
    assert!(
        out.stderr
            .contains("imports: 2 row(s) authenticated against the linked inputs by digest"),
        "{}",
        out.stderr
    );

    let rebuilt_leaf = chain_link("leaf", "leaf_k", None, 50);
    let (_dir, out) = run_modules(&[&rebuilt_leaf, &mid, &root], &[]);
    assert_eq!(out.code, Some(1), "stderr: {}", out.stderr);
    assert!(out.stdout.is_empty(), "nothing runs: {}", out.stdout);
    assert!(
        out.stderr.contains(&format!(
            r#"import.0 "leaf" pins digest {}, which matches no linked input"#,
            leaf.stable_digest()
        )),
        "stderr: {}",
        out.stderr
    );
    assert!(out.stderr.contains("01.bin: import.0"), "{}", out.stderr);
}

/// Review (adversarial): a digest match is necessary, not sufficient. The
/// dependency row is authentic by digest and name but records NO producer:
/// it is refused with the C5 `ProducerUnrecorded` text, not waved through.
#[test]
fn run_refuses_a_digest_matched_import_row_that_records_no_producer() {
    let leaf = chain_link("leaf", "leaf_k", None, 5);
    let mut root = chain_link("root", "program", Some(("leaf_k", &leaf)), 1);
    root.imports[0].producer = None;
    let (_dir, out) = run_modules(&[&leaf, &root], &[]);
    assert_eq!(out.code, Some(1), "stderr: {}", out.stderr);
    assert!(out.stdout.is_empty());
    assert!(
        out.stderr.contains(r#"import.0 "leaf": import #0"#)
            && !out.stderr.contains("matches no linked input"),
        "stderr: {}",
        out.stderr
    );
}

/// Review (adversarial): identity is the MODULE, not the transport. The
/// honest b4 pair converted to JSON and to MessagePack authenticates exactly
/// as the binary pair does (a transport that perturbed `stable_digest` would
/// refuse a legitimate link).
#[test]
fn run_authenticates_the_honest_pair_through_json_and_msgpack() {
    let dep = b4_fixtures::build_dep(3);
    let (root, _) = b4_fixtures::build_root(&dep, true);
    let dir = tempdir().expect("tempdir");
    for (format, ext) in [("json", "json"), ("msgpack", "msgpack")] {
        let mut cmd = trust_ir_cmd();
        cmd.args(["run", "--format", format, "--validate"]);
        for (i, module) in [&dep, &root].into_iter().enumerate() {
            let bin = dir.path().join(format!("{i:02}.bin"));
            let converted = dir.path().join(format!("{i:02}.{ext}"));
            fs::write(
                &bin,
                trust_ir::binary::serialize_module(module).expect("serialize_module: test fixture"),
            )
            .expect("write");
            let convert = trust_ir_cmd()
                .args(["convert", "--from", "bin", "--to", format])
                .arg(&bin)
                .arg(&converted)
                .output()
                .expect("convert");
            assert!(
                convert.status.success(),
                "{format}: {}",
                String::from_utf8_lossy(&convert.stderr)
            );
            cmd.arg(converted);
        }
        let out = cmd.output().expect("run");
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert_eq!(out.status.code(), Some(0), "{format}: {stderr}");
        assert_eq!(String::from_utf8_lossy(&out.stdout).trim(), "48");
        assert!(
            stderr.contains("imports: 2 row(s) authenticated against the linked inputs by digest"),
            "{format}: {stderr}"
        );
    }
}

/// Review (adversarial): entering a pinned trusted-runtime entry point
/// DIRECTLY (it is the `--entry`) is the same named refusal, not a generic
/// missing-block interpreter error.
#[test]
fn run_entry_that_is_a_pinned_runtime_entry_point_is_a_named_refusal() {
    let module = b5_fixtures::nat_program();
    let (_dir, out) = run_modules(
        &[&module],
        &[
            "--validate",
            "--entry",
            "trust_bignum_nat_from_u64",
            "--arg",
            "7",
        ],
    );
    assert_eq!(out.code, Some(1), "stderr: {}", out.stderr);
    assert!(out.stdout.is_empty());
    assert!(
        out.stderr
            .contains("error: reached trusted-runtime entry point @trust_bignum_nat_from_u64"),
        "stderr: {}",
        out.stderr
    );
    assert!(!out.stderr.contains("interpreter error:"), "{}", out.stderr);
}

/// Review (adversarial): an input that FORGES a pinned symbol — here a
/// handle-free module declaring `trust_bignum_nat_add` at a machine-word
/// signature — is the INPUT's defect. `run --validate` refuses it AS LINKED
/// (exit 1, the named `HandleEntryPointSignatureMismatch`), never as an
/// `internal:` lowering defect (exit 3). Without `--validate` the run still
/// fails closed by name: the forged declaration is not given a trap stub.
#[test]
fn run_validate_classifies_a_forged_pinned_symbol_as_the_inputs_defect() {
    let mut mb = ModuleBuilder::new_with_target_info("forge", b4_fixtures::target());
    let binary = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let nullary = mb.add_func_type(vec![], vec![Ty::U64]);
    let forged = mb.declare_function("trust_bignum_nat_add", binary);
    let mut fb = mb.function("program", nullary);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let a = fb.uconst(Ty::U64, 1);
    let b = fb.uconst(Ty::U64, 2);
    let sum = fb.call(forged, vec![a, b]);
    fb.ret(vec![sum]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");

    let (_dir, out) = run_modules(&[&module], &["--validate"]);
    assert_eq!(out.code, Some(1), "stderr: {}", out.stderr);
    assert!(
        out.stderr
            .contains("validation of linked image failed (as linked;")
            && out.stderr.contains("HandleEntryPointSignatureMismatch")
            && !out.stderr.contains("internal:"),
        "stderr: {}",
        out.stderr
    );

    let (_dir, out) = run_modules(&[&module], &[]);
    assert_eq!(out.code, Some(1), "stderr: {}", out.stderr);
    assert!(
        out.stderr
            .contains("error: reached trusted-runtime entry point @trust_bignum_nat_add")
            && !out.stderr.contains("trap:"),
        "stderr: {}",
        out.stderr
    );
}

/// A module whose `program` returns 3 beside a bodyless `prelude_contract`
/// declaration with INTERNAL linkage, carrying `summary` (a contract-only
/// declaration, valid by the validator's audit-F4 rule, when `Some`).
fn module_with_internal_prelude(summary: Option<trust_ir::FunctionSummary>) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("prelude", b4_fixtures::target());
    let unary = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let nullary = mb.add_func_type(vec![], vec![Ty::U64]);
    let contract = mb.declare_function("prelude_contract", unary);
    let mut fb = mb.function("program", nullary);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let three = fb.uconst(Ty::U64, 3);
    fb.ret(vec![three]);
    fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    let decl = module.function_by_id_mut(contract).expect("declared");
    decl.linkage = trust_ir::Linkage::Internal;
    decl.summary = summary;
    module
}

/// Review (adversarial, a legitimate module wrongly refused): an
/// Internal-linkage CONTRACT-ONLY declaration is a valid declaration only
/// because it carries a summary (`trust-ir validate` accepts the module).
/// Stripping the summary to `None` would turn the linker's own edit into an
/// `EmptyFunction` "as linked" — a false verdict about a valid input. The
/// image keeps the declaration valid with the claim-free EMPTY summary
/// (no clauses, not `proved`, no backing), so `run --validate` accepts and
/// runs it, and still counts the stripped summary. Negative twin: the same
/// declaration with NO summary is invalid in the input, and `run --validate`
/// refuses it as linked with the named `EmptyFunction`, exit 1.
#[test]
fn run_validate_keeps_an_internal_contract_only_declaration_valid() {
    use trust_ir::{FunctionSummary, ProofFormula};
    let contract = FunctionSummary::new()
        .with_params(vec!["x".to_string()])
        .ensuring(ProofFormula::smtlib2("(> result 0)", "Bool"));
    let module = module_with_internal_prelude(Some(contract));
    assert_eq!(trust_ir_build::validate_module(&module), Vec::new());
    let (_dir, out) = run_modules(&[&module], &["--validate"]);
    assert_eq!(out.code, Some(0), "stderr: {}", out.stderr);
    assert_eq!(out.stdout.trim(), "3");
    assert!(
        out.stderr.contains("stripped 1 summaries")
            && out
                .stderr
                .contains("linked image is well-formed (as linked)"),
        "stderr: {}",
        out.stderr
    );

    let hollow = module_with_internal_prelude(None);
    assert!(!trust_ir_build::validate_module(&hollow).is_empty());
    let (_dir, out) = run_modules(&[&hollow], &["--validate"]);
    assert_eq!(out.code, Some(1), "stderr: {}", out.stderr);
    assert!(
        out.stderr
            .contains("validation of linked image failed (as linked;")
            && out.stderr.contains("EmptyFunction")
            && !out.stderr.contains("internal:"),
        "stderr: {}",
        out.stderr
    );
}

// ---------------------------------------------------------------------------
// r11: fresh ids, reserved block ranges and intrinsic-name parsing
// (docs: the r11 refutations CHANGELOG entry). Every module below is built
// with the API and run through the `trust-ir` binary. The ones marked
// FAILING-FIRST exited 101 (a debug-build arithmetic panic) or ran a
// duplicate-id image on origin/main `b8f49083`; the log is kept with the r11
// implementation report.
// ---------------------------------------------------------------------------

mod r11 {
    use super::*;
    use trust_ir::constant::Constant;
    use trust_ir::inst::{ICmpOp, Inst};
    use trust_ir::node::InstrNode;
    use trust_ir::ty::FuncTy;
    use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
    use trust_ir::{Block, Function};

    /// `functy.0 = () -> ()`, `functy.1 = () -> (i64)`.
    fn module_with_signatures(name: &str) -> (Module, FuncTyId, FuncTyId) {
        let mut module = Module::new(name);
        let unit = module
            .add_func_type(FuncTy {
                abi: None,
                params: vec![],
                returns: vec![],
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let int = module
            .add_func_type(FuncTy {
                abi: None,
                params: vec![],
                returns: vec![Ty::I64],
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        (module, unit, int)
    }

    fn node(inst: Inst, result: Option<u32>) -> InstrNode {
        let node = InstrNode::new(inst);
        match result {
            Some(id) => node.with_result(ValueId::new(id)),
            None => node,
        }
    }

    fn const_i64(value: i128, result: u32) -> InstrNode {
        node(
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(value),
            },
            Some(result),
        )
    }

    fn block(id: u32, body: Vec<InstrNode>) -> Block {
        Block {
            id: BlockId::new(id),
            params: vec![],
            body,
        }
    }

    /// `@target: () -> ()` returns; `@program: () -> (i64)` has `blocks`
    /// (entry = the first). `@target`'s address is taken by `symaddr<target>`.
    fn dispatch_module(name: &str, blocks: Vec<Block>) -> Module {
        let (mut module, unit, int) = module_with_signatures(name);
        let mut target = Function::new(FuncId::new(0), "target", unit, BlockId::new(0));
        target.blocks = vec![block(0, vec![node(Inst::Return { values: vec![] }, None)])];
        let entry = blocks[0].id;
        let mut program = Function::new(FuncId::new(1), "program", int, entry);
        program.blocks = blocks;
        module.functions.push(target);
        module.functions.push(program);
        module
    }

    /// `%callee = const ptr symaddr<target>; call_indirect %callee (); ret 5`.
    fn indirect_call_to_target(callee: u32, unit: FuncTyId, result: u32) -> Vec<InstrNode> {
        vec![
            node(
                Inst::Const {
                    ty: Ty::Ptr,
                    value: Constant::SymbolAddr {
                        symbol: "target".to_string(),
                        addend: 0,
                    },
                },
                Some(callee),
            ),
            node(
                Inst::CallIndirect {
                    callee: ValueId::new(callee),
                    sig: unit,
                    args: vec![],
                    calling_conv: Default::default(),
                },
                None,
            ),
            const_i64(5, result),
            node(
                Inst::Return {
                    values: vec![ValueId::new(result)],
                },
                None,
            ),
        ]
    }

    /// `functy.0`, the `() -> ()` signature every `module_with_signatures`
    /// module declares first.
    const UNIT: FuncTyId = FuncTyId::new(0);

    fn unreachable_block(id: u32) -> Block {
        block(id, vec![node(Inst::Unreachable, None)])
    }

    /// Item 1, FAILING-FIRST: a v0 `core::intrinsics` extern whose length
    /// prefix no offset can hold (`usize::MAX`). The old parser computed
    /// `digits.len() + len` and panicked in debug (exit 101); the extern is
    /// now an ordinary unknown extern — a trap stub — and the program runs.
    #[test]
    fn an_intrinsic_length_no_offset_can_hold_is_a_trap_stub() {
        let (mut module, unit, int) = module_with_signatures("r11_intrinsic");
        module.functions.push(Function::new(
            FuncId::new(0),
            "_RNvNtCsbu97CrmFxuv_4core10intrinsics18446744073709551615x",
            unit,
            BlockId::new(0),
        ));
        let mut program = Function::new(FuncId::new(1), "program", int, BlockId::new(0));
        program.blocks = vec![block(
            0,
            vec![
                const_i64(0, 0),
                node(
                    Inst::Return {
                        values: vec![ValueId::new(0)],
                    },
                    None,
                ),
            ],
        )];
        module.functions.push(program);
        let (_dir, out) = run_modules(&[&module], &[]);
        assert_eq!(out.code, Some(0), "stderr: {}", out.stderr);
        assert_eq!(out.stdout.trim(), "0");
        assert!(
            out.stderr.contains("1 trap stub(s)"),
            "stderr: {}",
            out.stderr
        );
    }

    /// Item 2 (legalize_icmp), FAILING-FIRST: a function that defines
    /// `ValueId(u32::MAX)` and has a `bool` compare to legalize has no fresh
    /// value id. It used to panic on `index() + 1` in debug (exit 101) and wrap
    /// onto ids it already defines in release; it is now refused by name.
    #[test]
    fn a_bool_compare_with_no_fresh_value_id_is_refused_by_name() {
        let (mut module, _unit, int) = module_with_signatures("r11_icmp");
        let mut program = Function::new(FuncId::new(0), "program", int, BlockId::new(0));
        program.blocks = vec![block(
            0,
            vec![
                node(
                    Inst::Const {
                        ty: Ty::Bool,
                        value: Constant::Bool(true),
                    },
                    Some(u32::MAX),
                ),
                node(
                    Inst::Const {
                        ty: Ty::Bool,
                        value: Constant::Bool(false),
                    },
                    Some(0),
                ),
                node(
                    Inst::ICmp {
                        op: ICmpOp::Eq,
                        ty: Ty::Bool,
                        lhs: ValueId::new(u32::MAX),
                        rhs: ValueId::new(0),
                    },
                    Some(1),
                ),
                const_i64(1, 2),
                const_i64(2, 3),
                node(
                    Inst::Select {
                        ty: Ty::I64,
                        cond: ValueId::new(1),
                        then_val: ValueId::new(2),
                        else_val: ValueId::new(3),
                    },
                    Some(4),
                ),
                node(
                    Inst::Return {
                        values: vec![ValueId::new(4)],
                    },
                    None,
                ),
            ],
        )];
        module.functions.push(program);
        let (_dir, out) = run_modules(&[&module], &[]);
        assert_eq!(out.code, Some(1), "stderr: {}", out.stderr);
        assert!(
            out.stderr.contains(
                "error: cannot lower @program for the interpreter: the ValueId id space is \
                 exhausted"
            ),
            "stderr: {}",
            out.stderr
        );
    }

    /// Item 2, laziness, FAILING-FIRST: the same `ValueId(u32::MAX)` with
    /// nothing to lower needs no fresh id and runs. The old pass computed the
    /// seed eagerly for EVERY function and panicked (exit 101) even here.
    #[test]
    fn a_function_at_value_id_max_that_needs_no_fresh_id_runs() {
        let (mut module, _unit, int) = module_with_signatures("r11_lazy");
        let mut program = Function::new(FuncId::new(0), "program", int, BlockId::new(0));
        program.blocks = vec![block(
            0,
            vec![
                const_i64(7, u32::MAX),
                node(
                    Inst::Return {
                        values: vec![ValueId::new(u32::MAX)],
                    },
                    None,
                ),
            ],
        )];
        module.functions.push(program);
        let (_dir, out) = run_modules(&[&module], &[]);
        assert_eq!(out.code, Some(0), "stderr: {}", out.stderr);
        assert_eq!(out.stdout.trim(), "7");
    }

    /// Item 2 (devirtualization), FAILING-FIRST: a `ptr` `call_indirect`
    /// whose callee is `ValueId(u32::MAX)` needs fresh values for its
    /// dispatch ladder. It used to panic on `index() + 1` in debug (exit 101);
    /// it is now refused by name.
    #[test]
    fn a_dispatch_ladder_with_no_fresh_value_id_is_refused_by_name() {
        let unit = UNIT;
        let module = dispatch_module(
            "r11_devirt_values",
            vec![block(0, indirect_call_to_target(u32::MAX, unit, 0))],
        );
        let (_dir, out) = run_modules(&[&module], &[]);
        assert_eq!(out.code, Some(1), "stderr: {}", out.stderr);
        assert!(
            out.stderr.contains(
                "error: cannot lower @program for the interpreter: the ValueId id space is \
                 exhausted"
            ),
            "stderr: {}",
            out.stderr
        );
    }

    /// Sibling o, FAILING-FIRST: a user block inside the runner's reserved
    /// range (`0xF000_0000`, the first trap id) used to share its id with the
    /// synthesized dispatch-miss block (a duplicate block id, measured) and
    /// run. It is now refused at the input boundary, naming the range; and so
    /// is a block at `u32::MAX` (which also used to panic the ladder's
    /// block-id arithmetic in debug).
    #[test]
    fn a_user_block_in_the_reserved_range_is_refused_by_name() {
        let unit = UNIT;
        for reserved in [0xF000_0000_u32, u32::MAX, 0xE000_0000] {
            let module = dispatch_module(
                "r11_reserved",
                vec![
                    block(0, indirect_call_to_target(0, unit, 1)),
                    unreachable_block(reserved),
                ],
            );
            let (_dir, out) = run_modules(&[&module], &[]);
            assert_eq!(out.code, Some(1), "block {reserved:#x}: {}", out.stderr);
            assert!(
                out.stderr.contains(&format!(
                    "cannot run @program: block id {reserved} ({reserved:#x}) lies in the \
                     runner's reserved block-id range [0xe0000000, 0xffffffff]"
                )),
                "block {reserved:#x}: {}",
                out.stderr
            );
        }
    }

    /// Sibling o, FAILING-FIRST: the last user block id below the reserved
    /// ranges (`0xDFFF_FFFF`) is accepted at the input boundary, but a
    /// dispatch ladder in that function would need a block id past it — the
    /// first trusted-runtime entry id. That id used to be minted silently
    /// (the program ran); it is now refused by name. The same function with
    /// room for its ladder, and one with no ladder at all, run.
    #[test]
    fn a_ladder_block_is_never_minted_into_the_reserved_range() {
        let unit = UNIT;
        let crowded = dispatch_module(
            "r11_crowded",
            vec![
                block(0, indirect_call_to_target(0, unit, 1)),
                unreachable_block(0xDFFF_FFFF),
            ],
        );
        let (_dir, out) = run_modules(&[&crowded], &[]);
        assert_eq!(out.code, Some(1), "stderr: {}", out.stderr);
        assert!(
            out.stderr.contains(
                "error: cannot lower @program for the interpreter: the BlockId id space is \
                 exhausted"
            ),
            "stderr: {}",
            out.stderr
        );

        // One candidate needs two blocks: 0xDFFF_FFFE and 0xDFFF_FFFF.
        let roomy = dispatch_module(
            "r11_roomy",
            vec![
                block(0, indirect_call_to_target(0, unit, 1)),
                unreachable_block(0xDFFF_FFFD),
            ],
        );
        let (_dir, out) = run_modules(&[&roomy], &[]);
        assert_eq!(out.code, Some(0), "stderr: {}", out.stderr);
        assert_eq!(out.stdout.trim(), "5");

        let (mut plain, _unit, int) = module_with_signatures("r11_plain");
        let mut program = Function::new(FuncId::new(0), "program", int, BlockId::new(0));
        program.blocks = vec![
            block(
                0,
                vec![
                    const_i64(3, 0),
                    node(
                        Inst::Return {
                            values: vec![ValueId::new(0)],
                        },
                        None,
                    ),
                ],
            ),
            unreachable_block(0xDFFF_FFFF),
        ];
        plain.functions.push(program);
        let (_dir, out) = run_modules(&[&plain], &[]);
        assert_eq!(out.code, Some(0), "stderr: {}", out.stderr);
        assert_eq!(out.stdout.trim(), "3");
    }

    /// Sibling o, C3's regression pin: a dispatch miss reached at run time is
    /// still attributed by name — miss blocks stay in the trap range, whose
    /// `k`-th id maps back to the `k`-th trap name.
    #[test]
    fn a_reached_dispatch_miss_is_attributed() {
        let unit = UNIT;
        let mut body = indirect_call_to_target(0, unit, 1);
        // Call through NULL instead of the anchor: no candidate matches.
        body.insert(1, node(Inst::NullPtr, Some(2)));
        if let Inst::CallIndirect { callee, .. } = &mut body[2].inst {
            *callee = ValueId::new(2);
        }
        let module = dispatch_module("r11_miss", vec![block(0, body)]);
        let (_dir, out) = run_modules(&[&module], &[]);
        assert_ne!(out.code, Some(0), "stderr: {}", out.stderr);
        assert!(
            out.stderr.contains(
                "trap: reached extern builtin stub @<indirect-call dispatch miss in @program"
            ),
            "stderr: {}",
            out.stderr
        );
    }
}
