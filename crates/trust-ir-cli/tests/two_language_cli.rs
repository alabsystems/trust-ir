//! The two-language rows that execute the real `trust-ir` binary (roadmap
//! WS8.6, step 1d): multi-module linking lives only in this CLI (`trust-ir
//! run` links by symbol), so these rows run the binary Cargo builds for this
//! test, `env!("CARGO_BIN_EXE_trust-ir")`. There is no external scout binary
//! and no "not measured" row.
//!
//! The fixtures and the verdict harness are the conformance crate's, included
//! by path so both crates check their rows against the ONE ledger
//! (`crates/trust-ir-conformance/tests/two_language/RATCHETS.tsv`, target
//! `cli`).

#[path = "../../trust-ir-conformance/tests/two_language/b4_fixtures.rs"]
mod b4_fixtures;
#[path = "../../trust-ir-conformance/tests/two_language/b5_fixtures.rs"]
mod b5_fixtures;
#[path = "../../trust-ir-conformance/tests/two_language/harness.rs"]
mod harness;

use std::path::PathBuf;
use std::process::Command;

use harness::{Outcome, Refusal, feature_check};
use trust_ir::interpret::{InterpretOptions, InterpretValue, Interpreter};
use trust_ir::ty::Ty;
use trust_ir::{Linkage, Module, Producer};
use trust_ir_build::ModuleBuilder;

// ---------------------------------------------------------------------------
// The CLI lane
// ---------------------------------------------------------------------------

/// One `trust-ir run` invocation.
#[derive(Debug, Clone)]
struct LinkedRun {
    success: bool,
    stdout_lines: Vec<String>,
    stderr: String,
}

impl LinkedRun {
    /// `Accepted` when the run succeeded; otherwise every `[i] Variant {..}`
    /// line of a failed `--validate`, or the `trap:` line of a trapped run, or
    /// else every `error:` line (a named refusal such as an unauthenticated
    /// import row or a reached trusted-runtime entry point; variant `error`,
    /// the payload is the whole line).
    fn outcome(&self) -> Outcome {
        if self.success {
            return Outcome::Accepted;
        }
        let mut refusals: Vec<Refusal> = self
            .stderr
            .lines()
            .filter_map(|line| {
                let line = line.trim_start();
                let rest = line.strip_prefix('[')?;
                let (index, error) = rest.split_once("] ")?;
                index.parse::<usize>().ok()?;
                Some(Refusal::from_rendered(error.to_string()))
            })
            .collect();
        if refusals.is_empty() {
            refusals = self
                .stderr
                .lines()
                .filter(|line| line.starts_with("trap:"))
                .map(|line| Refusal::from_rendered(line.to_string()))
                .collect();
        }
        if refusals.is_empty() {
            refusals = self
                .stderr
                .lines()
                .filter(|line| line.starts_with("error:"))
                .map(|line| Refusal::from_rendered(line.to_string()))
                .collect();
        }
        if refusals.is_empty() {
            Outcome::measured(format!(
                "failed without a recognised diagnostic: {:?}",
                self.stderr
            ))
        } else {
            Outcome::Refused(refusals)
        }
    }
}

/// Serialise `modules` to `.bin` files under a per-row directory and run
/// `trust-ir run --format bin [--validate] --entry <entry> <files..>`.
fn cli_run(tag: &str, modules: &[&Module], entry: &str, validate: bool) -> LinkedRun {
    let flags: &[&str] = if validate { &["--validate"] } else { &[] };
    cli_run_with(tag, modules, entry, flags)
}

/// [`cli_run`] with an explicit flag list (`--validate`,
/// `--unauthenticated-imports`).
fn cli_run_with(tag: &str, modules: &[&Module], entry: &str, flags: &[&str]) -> LinkedRun {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join("two_language_cli")
        .join(tag);
    std::fs::create_dir_all(&dir).expect("create the row directory");
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_trust-ir"));
    cmd.args(["run", "--format", "bin"]);
    cmd.args(flags);
    cmd.args(["--entry", entry]);
    for (i, module) in modules.iter().enumerate() {
        let path = dir.join(format!("{i:02}.bin"));
        std::fs::write(
            &path,
            trust_ir::binary::serialize_module(module).expect("serialize_module: test fixture"),
        )
        .expect("write the module");
        cmd.arg(path);
    }
    let out = cmd.output().expect("spawn the trust-ir binary");
    LinkedRun {
        success: out.status.success(),
        stdout_lines: String::from_utf8_lossy(&out.stdout)
            .lines()
            .map(str::to_string)
            .collect(),
        stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
    }
}

/// In-process reference interpreter over ONE module (the expectation the CLI
/// output is compared with).
fn run_u64(module: &Module, entry: &str, args: &[u64]) -> Option<u128> {
    let func = module.function_by_name(entry)?.id;
    let args: Vec<InterpretValue> = args
        .iter()
        .map(|v| InterpretValue::int(Ty::U64, i128::from(*v)).expect("u64 value"))
        .collect();
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn_scoped(scope, move || {
                Interpreter::with_module(module)
                    .with_options(InterpretOptions {
                        fuel: 50_000_000,
                        max_call_depth: 4096,
                        ..InterpretOptions::default()
                    })
                    .execute_func(func, args)
                    .ok()
                    .and_then(|outcome| {
                        outcome
                            .returns
                            .first()
                            .and_then(|v| v.as_int())
                            .map(|i| i.as_unsigned())
                    })
            })
            .expect("spawn interpreter thread")
            .join()
            .expect("interpreter thread joins")
    })
}

// ---------------------------------------------------------------------------
// b0: the smallest linked two-language program
// ---------------------------------------------------------------------------

/// The b0 program split across two modules: `dep` DEFINES the Clean
/// `clean_addmul(a, b) = a*b + a`, `root` DECLARES it (bodyless) and its Rust
/// `program()` calls it with (6, 7).
fn b0_split() -> (Module, Module) {
    let mut dep = ModuleBuilder::new("b0_dep");
    let binary = dep.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    {
        let mut fb = dep.function("clean_addmul", binary);
        fb.set_producer(Producer::Clean);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::U64);
        let b = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        let ab = fb.mul(Ty::U64, a, b);
        let out = fb.add(Ty::U64, ab, a);
        fb.ret(vec![out]);
        fb.build();
    }

    let mut root = ModuleBuilder::new("b0_root");
    let binary = root.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let nullary = root.add_func_type(vec![], vec![Ty::U64]);
    root.set_default_producer(Producer::Clean);
    let far = root.declare_function("clean_addmul", binary);
    {
        let mut fb = root.function("program", nullary);
        fb.set_producer(Producer::TRust);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let six = fb.uconst(Ty::U64, 6);
        let seven = fb.uconst(Ty::U64, 7);
        let out = fb.call(far, vec![six, seven]);
        fb.ret(vec![out]);
        fb.build();
    }
    (
        dep.build().expect("ModuleBuilder::build: test fixture"),
        root.build().expect("ModuleBuilder::build: test fixture"),
    )
}

fn b0_linked_run() {
    let (dep, root) = b0_split();
    let run = cli_run("b0_smoke", &[&dep, &root], "program", true);
    // Negative twin: the root alone links its declaration to a trap stub and
    // traps naming it; the value comes from the Clean body in `dep`.
    let alone = cli_run("b0_root_alone", &[&root], "program", false);
    let trapped = !alone.success
        && alone
            .stderr
            .contains("trap: reached extern builtin stub @clean_addmul");
    assert!(feature_check(
        "b0.cli_linked_run",
        run.success && run.stdout_lines == ["48"] && trapped,
        &format!(
            "[dep, root] --validate => stdout={:?} stderr={:?}; negative twin root alone => {:?}",
            run.stdout_lines, run.stderr, alone.stderr
        ),
    ));
}

// ---------------------------------------------------------------------------
// b4: the proof-carrying cross-crate pair
// ---------------------------------------------------------------------------

fn b4_link_and_interpret() {
    use b4_fixtures::{ADDMUL, SCALE, build_dep, build_root, repin, tampered_dep};
    let dep = build_dep(3);
    let (root, _) = build_root(&dep, true);

    // The REAL proof-carrying pair, linked by the CLI and executed. Independent
    // expectation: the dependency's two bodies on the in-process interpreter,
    // composed by hand.
    let run = cli_run("b4_link", &[&dep, &root], "program", false);
    let scaled = run_u64(&dep, SCALE, &[2]);
    let expected =
        scaled.and_then(|s| run_u64(&dep, ADDMUL, &[u64::try_from(s).expect("fits"), 7]));
    assert!(feature_check(
        "b4.link_and_interpret",
        run.success
            && run.stdout_lines == ["48"]
            && scaled == Some(6)
            && expected == Some(48)
            && run
                .stderr
                .contains("linked 2 module(s): 3 function(s) (3 defined"),
        &format!(
            "program() = dep_addmul(dep_scale(2), 7) through TRust->TRust(far) and TRust->Clean(far), \
             `trust-ir run` WITHOUT --validate: stdout={:?} stderr={:?}; in-process interpreter on dep \
             alone: dep_scale(2)={scaled:?}, dep_addmul(6,7)={expected:?} (negative twin: \
             b4.link_and_interpret.negative_twin.root_alone, in-process)",
            run.stdout_lines, run.stderr
        ),
    ));

    // WS4.6 (F-067): the linked image of a PROOF-CARRYING pair passes the
    // linker's own `--validate`. The image carries no proof claims: the
    // obligations and certificates are not carried over, and neither are the
    // summaries that claim them, so an honest `proved` summary no longer
    // arrives with nothing behind it (`InvalidFunctionSummary` x2 before).
    // Negative twin: validation is still the artifact verdict, AS LINKED: the
    // same pair with `dep_scale`'s body AND summary removed (an
    // Internal-linkage bodyless function that is not a contract-only
    // declaration, the root repinned to that dependency) is refused with the
    // named `EmptyFunction` as a user error, never as an `internal:` defect.
    let validated = cli_run("b4_link_validated", &[&dep, &root], "program", true);
    let mut hollow_dep = dep.clone();
    let hollow_scale = hollow_dep
        .functions
        .iter_mut()
        .find(|f| f.name == SCALE)
        .expect("dep defines dep_scale");
    hollow_scale.blocks.clear();
    hollow_scale.summary = None;
    hollow_scale.linkage = Linkage::Internal;
    let mut hollow_root = root.clone();
    repin(&mut hollow_root, &hollow_dep);
    let hollow = cli_run(
        "b4_link_hollow",
        &[&hollow_dep, &hollow_root],
        "program",
        true,
    );
    let hollow_refusal = hollow.outcome();
    assert!(feature_check(
        "b4.gap.linked_image_of_proved_modules_fails_validation",
        validated.success
            && validated.stdout_lines == ["48"]
            && validated
                .stderr
                .contains("stripped 4 summaries / 0 ProofRefs")
            && validated
                .stderr
                .contains("linked image is well-formed (as linked)")
            && validated.stderr.contains("lowered image is well-formed")
            && matches!(
                &hollow_refusal,
                Outcome::Refused(refusals)
                    if refusals.len() == 1 && refusals[0].variant == "EmptyFunction"
            )
            && hollow
                .stderr
                .contains("validation of linked image failed (as linked;")
            && !hollow.stderr.contains("internal:"),
        &format!(
            "the honest proved pair + --validate => success={} stdout={:?} stderr={:?}; twin (dep_scale \
             hollowed, root repinned) => {hollow_refusal:?} stderr={:?}",
            validated.success, validated.stdout_lines, validated.stderr, hollow.stderr
        ),
    ));

    // WS4.6 (F-067): the CLI linker authenticates every import row by digest
    // before it links by name. The root pins the honest dep's digest; linked
    // against the REBUILT dep (factor 3 -> 2) the row matches no input and the
    // run is refused by name, printing nothing. Positive: the honest pair
    // authenticates both rows and prints 48. Escape hatch:
    // `--unauthenticated-imports` runs the rebuilt pair (32) and reports both
    // rows UNCHECKED, never as agreement.
    let tampered = tampered_dep();
    let refused = cli_run("b4_link_tampered", &[&tampered, &root], "program", false);
    let escaped = cli_run_with(
        "b4_link_tampered_unchecked",
        &[&tampered, &root],
        "program",
        &["--unauthenticated-imports"],
    );
    let refusal = refused.outcome();
    assert!(feature_check(
        "b4.gap.cli_linker_ignores_import_digest",
        run.stderr
            .contains("imports: 2 row(s) authenticated against the linked inputs by digest")
            && matches!(
                &refusal,
                Outcome::Refused(refusals)
                    if refusals.len() == 1
                        && refusals[0].rendered.contains(r#"import.0 "b4_dep" pins digest"#)
                        && refusals[0].rendered.contains("which matches no linked input")
            )
            && refused.stdout_lines.is_empty()
            && escaped.success
            && escaped.stdout_lines == ["32"]
            && escaped
                .stderr
                .contains("imports: 2 row(s) UNCHECKED (execution only; this is not agreement)"),
        &format!(
            "honest [dep,root] => 48 with rows authenticated; [dep rebuilt 3->2, SAME root] => \
             {refusal:?} stdout={:?}; with --unauthenticated-imports => success={} stdout={:?} \
             stderr={:?}",
            refused.stdout_lines, escaped.success, escaped.stdout_lines, escaped.stderr
        ),
    ));
}

// ---------------------------------------------------------------------------
// b5: the Nat handle program
// ---------------------------------------------------------------------------

fn b5_cli_executes_handle_program_host_assisted() {
    use b5_fixtures::{nat_program, u64_program};
    let analog = u64_program();
    let module = nat_program();
    let a = cli_run("b5_u64_analog", &[&analog], "program", true);
    let n = cli_run("b5_nat_handle", &[&module], "program", true);
    let h = cli_run_with(
        "b5_nat_handle_hosted",
        &[&module],
        "program",
        &["--validate", "--host", "pinned"],
    );
    // The count of bodyless pinned entry points is the pinned `Nat` row's length:
    // `nat_program()` declares the WHOLE row — five at the port (the release entry
    // point landed at 454ed396), nineteen since WS3.2 pinned the Clean kernel's native
    // `Nat` surface. Derived, never spelled.
    let pinned = trust_ir_build::TRUSTED_HANDLE_RUNTIMES[0]
        .entry_points
        .len();
    let entry_points = format!("0 trap stub(s), {pinned} trusted-runtime entry point(s)");
    // PASS (WS2.13, F-035; reshaped by WS4.6 which closed F-083 and by WS2.12
    // which gave the interpreter its host hook): under `--host pinned` the
    // reference model of the pinned `Nat` runtime is installed and the Nat
    // program prints the native value (1), reported HOST-ASSISTED; every
    // pinned entry point stays bodyless. Negative twin: the default `--host
    // none` still refuses by name at the first entry point reached, printing
    // nothing — the model is opt-in and a run without it stays fail-closed.
    let twin = n.outcome();
    assert!(feature_check(
        "b5.gap.cli_run_cannot_execute_handle_program",
        a.success
            && a.stdout_lines == ["1"]
            && h.success
            && h.stdout_lines == ["1"]
            && h.stderr.contains("linked image is well-formed (as linked)")
            && h.stderr.contains("lowered image is well-formed")
            && h.stderr.contains(&entry_points)
            && h.stderr.contains("host-assisted:")
            && h.stderr
                .contains("this run is not in-format execution evidence")
            && matches!(
                &twin,
                Outcome::Refused(refusals)
                    if refusals.len() == 1
                        && refusals[0].rendered.contains(
                            "error: reached trusted-runtime entry point @trust_bignum_nat_from_u64"
                        )
                        && refusals[0].rendered.contains("no host implementation")
            )
            && n.stdout_lines.is_empty()
            && n.stderr.contains(&entry_points),
        &format!(
            "U64 analog stdout={:?}; Nat module --host pinned success={} stdout={:?} stderr={:?}; \
             Nat module --host none => {twin:?} stderr={:?}",
            a.stdout_lines, h.success, h.stdout_lines, h.stderr, n.stderr
        ),
    ));

    // WS4.6 (F-083): the same CLI WITHOUT `--validate` no longer traps at a
    // synthesized stub of a pinned entry point: it refuses by name, naming the
    // trusted-runtime entry point it reached — and, since WS2.13, executes
    // under `--host pinned`. Negative twin: the skip is keyed on the PINNED
    // tables only, so an ordinary unresolved extern (the b0 root alone,
    // declaring `clean_addmul`) still becomes a trap stub and traps by name,
    // host or no host.
    let run = cli_run("b5_nat_handle_unvalidated", &[&module], "program", false);
    let hosted = cli_run_with(
        "b5_nat_handle_unvalidated_hosted",
        &[&module],
        "program",
        &["--host", "pinned"],
    );
    let (_, b0_root) = b0_split();
    let ordinary = cli_run("b5_ordinary_extern_twin", &[&b0_root], "program", false);
    let ordinary_hosted = cli_run_with(
        "b5_ordinary_extern_twin_hosted",
        &[&b0_root],
        "program",
        &["--host", "pinned"],
    );
    let refusal = run.outcome();
    assert!(feature_check(
        "b5.gap.cli_run_without_validate_traps_at_pinned_stub",
        matches!(
            &refusal,
            Outcome::Refused(refusals)
                if refusals.len() == 1
                    && refusals[0].rendered.contains(
                        "error: reached trusted-runtime entry point @trust_bignum_nat_from_u64"
                    )
        ) && run.stdout_lines.is_empty()
            && !run.stderr.contains("trap:")
            && run.stderr.contains("0 trap stub(s)")
            && hosted.success
            && hosted.stdout_lines == ["1"]
            && !ordinary.success
            && ordinary
                .stderr
                .contains("trap: reached extern builtin stub @clean_addmul")
            && ordinary.stderr.contains("1 trap stub(s)")
            && !ordinary_hosted.success
            && ordinary_hosted
                .stderr
                .contains("trap: reached extern builtin stub @clean_addmul"),
        &format!(
            "Nat module without --validate => {refusal:?} stderr={:?}; with --host pinned => \
             success={} stdout={:?}; twin (ordinary extern) => stderr={:?}; twin with --host \
             pinned => stderr={:?}",
            run.stderr,
            hosted.success,
            hosted.stdout_lines,
            ordinary.stderr,
            ordinary_hosted.stderr
        ),
    ));
}

#[test]
fn two_language_cli() {
    harness::run_target(
        "cli",
        &[
            ("b0_linked_run", b0_linked_run),
            ("b4_link_and_interpret", b4_link_and_interpret),
            (
                "b5_cli_executes_handle_program_host_assisted",
                b5_cli_executes_handle_program_host_assisted,
            ),
        ],
    );
}
