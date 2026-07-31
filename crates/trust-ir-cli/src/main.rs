// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `trust-ir` — command-line inspector for TrustIr modules.
//!
//! Subcommands:
//!   * `validate <path>` — run `trust-ir_build::validate_module` and print pass/fail.
//!     `--lineage <manifest>` additionally checks proof-lineage closure
//!     (Interpretation B) against a sidecar manifest (`.tmpl` binary or
//!     `.json`); `--forbid-trusted` runs the zero-`Trusted` census and fails
//!     on any faith-stamped obligation status or evidence; `--forbid-failed`
//!     runs the zero-`Failed` census (the violated-contract build abort) and
//!     fails on any refuted obligation status. All three are off by default.
//!   * `dump <path>` — auto-detect format and pretty-print the module.
//!   * `convert --from <fmt> --to <fmt> <in> [<out>]` — convert between
//!     bin / text / json / msgpack.
//!   * `show-gpu-eligibility <path> [--func <name>]` — print `is_safe_for_gpu`,
//!     `is_gpu_eligible`, `divergence_class`, and GPU-relevant proofs for each
//!     function (or just one).
//!   * `run <paths…> [--entry <name>]` — link one or more modules (or
//!     directories of `.trust_ir` modules) into a single executable image and
//!     run the entry function under the reference interpreter, printing its
//!     return value(s). See `run.rs` for the linker and extern-builtin story.
//!   * `spec-link <path> [--harness-manifest <m>] [--require-manifest |
//!     --allow-unverified-proofs]` — run
//!     the spec↔source cross-reference pass over the module's `SpecModule`
//!     objects. Prints a per-machine coverage report and enforces structural
//!     identity/ownership/resolution (S0/S1/S2), Ob.1 (action exists), Ob.3 (coverage), Ob.4
//!     (machine resolves), L1 (`proof_name` resolves against a valid harness
//!     manifest), and L2 (mandatory nonblank `project`). Exits 0 only for a
//!     certifying Linked report; violations and explicit non-certification
//!     states exit 1.
//!
//! Exit codes:
//!   * `0` — success.
//!   * `1` — validation failure or user error (bad args).
//!   * `2` — parse / I/O / format error.

use std::fs;
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clap::{Parser, Subcommand, ValueEnum};

use trust_ir::{Module, ProofLineageManifest, ProofStatus};
use trust_ir_build::validate::{ModuleValidationReport, ValidationError, validate_module_report};

mod run;

// ---------------------------------------------------------------------------
// Exit codes
// ---------------------------------------------------------------------------

pub(crate) const EXIT_OK: u8 = 0;
pub(crate) const EXIT_USER: u8 = 1;
pub(crate) const EXIT_IO: u8 = 2;

// ---------------------------------------------------------------------------
// CLI definition
// ---------------------------------------------------------------------------

#[derive(Parser)]
#[command(name = "trust-ir")]
#[command(about = "Inspector for TrustIr modules (validate/dump/convert/show-gpu-eligibility)")]
#[command(version)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Validate a TrustIr module. Exits 0 on success, 1 on validation failure.
    ///
    /// Runs the give-back certification pass by default (ON): every `&mut` function whose
    /// backward function is kernel-certifiable is reported, with NO annotations required.
    /// Pass `--no-giveback` to skip it.
    Validate {
        /// Path to module file. Use `-` to read from stdin.
        path: PathBuf,
        /// Explicit format override (auto-detected from extension by default).
        #[arg(long, value_enum)]
        format: Option<Format>,
        /// Skip the (default-ON) give-back certification pass.
        #[arg(long)]
        no_giveback: bool,
        /// Check proof-lineage closure (Interpretation B) against a sidecar
        /// manifest (`.tmpl` binary or `.json`): structural validation against
        /// the module's proof tables (`validate_against`) plus the
        /// validator-authority closure walk. Exits 1 on an open,
        /// non-replayable, or mis-threaded lineage.
        #[arg(long, value_name = "MANIFEST")]
        lineage: Option<PathBuf>,
        /// Forbid faith-stamped proofs (the zero-`Trusted` census gate): list
        /// every obligation whose status is `Trusted` and every certificate
        /// whose evidence is `Trusted`, and exit 1 if any exist.
        #[arg(long)]
        forbid_trusted: bool,
        /// Forbid refuted proofs (the violated-contract build-abort gate,
        /// CK1 WS3-M1): list every obligation whose status is `Failed` and
        /// exit 1 if any exist.
        #[arg(long)]
        forbid_failed: bool,
    },
    /// Read a module in any supported format and pretty-print it to stdout.
    Dump {
        /// Path to module file. Use `-` to read from stdin.
        path: PathBuf,
        /// Explicit format override (auto-detected from extension by default).
        #[arg(long, value_enum)]
        format: Option<Format>,
    },
    /// Convert a module between binary / text / JSON / MessagePack.
    Convert {
        /// Source format.
        #[arg(long, value_enum)]
        from: Format,
        /// Destination format.
        #[arg(long, value_enum)]
        to: Format,
        /// Input path. Use `-` for stdin.
        input: PathBuf,
        /// Output path. Omitted or `-` writes to stdout.
        output: Option<PathBuf>,
    },
    /// Link one or more modules into an executable image and run a function
    /// under the reference interpreter, printing its return value(s).
    ///
    /// A directory argument expands to its `*.trust_ir` modules (an emit-each
    /// battery output directory). Functions are linked by name: definitions
    /// win over declarations, identical duplicate definitions are deduped,
    /// conflicting definitions are an error. Externs that remain bodyless
    /// become interpreter builtins (Rust allocator shims, mem*, a few
    /// `core::intrinsics` bit ops) or trap stubs that fail with the extern's
    /// name when reached.
    Run {
        /// Module files and/or directories of `.trust_ir` modules.
        #[arg(required = true)]
        paths: Vec<PathBuf>,
        /// Explicit format override for FILE arguments (directories always
        /// scan `.trust_ir` text modules).
        #[arg(long, value_enum)]
        format: Option<Format>,
        /// Entry function name.
        #[arg(long, default_value = "program")]
        entry: String,
        /// Interpreter fuel (instruction budget).
        #[arg(long, default_value_t = 1_000_000_000)]
        fuel: u64,
        /// Maximum interpreted call depth.
        #[arg(long, default_value_t = 4096)]
        max_call_depth: u64,
        /// Interpreter memory budget in bytes.
        #[arg(long, default_value_t = 256 * 1024 * 1024)]
        mem_budget: u64,
        /// Also validate the linked image before executing.
        #[arg(long)]
        validate: bool,
    },
    /// Show GPU eligibility for each function (or one named function).
    ShowGpuEligibility {
        /// Path to module file. Use `-` to read from stdin.
        path: PathBuf,
        /// Explicit format override (auto-detected from extension by default).
        #[arg(long, value_enum)]
        format: Option<Format>,
        /// Restrict to a single function by name.
        #[arg(long)]
        func: Option<String>,
    },
    /// Run the spec↔source cross-reference pass over a module's `SpecModule`
    /// objects. Prints a per-machine coverage report and enforces structural
    /// identity/ownership/typed resolution (S0/S1/S2), closure and coverage
    /// (Ob.1/Ob.3/Ob.4), proof resolution against a valid manifest (L1), and a
    /// nonblank projection (L2). Exits 0 only for a certifying Linked report.
    SpecLink {
        /// Path to module file. Use `-` to read from stdin.
        path: PathBuf,
        /// Explicit format override (auto-detected from extension by default).
        #[arg(long, value_enum)]
        format: Option<Format>,
        /// Path to a harness manifest (JSON) listing the real `#[kani::proof]`
        /// harnesses. Enables L1 proof-name resolution: every `SpecProof`'s
        /// `proof_name` must resolve to an entry here.
        #[arg(long)]
        harness_manifest: Option<PathBuf>,
        /// Require a manifest even for DesignOnly proof bindings. Linked proof
        /// bindings already require one by default.
        #[arg(long)]
        require_manifest: bool,
        /// Analyze Linked proof bindings without a manifest. The result is
        /// explicitly non-certifying and exits nonzero even when no obligation
        /// violation is found.
        #[arg(long, conflicts_with_all = ["harness_manifest", "require_manifest"])]
        allow_unverified_proofs: bool,
    },
}

// ---------------------------------------------------------------------------
// Format detection and I/O
// ---------------------------------------------------------------------------

/// Supported serialization formats. Mirrors the `trust-ir` feature-flag table.
#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
pub(crate) enum Format {
    /// Binary codec (trust_ir `binary` feature).
    Bin,
    /// Text format (trust_ir `parser` feature + `Display` impl).
    Text,
    /// JSON via serde (trust_ir `serde` feature).
    Json,
    /// MessagePack via serde (trust_ir `serde` feature).
    Msgpack,
}

impl Format {
    /// Detect format from a file extension. Returns `None` if unknown.
    ///
    /// Extension contract (matches `docs/formats.md` and the conformance
    /// corpus): `.tmbc` is the binary codec, `.trust_ir` is the canonical
    /// text format, `.json`/`.msgpack` are the serde formats.
    fn from_extension(ext: &str) -> Option<Format> {
        match ext {
            "tmbc" => Some(Format::Bin),
            "trust_ir" => Some(Format::Text),
            "json" => Some(Format::Json),
            "msgpack" => Some(Format::Msgpack),
            _ => None,
        }
    }

    /// Resolve a format: explicit override wins; otherwise detect from path.
    pub(crate) fn resolve(explicit: Option<Format>, path: &Path) -> Result<Format, String> {
        if let Some(fmt) = explicit {
            return Ok(fmt);
        }
        let ext = path.extension().and_then(|s| s.to_str()).unwrap_or("");
        Format::from_extension(ext).ok_or_else(|| {
            format!(
                "cannot auto-detect format for {}: unknown extension {:?}; pass --format explicitly",
                path.display(),
                ext
            )
        })
    }
}

/// Read either a path or `-` (stdin). Returns raw bytes.
pub(crate) fn read_input(path: &Path) -> io::Result<Vec<u8>> {
    if path.as_os_str() == "-" {
        let mut buf = Vec::new();
        io::stdin().read_to_end(&mut buf)?;
        Ok(buf)
    } else {
        fs::read(path)
    }
}

/// Write bytes to a path or stdout if `None` / `Some("-")`.
fn write_output(path: Option<&Path>, bytes: &[u8]) -> io::Result<()> {
    match path {
        None => {
            let mut stdout = io::stdout().lock();
            stdout.write_all(bytes)?;
            stdout.flush()
        }
        Some(p) if p.as_os_str() == "-" => {
            let mut stdout = io::stdout().lock();
            stdout.write_all(bytes)?;
            stdout.flush()
        }
        Some(p) => fs::write(p, bytes),
    }
}

// ---------------------------------------------------------------------------
// Decode / encode
// ---------------------------------------------------------------------------

/// Decode a byte slice in the given format into a `Module`.
pub(crate) fn decode_module(fmt: Format, bytes: &[u8]) -> Result<Module, String> {
    match fmt {
        Format::Bin => trust_ir::binary::deserialize_module(bytes)
            .map_err(|e| format!("binary decode error: {e}")),
        Format::Text => {
            let s = std::str::from_utf8(bytes)
                .map_err(|e| format!("text decode: invalid UTF-8: {e}"))?;
            trust_ir::parser::parse_module(s).map_err(|e| format!("text parse error: {e}"))
        }
        Format::Json => {
            serde_json::from_slice::<Module>(bytes).map_err(|e| format!("json decode error: {e}"))
        }
        Format::Msgpack => {
            rmp_serde::from_slice::<Module>(bytes).map_err(|e| format!("msgpack decode error: {e}"))
        }
    }
}

/// Encode a `Module` into the given format.
fn encode_module(fmt: Format, module: &Module) -> Result<Vec<u8>, String> {
    match fmt {
        Format::Bin => Ok(trust_ir::binary::serialize_module(module)),
        Format::Text => Ok(format!("{module}").into_bytes()),
        Format::Json => {
            serde_json::to_vec_pretty(module).map_err(|e| format!("json encode error: {e}"))
        }
        Format::Msgpack => {
            rmp_serde::to_vec(module).map_err(|e| format!("msgpack encode error: {e}"))
        }
    }
}

/// Convenience: read a module from `path` with optional explicit format.
fn load_module(path: &Path, explicit: Option<Format>) -> Result<Module, (u8, String)> {
    let fmt = Format::resolve(explicit, path).map_err(|e| (EXIT_USER, e))?;
    let bytes = read_input(path).map_err(|e| (EXIT_IO, format!("read {}: {e}", path.display())))?;
    decode_module(fmt, &bytes).map_err(|e| (EXIT_IO, e))
}

// ---------------------------------------------------------------------------
// Subcommand implementations
// ---------------------------------------------------------------------------

fn cmd_validate(
    path: &Path,
    fmt: Option<Format>,
    giveback: bool,
    lineage: Option<&Path>,
    forbid_trusted: bool,
    forbid_failed: bool,
) -> u8 {
    let mut module = match load_module(path, fmt) {
        Ok(m) => m,
        Err((code, msg)) => {
            eprintln!("error: {msg}");
            return code;
        }
    };
    // Give-back certification pass — ON BY DEFAULT. Automatic (no annotations): every
    // `&mut` function whose backward function is kernel-certifiable is proven against the
    // ck0-checked pure model and reported; the rest are silently declined (fail-closed,
    // existing verdict path untouched). Attaches the certs to `module`, which
    // `validate_module` then reconfirms.
    if giveback {
        let report = trust_ir_build::certify_module_give_backs(&mut module);
        if report.certified_count() > 0 || !report.declined.is_empty() {
            println!(
                "give-back: {} &mut function{} kernel-certified{}",
                report.certified_count(),
                if report.certified_count() == 1 {
                    ""
                } else {
                    "s"
                },
                if report.declined.is_empty() {
                    String::new()
                } else {
                    format!(
                        " ({} declined/ineligible — fail-closed)",
                        report.declined.len()
                    )
                }
            );
        }
    }
    let validation = validate_module_report(&module);
    let errors = validation.errors();
    // Trust: non-fatal, byte-aware allocation-bound advisory. Unlike the MIR
    // layer, trust-ir Alloca/HeapAlloc carry the un-erased element type, so the
    // byte size is exact. This NEVER changes the exit code — it is advisory and
    // cannot reject valid IR (drop-in parity). 64-bit pointer width by default.
    // Byte-exact constant-over-budget findings print inline as warnings;
    // unbounded-runtime-count findings are advisory notes (the interpreter
    // memory budget enforces them at runtime) and are summarized so they never
    // bury the high-confidence warnings.
    use trust_ir::alloc_bound::AllocBoundReason;
    let mut notes = Vec::new();
    for finding in trust_ir::alloc_bound::check_allocation_bounds(&module, 64) {
        match finding.reason {
            AllocBoundReason::ConstantOverBudget => eprintln!("warning: {finding}"),
            AllocBoundReason::UnboundedRuntimeCount => notes.push(finding),
        }
    }
    if !notes.is_empty() {
        eprintln!(
            "note: {} allocation{} sized by an unbounded runtime count (advisory; enforced at \
             runtime by the interpreter memory budget):",
            notes.len(),
            if notes.len() == 1 { "" } else { "s" }
        );
        for finding in notes.iter().take(5) {
            eprintln!("  {finding}");
        }
        if notes.len() > 5 {
            eprintln!("  … and {} more", notes.len() - 5);
        }
    }
    // Obligation diagnostics carried by the module (the verifier sidecar):
    // rendered with source paths resolved against the module file table.
    // Reporting only — module data, not a validation verdict — so it never
    // changes the exit code.
    report_obligation_diagnostics(&module);
    let mut code = if errors.is_empty() {
        println!("ok: {} — module is well-formed", path.display());
        EXIT_OK
    } else {
        eprintln!(
            "validation failed: {} ({} error{})",
            path.display(),
            errors.len(),
            if errors.len() == 1 { "" } else { "s" }
        );
        for (i, err) in errors.iter().enumerate() {
            eprintln!("  [{i}] {}", format_validation_error(err));
        }
        EXIT_USER
    };
    // --lineage: the Interpretation-B closure check against a sidecar
    // manifest. Runs even when well-formedness failed above so the lineage
    // verdict is always reported; the exit code is the worst of the checks.
    if let Some(manifest_path) = lineage {
        code = code.max(check_lineage(&module, &validation, manifest_path, path));
    }
    // --forbid-trusted: the zero-`Trusted` census gate.
    if forbid_trusted {
        code = code.max(check_forbid_trusted(&module, path));
    }
    // --forbid-failed: the zero-`Failed` census gate (build abort on refuted
    // obligations).
    if forbid_failed {
        code = code.max(check_forbid_failed(&module, path));
    }
    code
}

/// Load a proof-lineage sidecar manifest. The manifest travels as a sidecar
/// (`binary::serialize_proof_lineage_manifest`, `TMPL` magic), never embedded
/// in the module, so the pairing of module and manifest is the caller's claim.
/// Formats: `.tmpl` is the canonical binary sidecar codec; `.json` is the
/// serde form.
fn load_lineage_manifest(path: &Path) -> Result<ProofLineageManifest, (u8, String)> {
    let bytes = read_input(path).map_err(|e| {
        (
            EXIT_IO,
            format!("read lineage manifest {}: {e}", path.display()),
        )
    })?;
    let ext = path.extension().and_then(|s| s.to_str()).unwrap_or("");
    match ext {
        "tmpl" => trust_ir::binary::deserialize_proof_lineage_manifest(&bytes).map_err(|e| {
            (
                EXIT_IO,
                format!(
                    "lineage manifest {}: binary decode error: {e}",
                    path.display()
                ),
            )
        }),
        "json" => serde_json::from_slice::<ProofLineageManifest>(&bytes).map_err(|e| {
            (
                EXIT_IO,
                format!("lineage manifest {} is not valid JSON: {e}", path.display()),
            )
        }),
        _ => Err((
            EXIT_USER,
            format!(
                "cannot detect lineage manifest format for {}: unknown extension {:?}; \
                 use .tmpl (binary sidecar) or .json",
                path.display(),
                ext
            ),
        )),
    }
}

/// `--lineage`: check Interpretation-B lineage closure for `module` against a
/// sidecar manifest. Two layers, both required (fail-closed):
///
/// 1. `ProofLineageManifest::validate_against` — structural validation of the
///    manifest against the module's proof tables. This is what catches a
///    MIS-THREADED chain (dependency digest mismatches, dangling ids, unknown
///    obligations, missing/stale certificates), which the closure walk alone
///    does not inspect.
/// 2. `ModuleValidationReport::lineage_is_closed` — the authority-aware
///    closure predicate: every rung present, `depends_on`-connected from the
///    emitted-code rung(s) back to the source, and backed by evidence replayed
///    during validation, with exact source/target semantics independently
///    rederived (no faith-stamped, opaque, or unrelated proof rung).
fn check_lineage(
    module: &Module,
    validation: &ModuleValidationReport<'_>,
    manifest_path: &Path,
    module_path: &Path,
) -> u8 {
    let manifest = match load_lineage_manifest(manifest_path) {
        Ok(m) => m,
        Err((code, msg)) => {
            eprintln!("error: {msg}");
            return code;
        }
    };
    let mut failed = false;
    if let Err(errors) =
        manifest.validate_against(&module.proof_obligations, &module.proof_certificates)
    {
        failed = true;
        eprintln!(
            "lineage check failed: {} against {} ({} error{})",
            manifest_path.display(),
            module_path.display(),
            errors.len(),
            if errors.len() == 1 { "" } else { "s" }
        );
        for (i, err) in errors.iter().enumerate() {
            eprintln!("  [{i}] {err}");
        }
    }
    if let Err(gap) = validation.lineage_is_closed(&manifest) {
        failed = true;
        eprintln!("lineage check failed: {gap}");
    }
    if failed {
        EXIT_USER
    } else {
        println!(
            "lineage: closed — {} against {}: every rung present, connected, and kernel-replayed",
            manifest_path.display(),
            module_path.display()
        );
        EXIT_OK
    }
}

/// `--forbid-trusted`: the zero-`Trusted` census gate (Program CK1). Censuses
/// every obligation STATUS and every certificate EVIDENCE variant in the
/// module; any `ProofStatus::Trusted` obligation or `ProofEvidence::Trusted`
/// certificate fails the gate, with each occurrence listed. Unlike
/// `--lineage` (which stops at the first gap on the manifest's reachable
/// chain), this enumerates every faith-stamped item module-wide.
fn check_forbid_trusted(module: &Module, path: &Path) -> u8 {
    let trusted_obligations: Vec<_> = module
        .proof_obligations
        .iter()
        .filter(|o| o.status == ProofStatus::Trusted)
        .collect();
    let trusted_evidence = module.trusted_evidence_census();
    if trusted_obligations.is_empty() && trusted_evidence.is_empty() {
        println!(
            "trusted census: {} — no Trusted obligation status, no Trusted evidence",
            path.display()
        );
        return EXIT_OK;
    }
    eprintln!(
        "trusted census failed: {} ({} Trusted obligation status{}, {} Trusted evidence certificate{})",
        path.display(),
        trusted_obligations.len(),
        if trusted_obligations.len() == 1 {
            ""
        } else {
            "es"
        },
        trusted_evidence.len(),
        if trusted_evidence.len() == 1 { "" } else { "s" },
    );
    for o in &trusted_obligations {
        eprintln!(
            "  obligation {} [{:?}{}]: status Trusted — {}",
            o.id,
            o.kind,
            obligation_scope(module, o.function),
            o.description
        );
    }
    let kind_of = |id: trust_ir::value::ProofId| {
        module
            .proof_obligations
            .iter()
            .find(|o| o.id == id)
            .map(|o| format!("{:?}{}", o.kind, obligation_scope(module, o.function)))
            .unwrap_or_else(|| "unknown obligation".to_string())
    };
    for (id, justification) in &trusted_evidence {
        eprintln!(
            "  certificate for obligation {id} [{}]: Trusted evidence — {justification}",
            kind_of(*id)
        );
    }
    EXIT_USER
}

/// Render an obligation's function scope as its resolved name when the
/// FuncId is real, or flag the dangling id — never silently drop it.
/// Shared by the `--forbid-trusted` and `--forbid-failed` censuses.
fn obligation_scope(module: &Module, function: Option<trust_ir::FuncId>) -> String {
    match function {
        Some(f) => match module.function_by_id(f) {
            Some(func) => format!(", function {}", func.name),
            None => format!(", function {f} (unresolved)"),
        },
        None => String::new(),
    }
}

/// `--forbid-failed`: the zero-`Failed` census gate (CK1 WS3-M1, the
/// violated-contract build abort). Censuses every obligation STATUS in the
/// module; any `ProofStatus::Failed` obligation fails the gate, with each
/// occurrence listed (id, kind, function scope, description). The refutation
/// counterexamples ride the obligation-diagnostics sidecar, which
/// `cmd_validate` already renders unconditionally.
///
/// This stays an opt-in flag (like `--forbid-trusted`) rather than a default
/// rejection: `validate_module` records `Failed` as an honest verification
/// state, and conformance fixtures (proof_annotations, proof_diagnostics)
/// legitimately carry `Failed` rows as serialization coverage.
fn check_forbid_failed(module: &Module, path: &Path) -> u8 {
    let failed_obligations: Vec<_> = module
        .proof_obligations
        .iter()
        .filter(|o| o.status == ProofStatus::Failed)
        .collect();
    if failed_obligations.is_empty() {
        println!(
            "failed-obligation census: {} — no Failed obligation status",
            path.display()
        );
        return EXIT_OK;
    }
    eprintln!(
        "failed-obligation census failed: {} ({} Failed obligation status{})",
        path.display(),
        failed_obligations.len(),
        if failed_obligations.len() == 1 {
            ""
        } else {
            "es"
        },
    );
    for o in &failed_obligations {
        eprintln!(
            "  obligation {} [{:?}{}]: status Failed — {}",
            o.id,
            o.kind,
            obligation_scope(module, o.function),
            o.description
        );
    }
    EXIT_USER
}

fn cmd_dump(path: &Path, fmt: Option<Format>) -> u8 {
    let module = match load_module(path, fmt) {
        Ok(m) => m,
        Err((code, msg)) => {
            eprintln!("error: {msg}");
            return code;
        }
    };
    // Pretty-print via the canonical Display impl — that's the text format.
    let mut stdout = io::stdout().lock();
    if let Err(e) = write!(stdout, "{module}") {
        eprintln!("error: write stdout: {e}");
        return EXIT_IO;
    }
    drop(stdout);
    // The text form above carries diagnostics in raw form (`diagnostic N …`
    // with a bare file index); the rendered report resolves the file table.
    // Goes to stderr so stdout stays exactly the parseable text format.
    report_obligation_diagnostics(&module);
    EXIT_OK
}

/// Render `Module::obligation_diagnostics` to stderr as compiler-style
/// `path:line:col: severity: message [detail]` lines (via
/// `Module::render_diagnostic`). Prints nothing when the module carries none.
fn report_obligation_diagnostics(module: &Module) {
    if module.obligation_diagnostics.is_empty() {
        return;
    }
    eprintln!(
        "obligation diagnostics ({}):",
        module.obligation_diagnostics.len()
    );
    for d in &module.obligation_diagnostics {
        eprintln!("  {}", module.render_diagnostic(d));
    }
}

fn cmd_convert(from: Format, to: Format, input: &Path, output: Option<&Path>) -> u8 {
    let bytes = match read_input(input) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("error: read {}: {e}", input.display());
            return EXIT_IO;
        }
    };
    let module = match decode_module(from, &bytes) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("error: {e}");
            return EXIT_IO;
        }
    };
    let out_bytes = match encode_module(to, &module) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("error: {e}");
            return EXIT_IO;
        }
    };
    if let Err(e) = write_output(output, &out_bytes) {
        eprintln!("error: write output: {e}");
        return EXIT_IO;
    }
    EXIT_OK
}

fn cmd_show_gpu_eligibility(path: &Path, fmt: Option<Format>, func_filter: Option<&str>) -> u8 {
    let module = match load_module(path, fmt) {
        Ok(m) => m,
        Err((code, msg)) => {
            eprintln!("error: {msg}");
            return code;
        }
    };
    let mut any = false;
    for func in &module.functions {
        if let Some(name) = func_filter
            && func.name != name
        {
            continue;
        }
        any = true;
        let safe = func.is_safe_for_gpu();
        let eligible = func.is_gpu_eligible();
        let divergence = match func.divergence_class() {
            Some(d) => format!("{d}"),
            None => "<none>".to_string(),
        };
        println!("function {}", func.name);
        println!("  is_safe_for_gpu  = {safe}");
        println!("  is_gpu_eligible  = {eligible}");
        println!("  divergence_class = {divergence}");
        let gpu_proofs = func.gpu_proofs();
        if gpu_proofs.is_empty() {
            println!("  gpu_proofs       = []");
        } else {
            println!("  gpu_proofs       =");
            for p in gpu_proofs {
                println!("    - {p:?}");
            }
        }
    }
    if !any {
        if let Some(name) = func_filter {
            eprintln!("error: no function named {name:?} in {}", path.display());
            return EXIT_USER;
        } else {
            println!("(module has no functions)");
        }
    }
    EXIT_OK
}

/// Load and parse a `HarnessManifest` from a JSON file.
fn load_harness_manifest(path: &Path) -> Result<trust_ir::HarnessManifest, (u8, String)> {
    let bytes = read_input(path).map_err(|e| {
        (
            EXIT_IO,
            format!("read harness manifest {}: {e}", path.display()),
        )
    })?;
    serde_json::from_slice::<trust_ir::HarnessManifest>(&bytes).map_err(|e| {
        (
            EXIT_IO,
            format!("harness manifest {} is not valid JSON: {e}", path.display()),
        )
    })
}

fn cmd_spec_link(
    path: &Path,
    fmt: Option<Format>,
    harness_manifest: Option<&Path>,
    require_manifest: bool,
    allow_unverified_proofs: bool,
) -> u8 {
    let module = match load_module(path, fmt) {
        Ok(m) => m,
        Err((code, msg)) => {
            eprintln!("error: {msg}");
            return code;
        }
    };

    if module.spec_modules.is_empty() {
        // Nothing to link. This is a user error: spec-link was asked to enforce
        // a cross-reference on a module that declares no SpecModule objects.
        eprintln!(
            "error: {} contains no SpecModule objects to link",
            path.display()
        );
        return EXIT_USER;
    }

    let proof_count: usize = module.spec_modules.iter().map(|m| m.proofs.len()).sum();
    let manifest = match harness_manifest {
        Some(mpath) => match load_harness_manifest(mpath) {
            Ok(manifest) => Some(manifest),
            Err((code, msg)) => {
                eprintln!("error: {msg}");
                return code;
            }
        },
        None => None,
    };
    let options = trust_ir::SpecLinkOptions {
        allow_unverified_linked_proofs: allow_unverified_proofs,
        require_manifest_for_design_only: require_manifest,
    };
    let report = match trust_ir::link_spec_modules(&module, manifest.as_ref(), options) {
        Ok(report) => report,
        Err(error) => {
            let manifest_path = harness_manifest.expect("link error requires supplied manifest");
            eprintln!(
                "error: harness manifest {} is structurally invalid: {error}",
                manifest_path.display()
            );
            return EXIT_USER;
        }
    };

    // Per-machine coverage report (always printed, to stdout).
    println!(
        "spec-link: {} machine(s) in {}",
        report.coverage.len(),
        path.display()
    );
    for cov in &report.coverage {
        let pct = cov.ratio * 100.0;
        println!(
            "  machine {:?} [{}] coverage {}/{} = {:.1}% ({} anchored, {} waived) [{}]",
            cov.machine,
            cov.origin,
            cov.anchored + cov.waived,
            cov.total_actions,
            pct,
            cov.anchored,
            cov.waived,
            cov.enforcement.tag(),
        );
    }

    if let (Some(mpath), Some(manifest)) = (harness_manifest, manifest.as_ref()) {
        println!(
            "spec-link: harness manifest {} ({} harness{}), checked {} proof binding{}",
            mpath.display(),
            manifest.harnesses.len(),
            if manifest.harnesses.len() == 1 {
                ""
            } else {
                "es"
            },
            proof_count,
            if proof_count == 1 { "" } else { "s" },
        );
    }

    if report.is_certifying() {
        println!("spec-link-status: certifying");
        let suffix = if harness_manifest.is_some() {
            " plus all proof bindings resolved (L1)"
        } else {
            ""
        };
        println!(
            "ok: {} — all spec↔source obligations hold (S0/S1/S2, Ob.1/Ob.3/Ob.4, L2){suffix}",
            path.display()
        );
        EXIT_OK
    } else {
        eprintln!("spec-link-status: non-certifying");
        if !report.is_ok() {
            eprintln!(
                "spec-link failed: {} ({} violation{})",
                path.display(),
                report.violations.len(),
                if report.violations.len() == 1 {
                    ""
                } else {
                    "s"
                }
            );
            for (i, v) in report.violations.iter().enumerate() {
                eprintln!("  [{i}] {}", v.describe());
            }
        }
        if !report.non_certifying_reasons.is_empty() {
            for reason in &report.non_certifying_reasons {
                eprintln!(
                    "spec-link-noncert: code={} detail={:?}",
                    reason.code(),
                    reason.describe()
                );
            }
        }
        EXIT_USER
    }
}

// ---------------------------------------------------------------------------
// ValidationError formatting
// ---------------------------------------------------------------------------

/// Render a single validation error in a human-friendly single line. Uses
/// `Debug` as the fallback formatter — `ValidationError` has many structured
/// variants and no `Display` impl.
fn format_validation_error(err: &ValidationError) -> String {
    format!("{err:?}")
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

fn main() -> ExitCode {
    let cli = Cli::parse();
    let code = match cli.command {
        Commands::Validate {
            path,
            format,
            no_giveback,
            lineage,
            forbid_trusted,
            forbid_failed,
        } => cmd_validate(
            &path,
            format,
            !no_giveback,
            lineage.as_deref(),
            forbid_trusted,
            forbid_failed,
        ),
        Commands::Dump { path, format } => cmd_dump(&path, format),
        Commands::Run {
            paths,
            format,
            entry,
            fuel,
            max_call_depth,
            mem_budget,
            validate,
        } => run::cmd_run(
            &paths,
            format,
            &entry,
            fuel,
            max_call_depth,
            mem_budget,
            validate,
        ),
        Commands::Convert {
            from,
            to,
            input,
            output,
        } => cmd_convert(from, to, &input, output.as_deref()),
        Commands::ShowGpuEligibility { path, format, func } => {
            cmd_show_gpu_eligibility(&path, format, func.as_deref())
        }
        Commands::SpecLink {
            path,
            format,
            harness_manifest,
            require_manifest,
            allow_unverified_proofs,
        } => cmd_spec_link(
            &path,
            format,
            harness_manifest.as_deref(),
            require_manifest,
            allow_unverified_proofs,
        ),
    };
    ExitCode::from(code)
}

#[cfg(test)]
mod tests {
    use super::Format;

    #[test]
    fn extension_contract_matches_formats_doc() {
        // docs/formats.md + the conformance corpus: .tmbc=binary,
        // .trust_ir=canonical text, .json/.msgpack=serde.
        assert_eq!(Format::from_extension("tmbc"), Some(Format::Bin));
        assert_eq!(Format::from_extension("trust_ir"), Some(Format::Text));
        assert_eq!(Format::from_extension("json"), Some(Format::Json));
        assert_eq!(Format::from_extension("msgpack"), Some(Format::Msgpack));
        // The old bogus extension is gone; unknown extensions are unresolved.
        assert_eq!(Format::from_extension("trust_irtxt"), None);
        assert_eq!(Format::from_extension("bin"), None);
    }
}
