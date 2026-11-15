// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `trust-ir` — command-line inspector for TrustIr modules.
//!
//! Subcommands:
//!   * `validate <path>` — run `trust-ir_build::validate_module` and print pass/fail.
//!     A BINARY input is additionally held to the v41 producer rule against
//!     the header version it declared (`validate_module_as_decoded`: a bodied
//!     function with no `body_gate` claim in a v41+ blob is refused); text /
//!     JSON / MessagePack input carries no wire version, and the run SAYS the
//!     rule is unchecked rather than skipping it silently. Every `--link`
//!     dependency is held to the same rule against ITS OWN header.
//!     `--bundle <b.json>` additionally re-derives every recorded
//!     `ProofCertificate::assurance` against the `NativeVerificationBundle` it
//!     cites; without it those rows are reported UNCHECKED, never as agreement.
//!     `--lineage <manifest>` additionally checks proof-lineage closure
//!     (Interpretation B) against a sidecar manifest (`.tmpl` binary or
//!     `.json`); `--forbid-trusted` runs the zero-`Trusted` census and fails
//!     on any faith-stamped obligation status or evidence; `--forbid-failed`
//!     runs the zero-`Failed` census (the violated-contract build abort) and
//!     fails on any refuted obligation status; `--forbid-prose-only` runs the
//!     formula-less non-`Pending` census (F-024) and fails on any row whose
//!     verdict is recorded over prose alone. All four are off by default.
//!   * `dump <path>` — auto-detect format and pretty-print the module.
//!   * `dependencies <path> --root <function-id>` — inspect explicit IR
//!     dependencies in the original module, without projection or proof claims.
//!     Exits 1 for unresolved dependencies, including every `Drop` (its
//!     destructor names no function: `ImplicitDestructor`); exit 0 is not
//!     module validation.
//!   * `convert --from <fmt> --to <fmt> <in> [<out>]` — convert between
//!     bin / text / json / msgpack.
//!   * `show-gpu-eligibility <path> [--func <name>]` — print `is_safe_for_gpu`,
//!     `is_gpu_eligible`, `divergence_class`, and GPU-relevant proofs for each
//!     function (or just one).
//!   * `run <paths…> [--entry <name>] [--arg <v>…]` — link one or more modules
//!     (or directories of `.trust_ir` modules) into a single executable image
//!     and run the entry function under the reference interpreter, printing
//!     its return value(s). `--arg` supplies scalar entry arguments, parsed and
//!     range-checked against the entry signature. Every import row is
//!     authenticated against the linked inputs by digest first
//!     (`--unauthenticated-imports` reports them UNCHECKED instead), the image
//!     carries no proof claims, and `--validate` checks the image both as
//!     linked (exit 1) and after the interpreter lowering (exit 3).
//!     `--host pinned` installs the reference model of the pinned trusted
//!     runtimes (host-assisted execution, reported as such); the default
//!     `--host none` refuses every bodyless declaration by name. See
//!     `run.rs` for the linker and extern-builtin story.
//!   * `digest <paths…>` — print each module's name, `stable_digest`,
//!     `executable_content_digest_v1` and minimal binary wire version.
//!   * `discharge --bvblast <in> <out>` (feature `ay`, WS5.4) — run the
//!     bit-blast route (`trust_ir_ay::attach_bvblast_evidence`) over every
//!     Pending assert-class row, then `validate_module_with_authority` with the
//!     replaying `BvBlastAuthority`, and write the result as a SEPARATE artifact
//!     (never over `<in>`). Discharged rows are valid only under that
//!     authority, so the input module stays the Pending one.
//!   * `handles` — list the pinned trusted handle runtimes
//!     (`TRUSTED_HANDLE_RUNTIMES`) and every entry point's signature.
//!   * `version [--json]` — the build identity in detail (also
//!     `--version --verbose`); `--version` alone prints
//!     `trust-ir <MAJOR.MINOR.0>+<source>`. See `trust_ir::BUILD_IDENTITY`.
//!   * `spec-link <path> [--harness-manifest <m>] [--require-manifest |
//!     --allow-unverified-proofs]` — run
//!     the spec↔source cross-reference pass over the module's `SpecModule`
//!     objects. Prints a per-machine coverage report and enforces structural
//!     identity/ownership/resolution (S0/S1/S2), the typed surface of every
//!     Linked machine (S3: variable types and invariant formulas parse as a
//!     well-sorted SMT-LIB2 subset), Ob.1 (action exists), Ob.3 (coverage), Ob.4
//!     (machine resolves), L1 (`proof_name` resolves against a valid harness
//!     manifest), the v46 typed carrier (S4: typed invariants and temporal
//!     properties bind only this machine's state variables, at their declared
//!     sorts, primed only in an action relation; a `clean-theorem` proof
//!     binding resolves only against the kernel re-check witness
//!     `trust_ir_build::kernel_certified_theorems` mints by validating the
//!     module), and L2 (mandatory nonblank `project`). Exits 0 only for a
//!     certifying Linked report; violations and explicit non-certification
//!     states exit 1.
//!
//! Format detection (every subcommand taking `--format`): an explicit
//! `--format` always wins; otherwise the file name decides (trustc's
//! `.trust-ir.bin` / `.trust-ir.txt`, then `.tmbc` / `.trust_ir` / `.json` /
//! `.msgpack`), cross-checked against the content's magic
//! (`trust_ir::codec::sniff_format`) — a disagreement is refused naming both,
//! and a trust-cg `tMBC` container is refused by name under any extension. A
//! name that says nothing (stdin, `.bin`, …) takes the sniffed format;
//! MessagePack is never sniffed.
//!
//! Exit codes:
//!   * `0` — success.
//!   * `1` — validation failure or user error (bad args).
//!   * `2` — parse / I/O / format error.
//!   * `3` — internal error: this tool produced an invalid artifact of its own
//!     (today only `run --validate`'s post-lowering pass, when the CLI's
//!     interpreter lowering turned a well-formed linked image into an invalid
//!     one). Never a verdict about the input.

use std::fs;
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clap::{CommandFactory, Parser, Subcommand, ValueEnum};

use trust_ir::binary::WireVersion;
use trust_ir::codec::{ModuleFormat, resolve_module_format};
use trust_ir::{BUILD_IDENTITY, Module, ProofLineageManifest, ProofStatus, SourceAttestation};
use trust_ir_build::validate::{ModuleValidationReport, ValidationError, validate_module_report};

mod run;

// ---------------------------------------------------------------------------
// Exit codes
// ---------------------------------------------------------------------------

pub(crate) const EXIT_OK: u8 = 0;
pub(crate) const EXIT_USER: u8 = 1;
pub(crate) const EXIT_IO: u8 = 2;
/// The tool itself produced an invalid artifact (see the module docs). Kept
/// distinct from [`EXIT_USER`] so a lowering defect is never reported as a
/// verdict about the user's input.
pub(crate) const EXIT_INTERNAL: u8 = 3;

// ---------------------------------------------------------------------------
// CLI definition
// ---------------------------------------------------------------------------

#[derive(Parser)]
#[command(name = "trust-ir")]
#[command(
    about = "Inspector for TrustIr modules (validate/dump/dependencies/convert/run/digest/handles/show-gpu-eligibility/spec-link)"
)]
// `--version` is this binary's own flag, not clap's: clap's version flag
// exits before `--verbose` is parsed, and its string would be the bare package
// version, which many commits share (roadmap WS8.4).
#[command(disable_version_flag = true)]
#[command(arg_required_else_help = true, args_conflicts_with_subcommands = true)]
struct Cli {
    /// Print the build identity, `trust-ir <MAJOR.MINOR.0>+<source>`, where
    /// `<source>` is `g<12-hex>` (packaging attested a clean tree),
    /// `g<12-hex>.dirty`, `g<12-hex>.local` (a local checkout whose working
    /// tree is NOT attested) or `unknown` — never a guessed sha.
    #[arg(short = 'V', long = "version")]
    version: bool,
    /// With `--version`: also print the full source sha and its attestation,
    /// the wire version range this build writes and reads, and the
    /// module-identity digest domain.
    #[arg(long, requires = "version")]
    verbose: bool,
    #[command(subcommand)]
    command: Option<Commands>,
}

#[derive(Subcommand)]
enum Commands {
    /// Print this build's identity in detail: the `--version --verbose` report,
    /// or with `--json` a machine-readable object (package version, source
    /// sha and attestation, wire version range, module-identity domain).
    Version {
        /// Emit JSON instead of text.
        #[arg(long)]
        json: bool,
    },
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
        /// Forbid prose-only proofs (WS1.8 rule (g), F-024): list every
        /// obligation whose status is NOT `Pending` and whose `formula` is
        /// absent — a discharged, failed, trusted or certified row that
        /// states its claim in prose alone — and exit 1 if any exist. A
        /// formula-less `Pending` row is legitimate (a producer records a
        /// check before stating it), so it is never listed here.
        #[arg(long)]
        forbid_prose_only: bool,
        /// Re-derive the module's coverage-assurance rows
        /// (`ProofCertificate::assurance`) against the
        /// `NativeVerificationBundle` they cite, read from a `.json` sidecar.
        /// Exits 1 on a bundle that is not this module's, a `request_digest`
        /// that resolves to no request, a citation about another obligation,
        /// or a bound the cited request contradicts. WITHOUT this flag every
        /// recorded assurance row is reported as UNCHECKED — never as
        /// agreement.
        #[arg(long, value_name = "BUNDLE")]
        bundle: Option<PathBuf>,
        /// AUTHENTICATE every import row and every cross-crate call edge, and
        /// RE-EARN every proof-bearing cross-crate row against the dependency
        /// artifact it cites, instead of taking `Module.imports` on faith.
        ///
        /// Every row is checked whether or not a proof cites it, so each
        /// recorded dependency must be supplied. A body-less declaration whose
        /// symbol a supplied dependency exports is signature-checked against
        /// it; one no dependency exports is reported as UNBOUND.
        ///
        /// Repeatable; each PATH is a dependency module in any supported
        /// format. The set is keyed by `Module::stable_digest` and NOTHING
        /// else, so a dependency is bound by CONTENT, not by the path it
        /// arrived on or the name it records: the wrong file is a
        /// `DigestMismatch`, a missing one an `ImportUnavailable`. Every
        /// dependency is then fully revalidated inside the closure walk and
        /// every far `Certified` row re-earned by an in-process kernel replay
        /// (`RejectingModuleProofAuthority` — nothing is taken on faith).
        ///
        /// WITHOUT this flag a module carrying import rows is reported as
        /// having them UNCHECKED, which is never agreement.
        #[arg(long = "link", value_name = "DEPENDENCY")]
        link: Vec<PathBuf>,
    },
    /// Read a module in any supported format and pretty-print it to stdout.
    Dump {
        /// Path to module file. Use `-` to read from stdin.
        path: PathBuf,
        /// Explicit format override (auto-detected from extension by default).
        #[arg(long, value_enum)]
        format: Option<Format>,
    },
    /// Inventory explicit dependencies of an exact function ID, without
    /// projecting the module. Exit 0 means no census refusals, NOT validation,
    /// semantic closure, proof admission, or source refinement.
    Dependencies {
        /// Path to the original module. Use `-` for stdin.
        path: PathBuf,
        /// Original module-local FuncId, never a function-table position.
        #[arg(long)]
        root: u32,
        /// Explicit input format override.
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
    /// name when reached. The entry points of a pinned trusted runtime
    /// (`trust-ir handles`, and the pinned Clean RC triple) are never
    /// stubbed: they stay bodyless, and reaching one is a named refusal
    /// unless `--host pinned` installs the reference host model.
    ///
    /// Every `Module.imports` row of every input is AUTHENTICATED before
    /// linking: its recorded digest must be the `stable_digest` of one of the
    /// linked inputs, which must then pass the name / producer / target checks.
    /// A row no input matches is refused. The linked image is an EXECUTION
    /// artifact: it carries no proof claims (obligations, certificates,
    /// summaries, `ProofRef`s and call proof contexts are all dropped); re-earn
    /// them with `trust-ir validate --link`.
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
        /// One entry argument, parsed against the entry signature's param
        /// type at the same position. Repeatable; the count must equal the
        /// entry's arity exactly. Integers take decimal or `0x` hex (an
        /// optional leading `-` for signed types) and are range-checked for
        /// the param's width and signedness; `bool` takes `true`/`false`;
        /// `f32`/`f64` take a float literal (one that overflows to infinity or
        /// underflows to zero is refused). Any other param type is refused.
        #[arg(long = "arg", value_name = "VALUE", allow_hyphen_values = true)]
        args: Vec<String>,
        /// Interpreter fuel (instruction budget).
        #[arg(long, default_value_t = 1_000_000_000)]
        fuel: u64,
        /// Maximum interpreted call depth.
        #[arg(long, default_value_t = 4096)]
        max_call_depth: u64,
        /// Also validate the image before executing, twice: the image AS
        /// LINKED (the artifact verdict; a refusal exits 1) and the image
        /// after the CLI's interpreter lowering (devirtualization, compare
        /// legalization, builtin synthesis; a refusal there is this tool's
        /// defect and exits 3).
        #[arg(long)]
        validate: bool,
        /// Skip import authentication. Every import row is then reported
        /// UNCHECKED: the run is execution only, and this is not agreement.
        /// The image carries no proof claims either way.
        #[arg(long)]
        unauthenticated_imports: bool,
        /// The host model to install in the reference interpreter. `none`
        /// (default): a call into any bodyless declaration, a pinned
        /// trusted-runtime entry point included, is refused by name.
        /// `pinned`: the reference model of the pinned handle runtimes
        /// (`trust-ir handles`) and the pinned Clean RC runtime is installed;
        /// a run it serves is reported HOST-ASSISTED and is evidence about the
        /// model's reading of the trusted runtime (TRUST.md items 9 and 13),
        /// never in-format execution evidence.
        #[arg(long, value_enum, default_value_t = HostArg::None)]
        host: HostArg,
    },
    /// Print each module's identity: its name, `stable_digest` (the portable
    /// V3 identity a new `ModuleImport.digest` records and what `validate
    /// --link` binds on), the legacy V2 digest a pre-v44 import row records,
    /// `executable_content_digest_v1`, and the minimal binary wire version the
    /// writer selects for it.
    Digest {
        /// Module files (any supported format). Use `-` to read from stdin.
        #[arg(required = true)]
        paths: Vec<PathBuf>,
        /// Explicit format override for every input (auto-detected by default).
        #[arg(long, value_enum)]
        format: Option<Format>,
        /// Refuse a module whose debug file table (`Module.files`) holds an
        /// absolute path that is not under a declared `--remap-prefix`: such a
        /// path embeds the checkout, so the artifact's bytes (and its
        /// executable digest) differ on every machine. Each hit is reported
        /// with its JSON pointer (`/files/<i>`).
        #[arg(long)]
        portable_check: bool,
        /// A path prefix a producer remapped the checkout to (for example
        /// `/rustc/<hash>/`); an absolute `files` entry under it is portable.
        /// Repeatable. Only meaningful with `--portable-check`.
        #[arg(long = "remap-prefix", requires = "portable_check")]
        remap_prefixes: Vec<String>,
    },
    /// Discharge the module's Pending assert-class obligations through the
    /// bit-blast route and write a SEPARATE discharged artifact (WS5.4).
    ///
    /// Runs `trust_ir_ay::attach_bvblast_evidence` (every Pending
    /// `BoundsCheck` / `ArithmeticSafety` row sited on an `Inst::Assert` or a
    /// lowered `CondBr` assert; a row whose own formula disagrees with its site
    /// goal is left untouched), then validates the result with
    /// `validate_module_with_authority(BvBlastAuthority)`, which re-derives and
    /// replays every certificate. The artifact is written only if that
    /// validation passes; it is never written over the input, because a
    /// `Discharged` row is valid only under the authority and the input stays
    /// the Pending module. The certificates name the pinned ay revision
    /// (`BVBLAST_PROVER`). Exit 0 when written, 1 on a validation failure or a
    /// usage error, 2 on an I/O or decode error.
    #[cfg(feature = "ay")]
    Discharge {
        /// Use the bit-blast route. Required: it is the only discharge route
        /// that can mint authority today, and naming it keeps the command's
        /// meaning explicit when another route lands.
        #[arg(long)]
        bvblast: bool,
        /// Input module (any supported format). Use `-` to read from stdin.
        input: PathBuf,
        /// Output path for the discharged artifact. Its format follows the file
        /// name (binary when the name says nothing); `--to` overrides.
        output: PathBuf,
        /// Explicit input format override (auto-detected by default).
        #[arg(long, value_enum)]
        format: Option<Format>,
        /// Explicit output format override.
        #[arg(long, value_enum)]
        to: Option<Format>,
    },
    /// List the trusted handle runtimes the validator pins
    /// (`TRUSTED_HANDLE_RUNTIMES`): each runtime's handle identity and calling
    /// convention, and every entry symbol with its pinned signature.
    /// Read-only: the registry is validator-owned and never on the wire.
    Handles,
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
    /// identity/ownership/typed resolution (S0/S1/S2), the Linked typed surface
    /// (S3: variable types and invariant formulas), closure and coverage
    /// (Ob.1/Ob.3/Ob.4), the v46 typed carrier (S4; a `clean-theorem` binding
    /// resolves only against the kernel re-check witness minted by validating
    /// the module), proof resolution against a valid manifest (L1), and a
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

/// `run --host`: which host model the reference interpreter runs with.
#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
pub(crate) enum HostArg {
    /// No host model: every bodyless declaration is refused by name.
    None,
    /// `trust_ir_build::PinnedHandleHost` — the reference model of the pinned
    /// trusted runtimes (host-assisted execution, WS2.13).
    Pinned,
}

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
    /// The extension contract is [`ModuleFormat::from_extension`] (matches
    /// `docs/formats.md` and the conformance corpus): `.tmbc` is the binary
    /// codec, `.trust_ir` is the canonical text format, `.json`/`.msgpack`
    /// are the serde formats. A bare `.bin` / `.txt` is deliberately NOT
    /// recognised — only the producer's full `.trust-ir.bin` /
    /// `.trust-ir.txt` suffixes are ([`ModuleFormat::from_path`]). Only the
    /// extension-contract unit test reads it: input resolution goes through
    /// the shared core rule, [`trust_ir::codec::resolve_module_format`].
    #[cfg(test)]
    fn from_extension(ext: &str) -> Option<Format> {
        ModuleFormat::from_extension(ext).map(Format::from)
    }

    /// Detect format from a path's name ([`ModuleFormat::from_path`]): first
    /// the full producer suffixes trustc publishes (`CRATE.trust-ir.bin` ⇒
    /// binary, `CRATE.trust-ir.txt` ⇒ text), then the single-extension
    /// contract of [`ModuleFormat::from_extension`]. Returns `None` when the name
    /// says nothing. Input resolution goes through
    /// [`trust_ir::codec::resolve_module_format`] directly; only the
    /// `discharge` output path (the `ay` feature) and the unit tests name a
    /// format from a path alone, so the helper is compiled for exactly those.
    #[cfg(any(test, feature = "ay"))]
    fn from_path(path: &Path) -> Option<Format> {
        ModuleFormat::from_path(path).map(Format::from)
    }

    /// The format's short name ([`ModuleFormat::name`]); read only by the
    /// `discharge` report line (the `ay` feature).
    #[cfg(feature = "ay")]
    fn name(self) -> &'static str {
        ModuleFormat::from(self).name()
    }

    /// Resolve the format of `bytes`, read from `path` — the ONE rule shared
    /// with `trust-ir-fmt` and `trust-ir-diff`,
    /// [`trust_ir::codec::resolve_module_format`]:
    ///
    /// 1. an explicit `--format` wins and is NEVER second-guessed by a sniff;
    /// 2. a trust-cg `tMBC` container is refused by name under ANY extension
    ///    (`.tmbc` included — the extension is TrustIr's own, the magic is
    ///    trust-cg's, and only the magic tells them apart), and so is a
    ///    `TRUST_IS` template (amendment S);
    /// 3. a name that resolves ([`ModuleFormat::from_path`]) is used — unless the
    ///    content claims a DIFFERENT format ([`trust_ir::codec::sniff_format`]),
    ///    or the name says binary and the content lacks the `TRUST_IR` magic;
    ///    both are refused naming the two claims;
    /// 4. a name that says nothing (stdin, `.bin`, any other extension) takes
    ///    the sniffed format. MessagePack is never sniffed.
    pub(crate) fn resolve(
        explicit: Option<Format>,
        path: &Path,
        bytes: &[u8],
    ) -> Result<Format, String> {
        resolve_module_format(explicit.map(ModuleFormat::from), path, bytes)
            .map(Format::from)
            .map_err(|refusal| refusal.to_string())
    }
}

impl From<Format> for ModuleFormat {
    fn from(format: Format) -> ModuleFormat {
        match format {
            Format::Bin => ModuleFormat::Binary,
            Format::Text => ModuleFormat::Text,
            Format::Json => ModuleFormat::Json,
            Format::Msgpack => ModuleFormat::Msgpack,
        }
    }
}

impl From<ModuleFormat> for Format {
    fn from(format: ModuleFormat) -> Format {
        match format {
            ModuleFormat::Binary => Format::Bin,
            ModuleFormat::Text => Format::Text,
            ModuleFormat::Json => Format::Json,
            ModuleFormat::Msgpack => Format::Msgpack,
        }
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

/// Decode a byte slice in the given format into a `Module`, keeping the
/// header version a BINARY blob declared beside it. Text / JSON / MessagePack
/// carry no wire version, so the second half is `None` for them — a fact
/// `validate` STATES rather than skips over, because the v41 producer rule
/// ([`trust_ir::BodyGate`]) can only be read against a declared version.
pub(crate) fn decode_module_with_provenance(
    fmt: Format,
    bytes: &[u8],
) -> Result<(Module, Option<WireVersion>), String> {
    match fmt {
        Format::Bin => trust_ir::binary::deserialize_module_with_wire_version(bytes)
            .map(|(module, wire_version)| (module, Some(wire_version)))
            .map_err(|e| format!("binary decode error: {e}")),
        Format::Text => {
            let s = std::str::from_utf8(bytes)
                .map_err(|e| format!("text decode: invalid UTF-8: {e}"))?;
            trust_ir::parser::parse_module(s)
                .map(|module| (module, None))
                .map_err(|e| format!("text parse error: {e}"))
        }
        Format::Json => serde_json::from_slice::<Module>(bytes)
            .map(|module| (module, None))
            .map_err(|e| format!("json decode error: {e}")),
        Format::Msgpack => rmp_serde::from_slice::<Module>(bytes)
            .map(|module| (module, None))
            .map_err(|e| format!("msgpack decode error: {e}")),
    }
}

/// [`decode_module_with_provenance`] minus the wire version, for the
/// subcommands that read a module as content only.
pub(crate) fn decode_module(fmt: Format, bytes: &[u8]) -> Result<Module, String> {
    decode_module_with_provenance(fmt, bytes).map(|(module, _wire_version)| module)
}

/// The `convert --to bin` refusal text for a writer refusal: the wording each
/// carrier had before D1a (pinned by `cli_inlined_scope_chain.rs`,
/// `cli_module_completeness.rs` and `cli_certificate_binding.rs`), naming the
/// function by name where the refusal names it by id.
fn unencodable_module_message(
    module: &Module,
    refusal: &trust_ir::BinaryProjectionError,
) -> String {
    use trust_ir::BinaryProjectionError as Refusal;
    let function_name = |function: u32| {
        module
            .function_by_id(trust_ir::FuncId::new(function))
            .map_or("?", |f| f.name.as_str())
            .to_owned()
    };
    match refusal {
        Refusal::ConstructAheadOfWireTag {
            construct,
            site: Some(site),
        } => format!(
            "function `{}` carries {construct}, which has no binary encoding yet; write text, \
             json or msgpack instead",
            function_name(site.function)
        ),
        Refusal::InlinedScopeChainUnencodable { function, scope } => format!(
            "function `{}` lexical scope #{scope} carries an inlining chain link \
             (ScopeData.inlined_at), which has no binary encoding yet (its carrier is the \
             deferred WS4.19 wire part); write text, json or msgpack instead",
            function_name(*function)
        ),
        Refusal::CompletenessClaimUnencodable => "the module carries a completeness claim \
             (Module.completeness), which has no binary encoding yet (its carrier is the \
             deferred WS5.3b wire part); write text, json or msgpack instead"
            .to_string(),
        Refusal::ProducerInternalType => format!(
            "the module carries the producer-internal Ty::Error, which has no binary encoding at \
             any version ({refusal}); write text, json or msgpack instead"
        ),
        other => format!("the binary writer refuses the module: {other}"),
    }
}

/// Encode a `Module` into the given format. The error carries the exit code.
///
/// Text is written through `trust_ir::format::text_checked` (roadmap WS4.2,
/// finding F-065): a module with fields the text grammar cannot carry
/// (`global_asm`, a `FunctionSummary`, struct field names, …) is REFUSED with
/// [`EXIT_USER`] and the full loss list, instead of being written as a text
/// that silently drops them. `dump` keeps the human `Display` form, which
/// marks such a module `; #lossy:`.
///
/// `text_checked`, NOT `canonical_checked`: `convert` is a transport, so it
/// must print the module's own SSA value ids and block order. Canonicalization
/// renumbers both (block params of every block first, then instruction
/// results), which no `TextLoss` reports — it is a declared rewrite, not a
/// grammar gap — so a non-canonical module used to come back from `bin -> text
/// -> bin` as a DIFFERENT, silently re-numbered module. The `trust-ir-fmt`
/// binary still emits the canonical form; that is its job.
fn encode_module(fmt: Format, module: &Module) -> Result<Vec<u8>, (u8, String)> {
    match fmt {
        // `serialize_module` runs the one pre-check first: the binary writer
        // itself over a check sink (`Module::wire_image_refusal`). A construct
        // it cannot encode, or a count past the format's `u32`, is refused by
        // name with the user exit code — never a panic in the writer, and
        // never a materialized image.
        Format::Bin => trust_ir::binary::serialize_module(module)
            .map_err(|refusal| (EXIT_USER, unencodable_module_message(module, &refusal))),
        Format::Text => trust_ir::format::text_checked(module)
            .map(String::into_bytes)
            .map_err(|e| (EXIT_USER, e.to_string())),
        Format::Json => serde_json::to_vec_pretty(module)
            .map_err(|e| (EXIT_IO, format!("json encode error: {e}"))),
        Format::Msgpack => {
            rmp_serde::to_vec(module).map_err(|e| (EXIT_IO, format!("msgpack encode error: {e}")))
        }
    }
}

/// Convenience: read a module from `path` with optional explicit format. The
/// bytes are read FIRST, because resolution may sniff them
/// ([`Format::resolve`]); a resolution refusal is a user error (exit 1), a
/// decode failure a format error (exit 2).
fn load_module(path: &Path, explicit: Option<Format>) -> Result<Module, (u8, String)> {
    load_module_with_provenance(path, explicit).map(|(module, _wire_version)| module)
}

/// [`load_module`], keeping the header version a binary input declared
/// (`None` for the formats that have none) — what `validate` needs to hold a
/// decoded blob to the v41 producer rule.
fn load_module_with_provenance(
    path: &Path,
    explicit: Option<Format>,
) -> Result<(Module, Option<WireVersion>), (u8, String)> {
    let bytes = read_input(path).map_err(|e| (EXIT_IO, format!("read {}: {e}", path.display())))?;
    let fmt = Format::resolve(explicit, path, &bytes).map_err(|e| (EXIT_USER, e))?;
    decode_module_with_provenance(fmt, &bytes).map_err(|e| (EXIT_IO, e))
}

// ---------------------------------------------------------------------------
// Subcommand implementations
// ---------------------------------------------------------------------------

#[allow(clippy::too_many_arguments)]
fn cmd_validate(
    path: &Path,
    fmt: Option<Format>,
    giveback: bool,
    lineage: Option<&Path>,
    forbid_trusted: bool,
    forbid_failed: bool,
    forbid_prose_only: bool,
    bundle: Option<&Path>,
    link: &[PathBuf],
) -> u8 {
    let (mut module, wire_version) = match load_module_with_provenance(path, fmt) {
        Ok(loaded) => loaded,
        Err((code, msg)) => {
            eprintln!("error: {msg}");
            return code;
        }
    };
    // --bundle: re-derive every `ProofCertificate::assurance` against the
    // bundle it cites. Run HERE, before the give-back pass, and deliberately
    // so: the bundle was minted for the artifact AS SHIPPED, while the
    // give-back pass below appends certified obligations to the local copy and
    // therefore moves `Module::stable_digest`. Checking afterwards would report
    // a legitimate bundle as "not this module's". Its exit code is folded in at
    // the end, so the code composition is unchanged.
    let assurance_code = check_coverage_assurance(&module, bundle, path);
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
    // The v41 producer rule ([`trust_ir::BodyGate`], "Producer conformance
    // rule"), read against the header version the input DECLARED. A binary
    // blob carries one; text / JSON / MessagePack do not, and that is STATED
    // — silence would read as a pass. One structural pass plus this layer is
    // exactly `validate_module_as_decoded`, without validating twice.
    let provenance_errors = check_decoded_provenance(&module, wire_version, path);
    let errors: Vec<&ValidationError> = validation
        .errors()
        .iter()
        .chain(&provenance_errors)
        .collect();
    // Allocation-size advisory (`trust_ir::alloc_bound`): the allocations whose
    // byte size is not provably within the largest object of the module's
    // target (`isize::MAX` at its pointer width; there is no availability
    // threshold), on every target. The element type is not erased here, so
    // the size is exact. This NEVER changes the exit code — it is advisory
    // and cannot reject valid IR. An allocation that can never succeed prints
    // as a warning; the unbounded ones, and those whose element type has no
    // byte size, follow as notes, every one of them.
    use trust_ir::alloc_bound::AllocBoundReason;
    let mut notes = Vec::new();
    for finding in trust_ir::alloc_bound::check_allocation_bounds(&module) {
        match finding.reason {
            AllocBoundReason::ExceedsObjectLimit => eprintln!("warning: {finding}"),
            AllocBoundReason::UnboundedRuntimeCount | AllocBoundReason::UnknownElementSize => {
                notes.push(finding)
            }
        }
    }
    if !notes.is_empty() {
        eprintln!(
            "note: {} allocation{} whose size no bound keeps within the target's largest object (advisory):",
            notes.len(),
            if notes.len() == 1 { "" } else { "s" }
        );
        for finding in &notes {
            eprintln!("  {finding}");
        }
    }
    // Obligation diagnostics carried by the module (the verifier sidecar):
    // rendered with source paths resolved against the module file table.
    // Reporting only — module data, not a validation verdict — so it never
    // changes the exit code.
    report_obligation_diagnostics(&module);
    // --link: the import-closure walk. When dependencies are supplied it
    // REPLACES the structural verdict rather than adding to it, because it is a
    // strict SUPERSET: `validate_linked_module` runs the module validator on
    // this very module (under `ImportPolicy::Authenticated` and an authority
    // admitting exactly the inheritances it authenticated) as its own step L8,
    // on top of the closure walk. Supplementing would make a CORRECTLY linked
    // client permanently red — a cross-crate `Discharged` row is ungrounded by
    // construction at the faith floor, which is precisely the refusal the walk
    // exists to discharge — and a flag that cannot be satisfied is not a check.
    // Nothing is softened: every error the floor would raise is raised by L8.
    let linked_code = check_linked_imports(&module, link, fmt, path);
    let mut code = match linked_code {
        // The closure walk supersedes the STRUCTURAL verdict only. The
        // decoded-provenance refusal is not part of `validate_linked_module`
        // (a linked image has no wire version either), so it is reported
        // here and folded into the worst code, never dropped by `--link`.
        Some(linked) if provenance_errors.is_empty() => linked,
        Some(linked) => {
            eprintln!(
                "validation failed: {} ({} decoded-provenance error{})",
                path.display(),
                provenance_errors.len(),
                if provenance_errors.len() == 1 {
                    ""
                } else {
                    "s"
                }
            );
            for (i, err) in provenance_errors.iter().enumerate() {
                print_validation_error(i, err);
            }
            linked.max(EXIT_USER)
        }
        None if errors.is_empty() => {
            println!("ok: {} — module is well-formed", path.display());
            EXIT_OK
        }
        None => {
            eprintln!(
                "validation failed: {} ({} error{})",
                path.display(),
                errors.len(),
                if errors.len() == 1 { "" } else { "s" }
            );
            for (i, err) in errors.iter().enumerate() {
                print_validation_error(i, err);
            }
            EXIT_USER
        }
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
    // --forbid-prose-only: the formula-less non-Pending census (F-024).
    if forbid_prose_only {
        code = code.max(check_forbid_prose_only(&module, path));
    }
    code = code.max(assurance_code);
    code
}

/// `--link`: the import-closure walk that authenticates EVERY import row,
/// every cross-crate call edge, and RE-EARNS every proof-bearing cross-crate
/// row against the dependency artifact it cites.
///
/// Plain `validate_module` takes [`trust_ir::Module::imports`] on faith: a
/// `backed_by` citation or an `external: Some` inheritance is checked to
/// RESOLVE and nothing more. That is the right floor for a tool holding one
/// artifact, and it is exactly the surface a laundering producer would use —
/// which is why a shipped binary has to be able to close it. With `--link` the
/// dependency modules are supplied and
/// [`trust_ir_build::validate_linked_module`] runs the closure:
///
/// * each dependency is bound by CONTENT — [`trust_ir_build::ModuleSet`] keys
///   on [`trust_ir::Module::stable_digest`] and ignores
///   [`trust_ir::ModuleImport::name`] entirely, so the wrong file named right
///   is a `DigestMismatch` and a right file absent is an `ImportUnavailable`;
/// * each dependency is then fully revalidated inside the walk, recursively;
/// * every import row is authenticated, cited or not — a row whose
///   dependency was not supplied is refused, never skipped — and every call
///   edge into a supplied dependency is resolved across it (symbol, export
///   linkage, producer, signature; a symbol two dependencies export is
///   `AmbiguousImportedSymbol`). A body-less declaration bound to NO supplied
///   dependency (an FFI extern, or an import the producer never recorded) is
///   listed by the `cross-crate call edges:` line — counted, not refused;
/// * every far `Certified` row is re-earned by an in-process kernel replay,
///   because the authority passed is
///   [`trust_ir::proof::RejectingModuleProofAuthority`]: this binary can
///   replay nothing on its own account, so a bare `Trusted` or `Discharged`
///   label across the edge grounds nothing.
///
/// WITHOUT the flag, a module that carries import rows is reported as having
/// them UNCHECKED and the exit code is unchanged — the `None`-is-not-a-wildcard
/// rule applied to a whole table, the same shape `--bundle` uses. Silence is
/// never agreement.
fn check_linked_imports(
    module: &Module,
    link: &[PathBuf],
    fmt: Option<Format>,
    module_path: &Path,
) -> Option<u8> {
    let rows = module.imports.len();
    if link.is_empty() {
        if rows == 0 {
            // Nothing recorded and nothing supplied: no finding either way.
            return None;
        }
        println!(
            "imports: {rows} recorded dependenc{} UNCHECKED (no --link supplied; \
             cross-crate rows were resolved, not re-earned — this is not agreement)",
            if rows == 1 { "y" } else { "ies" }
        );
        for import in &module.imports {
            println!(
                "  {} digest={} producer={}",
                import.name,
                import.digest,
                import
                    .producer
                    .as_ref()
                    .map_or_else(|| "UNRECORDED".to_string(), |p| format!("{p:?}")),
            );
        }
        return None;
    }
    // Decode every dependency FIRST into a caller-owned store; the set borrows
    // it, which is why decoding cannot insert directly. Each dependency is
    // decoded WITH its header version and held to the v41 producer rule
    // against it exactly as the subject is (`check_decoded_provenance` prints
    // one verdict line per path; a non-binary dependency is reported
    // UNCHECKED). The closure walk validates a dependency's CONTENT and has
    // no wire version to read, so this is the one place a dependency's
    // producer conformance is decided; its refusals are folded into the
    // walk's code below, never dropped.
    let mut store: Vec<Module> = Vec::with_capacity(link.len());
    let mut dependency_provenance: Vec<(&Path, Vec<ValidationError>)> = Vec::new();
    for path in link {
        match load_module_with_provenance(path, fmt) {
            Ok((m, wire_version)) => {
                let errors = check_decoded_provenance(&m, wire_version, path);
                if !errors.is_empty() {
                    dependency_provenance.push((path.as_path(), errors));
                }
                store.push(m);
            }
            Err((code, msg)) => {
                eprintln!("error: --link {}: {msg}", path.display());
                return Some(code);
            }
        }
    }
    // A dependency with no wire identity (`wire_identity_blocker`: the binary
    // writer, run in check mode, refuses a construct or count in it) has no
    // digest to index the set by or to print, and can back no row: refuse it
    // by name before `ModuleSet::new` reaches the panicking identity writer.
    for (path, m) in link.iter().zip(store.iter()) {
        if let Some(blocker) = trust_ir_build::wire_identity_blocker(m) {
            eprintln!(
                "error: --link {}: the dependency has no wire identity to authenticate against: \
                 {blocker}",
                path.display()
            );
            return Some(EXIT_USER);
        }
    }
    let set = trust_ir_build::ModuleSet::new(store.iter());
    for (path, m) in link.iter().zip(store.iter()) {
        println!(
            "link: {} — name {:?} digest {}",
            path.display(),
            m.name,
            m.stable_digest()
        );
    }
    let report = trust_ir_build::validate_linked_module(
        module,
        &set,
        &trust_ir::proof::RejectingModuleProofAuthority,
    );
    if report.is_ok() {
        println!(
            "ok: {} — module is well-formed and all {rows} import row{} authenticated against {} \
             supplied dependenc{}, every cross-crate claim re-earned",
            module_path.display(),
            if rows == 1 { "" } else { "s" },
            set.len(),
            if set.len() == 1 { "y" } else { "ies" },
        );
        println!("  {}", report.coverage_summary());
        println!("  {}", report.call_edge_summary());
        if let Some(replayed) = report.replayed_certificate_refs() {
            println!(
                "  {} certificate{} re-earned by in-process kernel replay",
                replayed.len(),
                if replayed.len() == 1 { "" } else { "s" }
            );
        }
        return Some(fold_dependency_provenance(EXIT_OK, &dependency_provenance));
    }
    let errors = report.errors();
    eprintln!(
        "linked validation failed: {} ({} refusal{})",
        module_path.display(),
        errors.len(),
        if errors.len() == 1 { "" } else { "s" }
    );
    for (i, err) in errors.iter().enumerate() {
        print_validation_error(i, err);
    }
    // The unbound residue is reported on a red verdict too: it is not a
    // refusal, and silence about it would read as agreement.
    eprintln!("  {}", report.call_edge_summary());
    Some(fold_dependency_provenance(
        EXIT_USER,
        &dependency_provenance,
    ))
}

/// `--link`: the decoded-provenance refusals of the supplied DEPENDENCIES,
/// printed by path and by name and folded into the walk's verdict — the
/// same fold the subject's own provenance errors get in `cmd_validate`. A
/// dependency that fails the v41 producer rule turns a green walk red; it
/// never softens a red one.
fn fold_dependency_provenance(code: u8, refused: &[(&Path, Vec<ValidationError>)]) -> u8 {
    if refused.is_empty() {
        return code;
    }
    for (path, errors) in refused {
        eprintln!(
            "validation failed: --link {} ({} decoded-provenance error{})",
            path.display(),
            errors.len(),
            if errors.len() == 1 { "" } else { "s" }
        );
        for (i, err) in errors.iter().enumerate() {
            print_validation_error(i, err);
        }
    }
    code.max(EXIT_USER)
}

/// The v41 producer conformance rule ([`trust_ir::BodyGate`]) read against
/// the header version the input DECLARED, through
/// [`trust_ir_build::decoded_provenance_errors`]. Three honest outcomes, each
/// printed, none silent:
///
/// * binary at v41 or later: every bodied function must carry a `body_gate`
///   claim; a tag-0 body comes back as
///   [`ValidationError::ProducerOmittedBodyGate`] and fails the run;
/// * binary below v41: an absent `body_gate` is the grandfather state, the
///   rule does not apply, and the line says so;
/// * text / JSON / MessagePack: there is no wire version, so the rule CANNOT
///   be checked. UNCHECKED is printed, which is never agreement — the same
///   `None`-is-not-a-wildcard reading `--bundle`'s absence gets below.
///
/// The residual the third case names is the rule's, not this command's: a
/// `Module` carries no wire version, so only the artifact actually decoded
/// from binary can be held to a rule phrased over its producing version.
fn check_decoded_provenance(
    module: &Module,
    wire_version: Option<WireVersion>,
    path: &Path,
) -> Vec<ValidationError> {
    let Some(wire_version) = wire_version else {
        println!(
            "decoded provenance: {} carries no wire version (not a binary blob), so the v41 \
             producer rule — every bodied function makes a `body_gate` claim — is UNCHECKED, \
             not passed",
            path.display()
        );
        return Vec::new();
    };
    if !wire_version.claims_contract_surface() {
        println!(
            "decoded provenance: {} is a {wire_version} blob — pre-v41, so an absent `body_gate` \
             is the grandfather state and the v41 producer rule does not apply",
            path.display()
        );
        return Vec::new();
    }
    let errors = trust_ir_build::decoded_provenance_errors(module, wire_version);
    if errors.is_empty() {
        let bodied = module
            .functions
            .iter()
            .filter(|f| !f.is_declaration())
            .count();
        println!(
            "decoded provenance: {} is a {wire_version} blob — {bodied} bodied function{} \
             {} a `body_gate` claim (v41 producer rule checked)",
            path.display(),
            if bodied == 1 { "" } else { "s" },
            if bodied == 1 { "carries" } else { "carry" },
        );
    }
    errors
}

/// `--bundle`: the coverage-assurance re-derivation.
///
/// `ProofCertificate::assurance` projects a `CoverageBound` plus the
/// `request_digest` of the evidence bundle it was projected FROM, so that the
/// projection is checkable rather than a second source of truth. This is the
/// consumer side of that contract: with the bundle in hand the bound is
/// re-derived and a mismatch is a named refusal; WITHOUT it every recorded row
/// is printed as UNCHECKED, which is the `None`-is-not-a-wildcard rule applied
/// to a whole table — a module separated from its bundle still reads an honest
/// "depth-1 BMC", and nobody may read its silence as confirmation.
fn check_coverage_assurance(module: &Module, bundle_path: Option<&Path>, module_path: &Path) -> u8 {
    let bundle = match bundle_path {
        None => None,
        Some(path) => match load_native_bundle(path) {
            Ok(bundle) => Some(bundle),
            Err((code, msg)) => {
                eprintln!("error: {msg}");
                return code;
            }
        },
    };
    // The legacy rule is deprecated (false provenance); this subcommand moves to
    // `coverage_establishment_report` with `--coverage-attestation` once no
    // downstream pin still depends on it.
    #[allow(deprecated)]
    let report = trust_ir_build::coverage_assurance_report(module, bundle.as_ref());
    if report.recorded() == 0 && bundle_path.is_none() {
        // Nothing recorded and nothing supplied: no finding either way.
        return EXIT_OK;
    }
    if report.errors().is_empty() {
        println!("{}", report.summary());
        return EXIT_OK;
    }
    eprintln!(
        "coverage assurance failed: {} ({} refusal{})",
        module_path.display(),
        report.errors().len(),
        if report.errors().len() == 1 { "" } else { "s" }
    );
    for (i, err) in report.errors().iter().enumerate() {
        eprintln!("  [{i}] {err}");
    }
    EXIT_USER
}

/// Load a `NativeVerificationBundle` sidecar. JSON only: the bundle is an
/// in-memory cross-repo handshake with no binary codec of its own (unlike the
/// lineage manifest's `.tmpl`), and its schema version is exact-matched by
/// `NativeVerificationBundle::validate`, which a consumer runs separately.
fn load_native_bundle(
    path: &Path,
) -> Result<trust_ir::request::NativeVerificationBundle, (u8, String)> {
    let bytes =
        read_input(path).map_err(|e| (EXIT_IO, format!("read bundle {}: {e}", path.display())))?;
    serde_json::from_slice(&bytes).map_err(|e| {
        (
            EXIT_IO,
            format!("bundle {} is not valid JSON: {e}", path.display()),
        )
    })
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

/// `--forbid-prose-only`: the formula-less non-`Pending` census (WS1.8 rule
/// (g), finding F-024). A row whose `formula` is `None` states its claim in
/// prose only, and no verifier can bind, replay or refute prose. Once such a
/// row is `Discharged`, `Failed`, `Trusted` or `Certified` the recorded verdict
/// is about nothing checkable, so this census lists every one and fails.
///
/// A formula-less `Pending` row is NOT listed: producers legitimately record a
/// check before they can state it (F-086), and `Pending` claims nothing. This
/// stays an opt-in flag, mirroring `--forbid-trusted`, because the
/// structural validator has no default refusal for the shape.
fn check_forbid_prose_only(module: &Module, path: &Path) -> u8 {
    let prose_only: Vec<_> = module
        .proof_obligations
        .iter()
        .filter(|o| o.status != ProofStatus::Pending && o.formula.is_none())
        .collect();
    if prose_only.is_empty() {
        println!(
            "prose-only census: {} — no formula-less non-Pending obligation",
            path.display()
        );
        return EXIT_OK;
    }
    eprintln!(
        "prose-only census failed: {} ({} formula-less non-Pending obligation{})",
        path.display(),
        prose_only.len(),
        if prose_only.len() == 1 { "" } else { "s" },
    );
    for o in &prose_only {
        eprintln!(
            "  obligation {} [{:?}{}]: status {:?} with no formula — {}",
            o.id,
            o.kind,
            obligation_scope(module, o.function),
            o.status,
            o.description
        );
    }
    EXIT_USER
}

/// Render an obligation's function scope as its resolved name when the
/// FuncId is real, or flag the dangling id — never silently drop it.
/// Shared by the `--forbid-trusted`, `--forbid-failed` and
/// `--forbid-prose-only` censuses.
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
    // Pretty-print via the Display impl — the human dump. A module with fields
    // the text grammar cannot carry prints a `; #lossy:` line after the header
    // (roadmap WS4.2), which the parser refuses; `convert --to text` refuses
    // such a module outright.
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

fn cmd_dependencies(path: &Path, root: u32, fmt: Option<Format>) -> u8 {
    let module = match load_module(path, fmt) {
        Ok(module) => module,
        Err((code, message)) => {
            eprintln!("error: {message}");
            return code;
        }
    };
    let census = trust_ir::function_dependencies::inspect_function_dependencies(
        &module,
        trust_ir::FuncId::new(root),
    );
    let result = (|| -> io::Result<()> {
        let mut out = io::stdout().lock();
        writeln!(
            out,
            "dependency census: module={:?} root={root}",
            module.name
        )?;
        writeln!(
            out,
            "validation=not-run source_refinement=unproved proof_authority=none"
        )?;
        writeln!(
            out,
            "original module retained: functions={} globals={} completeness={:?}",
            module.functions.len(),
            module.globals.len(),
            module.completeness
        )?;
        writeln!(
            out,
            "destructors are refused; other implicit runtime services and proof/producer claims are not checked"
        )?;
        for node in census.nodes() {
            writeln!(out, "node {node:?}")?;
        }
        for edge in census.edges() {
            writeln!(out, "edge {:?} -> {:?}", edge.site, edge.target)?;
        }
        for refusal in census.refusals() {
            writeln!(out, "refusal {:?}: {:?}", refusal.site, refusal.kind)?;
        }
        writeln!(
            out,
            "nodes={} edges={} refusals={}",
            census.nodes().len(),
            census.edges().len(),
            census.refusals().len()
        )
    })();
    if let Err(error) = result {
        eprintln!("error: write stdout: {error}");
        EXIT_IO
    } else if census.refusals().is_empty() {
        EXIT_OK
    } else {
        EXIT_USER
    }
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
        Err((code, e)) => {
            eprintln!("error: {e}");
            return code;
        }
    };
    if let Err(e) = write_output(output, &out_bytes) {
        eprintln!("error: write output: {e}");
        return EXIT_IO;
    }
    EXIT_OK
}

/// The identity facts `trust-ir digest` prints for one module.
struct ModuleIdentity {
    stable: trust_ir::proof::ProofDigest,
    stable_v2: trust_ir::proof::ProofDigest,
    executable: trust_ir::proof::ProofDigest,
    wire_version: u32,
}

/// Compute a module's identity facts. Every one of them runs the binary
/// writer, which has no image for some content a JSON or MessagePack input
/// can spell (the producer-internal `Ty::Error`, a carrier ahead of its wire
/// part, a count past the format's `u32`). The one pre-check,
/// `Module::wire_image_refusal` (the writer in check mode, D1a), refuses
/// such a module by name first, so nothing here can reach a refusing arm and
/// no panic needs catching.
fn module_identity(module: &Module) -> Result<ModuleIdentity, String> {
    let bytes = trust_ir::binary::serialize_module(module)
        .map_err(|refusal| format!("module is not encodable, so it has no digest: {refusal}"))?;
    // Header: 8-byte magic, then the u32 LE version the writer selected — by
    // construction the minimal lossless version for this content.
    let wire_version = bytes
        .get(8..12)
        .and_then(|header| <[u8; 4]>::try_from(header).ok())
        .map(u32::from_le_bytes)
        .ok_or_else(|| "the serialized module carries no 12-byte header".to_string())?;
    Ok(ModuleIdentity {
        stable: module.stable_digest(),
        stable_v2: module.stable_digest_under(trust_ir::IdentityScheme::V2),
        executable: module.executable_content_digest_v1(),
        wire_version,
    })
}

/// The `Module.files` entries that are NOT portable: an absolute path (POSIX
/// `/…`, a Windows drive `C:\…` / `C:/…`, or a UNC `\\…`) that is not under
/// one of `remap_prefixes`. Returned as `(index, path)`; a relative path is
/// always portable. Only the debug file table is judged here: whether other
/// strings (names, panic-location bytes, `global_asm`) embed a checkout is
/// the all-strings scan WS8.9 layers on top.
///
/// "Under a prefix" is judged by PATH COMPONENT, not by string prefix: the
/// prefix must end at a separator in the path (`/rustc` covers `/rustc/x.rs`,
/// never `/rustc-evil/home/a/x.rs`), and the remainder may not climb out of
/// it through a `..` component (`/rustc/../home/a/x.rs` names the checkout,
/// whatever its first bytes say).
fn non_portable_files<'m>(module: &'m Module, remap_prefixes: &[String]) -> Vec<(usize, &'m str)> {
    let is_sep = |c: char| c == '/' || c == '\\';
    let absolute = |path: &str| {
        let bytes = path.as_bytes();
        path.starts_with('/')
            || path.starts_with("\\\\")
            || (bytes.len() >= 3
                && bytes[0].is_ascii_alphabetic()
                && bytes[1] == b':'
                && (bytes[2] == b'\\' || bytes[2] == b'/'))
    };
    let under = |path: &str, prefix: &str| {
        if prefix.is_empty() {
            return false;
        }
        let Some(rest) = path.strip_prefix(prefix) else {
            return false;
        };
        // The prefix must end on a component boundary.
        let bounded = prefix.ends_with(is_sep) || rest.is_empty() || rest.starts_with(is_sep);
        bounded && !rest.split(is_sep).any(|component| component == "..")
    };
    module
        .files
        .iter()
        .enumerate()
        .filter(|(_, path)| {
            absolute(path)
                && !remap_prefixes
                    .iter()
                    .any(|prefix| under(path, prefix.as_str()))
        })
        .map(|(index, path)| (index, path.as_str()))
        .collect()
}

/// `trust-ir digest <path>…`: the shell counterpart of what
/// `ModuleImport.digest` records. For each input prints the module name,
/// `Module::stable_digest` (under `MODULE_IDENTITY_DOMAIN`, the portable V3
/// identity), the legacy V2 digest (under `MODULE_IDENTITY_DOMAIN_V2`),
/// `Module::executable_content_digest_v1`, and the minimal binary wire
/// version. With `portable` (`--portable-check`, carrying the declared
/// `--remap-prefix`es) a module whose debug file table embeds a
/// non-remapped absolute path is refused, each hit named by JSON pointer.
/// Every input is attempted; the exit code is the worst seen.
fn cmd_digest(paths: &[PathBuf], fmt: Option<Format>, portable: Option<&[String]>) -> u8 {
    let mut code = EXIT_OK;
    for path in paths {
        let module = match load_module(path, fmt) {
            Ok(m) => m,
            Err((c, msg)) => {
                eprintln!("error: {msg}");
                code = code.max(c);
                continue;
            }
        };
        match module_identity(&module) {
            Ok(identity) => {
                println!("{}", path.display());
                println!("  name: {:?}", module.name);
                println!("  stable_digest: {}", identity.stable);
                println!("  identity_domain: {}", trust_ir::MODULE_IDENTITY_DOMAIN);
                println!("  stable_digest_legacy: {}", identity.stable_v2);
                println!(
                    "  legacy_identity_domain: {}",
                    trust_ir::MODULE_IDENTITY_DOMAIN_V2
                );
                println!("  executable_content_digest_v1: {}", identity.executable);
                println!("  wire_version: {}", identity.wire_version);
                if let Some(remap_prefixes) = portable {
                    let hits = non_portable_files(&module, remap_prefixes);
                    if hits.is_empty() {
                        println!(
                            "  portable: yes ({} debug file path(s))",
                            module.files.len()
                        );
                    } else {
                        println!("  portable: no");
                        for (index, file) in hits {
                            eprintln!(
                                "error: {}: /files/{index}: debug file path {file:?} is absolute \
                                 and not under a declared --remap-prefix; it embeds the checkout",
                                path.display()
                            );
                        }
                        code = code.max(EXIT_USER);
                    }
                }
            }
            Err(msg) => {
                eprintln!("error: {}: {msg}", path.display());
                code = code.max(EXIT_USER);
            }
        }
    }
    code
}

/// `discharge --bvblast IN OUT` (WS5.4 (5)). See [`Commands::Discharge`].
#[cfg(feature = "ay")]
fn cmd_discharge(
    bvblast: bool,
    input: &Path,
    output: &Path,
    fmt: Option<Format>,
    to: Option<Format>,
) -> u8 {
    use trust_ir_ay::bvblast::{BVBLAST_PROVER, BvBlastAuthority, attach_bvblast_evidence};

    if !bvblast {
        eprintln!("error: name the discharge route: `discharge --bvblast IN OUT`");
        return EXIT_USER;
    }
    if output.as_os_str() == "-" {
        eprintln!("error: the discharged artifact must be written to a file, not stdout");
        return EXIT_USER;
    }
    let same_file = input.as_os_str() == output.as_os_str()
        || matches!(
            (fs::canonicalize(input), fs::canonicalize(output)),
            (Ok(a), Ok(b)) if a == b
        );
    if same_file {
        eprintln!(
            "error: refusing to write the discharged artifact over its input {}: the \
             input stays the Pending module, and a Discharged row is valid only under the \
             replaying authority",
            input.display()
        );
        return EXIT_USER;
    }
    let mut module = match load_module(input, fmt) {
        Ok(m) => m,
        Err((code, msg)) => {
            eprintln!("error: {msg}");
            return code;
        }
    };
    let outcomes = attach_bvblast_evidence(&mut module);
    let discharged = outcomes.iter().filter(|o| o.discharged).count();
    for outcome in &outcomes {
        println!(
            "obligation #{}: {} — {}",
            outcome.obligation,
            if outcome.discharged {
                "DISCHARGED"
            } else {
                "not discharged"
            },
            outcome.detail
        );
    }
    println!(
        "{discharged} of {} in-scope obligation(s) discharged (prover {BVBLAST_PROVER})",
        outcomes.len()
    );
    let authority = BvBlastAuthority::new();
    let errors = trust_ir_build::validate_module_with_authority(&module, &authority);
    if !errors.is_empty() {
        eprintln!(
            "error: the discharged module does not validate under BvBlastAuthority ({} error(s)); \
             nothing written",
            errors.len()
        );
        for err in &errors {
            eprintln!("  {}", format_validation_error(err));
        }
        return EXIT_USER;
    }
    let out_fmt = to
        .or_else(|| Format::from_path(output))
        .unwrap_or(Format::Bin);
    // WS4.2: text is a refusal format — a discharged module whose rows the
    // canonical text cannot carry is refused (EXIT_USER), never written lossy.
    let bytes = match encode_module(out_fmt, &module) {
        Ok(b) => b,
        Err((code, msg)) => {
            eprintln!("error: {msg}");
            return code;
        }
    };
    if let Err(e) = write_output(Some(output), &bytes) {
        eprintln!("error: write {}: {e}", output.display());
        return EXIT_IO;
    }
    println!("wrote {} ({})", output.display(), out_fmt.name());
    EXIT_OK
}

/// `trust-ir handles`: list `TRUSTED_HANDLE_RUNTIMES` — for each pinned
/// runtime its handle identity, runtime path and calling convention, then
/// every entry point's role, link-time symbol, exact pinned signature and
/// definition path. Read-only; nothing here is configurable.
fn cmd_handles() -> u8 {
    for pin in trust_ir_build::TRUSTED_HANDLE_RUNTIMES {
        println!(
            "handle {:?}: runtime {:?}, calling convention {}, handle type {}",
            pin.name,
            pin.runtime,
            pin.calling_conv,
            pin.handle_ty()
        );
        for entry in pin.entry_points {
            let sig = pin.func_ty(entry);
            let render = |tys: &[trust_ir::ty::Ty]| {
                tys.iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", ")
            };
            println!(
                "  {} @{} ({}) -> ({}) [{}]",
                entry.role,
                entry.symbol,
                render(&sig.params),
                render(&sig.returns),
                entry.def_path
            );
        }
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
    // v46: a `CleanTheorem` proof binding resolves only against the kernel
    // re-check witness, which `trust_ir_build` mints by validating the whole
    // module (in-process CleanCic re-check included). An invalid module gets
    // NO witness — its bindings are then reported unresolved by the linker —
    // and a module with no such binding is not validated here at all (the
    // pre-v46 contract of this subcommand).
    let cites_clean_theorem = module.spec_modules.iter().any(|spec| {
        spec.proofs
            .iter()
            .any(|proof| matches!(proof.kind, trust_ir::ProofKind::CleanTheorem { .. }))
    });
    let theorems = if cites_clean_theorem {
        match trust_ir_build::kernel_certified_theorems(&module) {
            Ok(theorems) => {
                println!(
                    "spec-link: kernel re-check witness established {} theorem{}",
                    theorems.len(),
                    if theorems.len() == 1 { "" } else { "s" }
                );
                Some(theorems)
            }
            Err(errors) => {
                eprintln!(
                    "spec-link: no kernel re-check witness — the module does not validate \
                     ({} error{}); Clean-theorem bindings cannot resolve",
                    errors.len(),
                    if errors.len() == 1 { "" } else { "s" }
                );
                for (i, err) in errors.iter().enumerate() {
                    print_validation_error(i, err);
                }
                None
            }
        }
    } else {
        None
    };
    let report = match trust_ir::link_spec_modules_with_theorems(
        &module,
        manifest.as_ref(),
        theorems.as_ref(),
        options,
    ) {
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
            "ok: {} — all spec↔source obligations hold (S0/S1/S2/S3, Ob.1/Ob.3/Ob.4, L2){suffix}",
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

/// Print one numbered refusal and, under it, its enumerated repair options
/// (`ValidationError::repair_options`, roadmap WS4.18) as a single
/// `      options: a; b` line. A variant with no options prints no `options:`
/// line. This is the ONLY reader of the repair options in the workspace:
/// they are advice text, printed after the verdict is fixed, and nothing
/// branches on them (a test in `trust-ir-build` fails on any other caller).
fn print_validation_error(index: usize, err: &ValidationError) {
    eprintln!("  [{index}] {}", format_validation_error(err));
    let options = err.repair_options();
    if !options.is_empty() {
        eprintln!("      options: {}", options.join("; "));
    }
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

// The CLI prints the COMPILED trust-ir's identity as its own; that is only
// honest while the two packages are one release. A CLI built against a
// different trust-ir version must not compile.
const _: () = assert!(
    BUILD_IDENTITY.has_pkg_version(env!("CARGO_PKG_VERSION")),
    "trust-ir-cli and trust-ir must share one package version"
);

/// `trust-ir <MAJOR.MINOR.0>+<source>` — the `--version` line.
fn version_line() -> String {
    format!("trust-ir {}", BUILD_IDENTITY.version)
}

fn attestation_note(attestation: SourceAttestation) -> &'static str {
    match attestation {
        SourceAttestation::PackagedClean => "packaged; working tree attested clean",
        SourceAttestation::PackagedDirty => "packaged; working tree attested DIRTY",
        SourceAttestation::Local => "local checkout; working tree NOT attested",
        SourceAttestation::Unknown => "no source identity available",
    }
}

/// The `--version --verbose` / `version` report.
fn version_report() -> String {
    let id = BUILD_IDENTITY;
    format!(
        "{}\nsource {} ({})\nwire v{}; reads {}\nmodule identity domain {}\n",
        version_line(),
        id.source_sha,
        attestation_note(id.attestation),
        id.wire_version,
        id.read_range_summary(),
        id.digest_domain,
    )
}

/// The `version --json` object.
fn version_json() -> serde_json::Value {
    let id = BUILD_IDENTITY;
    let readable: Vec<u32> = (0..=id.wire_version).filter(|v| id.reads(*v)).collect();
    serde_json::json!({
        "name": "trust-ir",
        "version": id.version,
        "package_version": id.pkg_version,
        "source": id.source,
        "source_sha": (id.attestation != SourceAttestation::Unknown).then_some(id.source_sha),
        "attestation": id.attestation.as_str(),
        "wire_version": id.wire_version,
        "min_read_version": id.min_read_version,
        "refused_read_versions": [id.refused_read_versions.0, id.refused_read_versions.1],
        "readable_wire_versions": readable,
        "digest_domain": id.digest_domain,
    })
}

fn cmd_version(json: bool) -> u8 {
    if json {
        println!("{:#}", version_json());
    } else {
        print!("{}", version_report());
    }
    EXIT_OK
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    if cli.version {
        if cli.verbose {
            print!("{}", version_report());
        } else {
            println!("{}", version_line());
        }
        return ExitCode::from(EXIT_OK);
    }
    let Some(command) = cli.command else {
        Cli::command()
            .error(
                clap::error::ErrorKind::MissingSubcommand,
                "a subcommand is required",
            )
            .exit()
    };
    let code = match command {
        Commands::Version { json } => cmd_version(json),
        Commands::Validate {
            path,
            format,
            no_giveback,
            lineage,
            forbid_trusted,
            forbid_failed,
            forbid_prose_only,
            bundle,
            link,
        } => cmd_validate(
            &path,
            format,
            !no_giveback,
            lineage.as_deref(),
            forbid_trusted,
            forbid_failed,
            forbid_prose_only,
            bundle.as_deref(),
            &link,
        ),
        Commands::Dump { path, format } => cmd_dump(&path, format),
        Commands::Dependencies { path, root, format } => cmd_dependencies(&path, root, format),
        Commands::Run {
            paths,
            format,
            entry,
            args,
            fuel,
            max_call_depth,
            validate,
            unauthenticated_imports,
            host,
        } => run::cmd_run(
            &paths,
            format,
            &entry,
            &args,
            run::RunOptions {
                fuel,
                max_call_depth,
                validate,
                authenticate_imports: !unauthenticated_imports,
                host: match host {
                    HostArg::None => run::HostChoice::None,
                    HostArg::Pinned => run::HostChoice::Pinned,
                },
            },
        ),
        Commands::Convert {
            from,
            to,
            input,
            output,
        } => cmd_convert(from, to, &input, output.as_deref()),
        Commands::Digest {
            paths,
            format,
            portable_check,
            remap_prefixes,
        } => cmd_digest(
            &paths,
            format,
            portable_check.then_some(remap_prefixes.as_slice()),
        ),
        Commands::Handles => cmd_handles(),
        #[cfg(feature = "ay")]
        Commands::Discharge {
            bvblast,
            input,
            output,
            format,
            to,
        } => cmd_discharge(bvblast, &input, &output, format, to),
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
    use std::path::Path;

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
        // A BARE `.bin` stays unrecognised by name (it is sniffed instead):
        // only the producer's full `.trust-ir.bin` suffix names the codec.
        assert_eq!(Format::from_extension("bin"), None);
        assert_eq!(Format::from_extension("txt"), None);
    }

    /// WS4.9 / F-074: trustc publishes `CRATE.trust-ir.bin` and
    /// `CRATE.trust-ir.txt`. The FULL suffix resolves; the bare trailing
    /// extension does not.
    #[test]
    fn producer_suffix_contract() {
        let by = |name: &str| Format::from_path(Path::new(name));
        assert_eq!(by("out/foo.trust-ir.bin"), Some(Format::Bin));
        assert_eq!(by("out/foo.trust-ir.txt"), Some(Format::Text));
        assert_eq!(by("foo.tmbc"), Some(Format::Bin));
        assert_eq!(by("foo.trust_ir"), Some(Format::Text));
        assert_eq!(by("foo.json"), Some(Format::Json));
        assert_eq!(by("foo.msgpack"), Some(Format::Msgpack));
        assert_eq!(by("foo.bin"), None);
        assert_eq!(by("foo.txt"), None);
        assert_eq!(by("foo.trust-ir.coverage.json"), Some(Format::Json));
        assert_eq!(by("-"), None);
    }

    /// An explicit format is never second-guessed by a sniff — not even for
    /// a trust-cg container or a disagreeing magic.
    #[test]
    fn explicit_format_is_never_overridden() {
        let path = Path::new("x.json");
        assert_eq!(
            Format::resolve(Some(Format::Text), path, b"TRUST_IR\x26\0\0\0"),
            Ok(Format::Text)
        );
        assert_eq!(
            Format::resolve(Some(Format::Bin), Path::new("x.tmbc"), b"tMBC\x01"),
            Ok(Format::Bin)
        );
    }
}
