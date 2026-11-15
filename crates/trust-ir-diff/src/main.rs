// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// `trust-ir-diff` — semantic module diff CLI for TrustIr.
//
// Reads two TrustIr modules from disk — each in any of the four formats
// (binary, text, serde JSON, serde MessagePack), resolved per file by the
// shared rule `trust_ir::codec::resolve_module_format` (an explicit
// `--format` wins; a trust-cg `tMBC` container and a name/content
// disagreement are refused by name) — and prints either a unified-diff text
// report (default) or a machine-readable JSON report (`--json`). The
// `--ignore-proofs` flag suppresses proof-annotation differences on both
// functions and instructions.
//
// Exit codes:
//   0 — modules are semantically isomorphic (ignoring ID renumbering
//       and declaration order)
//   1 — differences were found
//   2 — parse / I/O / validate / format-resolution error (never 1: 1 is a
//       verdict about the two modules, and an input that was never read has
//       no verdict)
//
// This binary is a thin shell over `trust-ir::diff` and adds no semantic
// logic of its own.
#![forbid(unsafe_code)]

use std::ffi::{OsStr, OsString};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use trust_ir::Module;
use trust_ir::codec::{ModuleFormat, resolve_module_format};
use trust_ir::diff::{Diff, DiffOptions, diff_with};

const USAGE: &str = "\
trust_ir-diff — semantic module diff for TrustIr

USAGE:
    trust_ir-diff [OPTIONS] <A> <B>

ARGS:
    <A>    Path to the first TrustIr module
    <B>    Path to the second TrustIr module
           Either may be binary, text, serde JSON or serde MessagePack, and
           the two need not match. Each file's format is resolved like the
           `trust-ir` CLI's: the name first (`.trust-ir.bin` / `.trust-ir.txt`,
           then `.tmbc` / `.trust_ir` / `.json` / `.msgpack`), cross-checked
           against the content (TRUST_IR magic, leading `{`, `;` or
           `module \"`); a name the content contradicts, and a trust-cg
           `tMBC` container, are refused. A name that says nothing takes the
           content's claim; MessagePack is never sniffed.

OPTIONS:
    --format <FMT>      Read BOTH inputs as FMT (bin | text | json | msgpack),
                        overriding detection
    --json              Emit machine-readable JSON instead of unified-diff text
    --ignore-proofs     Ignore proof annotations (function- and instruction-level)
    --include-debug     Also compare each function's lexical scope tree (spans,
                        parents, WS4.19 inlining chain links) as a `scopes` row
    -h, --help          Print this help message
    -V, --version       Print the build identity:
                        trust-ir-diff <MAJOR.MINOR.0>+<source>

EXIT CODES:
    0    modules are semantically isomorphic
    1    differences were found
    2    parse / I/O / validate / format-resolution error

SEMANTICS:
    ID renumbering (ValueId, BlockId, StructId, EnumId, RecordId,
    FuncId, TyId, etc.) and declaration order are ignored. Functions
    are aligned by name, blocks by DFS preorder from the entry block,
    and instructions positionally within each block. Types, constants,
    and proof annotations are compared by structural fingerprint.

    Authority, ABI and linkage metadata is NEVER ignored, and is
    reported even under --ignore-proofs: per function `producer`,
    `source_provenance`, `body_gate` (the codegen license),
    `display_path`, `linkage`, `calling_conv`, `signature` and
    `attrs`; per module `target_info`, `global_asm`, `imports`,
    every `global @<name>` (all fields, matched by symbol) and every
    `spec_module <name>` (matched by machine name). Only debug spans,
    value names, scopes, the file table and the module name are
    cosmetic; --include-debug adds the scope tree (with its WS4.19
    inlining chain links) as a per-function `scopes` row.
";

// `--version` prints the COMPILED trust-ir's build identity (roadmap WS8.4);
// that is only honest while the two packages are one release.
const _: () = assert!(
    trust_ir::BUILD_IDENTITY.has_pkg_version(env!("CARGO_PKG_VERSION")),
    "trust-ir-diff and trust-ir must share one package version"
);

fn main() -> ExitCode {
    let args: Vec<OsString> = std::env::args_os().skip(1).collect();
    let outcome = match parse_args(&args) {
        Ok(Cli::Run(parsed)) => run(&parsed),
        Ok(Cli::Help) => Ok(print_usage()),
        Ok(Cli::Version) => Ok(print_version()),
        Err(e) => Err(e),
    };
    match outcome {
        Ok(code) => ExitCode::from(code as u8),
        Err(e) => {
            eprintln!("trust_ir-diff: error: {e}");
            ExitCode::from(2)
        }
    }
}

struct ParsedArgs {
    a: PathBuf,
    b: PathBuf,
    format: Option<ModuleFormat>,
    json: bool,
    ignore_proofs: bool,
    include_debug: bool,
}

/// A `--format` value; anything but the four names is a usage error.
fn parse_format(value: Option<&OsStr>) -> Result<ModuleFormat, String> {
    let value = value.ok_or("--format needs a value (bin | text | json | msgpack)")?;
    value
        .to_str()
        .and_then(ModuleFormat::from_name)
        .ok_or_else(|| {
            format!("invalid --format value {value:?}: expected bin | text | json | msgpack")
        })
}

/// What the command line asks for. `--help` / `--version` are outcomes the
/// caller prints, not a `process::exit` inside the parser: a diverging exit
/// in the middle of the loop is opaque to the verified lane (gate 16 refuted
/// `parse_args` with "unreachable code reached" past the exit call), and the
/// first `--help` / `--version` still wins exactly as the exit did.
enum Cli {
    Run(ParsedArgs),
    Help,
    Version,
}

fn parse_args(args: &[OsString]) -> Result<Cli, String> {
    let mut format = None;
    let mut json = false;
    let mut ignore_proofs = false;
    let mut include_debug = false;
    let mut positional: Vec<PathBuf> = Vec::new();
    let mut i = 0;
    while i < args.len() {
        let a = &args[i];
        // `i < args.len()` bounds `i` below `usize::MAX`, so the step never
        // saturates; it is spelled so the step cannot panic either.
        i = i.saturating_add(1);
        match a.to_str() {
            Some("--format") => {
                // `i` already names the value; step past it the same
                // panic-free way.
                format = Some(parse_format(args.get(i).map(OsString::as_os_str))?);
                i = i.saturating_add(1);
            }
            Some("--json") => json = true,
            Some("--ignore-proofs") => ignore_proofs = true,
            Some("--include-debug") => include_debug = true,
            Some("-h" | "--help") => return Ok(Cli::Help),
            Some("-V" | "--version") => return Ok(Cli::Version),
            Some(s) if s.starts_with("--") => match s.strip_prefix("--format=") {
                Some(value) => format = Some(parse_format(Some(OsStr::new(value)))?),
                None => return Err(format!("unknown option: {s}")),
            },
            _ if a.as_encoded_bytes().starts_with(b"--") => {
                return Err(format!("unknown option: {a:?}"));
            }
            _ => positional.push(PathBuf::from(a)),
        }
    }
    ParsedArgs::new(positional, format, json, ignore_proofs, include_debug).map(Cli::Run)
}

impl ParsedArgs {
    /// The parsed command line, or the arity refusal: exactly two positionals.
    /// The conversion to a two-element array IS the count check and hands the
    /// refused vector back for the message, so no step after it can find a
    /// path missing (no `unwrap` after a separate count).
    fn new(
        positional: Vec<PathBuf>,
        format: Option<ModuleFormat>,
        json: bool,
        ignore_proofs: bool,
        include_debug: bool,
    ) -> Result<Self, String> {
        let [a, b] = <[PathBuf; 2]>::try_from(positional).map_err(|positional| {
            format!(
                "expected exactly 2 positional arguments (got {})",
                positional.len()
            )
        })?;
        Ok(ParsedArgs {
            a,
            b,
            format,
            json,
            ignore_proofs,
            include_debug,
        })
    }
}

fn print_usage() -> i32 {
    print!("{USAGE}");
    0
}

fn print_version() -> i32 {
    println!("trust-ir-diff {}", trust_ir::BUILD_IDENTITY.version);
    0
}

fn run(parsed: &ParsedArgs) -> Result<i32, String> {
    let ma = load(&parsed.a, parsed.format)?;
    let mb = load(&parsed.b, parsed.format)?;
    let opts = DiffOptions {
        ignore_proofs: parsed.ignore_proofs,
        include_debug: parsed.include_debug,
    };
    let d = diff_with(&ma, &mb, opts);
    emit(&d, parsed.json);
    Ok(d.exit_code())
}

/// Print the diff. Kept out of `run` so the verified lane builds `run`'s
/// native bundle without the formatting dispatch (gate 16 measured `run`
/// expiring its per-function budget during bundle construction under load).
fn emit(d: &Diff, json: bool) {
    let out = if json { d.to_json() } else { d.to_text() };
    // Always terminate with a newline for terminal ergonomics when
    // producing text; JSON also gets a trailing newline so shell
    // pipelines behave predictably.
    if out.is_empty() {
        // Isomorphic: stay silent in text mode, emit empty JSON doc in JSON mode.
        if json {
            println!("{}", d.to_json());
        }
    } else {
        println!("{out}");
    }
}

/// Read one input: resolve its format through the shared rule
/// ([`resolve_module_format`]), then decode it with that format's codec.
fn load(path: &Path, explicit: Option<ModuleFormat>) -> Result<Module, String> {
    let bytes = fs::read(path).map_err(|e| format!("read {}: {e}", path.display()))?;
    let format = resolve_module_format(explicit, path, &bytes).map_err(|e| e.to_string())?;
    let m = decode(format, &bytes).map_err(|e| format!("parse {}: {e}", path.display()))?;
    m.validate_tuple_layouts()
        .map_err(|e| format!("validate {}: {e}", path.display()))?;
    m.validate_closure_layouts()
        .map_err(|e| format!("validate {}: {e}", path.display()))?;
    Ok(m)
}

/// Decode `bytes` with the codec `format` names.
fn decode(format: ModuleFormat, bytes: &[u8]) -> Result<Module, String> {
    match format {
        ModuleFormat::Binary => trust_ir::binary::deserialize_module(bytes)
            .map_err(|e| format!("binary decode error: {e}")),
        ModuleFormat::Text => {
            let text = std::str::from_utf8(bytes)
                .map_err(|e| format!("text decode: invalid UTF-8: {e}"))?;
            trust_ir::parser::parse_module(text).map_err(|e| format!("text parse error: {e}"))
        }
        ModuleFormat::Json => {
            serde_json::from_slice(bytes).map_err(|e| format!("json decode error: {e}"))
        }
        ModuleFormat::Msgpack => {
            rmp_serde::from_slice(bytes).map_err(|e| format!("msgpack decode error: {e}"))
        }
    }
}
