// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// `trust-ir-fmt` — canonical TrustIr text pretty-printer CLI.
//
// Reads a TrustIr module (from a file path, or from stdin when the path is
// `-`) in any of the four formats — binary, text, serde JSON, serde
// MessagePack — decodes it into the in-memory IR, runs the canonical rewrite
// pass from `trust-ir::format::canonical_checked`, and writes the canonical
// text to stdout — or exits 1 with the loss list when the module has fields
// the text grammar cannot carry (roadmap WS4.2).
//
// The input's format is resolved by the ONE rule every TrustIr tool shares,
// `trust_ir::codec::resolve_module_format` (roadmap WS4.9): an explicit
// `--format` wins; otherwise the file name decides, cross-checked against the
// content's magic; a disagreement, and a trust-cg `tMBC` container under any
// name, are refused by name; a name that says nothing (stdin) takes the
// content's claim. MessagePack is never sniffed.
//
// Design: the entire transformation lives in the `trust-ir` crate
// (`trust-ir::format::canonical`) so that downstream consumers (e.g. an
// eventual `trust-ir` CLI sub-command from issue #61, or diff tooling from
// issue #63) can reuse the exact same canonicalization without depending
// on this binary. This file is just a thin I/O shell around that API.

use std::ffi::{OsStr, OsString};
use std::io::{self, Read, Write};
use std::path::Path;
use std::process::ExitCode;

use trust_ir::Module;
use trust_ir::codec::{ModuleFormat, resolve_module_format};

const USAGE: &str = "\
trust_ir-fmt — canonical TrustIr text pretty-printer

USAGE:
    trust_ir-fmt [--format <FMT>] <FILE>   Format the given TrustIr module, write canonical text to stdout
    trust_ir-fmt [--format <FMT>] -        Read a TrustIr module from stdin, write canonical text to stdout
    trust_ir-fmt --help                    Print this message
    trust_ir-fmt --version                 Print the build identity: trust-ir-fmt <MAJOR.MINOR.0>+<source>

The input may be binary, text, serde JSON or serde MessagePack. Its format is
resolved like the `trust-ir` CLI's: the name first (`.trust-ir.bin` /
`.trust-ir.txt`, then `.tmbc` / `.trust_ir` / `.json` / `.msgpack`),
cross-checked against the content (TRUST_IR magic, leading `{`, `;` or
`module \"`); a name the content contradicts, and a trust-cg `tMBC` container,
are refused. A name that says nothing (stdin) takes the content's claim;
MessagePack is never sniffed. `--format <bin | text | json | msgpack>` names
the format and overrides detection.

The canonical form is idempotent: trust_ir-fmt(trust_ir-fmt(x)) == trust_ir-fmt(x).
";

// `--version` prints the COMPILED trust-ir's build identity (roadmap WS8.4);
// that is only honest while the two packages are one release.
const _: () = assert!(
    trust_ir::BUILD_IDENTITY.has_pkg_version(env!("CARGO_PKG_VERSION")),
    "trust-ir-fmt and trust-ir must share one package version"
);

fn main() -> ExitCode {
    let args: Vec<OsString> = std::env::args_os().skip(1).collect();

    // `--help` / `--version` stand alone.
    if let [arg] = args.as_slice() {
        match arg.to_str() {
            Some("-h" | "--help") => {
                print!("{USAGE}");
                return ExitCode::SUCCESS;
            }
            Some("-V" | "--version") => {
                println!("trust-ir-fmt {}", trust_ir::BUILD_IDENTITY.version);
                return ExitCode::SUCCESS;
            }
            _ => {}
        }
    }

    // Exactly one input, optionally preceded by `--format <FMT>` (or
    // `--format=<FMT>`). Everything else is a usage error.
    let (explicit, input) = match args.as_slice() {
        [input] => (None, input),
        [flag, value, input] if flag == "--format" => match parse_format(value) {
            Ok(format) => (Some(format), input),
            Err(e) => return usage_error(&e),
        },
        [flag, input] => match flag
            .to_str()
            .and_then(|flag| flag.strip_prefix("--format="))
            .map(|value| parse_format(OsStr::new(value)))
        {
            Some(Ok(format)) => (Some(format), input),
            Some(Err(e)) => return usage_error(&e),
            None => {
                eprintln!("{USAGE}");
                return ExitCode::from(2);
            }
        },
        _ => {
            eprintln!("{USAGE}");
            return ExitCode::from(2);
        }
    };
    if input.as_encoded_bytes().starts_with(b"--") {
        let message = match input.to_str() {
            Some(input) => format!("unknown option: {input}"),
            None => format!("unknown option: {input:?}"),
        };
        return usage_error(&message);
    }

    let path = Path::new(input);
    let bytes = if input == "-" {
        read_stdin()
    } else {
        read_file(path)
    };
    run(explicit, path, bytes)
}

fn usage_error(message: &str) -> ExitCode {
    eprintln!("trust_ir-fmt: {message}\n\n{USAGE}");
    ExitCode::from(2)
}

/// A `--format` value; anything but the four names is a usage error.
fn parse_format(value: &OsStr) -> Result<ModuleFormat, String> {
    value
        .to_str()
        .and_then(ModuleFormat::from_name)
        .ok_or_else(|| {
            format!("invalid --format value {value:?}: expected bin | text | json | msgpack")
        })
}

fn run(explicit: Option<ModuleFormat>, path: &Path, bytes: Result<Vec<u8>, String>) -> ExitCode {
    let bytes = match bytes {
        Ok(b) => b,
        Err(e) => {
            eprintln!("trust_ir-fmt: {e}");
            return ExitCode::from(1);
        }
    };

    // The shared resolution rule (roadmap WS4.9): refuse a name the content
    // contradicts and a trust-cg container, never guess.
    let format = match resolve_module_format(explicit, path, &bytes) {
        Ok(format) => format,
        Err(refusal) => {
            eprintln!("trust_ir-fmt: {refusal}");
            return ExitCode::from(1);
        }
    };

    let module = match decode(format, &bytes) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("trust_ir-fmt: {e}");
            return ExitCode::from(1);
        }
    };

    // `canonical_checked` (roadmap WS4.2): never write a text that silently
    // drops a field. The strict parser already refuses a `#lossy` input, so a
    // parsed module is normally loss-free; this is the belt to that brace — and
    // the ONLY guard for a binary / JSON / MessagePack input, which may carry
    // fields the text grammar cannot.
    let canonical = match trust_ir::format::canonical_checked(&module) {
        Ok(text) => text,
        Err(e) => {
            eprintln!("trust_ir-fmt: {e}");
            return ExitCode::from(1);
        }
    };

    // Write to stdout. Ignore broken pipe (e.g. piping into `head`).
    let stdout = io::stdout();
    let mut handle = stdout.lock();
    if let Err(e) = handle.write_all(canonical.as_bytes()) {
        if e.kind() == io::ErrorKind::BrokenPipe {
            return ExitCode::SUCCESS;
        }
        eprintln!("trust_ir-fmt: write error: {e}");
        return ExitCode::from(1);
    }
    ExitCode::SUCCESS
}

/// Decode `bytes` with the codec `format` names.
fn decode(format: ModuleFormat, bytes: &[u8]) -> Result<Module, String> {
    match format {
        ModuleFormat::Binary => trust_ir::binary::deserialize_module(bytes)
            .map_err(|e| format!("binary decode error: {e}")),
        ModuleFormat::Text => {
            let source = std::str::from_utf8(bytes)
                .map_err(|e| format!("text decode: invalid UTF-8: {e}"))?;
            trust_ir::parser::parse_module(source).map_err(|e| format!("parse error: {e:?}"))
        }
        ModuleFormat::Json => {
            serde_json::from_slice(bytes).map_err(|e| format!("json decode error: {e}"))
        }
        ModuleFormat::Msgpack => {
            rmp_serde::from_slice(bytes).map_err(|e| format!("msgpack decode error: {e}"))
        }
    }
}

fn read_file(path: &Path) -> Result<Vec<u8>, String> {
    std::fs::read(path).map_err(|e| format!("failed to read {}: {e}", path.display()))
}

fn read_stdin() -> Result<Vec<u8>, String> {
    let mut buf = Vec::new();
    io::stdin()
        .read_to_end(&mut buf)
        .map_err(|e| format!("failed to read stdin: {e}"))?;
    Ok(buf)
}
