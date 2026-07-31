// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// `trust-ir-fmt` — canonical TrustIr text pretty-printer CLI.
//
// Reads a TrustIr text-format module (from a file path, or from stdin when the
// path is `-`), parses it into the in-memory IR, runs the canonical
// rewrite pass from `trust-ir::format::canonical`, and writes the canonical
// text to stdout.
//
// Design: the entire transformation lives in the `trust-ir` crate
// (`trust-ir::format::canonical`) so that downstream consumers (e.g. an
// eventual `trust-ir` CLI sub-command from issue #61, or diff tooling from
// issue #63) can reuse the exact same canonicalization without depending
// on this binary. This file is just a thin I/O shell around that API.

use std::io::{self, Read, Write};
use std::path::Path;
use std::process::ExitCode;

const USAGE: &str = "\
trust_ir-fmt — canonical TrustIr text pretty-printer

USAGE:
    trust_ir-fmt <FILE>     Format the given TrustIr text file, write canonical text to stdout
    trust_ir-fmt -          Read TrustIr text from stdin, write canonical text to stdout
    trust_ir-fmt --help     Print this message
    trust_ir-fmt --version  Print the trust_ir-fmt version

The canonical form is idempotent: trust_ir-fmt(trust_ir-fmt(x)) == trust_ir-fmt(x).
";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();

    // Exactly one positional argument is required. Everything else is an error.
    if args.len() != 1 {
        eprintln!("{USAGE}");
        return ExitCode::from(2);
    }

    let arg = &args[0];
    match arg.as_str() {
        "-h" | "--help" => {
            print!("{USAGE}");
            ExitCode::SUCCESS
        }
        "--version" => {
            println!("trust_ir-fmt {}", env!("CARGO_PKG_VERSION"));
            ExitCode::SUCCESS
        }
        "-" => run(read_stdin()),
        path => run(read_file(Path::new(path))),
    }
}

fn run(source: Result<String, String>) -> ExitCode {
    let source = match source {
        Ok(s) => s,
        Err(e) => {
            eprintln!("trust_ir-fmt: {e}");
            return ExitCode::from(1);
        }
    };

    let module = match trust_ir::parser::parse_module(&source) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("trust_ir-fmt: parse error: {e:?}");
            return ExitCode::from(1);
        }
    };

    let canonical = trust_ir::format::canonical(&module);

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

fn read_file(path: &Path) -> Result<String, String> {
    std::fs::read_to_string(path).map_err(|e| format!("failed to read {}: {e}", path.display()))
}

fn read_stdin() -> Result<String, String> {
    let mut buf = String::new();
    io::stdin()
        .read_to_string(&mut buf)
        .map_err(|e| format!("failed to read stdin: {e}"))?;
    Ok(buf)
}
