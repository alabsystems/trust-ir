// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// `trust-ir-diff` — semantic module diff CLI for TrustIr.
//
// Reads two TrustIr modules from disk (serde JSON) and prints either a
// unified-diff text report (default) or a machine-readable JSON report
// (`--json`). The `--ignore-proofs` flag suppresses proof-annotation
// differences on both functions and instructions.
//
// Exit codes:
//   0 — modules are semantically isomorphic (ignoring ID renumbering
//       and declaration order)
//   1 — differences were found
//   2 — parse / I/O / validate error
//
// This binary is a thin shell over `trust-ir::diff` and adds no semantic
// logic of its own.
#![forbid(unsafe_code)]

use std::fs;
use std::path::PathBuf;
use std::process::ExitCode;

use trust_ir::Module;
use trust_ir::diff::{DiffOptions, diff_with};

const USAGE: &str = "\
trust_ir-diff — semantic module diff for TrustIr

USAGE:
    trust_ir-diff [OPTIONS] <A> <B>

ARGS:
    <A>    Path to the first TrustIr module (serde JSON)
    <B>    Path to the second TrustIr module (serde JSON)

OPTIONS:
    --json              Emit machine-readable JSON instead of unified-diff text
    --ignore-proofs     Ignore proof annotations (function- and instruction-level)
    -h, --help          Print this help message

EXIT CODES:
    0    modules are semantically isomorphic
    1    differences were found
    2    parse / I/O / validate error

SEMANTICS:
    ID renumbering (ValueId, BlockId, StructId, EnumId, RecordId,
    FuncId, TyId, etc.) and declaration order are ignored. Functions
    are aligned by name, blocks by DFS preorder from the entry block,
    and instructions positionally within each block. Types, constants,
    and proof annotations are compared by structural fingerprint.
";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match run(&args) {
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
    json: bool,
    ignore_proofs: bool,
}

fn parse_args(args: &[String]) -> Result<ParsedArgs, String> {
    let mut json = false;
    let mut ignore_proofs = false;
    let mut positional: Vec<PathBuf> = Vec::new();
    let mut i = 0;
    while i < args.len() {
        let a = &args[i];
        match a.as_str() {
            "--json" => json = true,
            "--ignore-proofs" => ignore_proofs = true,
            "-h" | "--help" => {
                print!("{USAGE}");
                std::process::exit(0);
            }
            s if s.starts_with("--") => {
                return Err(format!("unknown option: {s}"));
            }
            _ => positional.push(PathBuf::from(a)),
        }
        i += 1;
    }
    if positional.len() != 2 {
        return Err(format!(
            "expected exactly 2 positional arguments (got {})",
            positional.len()
        ));
    }
    let mut it = positional.into_iter();
    let a = it.next().unwrap();
    let b = it.next().unwrap();
    Ok(ParsedArgs {
        a,
        b,
        json,
        ignore_proofs,
    })
}

fn run(args: &[String]) -> Result<i32, String> {
    let parsed = parse_args(args)?;
    let ma = load(&parsed.a)?;
    let mb = load(&parsed.b)?;
    let opts = DiffOptions {
        ignore_proofs: parsed.ignore_proofs,
    };
    let d = diff_with(&ma, &mb, opts);
    let out = if parsed.json {
        d.to_json()
    } else {
        d.to_text()
    };
    // Always terminate with a newline for terminal ergonomics when
    // producing text; JSON also gets a trailing newline so shell
    // pipelines behave predictably.
    if out.is_empty() {
        // Isomorphic: stay silent in text mode, emit empty JSON doc in JSON mode.
        if parsed.json {
            println!("{}", d.to_json());
        }
    } else {
        println!("{out}");
    }
    Ok(d.exit_code())
}

fn load(path: &PathBuf) -> Result<Module, String> {
    let bytes = fs::read(path).map_err(|e| format!("read {}: {e}", path.display()))?;
    let m: Module =
        serde_json::from_slice(&bytes).map_err(|e| format!("parse {}: {e}", path.display()))?;
    Ok(m)
}
