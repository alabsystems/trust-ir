//! Shared helpers of the two-language area targets: the verdict harness
//! (`harness.rs`), the four-format round trip, validation and the reference
//! interpreter. `mod common;` from every `bN_*.rs`.
//!
//! Multi-module execution goes through the `trust-ir` CLI's private linker,
//! so those rows live in `crates/trust-ir-cli/tests/two_language_cli.rs`,
//! which runs the CLI binary Cargo builds for that test
//! (`CARGO_BIN_EXE_trust-ir`).
#![allow(dead_code)]

#[path = "harness.rs"]
pub mod harness;
#[allow(unused_imports)]
pub use harness::{
    Case, Expect, FAIL, GAP, Outcome, PASS, Verdict, feature, feature_check, feature_gap,
    feature_ratified, run_target,
};

use trust_ir::Module;
use trust_ir::interpret::{InterpretOptions, InterpretValue, InterpretValueKind, Interpreter};

// ---------------------------------------------------------------------------
// Four-format round trip
// ---------------------------------------------------------------------------

/// One format's encode -> decode -> re-encode measurement. Nothing here
/// asserts; the caller decides what is a PASS and what is a GAP.
#[derive(Debug, Clone)]
pub struct FormatTrip {
    pub format: &'static str,
    /// First encoding (bytes; UTF-8 for text and JSON).
    pub encoded: Vec<u8>,
    /// `None` = decoded fine; `Some(reason)` = the decoder refused.
    pub decode_error: Option<String>,
    /// (a) re-encoding the decoded module reproduces `encoded` byte for byte.
    pub reencode_identical: bool,
    /// (b) the decoded module `==` the reference module. The reference is the
    /// original module for binary/JSON/MessagePack and
    /// `trust_ir::format::canonicalize(original)` for text (canonical text
    /// renumbers SSA values densely; `canonicalize` applies the same
    /// renumbering). STRICT: the known text-lossy fields are NOT normalised
    /// away, so for text this is expected to be `false` on many modules.
    pub structurally_equal: bool,
    /// The decoded module, so a caller can show WHICH field was lost.
    pub decoded: Option<Module>,
    /// Text only (roadmap WS4.2): the `; #lossy:` summary the printer wrote
    /// because `format::text_losses` of the canonicalized module is
    /// non-empty. The parser then REFUSES the text (`decode_error` is that
    /// refusal and `decoded` is `None`): a lossy text can no longer be parsed
    /// back into a module that silently lacks the fields.
    pub lossy: Option<String>,
    /// Text only, when `lossy` is set: the module the parser rebuilds from the
    /// same text with the marker line DELETED — the edit a human can make,
    /// because the marker is a tripwire, not integrity. It measures what the
    /// GRAMMAR carries, so a row can still pin exactly which fields text
    /// drops; `reencode_identical` / `structurally_equal` are measured on it.
    pub unmarked: Option<Module>,
}

impl FormatTrip {
    /// What the format carries: the decoded module, or — for a `#lossy`
    /// text the parser refused — the module its grammar rebuilds with the
    /// marker deleted ([`FormatTrip::unmarked`]).
    pub fn carried(&self) -> Option<&Module> {
        self.decoded.as_ref().or(self.unmarked.as_ref())
    }

    /// Text only: parse the encoded text with any `; #lossy:` marker line
    /// deleted (the tripwire edit; see [`FormatTrip::unmarked`]), returning
    /// the parser's refusal when the grammar cannot even read what remains.
    pub fn parse_unmarked(&self) -> Result<Module, String> {
        let text = String::from_utf8_lossy(&self.encoded);
        let stripped: String = text
            .lines()
            .filter(|line| !line.starts_with("; #lossy:"))
            .map(|line| format!("{line}\n"))
            .collect();
        trust_ir::parser::parse_module(&stripped).map_err(|e| format!("{e:?}"))
    }

    /// Text only: the text was printed `#lossy` AND the parser refused it
    /// with the WS4.2 lossy refusal (never a silent drop).
    pub fn refused_as_lossy(&self) -> bool {
        self.lossy.is_some()
            && self
                .decode_error
                .as_deref()
                .is_some_and(|e| e.contains("this text was printed LOSSILY ("))
    }

    pub fn lossless(&self) -> bool {
        self.decode_error.is_none() && self.reencode_identical && self.structurally_equal
    }

    pub fn summary(&self) -> String {
        match &self.decode_error {
            Some(e) => format!("{}:{}B decode-error({e})", self.format, self.encoded.len()),
            None => format!(
                "{}:{}B reencode={} equal={}",
                self.format,
                self.encoded.len(),
                self.reencode_identical,
                self.structurally_equal
            ),
        }
    }
}

#[derive(Debug, Clone)]
pub struct RoundTrip {
    pub binary: FormatTrip,
    pub text: FormatTrip,
    pub json: FormatTrip,
    pub msgpack: FormatTrip,
    /// Wire version the binary writer SELECTED for this module (the minimum
    /// lossless version: 38 legacy .. 43 handle-bearing).
    pub binary_version: u32,
}

impl RoundTrip {
    pub fn all(&self) -> [&FormatTrip; 4] {
        [&self.binary, &self.text, &self.json, &self.msgpack]
    }

    /// All four formats lossless (byte-identical re-encode AND structural equality).
    pub fn lossless_all(&self) -> bool {
        self.all().iter().all(|t| t.lossless())
    }

    /// The three LOSSLESS PRODUCTION transports (binary, JSON, MessagePack).
    pub fn lossless_production(&self) -> bool {
        self.binary.lossless() && self.json.lossless() && self.msgpack.lossless()
    }

    pub fn summary(&self) -> String {
        format!(
            "wire=v{} {} | {} | {} | {}",
            self.binary_version,
            self.binary.summary(),
            self.text.summary(),
            self.json.summary(),
            self.msgpack.summary()
        )
    }
}

/// The four codecs of `tests/conformance.rs`: binary (`trust_ir::binary`),
/// canonical text (`trust_ir::format::canonical` then
/// `trust_ir::parser::parse_module`), JSON (`serde_json`, pretty) and
/// POSITIONAL MessagePack (`rmp_serde::to_vec`, the compact array encoding,
/// not `to_vec_named`).
pub fn roundtrip_all(module: &Module) -> RoundTrip {
    // --- binary ---
    let bin = trust_ir::binary::serialize_module(module).expect("serialize_module: test fixture");
    let binary_version = binary_version(&bin);
    let binary = match trust_ir::binary::deserialize_module(&bin) {
        Ok(back) => FormatTrip {
            format: "binary",
            reencode_identical: trust_ir::binary::serialize_module(&back)
                .expect("serialize_module: test fixture")
                == bin,
            structurally_equal: &back == module,
            decode_error: None,
            decoded: Some(back),
            encoded: bin,
            lossy: None,
            unmarked: None,
        },
        Err(e) => failed("binary", bin, format!("{e:?}")),
    };

    // --- canonical text ---
    let text_src = trust_ir::format::canonical(module);
    let canon = trust_ir::format::canonicalize(module);
    let losses = trust_ir::format::text_losses(&canon);
    let lossy = (!losses.is_empty()).then(|| {
        losses
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(", ")
    });
    let text = match trust_ir::parser::parse_module(&text_src) {
        Ok(back) => FormatTrip {
            format: "text",
            reencode_identical: trust_ir::format::canonical(&back) == text_src,
            structurally_equal: back == canon,
            decode_error: None,
            decoded: Some(back),
            encoded: text_src.into_bytes(),
            lossy,
            unmarked: None,
        },
        Err(e) => {
            // WS4.2: a `#lossy` text is refused; measure what the grammar
            // carries by deleting the marker (test-only; see `unmarked`).
            let stripped: String = text_src
                .lines()
                .filter(|line| !line.starts_with("; #lossy:"))
                .map(|line| format!("{line}\n"))
                .collect();
            let unmarked = lossy
                .as_ref()
                .and_then(|_| trust_ir::parser::parse_module(&stripped).ok());
            let mut trip = failed("text", text_src.into_bytes(), format!("{e:?}"));
            if let Some(back) = &unmarked {
                trip.reencode_identical = trust_ir::format::canonical(back) == stripped;
                trip.structurally_equal = *back == canon;
            }
            trip.lossy = lossy;
            trip.unmarked = unmarked;
            trip
        }
    };

    // --- JSON ---
    let json = match serde_json::to_string_pretty(module) {
        Err(e) => failed("json", Vec::new(), format!("ENCODE: {e}")),
        Ok(src) => match serde_json::from_str::<Module>(&src) {
            Ok(back) => FormatTrip {
                format: "json",
                reencode_identical: serde_json::to_string_pretty(&back)
                    .map(|again| again == src)
                    .unwrap_or(false),
                structurally_equal: &back == module,
                decode_error: None,
                decoded: Some(back),
                encoded: src.into_bytes(),
                lossy: None,
                unmarked: None,
            },
            Err(e) => failed("json", src.into_bytes(), e.to_string()),
        },
    };

    // --- positional MessagePack ---
    let msgpack = match rmp_serde::to_vec(module) {
        Err(e) => failed("msgpack", Vec::new(), format!("ENCODE: {e}")),
        Ok(bytes) => match rmp_serde::from_slice::<Module>(&bytes) {
            Ok(back) => FormatTrip {
                format: "msgpack",
                reencode_identical: rmp_serde::to_vec(&back)
                    .map(|again| again == bytes)
                    .unwrap_or(false),
                structurally_equal: &back == module,
                decode_error: None,
                decoded: Some(back),
                encoded: bytes,
                lossy: None,
                unmarked: None,
            },
            Err(e) => failed("msgpack", bytes, e.to_string()),
        },
    };

    RoundTrip {
        binary,
        text,
        json,
        msgpack,
        binary_version,
    }
}

fn failed(format: &'static str, encoded: Vec<u8>, reason: String) -> FormatTrip {
    FormatTrip {
        format,
        encoded,
        decode_error: Some(reason),
        reencode_identical: false,
        structurally_equal: false,
        decoded: None,
        lossy: None,
        unmarked: None,
    }
}

/// Wire version from a TrustIr binary header: 8-byte magic `TRUST_IR` then a
/// little-endian `u32`. Panics on a blob that is not a TrustIr module (a test
/// bug, not a verdict).
pub fn binary_version(bytes: &[u8]) -> u32 {
    assert!(
        bytes.len() >= 12 && &bytes[..8] == b"TRUST_IR",
        "binary_version: not a TrustIr module blob (bad magic / too short)"
    );
    u32::from_le_bytes([bytes[8], bytes[9], bytes[10], bytes[11]])
}

// ---------------------------------------------------------------------------
// Validation convenience
// ---------------------------------------------------------------------------

/// `validate_module` errors, Debug-rendered. Empty = well-formed.
pub fn validation_errors(module: &Module) -> Vec<String> {
    trust_ir_build::validate_module(module)
        .iter()
        .map(|e| format!("{e:?}"))
        .collect()
}

// ---------------------------------------------------------------------------
// Reference interpreter
// ---------------------------------------------------------------------------

/// Host stack for the interpreter thread: `execute_function` recurses on the
/// Rust stack once per interpreted call frame (the CLI uses 512 MiB).
const RUN_STACK_BYTES: usize = 256 * 1024 * 1024;

pub fn run_options() -> InterpretOptions {
    InterpretOptions {
        fuel: 50_000_000,
        max_call_depth: 4096,
        ..InterpretOptions::default()
    }
}

/// Execute `entry` (looked up by `Function.name`, i.e. the link-time symbol)
/// with `args` on the in-process reference interpreter (ONE module, calls
/// resolved by FuncId). `Err` carries the interpreter's own `code: message`.
pub fn run_with_args(
    module: &Module,
    entry: &str,
    args: Vec<InterpretValue>,
) -> Result<Vec<InterpretValue>, String> {
    let func = module
        .function_by_name(entry)
        .ok_or_else(|| format!("no function named @{entry}"))?;
    let id = func.id;
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .name("two-language-interp".into())
            .stack_size(RUN_STACK_BYTES)
            .spawn_scoped(scope, move || {
                Interpreter::with_module(module)
                    .with_options(run_options())
                    .execute_func(id, args)
                    .map(|outcome| outcome.returns)
                    .map_err(|e| format!("{:?}: {e}", e.code))
            })
            .map_err(|e| format!("spawn interpreter thread: {e}"))?
            .join()
            .map_err(|_| "interpreter thread panicked".to_string())?
    })
}

/// `run_with_args` with no arguments, refusing a non-nullary entry up front.
pub fn run_nullary(module: &Module, entry: &str) -> Result<Vec<InterpretValue>, String> {
    let func = module
        .function_by_name(entry)
        .ok_or_else(|| format!("no function named @{entry}"))?;
    match module.func_type(func.ty) {
        Some(sig) if sig.params.is_empty() => run_with_args(module, entry, Vec::new()),
        Some(sig) => Err(format!("@{entry} takes {} parameter(s)", sig.params.len())),
        None => Err(format!("@{entry} references an undefined signature")),
    }
}

/// Integer return value as unsigned (`None` for a non-integer).
pub fn as_u128(value: &InterpretValue) -> Option<u128> {
    value.as_int().map(|i| i.as_unsigned())
}

/// Integer return value as signed.
pub fn as_i128(value: &InterpretValue) -> Option<i128> {
    value.as_int().map(|i| i.as_signed())
}

/// Same rendering as `trust-ir run` prints (ints decimal, bool 0/1).
pub fn render_value(value: &InterpretValue) -> String {
    match &value.kind {
        InterpretValueKind::Int(int) => {
            if int.signed {
                int.as_signed().to_string()
            } else {
                int.as_unsigned().to_string()
            }
        }
        InterpretValueKind::Bool(b) => u8::from(*b).to_string(),
        InterpretValueKind::Unit => "()".to_string(),
        InterpretValueKind::NullPtr => "null".to_string(),
        other => format!("{other:?}"),
    }
}
