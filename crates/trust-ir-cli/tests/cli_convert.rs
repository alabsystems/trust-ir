// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for `trust-ir convert` — including the 4-format round-trip
//! acceptance criterion from issue #61.

mod common;

use std::fs;

use tempfile::tempdir;

use common::{build_valid_module, trust_ir_cmd};

fn run_convert(
    from: &str,
    to: &str,
    input: &std::path::Path,
    output: &std::path::Path,
) -> std::process::Output {
    trust_ir_cmd()
        .arg("convert")
        .arg("--from")
        .arg(from)
        .arg("--to")
        .arg(to)
        .arg(input)
        .arg(output)
        .output()
        .expect("run trust-ir")
}

#[test]
fn convert_bin_to_json_succeeds() {
    let dir = tempdir().expect("tempdir");
    let bin_path = dir.path().join("m.tmbc");
    let json_path = dir.path().join("m.json");
    let module = build_valid_module();
    fs::write(
        &bin_path,
        trust_ir::binary::serialize_module(&module).expect("serialize_module: test fixture"),
    )
    .expect("write");

    let out = run_convert("bin", "json", &bin_path, &json_path);
    assert!(
        out.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );

    let bytes = fs::read(&json_path).expect("read json");
    let decoded: trust_ir::Module = serde_json::from_slice(&bytes).expect("json decode");
    assert_eq!(decoded, module);
}

/// Acceptance criterion (#61): `trust-ir dump` round-trips through all four
/// formats. We exercise the CLI's `convert` chain rather than `dump` (which
/// only writes text to stdout); the invariant under test is that the CLI
/// preserves the module across every supported format transition.
///
/// NB: the text format is intentionally lossy for a handful of
/// bookkeeping fields — in particular `Module::func_types` and function-
/// level `proofs` are not serialized in v1 text (see
/// `crates/trust_ir/src/display.rs`). This test therefore runs two chains:
///
///   1. Lossless formats only: bin → json → msgpack → bin (module equality).
///   2. Every format including text: bin → text → json → msgpack → bin
///      (pipeline completes without error; text→text is already covered by
///      the parser's own round-trip tests).
#[test]
fn convert_round_trip_through_all_four_formats() {
    let dir = tempdir().expect("tempdir");
    let original = build_valid_module();

    // ---- Chain 1: lossless formats (strict module equality) ----
    let bin_path = dir.path().join("m.tmbc");
    fs::write(
        &bin_path,
        trust_ir::binary::serialize_module(&original).expect("serialize_module: test fixture"),
    )
    .expect("write");

    let json_path = dir.path().join("m.json");
    let out = run_convert("bin", "json", &bin_path, &json_path);
    assert!(
        out.status.success(),
        "bin->json: {}",
        String::from_utf8_lossy(&out.stderr)
    );

    let msg_path = dir.path().join("m.msgpack");
    let out = run_convert("json", "msgpack", &json_path, &msg_path);
    assert!(
        out.status.success(),
        "json->msgpack: {}",
        String::from_utf8_lossy(&out.stderr)
    );

    let bin2_path = dir.path().join("m_back.tmbc");
    let out = run_convert("msgpack", "bin", &msg_path, &bin2_path);
    assert!(
        out.status.success(),
        "msgpack->bin: {}",
        String::from_utf8_lossy(&out.stderr)
    );

    let final_bytes = fs::read(&bin2_path).expect("read bin2");
    let final_module = trust_ir::binary::deserialize_module(&final_bytes).expect("decode bin2");
    assert_eq!(
        final_module, original,
        "lossless round-trip (bin -> json -> msgpack -> bin) must preserve the module"
    );

    // ---- Chain 2: every format including text (pipeline completes) ----
    // We cannot assert module equality here: the v1 text format deliberately
    // omits Module::func_types and Function::proofs (see display.rs). The
    // invariant we CAN check is that every CLI step returns success and
    // produces a file the next step can read.
    let text_path = dir.path().join("m_text.trust_ir");
    let out = run_convert("bin", "text", &bin_path, &text_path);
    assert!(
        out.status.success(),
        "bin->text: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(fs::metadata(&text_path).expect("text exists").len() > 0);

    let json2_path = dir.path().join("m2.json");
    let out = run_convert("text", "json", &text_path, &json2_path);
    assert!(
        out.status.success(),
        "text->json: {}",
        String::from_utf8_lossy(&out.stderr)
    );

    let msg2_path = dir.path().join("m2.msgpack");
    let out = run_convert("json", "msgpack", &json2_path, &msg2_path);
    assert!(
        out.status.success(),
        "json->msgpack: {}",
        String::from_utf8_lossy(&out.stderr)
    );

    let bin3_path = dir.path().join("m2_back.tmbc");
    let out = run_convert("msgpack", "bin", &msg2_path, &bin3_path);
    assert!(
        out.status.success(),
        "msgpack->bin: {}",
        String::from_utf8_lossy(&out.stderr)
    );

    // Final sanity check: the final binary is a valid TrustIr blob with the
    // TRUST_IR magic and can be re-decoded.
    let tail_bytes = fs::read(&bin3_path).expect("read bin3");
    assert!(tail_bytes.starts_with(b"TRUST_IR"));
    let _final2 = trust_ir::binary::deserialize_module(&tail_bytes).expect("final decode");
}

#[test]
fn convert_text_to_bin_produces_valid_trust_ir_file() {
    let dir = tempdir().expect("tempdir");
    let text_path = dir.path().join("m_text.trust_ir");
    let bin_path = dir.path().join("m.tmbc");
    fs::write(&text_path, format!("{}", build_valid_module())).expect("write");

    let out = run_convert("text", "bin", &text_path, &bin_path);
    assert!(
        out.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );

    let bytes = fs::read(&bin_path).expect("read");
    assert!(
        bytes.starts_with(b"TRUST_IR"),
        "binary output must carry the TRUST_IR magic"
    );
}

// ---------------------------------------------------------------------------
// Roadmap WS4.2 (F-065): `convert --to text` refuses what text cannot carry.
// ---------------------------------------------------------------------------

/// Negative twin: ONE `FunctionSummary` clause whose binding sort nests deeper
/// than `MAX_TEXT_CLAUSE_SORT_DEPTH` — the one summary shape text still cannot
/// carry since WS4.4 carried the summary itself. The conversion exits 1, names
/// the loss, and writes NO output file. (Until WS4.5 the example was ONE
/// `global_asm` block, the field whose silent loss used to launder the
/// `GlobalAsmNotConsumable` codegen refusal through text; text now CARRIES it —
/// see `convert_to_text_carries_global_asm_and_its_refusal`.)
#[test]
fn convert_to_text_refuses_a_module_text_cannot_carry() {
    use trust_ir::proof::{ClauseBinding, ClausePlace, ClauseSort, ProofFormula};
    let dir = tempdir().expect("tempdir");
    let bin_path = dir.path().join("summary.tmbc");
    let text_path = dir.path().join("summary.trust_ir");
    let mut module = build_valid_module();
    let mut sort = ClauseSort::Bool;
    for _ in 0..trust_ir::text_loss::MAX_TEXT_CLAUSE_SORT_DEPTH {
        sort = ClauseSort::Array(Box::new(ClauseSort::Int), Box::new(sort));
    }
    let mut clause = ProofFormula::smtlib2("(= x x)", "Bool");
    clause.bindings.push((
        "x".to_string(),
        ClauseBinding {
            sort,
            place: ClausePlace::World,
        },
    ));
    module.functions[0].summary = Some(trust_ir::FunctionSummary::new().ensuring(clause));
    fs::write(
        &bin_path,
        trust_ir::binary::serialize_module(&module).expect("serialize_module: test fixture"),
    )
    .expect("write");

    let out = run_convert("bin", "text", &bin_path, &text_path);
    assert_eq!(out.status.code(), Some(1), "{out:?}");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("the TrustIr text format cannot carry 1 field(s)")
            && stderr.contains("function-summary(fn 0)"),
        "stderr names the loss: {stderr}"
    );
    assert!(!text_path.exists(), "no lossy text is written");

    // The lossless transports still carry it: bin -> msgpack -> bin through
    // the CLI gives back the exact summary. (Measured: JSON cannot be the
    // witness for THIS clause — serde_json's reader stops at its 128-level
    // recursion limit, and a 65-deep sort is 130 JSON levels.)
    let msg_path = dir.path().join("summary.msgpack");
    let out = run_convert("bin", "msgpack", &bin_path, &msg_path);
    assert!(out.status.success(), "{out:?}");
    let back_path = dir.path().join("summary_back.tmbc");
    let out = run_convert("msgpack", "bin", &msg_path, &back_path);
    assert!(out.status.success(), "{out:?}");
    let back = trust_ir::binary::deserialize_module(&fs::read(&back_path).expect("read"))
        .expect("binary decode");
    assert!(back.functions[0].summary.is_some());
    assert_eq!(back.functions[0].summary, module.functions[0].summary);
}

/// WS4.5 (F-065): ONE `global_asm` block converts to text, the text carries
/// it as a `global_asm "<escaped>"` line, and `text -> bin` gives back the
/// SAME bytes — so the `GlobalAsmNotConsumable` codegen refusal cannot be
/// laundered through `convert`.
#[test]
fn convert_to_text_carries_global_asm_and_its_refusal() {
    let dir = tempdir().expect("tempdir");
    let bin_path = dir.path().join("asm.tmbc");
    let text_path = dir.path().join("asm.trust_ir");
    let back_path = dir.path().join("asm.back.tmbc");
    let mut module = build_valid_module();
    module.global_asm.push(".globl _x\n_x: ret".into());
    let bytes =
        trust_ir::binary::serialize_module(&module).expect("serialize_module: test fixture");
    fs::write(&bin_path, &bytes).expect("write");

    let out = run_convert("bin", "text", &bin_path, &text_path);
    assert!(out.status.success(), "{out:?}");
    let text = fs::read_to_string(&text_path).expect("read text");
    assert!(!text.contains("#lossy"), "{text}");
    assert!(
        text.contains("global_asm \".globl _x\\n_x: ret\"\n"),
        "{text}"
    );
    let out = run_convert("text", "bin", &text_path, &back_path);
    assert!(out.status.success(), "{out:?}");
    assert_eq!(fs::read(&back_path).expect("read back"), bytes);
}

/// Positive twin (mutation control: the refusal is caused by the loss, not
/// by the command): the same module WITHOUT the block converts to text, and
/// that text parses back to the module exactly — not to a canonicalized
/// rewrite of it.
#[test]
fn convert_to_text_of_a_loss_free_module_is_exact() {
    let dir = tempdir().expect("tempdir");
    let bin_path = dir.path().join("ok.tmbc");
    let text_path = dir.path().join("ok.trust_ir");
    let module = build_valid_module();
    assert!(trust_ir::format::text_losses(&module).is_empty());
    fs::write(
        &bin_path,
        trust_ir::binary::serialize_module(&module).expect("serialize_module: test fixture"),
    )
    .expect("write");

    let out = run_convert("bin", "text", &bin_path, &text_path);
    assert!(out.status.success(), "{out:?}");
    let text = fs::read_to_string(&text_path).expect("read text");
    assert!(!text.contains("#lossy"), "{text}");
    let parsed = trust_ir::parser::parse_module(&text).expect("parses");
    assert_eq!(parsed, module);
}

/// `convert` is a TRANSPORT: `bin -> text -> bin` must be byte-identical for a
/// module the text grammar can carry, INCLUDING one whose SSA value ids are
/// not in canonical order.
///
/// The regression this pins: `convert --to text` used to emit
/// `format::canonical_checked`, which renumbers every value densely (all block
/// parameters first, then instruction results) before printing. Nothing
/// reported that — canonicalization is a declared rewrite, not a `TextLoss` —
/// so the text parsed back cleanly into a DIFFERENT module than the producer
/// emitted, and the byte compare failed with an empty loss list. Sparse and
/// interleaved ids are legal: SSA validation requires unique definitions and
/// dominance, not density.
#[test]
fn convert_bin_text_bin_is_byte_identical_for_non_canonical_value_ids() {
    use trust_ir::inst::Inst;
    use trust_ir::node::InstrNode;
    use trust_ir::ty::{FuncTy, Ty};
    use trust_ir::value::{BlockId, FuncId, ValueId};
    use trust_ir::{Block, Function, Module};

    // Two blocks whose definitions INTERLEAVE the way a real producer's do:
    // bb0's parameter (%0), then bb0's instruction result (%1), and only then
    // bb1's parameter (%2). Canonical form would renumber that last one to %1.
    let mut module = Module::new("interleaved");
    let ft = module
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = Function::new(FuncId::new(0), "f", ft, BlockId::new(0));

    let mut bb0 = Block::new(BlockId::new(0));
    bb0.params.push((ValueId::new(0), Ty::I64));
    bb0.body.push(
        InstrNode::new(Inst::BinOp {
            op: trust_ir::inst::BinOp::Add,
            ty: Ty::I64,
            lhs: ValueId::new(0),
            rhs: ValueId::new(0),
        })
        .with_result(ValueId::new(1)),
    );
    bb0.body.push(InstrNode::new(Inst::Br {
        target: BlockId::new(1),
        args: vec![ValueId::new(1)],
    }));

    let mut bb1 = Block::new(BlockId::new(1));
    bb1.params.push((ValueId::new(2), Ty::I64));
    bb1.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(2)],
    }));

    func.blocks.push(bb0);
    func.blocks.push(bb1);
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");

    // The fixture is well-formed, text-carryable, and genuinely NOT canonical
    // — otherwise this test could not see a renumbering printer.
    assert!(trust_ir_build::validate_module(&module).is_empty());
    assert!(trust_ir::format::text_losses(&module).is_empty());
    assert_ne!(trust_ir::format::canonicalize(&module), module);

    let dir = tempdir().expect("tempdir");
    let bin_path = dir.path().join("m.tmbc");
    let text_path = dir.path().join("m.trust_ir");
    let back_path = dir.path().join("m_back.tmbc");
    let original =
        trust_ir::binary::serialize_module(&module).expect("serialize_module: test fixture");
    fs::write(&bin_path, &original).expect("write");

    let out = run_convert("bin", "text", &bin_path, &text_path);
    assert!(
        out.status.success(),
        "bin->text: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let text = fs::read_to_string(&text_path).expect("read text");
    assert!(
        text.contains("bb1(%2: i64)"),
        "the text must carry bb1's OWN parameter id, not a renumbered one:\n{text}"
    );

    let out = run_convert("text", "bin", &text_path, &back_path);
    assert!(
        out.status.success(),
        "text->bin: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(
        fs::read(&back_path).expect("read back"),
        original,
        "bin -> text -> bin must be byte-identical"
    );
}
