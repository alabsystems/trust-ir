// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// TrustIr serialization conformance corpus.
//
// This harness is the single entry point for cross-format compatibility
// verification. It runs every fixture from `generate.rs` through all
// four supported serialization formats and compares the output
// byte-for-byte against the checked-in goldens in `tests/fixtures/`.
//
// Running:
//   cargo test -p trust-ir-conformance --test conformance
//
// Regenerating goldens after an intentional format change:
//   TRUST_IR_UPDATE_FIXTURES=1 cargo test -p trust-ir-conformance --test conformance
//
// When TRUST_IR_UPDATE_FIXTURES is set, the harness writes goldens instead
// of comparing and still fails the run if the regenerated output does
// not round-trip (catches one-way breakage even during a bump).
//
// What this corpus guarantees:
//
//   1. Every `Ty`, `Inst`, and `ProofAnnotation` variant is exercised
//      by at least one fixture (see `coverage` test below).
//   2. Every fixture round-trips losslessly through binary, text,
//      JSON, and MessagePack. (Binding-frame instructions now parse
//      from text too, closing the former TrustIr#64 gap.)
//   3. The produced bytes are byte-identical to the checked-in
//      golden for every format, i.e. downstream consumers (TrustIr,
//      tRust, ay, ty) can pin this corpus and detect wire-format
//      drift immediately.
//   4. Proof-lineage sidecars have standalone binary/JSON/MessagePack
//      goldens so Trust can pin proof persistence independently from
//      the module `.tmbc` format.
//
// Format-specific notes:
//
// * Binary (`.tmbc`): produced via `trust-ir::binary::serialize_module`
//   (header carries `binary::VERSION`, currently v34; v23 is
//   MIN_READ_VERSION; readers accept v23–v25 and v29–v34 and reject ambiguous
//   v26–v28). The per-section tag layout is documented in
//   `docs/binary-format.md` (the TrustIr#65 freeze doc, normative for
//   the wire format).
// * Text (`.trust_ir`): produced via `trust-ir::format::canonical` so the
//   output is diff-stable regardless of the builder's internal arena
//   layout. The text parser is re-run on the canonical form as a
//   round-trip sanity check.
// * JSON (`.json`): serde_json pretty-printed (4-space indent) with
//   sorted keys implicit via serde derive ordering. `Constant::Float`
//   uses the `{"bits": <u64>}` codec (see `trust-ir::constant`), so every
//   IEEE-754 bit pattern — including NaN/∞ — round-trips.
// * MessagePack (`.msgpack`): `rmp_serde::to_vec` default encoding.
//   Proof-lineage sidecar `.msgpack` fixtures use `to_vec_named` so the
//   C-like lineage enums remain self-describing across rmp-serde versions.

use std::fs;
use std::path::{Path, PathBuf};

use trust_ir::proof::ProofAnnotation;
use trust_ir::{
    Block, BlockId, CastLayoutEvidence, Constant, FuncId, FuncTy, Function, ICmpOp, Inst,
    InstrNode, InterpretValue, InterpretValueKind, Interpreter, Module, NativeAssertionId,
    NativeCompilerFactId, NativeCompilerFactRef, NativeEvidenceArtifactKind, NativeEvidenceBundle,
    NativeMonomorphizationId, NativeObligationCause, NativeReplayAtomKind,
    NativeUnknownFieldPolicy, NativeUnsupportedMode, NativeUnsupportedModeReason,
    NativeVerificationBundle, NativeVerificationBundleError, NativeVerificationRequest,
    NativeVerifierSuite, ProofCertificate, ProofDigest, ProofEvidence, ProofId, ProofLineageError,
    ProofLineageId, ProofLineageManifest, ProofStatus, TrustMcChcEngine, TrustMcPdrGeneralization,
    TrustMcVerificationMode, TrustVcVerificationMode, TrustWpVerificationMode, Ty, ValueId,
};

// Fixture generators live in a sibling file and are included directly
// so they share the test binary (keeping a single `#[test]` crate).
#[path = "generate.rs"]
mod generate;

/// Returns the absolute path to the `tests/fixtures/` directory.
fn fixtures_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
}

/// True when `TRUST_IR_UPDATE_FIXTURES` is set to a non-empty value.
fn update_mode() -> bool {
    std::env::var("TRUST_IR_UPDATE_FIXTURES")
        .map(|v| !v.is_empty())
        .unwrap_or(false)
}

/// Compare `got` against the golden at `path`, or write `got` when
/// `TRUST_IR_UPDATE_FIXTURES=1` is set. Used for byte-oriented formats.
fn assert_or_update_bytes(path: &Path, got: &[u8]) {
    if update_mode() {
        fs::create_dir_all(path.parent().unwrap()).expect("create fixture dir");
        fs::write(path, got).expect("write fixture");
        return;
    }
    let expected = fs::read(path).unwrap_or_else(|e| {
        panic!(
            "missing fixture {}: {}. Run `TRUST_IR_UPDATE_FIXTURES=1 cargo test -p trust-ir-conformance --test conformance` to generate.",
            path.display(),
            e
        )
    });
    if expected != got {
        panic!(
            "byte-level mismatch for fixture {}: got {} bytes, expected {} bytes.\n\
             Hint: if this is an intentional format change, re-run with \
             `TRUST_IR_UPDATE_FIXTURES=1` and review the diff before committing.",
            path.display(),
            got.len(),
            expected.len()
        );
    }
}

/// Text variant of [`assert_or_update_bytes`] used for the canonical
/// `.trust_ir` golden files (keeps error messages readable).
fn assert_or_update_text(path: &Path, got: &str) {
    if update_mode() {
        fs::create_dir_all(path.parent().unwrap()).expect("create fixture dir");
        fs::write(path, got).expect("write fixture");
        return;
    }
    let expected = fs::read_to_string(path).unwrap_or_else(|e| {
        panic!(
            "missing fixture {}: {}. Run `TRUST_IR_UPDATE_FIXTURES=1 cargo test -p trust-ir-conformance --test conformance` to generate.",
            path.display(),
            e
        )
    });
    if expected != got {
        // Print a minimal diff-style line count so the failure message
        // stays short (Rust's `assert_eq!` on long strings can swamp
        // the terminal).
        panic!(
            "text mismatch for fixture {}: got {} lines, expected {} lines.\n\
             Hint: if this is an intentional format change, re-run with \
             `TRUST_IR_UPDATE_FIXTURES=1` and review the diff before committing.",
            path.display(),
            got.lines().count(),
            expected.lines().count()
        );
    }
}

/// One row of the corpus. `text_supported == false` means the text
/// parser cannot (yet) round-trip this fixture; the `.trust_ir` golden is
/// skipped until the blocking issue is resolved.
struct Fixture {
    name: &'static str,
    build: fn() -> Module,
    text_supported: bool,
    text_skip_reason: &'static str,
}

/// The fixtures are intentionally ordered by the prompt layout
/// (ty → inst → proof) so a directory listing reads top-to-bottom.
fn corpus() -> Vec<Fixture> {
    vec![
        Fixture {
            name: "ty_primitives",
            build: generate::build_ty_primitives,
            text_supported: true,
            text_skip_reason: "",
        },
        Fixture {
            name: "ty_composite",
            build: generate::build_ty_composite,
            text_supported: true,
            text_skip_reason: "",
        },
        Fixture {
            name: "inst_arithmetic",
            build: generate::build_inst_arithmetic,
            text_supported: true,
            text_skip_reason: "",
        },
        Fixture {
            name: "inst_seq_map",
            build: generate::build_inst_seq_map,
            text_supported: true,
            text_skip_reason: "",
        },
        Fixture {
            name: "inst_seq_map_not",
            build: generate::build_inst_seq_map_not,
            text_supported: true,
            text_skip_reason: "",
        },
        Fixture {
            name: "inst_seq_map_general",
            build: generate::build_inst_seq_map_general,
            text_supported: true,
            text_skip_reason: "",
        },
        Fixture {
            name: "inst_vector",
            build: generate::build_inst_vector,
            text_supported: true,
            text_skip_reason: "",
        },
        Fixture {
            name: "inst_vector_dialect",
            build: generate::build_inst_vector_dialect,
            text_supported: true,
            text_skip_reason: "",
        },
        Fixture {
            name: "inst_vector_crosslane",
            build: generate::build_inst_vector_crosslane,
            text_supported: true,
            text_skip_reason: "",
        },
        Fixture {
            name: "inst_memory",
            build: generate::build_inst_memory,
            text_supported: true,
            text_skip_reason: "",
        },
        Fixture {
            name: "inst_control",
            build: generate::build_inst_control,
            text_supported: true,
            text_skip_reason: "",
        },
        Fixture {
            name: "inst_atomic",
            build: generate::build_inst_atomic,
            text_supported: true,
            text_skip_reason: "",
        },
        Fixture {
            name: "inst_borrow_arc",
            build: generate::build_inst_borrow_arc,
            text_supported: true,
            text_skip_reason: "",
        },
        Fixture {
            name: "inst_binding_frames",
            build: generate::build_inst_binding_frames,
            text_supported: true,
            text_skip_reason: "",
        },
        Fixture {
            name: "inst_dialect",
            build: generate::build_inst_dialect,
            text_supported: true,
            text_skip_reason: "",
        },
        Fixture {
            name: "proof_annotations",
            build: generate::build_proof_annotations,
            text_supported: true,
            text_skip_reason: "",
        },
        // ABI pinning: v20 byval/sret ParamAttrs (aggregate passed/returned
        // through memory at a call edge).
        Fixture {
            name: "func_param_abi",
            build: generate::build_func_param_abi,
            text_supported: true,
            text_skip_reason: "",
        },
        Fixture {
            name: "proof_diagnostics",
            build: generate::build_proof_diagnostics,
            text_supported: true,
            text_skip_reason: "",
        },
        Fixture {
            name: "chc_batch",
            build: generate::build_chc_batch_fixture,
            text_supported: true,
            text_skip_reason: "",
        },
        // The integration-frontend-emission worked example: a two-function
        // module emitted entirely through the v1 lowering-target subset
        // (lowering-target-subset.md, repo root) with spans + function-level
        // conv/attrs set through the builder. The lowering_subset gate test
        // additionally asserts it is subset-clean, validates, and is fully
        // span-covered.
        Fixture {
            name: "frontend_emission_subset",
            build: generate::build_frontend_emission_subset,
            text_supported: true,
            text_skip_reason: "",
        },
        // The Rust frontend's panic-class obligation rung: `Pending`
        // BoundsCheck / ArithmeticSafety / PanicFreedom rows recorded from
        // rustc MIR `Assert` terminators, B4-scoped and source-identified.
        // BoundsCheck and ArithmeticSafety appear in NO other fixture, so this
        // is the only byte-golden guard on their text/binary/JSON/MessagePack
        // spelling.
        Fixture {
            name: "frontend_panic_obligations",
            build: generate::build_frontend_panic_obligations,
            text_supported: true,
            text_skip_reason: "",
        },
        // Separate-compilation contract: a body-less, contract-only declaration
        // (`Function.summary`) plus a defined function that also publishes its
        // contract. The canonical text form intentionally does not render the
        // verifier-facing contract (`text_supported: false`); binary / JSON /
        // MessagePack guard it losslessly. (`summary` is positionally-safe in
        // MessagePack — always emitted, declared before the single trailing
        // optional `attrs` — so this round-trips through every format.)
        Fixture {
            name: "composition",
            build: generate::build_composition,
            text_supported: false,
            text_skip_reason: "canonical text does not render the verifier-facing FunctionSummary contract; \
                 the binary/JSON/MessagePack goldens guard it losslessly",
        },
        // v23 producer provenance: every `Producer` wire tag (including the
        // `Other` string escape) plus an untagged function, emitted through
        // the ModuleBuilder default + FunctionBuilder override surface. The
        // `.trust_ir` golden additionally pins the `; #producer:` header
        // clause in canonical text.
        Fixture {
            name: "producer_provenance",
            build: generate::build_producer_provenance,
            text_supported: true,
            text_skip_reason: "",
        },
        // v32/v33 debug metadata plus v23 producer provenance in one Function
        // record: sparse SSA names, lexical-scope tree, and per-node scope
        // indices must agree across all four formats.
        Fixture {
            name: "debug_metadata_v33",
            build: generate::build_debug_metadata_v33,
            text_supported: true,
            text_skip_reason: "",
        },
        // v24 128-bit-faithful integer carrier: `Constant::U128` (wire tag
        // 13) at both canonical boundaries (i128::MAX + 1, u128::MAX) plus
        // the Int spelling AT the boundary — pinning the one-spelling split
        // across binary/text/JSON/MessagePack.
        Fixture {
            name: "u128_constants",
            build: generate::build_u128_constants,
            text_supported: true,
            text_skip_reason: "",
        },
        // v25 byte-array carrier: Constant::Bytes (wire tag 14) — raw, utf8
        // (multibyte), and empty payloads as global initializers plus one
        // in-body Inst::Const use, across all four formats.
        Fixture {
            name: "bytes_constants",
            build: generate::build_bytes_constants,
            text_supported: true,
            text_skip_reason: "",
        },
        // v25 B1 scalars: pointer-width ints (isize/usize) and char across
        // signatures, arithmetic, and constants — wire coverage for tags
        // 33-35 in all four formats.
        Fixture {
            name: "b1_scalars",
            build: generate::build_b1_scalars,
            text_supported: true,
            text_skip_reason: "",
        },
        // WS3-M1 seed: one module, BOTH producers (TRust + Clean v23 tags),
        // cross-producer calls in BOTH directions, subset-clean arithmetic
        // bodies. Validation/rejection/interpreter acceptance lives in
        // tests/mixed_producer.rs; this corpus row pins the wire form.
        Fixture {
            name: "mixed_producer_module",
            build: generate::build_mixed_producer_module,
            text_supported: true,
            text_skip_reason: "",
        },
    ]
}

struct LineageFixture {
    name: &'static str,
    build: fn() -> generate::ProofLineageFixture,
}

fn lineage_corpus() -> Vec<LineageFixture> {
    vec![
        LineageFixture {
            name: "proof_lineage_single_stage",
            build: generate::build_proof_lineage_single_stage,
        },
        LineageFixture {
            name: "proof_lineage_multi_stage",
            build: generate::build_proof_lineage_multi_stage,
        },
    ]
}

struct NativeBundleFixture {
    name: &'static str,
    build: fn() -> generate::NativeBundleFixture,
}

fn native_bundle_corpus() -> Vec<NativeBundleFixture> {
    vec![NativeBundleFixture {
        name: "native_request_trust_bundle",
        build: generate::build_trust_native_request_bundle,
    }]
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crates dir")
        .parent()
        .expect("repo root")
        .to_path_buf()
}

fn executable_fixtures_lean_path() -> PathBuf {
    repo_root()
        .join("lean")
        .join("trust_ir-semantics")
        .join("TrustIr")
        .join("Semantics")
        .join("ExecutableFixtures.lean")
}

fn read_native_bundle_fixture(name: &str) -> NativeVerificationBundle {
    let path = fixtures_dir().join(format!("{name}.json"));
    let json = fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("read native bundle fixture {}: {e}", path.display()));
    serde_json::from_str(&json)
        .unwrap_or_else(|e| panic!("parse native bundle fixture {}: {e}", path.display()))
}

fn icmp_op_name(op: ICmpOp) -> &'static str {
    match op {
        ICmpOp::Eq => "eq",
        ICmpOp::Ne => "ne",
        ICmpOp::Ult => "ult",
        ICmpOp::Ule => "ule",
        ICmpOp::Ugt => "ugt",
        ICmpOp::Uge => "uge",
        ICmpOp::Slt => "slt",
        ICmpOp::Sle => "sle",
        ICmpOp::Sgt => "sgt",
        ICmpOp::Sge => "sge",
    }
}

fn mask_ty_lanes(mask_ty: &Ty) -> u32 {
    match mask_ty {
        Ty::Vector(elem, lanes) if **elem == Ty::Bool => *lanes,
        other => panic!("oracle mask_ty must be a bool vector, got {other}"),
    }
}

fn vector_ty_lanes(ty: &Ty) -> u32 {
    match ty {
        Ty::Vector(_, lanes) => *lanes,
        other => panic!("oracle compare_ty must be a vector, got {other}"),
    }
}

fn integer_result_bits(ty: &Ty) -> u32 {
    match ty {
        Ty::I32 => 32,
        Ty::I64 => 64,
        other => panic!("oracle result_ty must be i32 or i64, got {other}"),
    }
}

fn upper_zero_mask(result_bits: u32, active_bits: u32) -> u128 {
    assert!(
        active_bits < result_bits,
        "oracle active bits must leave upper-zero bits"
    );
    let all_bits = (1u128 << result_bits) - 1;
    let active = (1u128 << active_bits) - 1;
    all_bits & !active
}

fn upper_zero_mask_hex(result_bits: u32, active_bits: u32) -> String {
    let mask = upper_zero_mask(result_bits, active_bits);
    let width = result_bits.div_ceil(4) as usize;
    format!("0x{mask:0width$x}")
}

fn compact_bool_lanes(lanes: &[bool]) -> u64 {
    lanes.iter().enumerate().fold(
        0u64,
        |bits, (index, lane)| {
            if *lane { bits | (1u64 << index) } else { bits }
        },
    )
}

fn expected_mask_lanes(oracle: &generate::VectorMaskOracleFixture) -> Vec<bool> {
    match &oracle.case {
        generate::VectorMaskOracleCase::LogicalMask { input_lanes } => input_lanes.clone(),
        generate::VectorMaskOracleCase::CompareMask {
            expected_mask_lanes,
            ..
        } => expected_mask_lanes.clone(),
    }
}

fn oracle_inputs_json(oracle: &generate::VectorMaskOracleFixture) -> serde_json::Value {
    match &oracle.case {
        generate::VectorMaskOracleCase::LogicalMask { input_lanes } => serde_json::json!({
            "kind": "logical_mask",
            "mask_lanes": input_lanes,
        }),
        generate::VectorMaskOracleCase::CompareMask {
            compare_op,
            compare_ty,
            lhs_lanes,
            rhs_lanes,
            expected_mask_lanes,
        } => serde_json::json!({
            "kind": "compare_mask",
            "compare_op": icmp_op_name(*compare_op),
            "compare_ty": compare_ty.to_string(),
            "lhs_lanes": lhs_lanes,
            "rhs_lanes": rhs_lanes,
            "expected_mask_lanes": expected_mask_lanes,
        }),
    }
}

fn vector_mask_oracle_json(fixtures: &[generate::VectorMaskOracleFixture]) -> String {
    let rows = fixtures
        .iter()
        .map(|oracle| {
            let lanes = mask_ty_lanes(&oracle.mask_ty);
            let result_bits = integer_result_bits(&oracle.result_ty);
            let lane_to_result_bit = (0..lanes).collect::<Vec<_>>();
            serde_json::json!({
                "name": oracle.name,
                "operation": "vector.mask_to_bits",
                "mask_type": oracle.mask_ty.to_string(),
                "result_type": oracle.result_ty.to_string(),
                "bit_order": oracle.bit_order,
                "lane_to_result_bit": lane_to_result_bit,
                "inputs": oracle_inputs_json(oracle),
                "expected_interpreter": {
                    "compacted_integer": oracle.expected_compacted_integer,
                    "mask_lanes": expected_mask_lanes(oracle),
                    "rust_output": oracle.expected_rust_output,
                    "lean_output": oracle.expected_lean_output,
                },
                "upper_zero": {
                    "result_bits": result_bits,
                    "zero_bits_from": lanes,
                    "zero_bits_through": result_bits - 1,
                    "zero_mask_hex": upper_zero_mask_hex(result_bits, lanes),
                },
                "cross_check": {
                    "lean_file": "lean/trust_ir-semantics/TrustIr/Semantics/ExecutableFixtures.lean",
                    "lean_theorem": oracle.lean_theorem,
                },
            })
        })
        .collect::<Vec<_>>();
    serde_json::to_string_pretty(&rows).expect("serialize vector mask oracle JSON")
}

fn assert_vector_mask_oracle_json_schema(name: &str, json: &str) {
    let rows: serde_json::Value = serde_json::from_str(json)
        .unwrap_or_else(|e| panic!("{name}: vector mask oracle JSON is invalid: {e}"));
    let rows = rows
        .as_array()
        .unwrap_or_else(|| panic!("{name}: vector mask oracle JSON must be an array"));
    assert!(
        !rows.is_empty(),
        "{name}: vector mask oracle JSON must contain at least one row"
    );
    for row in rows {
        let row_name = row
            .get("name")
            .and_then(serde_json::Value::as_str)
            .unwrap_or("<unnamed>");
        assert!(
            row.get("lane_to_result_bit")
                .and_then(serde_json::Value::as_array)
                .is_some_and(|lanes| !lanes.is_empty()),
            "{name}:{row_name}: missing lane-order field"
        );
        assert!(
            row.pointer("/expected_interpreter/compacted_integer")
                .and_then(serde_json::Value::as_u64)
                .is_some(),
            "{name}:{row_name}: missing expected compacted integer"
        );
        assert!(
            row.pointer("/expected_interpreter/rust_output")
                .and_then(serde_json::Value::as_str)
                .is_some_and(|value| !value.is_empty()),
            "{name}:{row_name}: missing Rust expected output"
        );
        assert!(
            row.pointer("/expected_interpreter/lean_output")
                .and_then(serde_json::Value::as_str)
                .is_some_and(|value| !value.is_empty()),
            "{name}:{row_name}: missing Lean expected output"
        );
        assert!(
            row.get("upper_zero")
                .and_then(serde_json::Value::as_object)
                .is_some_and(|upper_zero| {
                    upper_zero.contains_key("zero_bits_from")
                        && upper_zero.contains_key("zero_bits_through")
                        && upper_zero.contains_key("zero_mask_hex")
                }),
            "{name}:{row_name}: missing upper-zero field"
        );
        assert!(
            row.pointer("/cross_check/lean_theorem")
                .and_then(serde_json::Value::as_str)
                .is_some_and(|value| !value.is_empty()),
            "{name}:{row_name}: missing Lean cross-check reference"
        );
    }
}

fn assert_vector_mask_oracle_metadata(oracle: &generate::VectorMaskOracleFixture) {
    assert!(!oracle.name.is_empty(), "oracle name must be present");
    assert_eq!(
        oracle.bit_order, "lsb_lane0",
        "{}: bit order must be lane 0 -> bit 0",
        oracle.name
    );
    assert!(
        !oracle.expected_rust_output.is_empty(),
        "{}: missing expected Rust interpreter output",
        oracle.name
    );
    assert!(
        !oracle.expected_lean_output.is_empty(),
        "{}: missing expected Lean executable output",
        oracle.name
    );
    assert!(
        !oracle.lean_theorem.is_empty(),
        "{}: missing Lean theorem cross-check reference",
        oracle.name
    );

    let lanes = mask_ty_lanes(&oracle.mask_ty);
    let result_bits = integer_result_bits(&oracle.result_ty);
    let expected_mask_lanes = expected_mask_lanes(oracle);
    assert_eq!(
        expected_mask_lanes.len(),
        lanes as usize,
        "{}: expected mask lane count must match mask_ty",
        oracle.name
    );
    assert_eq!(
        compact_bool_lanes(&expected_mask_lanes),
        oracle.expected_compacted_integer,
        "{}: expected compacted integer must encode lane N at bit N",
        oracle.name
    );
    assert_eq!(
        oracle.expected_compacted_integer as u128 & upper_zero_mask(result_bits, lanes),
        0,
        "{}: expected upper bits must be zero",
        oracle.name
    );

    match &oracle.case {
        generate::VectorMaskOracleCase::LogicalMask { input_lanes } => {
            assert_eq!(
                input_lanes, &expected_mask_lanes,
                "{}: logical mask input lanes are the expected mask lanes",
                oracle.name
            );
        }
        generate::VectorMaskOracleCase::CompareMask {
            compare_ty,
            lhs_lanes,
            rhs_lanes,
            expected_mask_lanes,
            ..
        } => {
            let compare_lanes = vector_ty_lanes(compare_ty);
            assert_eq!(
                compare_lanes, lanes,
                "{}: compare vector lane count must match mask_ty",
                oracle.name
            );
            assert_eq!(
                compare_ty.comparison_result_ty(),
                oracle.mask_ty,
                "{}: compare result type must be the logical mask_ty",
                oracle.name
            );
            assert_eq!(
                lhs_lanes.len(),
                lanes as usize,
                "{}: lhs lane count must match compare_ty",
                oracle.name
            );
            assert_eq!(
                rhs_lanes.len(),
                lanes as usize,
                "{}: rhs lane count must match compare_ty",
                oracle.name
            );
            assert_eq!(
                expected_mask_lanes.len(),
                lanes as usize,
                "{}: compare expected mask lane count must match compare_ty",
                oracle.name
            );
        }
    }
}

fn const_vector_bool(lanes: &[bool]) -> Constant {
    Constant::Vector(lanes.iter().copied().map(Constant::Bool).collect())
}

fn const_vector_int(lanes: &[i128]) -> Constant {
    Constant::Vector(lanes.iter().copied().map(Constant::Int).collect())
}

fn result(inst: Inst, value: ValueId) -> InstrNode {
    InstrNode::new(inst).with_result(value)
}

fn void(inst: Inst) -> InstrNode {
    InstrNode::new(inst)
}

fn build_vector_mask_oracle_module(oracle: &generate::VectorMaskOracleFixture) -> Module {
    let mut module = Module::new(format!("vector_mask_oracle_{}", oracle.name));
    let returns = match &oracle.case {
        generate::VectorMaskOracleCase::LogicalMask { .. } => vec![oracle.result_ty.clone()],
        generate::VectorMaskOracleCase::CompareMask { .. } => {
            vec![oracle.mask_ty.clone(), oracle.result_ty.clone()]
        }
    };
    let func_ty = module.add_func_type(FuncTy {
        params: Vec::new(),
        returns,
        is_vararg: false,
    });
    let mut function = Function::new(FuncId::new(0), oracle.name, func_ty, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));

    match &oracle.case {
        generate::VectorMaskOracleCase::LogicalMask { input_lanes } => {
            block.body.push(result(
                Inst::Const {
                    ty: oracle.mask_ty.clone(),
                    value: const_vector_bool(input_lanes),
                },
                ValueId::new(0),
            ));
            block.body.push(result(
                Inst::DialectOp(Box::new(trust_ir::dialect::vector::mask_to_bits(
                    oracle.mask_ty.clone(),
                    ValueId::new(0),
                    oracle.result_ty.clone(),
                ))),
                ValueId::new(1),
            ));
            block.body.push(void(Inst::Return {
                values: vec![ValueId::new(1)],
            }));
        }
        generate::VectorMaskOracleCase::CompareMask {
            compare_op,
            compare_ty,
            lhs_lanes,
            rhs_lanes,
            ..
        } => {
            block.body.push(result(
                Inst::Const {
                    ty: compare_ty.clone(),
                    value: const_vector_int(lhs_lanes),
                },
                ValueId::new(0),
            ));
            block.body.push(result(
                Inst::Const {
                    ty: compare_ty.clone(),
                    value: const_vector_int(rhs_lanes),
                },
                ValueId::new(1),
            ));
            block.body.push(result(
                Inst::ICmp {
                    op: *compare_op,
                    ty: compare_ty.clone(),
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                },
                ValueId::new(2),
            ));
            block.body.push(result(
                Inst::DialectOp(Box::new(trust_ir::dialect::vector::mask_to_bits(
                    oracle.mask_ty.clone(),
                    ValueId::new(2),
                    oracle.result_ty.clone(),
                ))),
                ValueId::new(3),
            ));
            block.body.push(void(Inst::Return {
                values: vec![ValueId::new(2), ValueId::new(3)],
            }));
        }
    }

    function.blocks.push(block);
    module.add_function(function);
    module
}

fn stable_interpret_value(value: &InterpretValue) -> String {
    match &value.kind {
        InterpretValueKind::Int(int) => format!("int{}:{}", int.bits, int.as_signed()),
        InterpretValueKind::FloatBits(bits) => format!("float_bits:{bits}"),
        InterpretValueKind::Bool(true) => "bool:true".to_string(),
        InterpretValueKind::Bool(false) => "bool:false".to_string(),
        InterpretValueKind::Ptr(ptr) => format!("ptr:{}:{}", ptr.allocation, ptr.offset),
        InterpretValueKind::Vector(lanes) => format!(
            "vector[{}]",
            lanes
                .iter()
                .map(stable_interpret_value)
                .collect::<Vec<_>>()
                .join(",")
        ),
        InterpretValueKind::Aggregate(values) => format!("aggregate({})", values.len()),
        InterpretValueKind::Array(values) => format!("array({})", values.len()),
        InterpretValueKind::Sequence(values) => format!("sequence({})", values.len()),
        InterpretValueKind::Set(values) => format!("set({})", values.len()),
        InterpretValueKind::Record(fields) => format!("record({})", fields.len()),
        InterpretValueKind::Closure { func, captures } => {
            format!("closure:{}:{}", func.index(), captures.len())
        }
        InterpretValueKind::FatPtr { data, metadata } => format!(
            "fat_ptr(data={},metadata={})",
            stable_interpret_value(data),
            stable_interpret_value(metadata)
        ),
        InterpretValueKind::FnDef(func) => format!("fn:{}", func.index()),
        InterpretValueKind::PhantomData => "phantom_data".to_string(),
        InterpretValueKind::NullPtr => "null".to_string(),
        InterpretValueKind::Unit => "unit".to_string(),
        InterpretValueKind::Frame(id) => format!("frame:{id}"),
        InterpretValueKind::PartialBytes(bytes) => format!("partial_bytes({})", bytes.len()),
        InterpretValueKind::DanglingPtr(addr) => format!("dangling_ptr:{addr}"),
    }
}

#[test]
fn stable_interpret_value_covers_first_class_fat_pointers() {
    let value = InterpretValue {
        ty: Ty::FatPtr(trust_ir::FatPtrKind::Str),
        kind: InterpretValueKind::FatPtr {
            data: Box::new(InterpretValue {
                ty: Ty::Ptr,
                kind: InterpretValueKind::NullPtr,
            }),
            metadata: Box::new(InterpretValue::int(Ty::U64, 3).expect("u64 metadata")),
        },
    };
    assert_eq!(
        stable_interpret_value(&value),
        "fat_ptr(data=null,metadata=int64:3)"
    );
}

fn stable_interpret_returns(values: &[InterpretValue]) -> String {
    format!(
        "ok:return:[{}]",
        values
            .iter()
            .map(stable_interpret_value)
            .collect::<Vec<_>>()
            .join(",")
    )
}

#[test]
fn stable_interpret_value_preserves_both_fat_pointer_lanes() {
    let value = InterpretValue {
        ty: Ty::FatPtr(trust_ir::FatPtrKind::Slice(trust_ir::TyId::new(0))),
        kind: InterpretValueKind::FatPtr {
            data: Box::new(InterpretValue {
                ty: Ty::Ptr,
                kind: InterpretValueKind::NullPtr,
            }),
            metadata: Box::new(
                InterpretValue::int(Ty::U64, 4).expect("slice metadata fits in u64"),
            ),
        },
    };

    assert_eq!(
        stable_interpret_value(&value),
        "fat_ptr(data=null,metadata=int64:4)"
    );
}

fn interpret_bool_vector(value: &InterpretValue) -> Vec<bool> {
    match &value.kind {
        InterpretValueKind::Vector(lanes) => lanes
            .iter()
            .map(|lane| {
                lane.as_bool()
                    .unwrap_or_else(|| panic!("expected bool lane, got {lane:?}"))
            })
            .collect(),
        other => panic!("expected bool vector, got {other:?}"),
    }
}

fn interpret_unsigned_int(value: &InterpretValue) -> u64 {
    let raw = value
        .as_int()
        .unwrap_or_else(|| panic!("expected integer value, got {value:?}"))
        .as_unsigned();
    u64::try_from(raw).expect("oracle compacted integer fits in u64")
}

// ============================================================
// Per-format round-trip helpers
// ============================================================

/// Binary: serialize, compare, deserialize, re-serialize and assert
/// the bytes are stable across the round-trip (catches codec state
/// carried across invocations).
fn roundtrip_binary(name: &str, module: &Module) -> Vec<u8> {
    let bytes = trust_ir::binary::serialize_module(module);
    let back = trust_ir::binary::deserialize_module(&bytes)
        .unwrap_or_else(|e| panic!("{name}: binary deserialize failed: {e:?}"));
    let bytes2 = trust_ir::binary::serialize_module(&back);
    assert_eq!(
        bytes, bytes2,
        "{name}: binary serialize is not idempotent across a round-trip"
    );
    bytes
}

/// Canonical text: format, compare, re-parse, re-format.
///
/// Asserts BOTH text idempotence AND module-structural equality. Text
/// idempotence alone is blind to data loss: a printer that silently drops a
/// field and a parser that fills the same default will still round-trip the
/// text byte-for-byte. The structural-equality check —
/// `parse(canonical(m)) == canonicalize(m)` — is what makes findings A-F
/// (types table, function proofs/attrs, obligation scope, proof_context,
/// value facts, explicit struct/enum/record ids) regression-proof. We compare
/// against `canonicalize(m)` rather than `m` because canonical text renumbers
/// SSA values densely; canonicalize applies the same renumbering so the two
/// modules are field-for-field identical when nothing is lost.
fn roundtrip_text(name: &str, module: &Module) -> String {
    let text = trust_ir::format::canonical(module);
    let back = trust_ir::parser::parse_module(&text)
        .unwrap_or_else(|e| panic!("{name}: text parse failed: {e:?}"));
    let text2 = trust_ir::format::canonical(&back);
    assert_eq!(
        text, text2,
        "{name}: canonical text is not idempotent across a round-trip"
    );
    // Structural equality catches silent field loss that text idempotence
    // cannot. `canonicalize` is the same SSA-renumbering the printer applies.
    let mut expected = trust_ir::format::canonicalize(module);
    let mut got = back;
    // The KNOWN text-only limitations are normalized away here so the
    // structural check still guards every other field (findings A-G): the
    // human-readable struct text form is `struct @N { ty } id=N`, which
    // carries field TYPES but not field NAMES or layout OFFSETS (records keep
    // field names since their text form is `name: ty`), and no per-node span
    // clause exists, so instruction spans do not survive text. These are
    // text-debug-form limitations only: the binary/JSON/MessagePack
    // round-trips below assert FULL equality (names + offsets + spans) and
    // are the lossless production paths.
    normalize_text_lossy_fields(&mut got);
    normalize_text_lossy_fields(&mut expected);
    assert_eq!(
        got, expected,
        "{name}: text round-trip lost module structure (parse(print(m)) != canonicalize(m))"
    );
    text
}

/// Erase the state the human-readable text form does not carry: struct field
/// names and layout offsets (the text struct form is `struct @N { ty } id=N`,
/// which keeps field TYPES but not NAMES/OFFSETS — records keep names since
/// their form is `name: ty`) and instruction spans (no per-node span clause
/// exists in the text grammar; `file N "path"` tables and diagnostic `at`
/// locations DO round-trip). Applied to BOTH sides of the structural compare
/// so the check still catches every other kind of data loss, including the
/// `Ty::Unit` vs empty-`Tuple` distinction (finding G, now fixed: `()` vs
/// `(,)`).
fn normalize_text_lossy_fields(module: &mut Module) {
    for sd in &mut module.structs {
        for fd in &mut sd.fields {
            fd.name = String::new();
            fd.offset = None;
        }
    }
    for func in &mut module.functions {
        for block in &mut func.blocks {
            for node in &mut block.body {
                node.span = None;
            }
        }
    }
}

/// JSON: pretty-print (stable spacing) and round-trip.
fn roundtrip_json(name: &str, module: &Module) -> String {
    let json = serde_json::to_string_pretty(module)
        .unwrap_or_else(|e| panic!("{name}: JSON serialize failed: {e}"));
    let back: Module = serde_json::from_str(&json)
        .unwrap_or_else(|e| panic!("{name}: JSON deserialize failed: {e}"));
    // Float bits-encoded, so module equality is exact.
    assert_eq!(module, &back, "{name}: JSON round-trip lost information");
    json
}

/// MessagePack: compact binary, round-trip.
fn roundtrip_msgpack(name: &str, module: &Module) -> Vec<u8> {
    let bytes = rmp_serde::to_vec(module)
        .unwrap_or_else(|e| panic!("{name}: MessagePack serialize failed: {e}"));
    let back: Module = rmp_serde::from_slice(&bytes)
        .unwrap_or_else(|e| panic!("{name}: MessagePack deserialize failed: {e}"));
    assert_eq!(
        module, &back,
        "{name}: MessagePack round-trip lost information"
    );
    bytes
}

fn roundtrip_lineage_binary(name: &str, manifest: &ProofLineageManifest) -> Vec<u8> {
    let bytes = trust_ir::binary::serialize_proof_lineage_manifest(manifest);
    let back = trust_ir::binary::deserialize_proof_lineage_manifest(&bytes)
        .unwrap_or_else(|e| panic!("{name}: proof lineage binary deserialize failed: {e:?}"));
    let bytes2 = trust_ir::binary::serialize_proof_lineage_manifest(&back);
    assert_eq!(
        bytes, bytes2,
        "{name}: proof lineage binary serialize is not idempotent"
    );
    bytes
}

fn roundtrip_lineage_json(name: &str, manifest: &ProofLineageManifest) -> String {
    let json = serde_json::to_string_pretty(manifest)
        .unwrap_or_else(|e| panic!("{name}: proof lineage JSON serialize failed: {e}"));
    let back: ProofLineageManifest = serde_json::from_str(&json)
        .unwrap_or_else(|e| panic!("{name}: proof lineage JSON deserialize failed: {e}"));
    assert_eq!(
        manifest, &back,
        "{name}: proof lineage JSON round-trip lost information"
    );
    json
}

fn roundtrip_lineage_msgpack(name: &str, manifest: &ProofLineageManifest) -> Vec<u8> {
    let bytes = rmp_serde::to_vec_named(manifest)
        .unwrap_or_else(|e| panic!("{name}: proof lineage MessagePack serialize failed: {e}"));
    let back: ProofLineageManifest = rmp_serde::from_slice(&bytes)
        .unwrap_or_else(|e| panic!("{name}: proof lineage MessagePack deserialize failed: {e}"));
    assert_eq!(
        manifest, &back,
        "{name}: proof lineage MessagePack round-trip lost information"
    );
    bytes
}

fn roundtrip_native_bundle_json(name: &str, bundle: &NativeVerificationBundle) -> String {
    let json = serde_json::to_string_pretty(bundle)
        .unwrap_or_else(|e| panic!("{name}: native request bundle JSON serialize failed: {e}"));
    let back: NativeVerificationBundle = serde_json::from_str(&json)
        .unwrap_or_else(|e| panic!("{name}: native request bundle JSON deserialize failed: {e}"));
    assert_eq!(
        bundle, &back,
        "{name}: native request bundle JSON round-trip lost information"
    );
    json
}

fn roundtrip_native_bundle_msgpack(name: &str, bundle: &NativeVerificationBundle) -> Vec<u8> {
    let bytes = rmp_serde::to_vec_named(bundle).unwrap_or_else(|e| {
        panic!("{name}: native request bundle MessagePack serialize failed: {e}")
    });
    let back: NativeVerificationBundle = rmp_serde::from_slice(&bytes).unwrap_or_else(|e| {
        panic!("{name}: native request bundle MessagePack deserialize failed: {e}")
    });
    assert_eq!(
        bundle, &back,
        "{name}: native request bundle MessagePack round-trip lost information"
    );
    bytes
}

// ============================================================
// Tests
// ============================================================

/// Main corpus test. Iterates every fixture, produces all four formats,
/// asserts byte-for-byte equality against the goldens. Also asserts
/// that swapping formats (binary -> Module -> JSON) produces output
/// that matches the JSON golden — catches cases where only one writer
/// path agrees with the golden.
#[test]
fn corpus_roundtrip() {
    let dir = fixtures_dir();
    for Fixture {
        name,
        build,
        text_supported,
        text_skip_reason,
    } in corpus()
    {
        let module = build();

        // 1. Binary.
        let bin_bytes = roundtrip_binary(name, &module);
        assert_or_update_bytes(&dir.join(format!("{name}.tmbc")), &bin_bytes);

        // 2. Canonical text (skipped only if a fixture opts out via
        //    text_supported: false; all current fixtures support it).
        if text_supported {
            let text = roundtrip_text(name, &module);
            assert_or_update_text(&dir.join(format!("{name}.trust_ir")), &text);
        } else {
            eprintln!("conformance: skipping .trust_ir for `{name}`: {text_skip_reason}");
        }

        // 3. JSON.
        let json = roundtrip_json(name, &module);
        assert_or_update_text(&dir.join(format!("{name}.json")), &json);

        // 4. MessagePack.
        let msgpack = roundtrip_msgpack(name, &module);
        assert_or_update_bytes(&dir.join(format!("{name}.msgpack")), &msgpack);

        // 5. Cross-format coherence: decode the binary golden and
        //    re-encode through JSON / MessagePack; the outputs must
        //    match the JSON / MessagePack goldens byte-for-byte.
        //    (This is the strongest wire-format guarantee the harness
        //    can give downstream consumers.)
        let from_bin = trust_ir::binary::deserialize_module(&bin_bytes).expect("binary re-decode");
        let json_from_bin = serde_json::to_string_pretty(&from_bin).unwrap();
        assert_eq!(
            json_from_bin, json,
            "{name}: binary -> JSON does not match JSON golden (cross-format drift)"
        );
        let msgpack_from_bin = rmp_serde::to_vec(&from_bin).unwrap();
        assert_eq!(
            msgpack_from_bin, msgpack,
            "{name}: binary -> MessagePack does not match MessagePack golden"
        );
    }
}

/// Proof-lineage sidecar corpus. These fixtures deliberately live beside the
/// module fixtures but use standalone `.trust_irpl` binary files rather than the
/// module `.tmbc` codec, so Trust can pin proof persistence without forcing a
/// module binary-format bump.
#[test]
fn proof_lineage_corpus_roundtrip() {
    let dir = fixtures_dir();
    for LineageFixture { name, build } in lineage_corpus() {
        let fixture = build();
        fixture
            .manifest
            .validate_against(&fixture.obligations, &fixture.certificates)
            .unwrap_or_else(|e| panic!("{name}: proof lineage fixture invalid: {e:?}"));

        let binary = roundtrip_lineage_binary(name, &fixture.manifest);
        assert_or_update_bytes(&dir.join(format!("{name}.trust_irpl")), &binary);

        let json = roundtrip_lineage_json(name, &fixture.manifest);
        assert_or_update_text(&dir.join(format!("{name}.json")), &json);

        let msgpack = roundtrip_lineage_msgpack(name, &fixture.manifest);
        assert_or_update_bytes(&dir.join(format!("{name}.msgpack")), &msgpack);

        let from_binary = trust_ir::binary::deserialize_proof_lineage_manifest(&binary)
            .expect("proof lineage binary re-decode");
        assert_eq!(
            from_binary.stable_digest(),
            fixture.manifest.stable_digest(),
            "{name}: binary proof lineage digest drift"
        );
    }
}

/// Native request bundle corpus. These fixtures pin the typed in-process
/// request boundary that tRust hands to TrustVc/TrustMc/TrustWp; they intentionally
/// use serde goldens rather than a new `.tmbc` section.
#[test]
fn native_request_bundle_corpus_roundtrip() {
    let dir = fixtures_dir();
    for NativeBundleFixture { name, build } in native_bundle_corpus() {
        let fixture = build();
        let module_errors = trust_ir_build::validate_module(&fixture.bundle.module);
        assert!(
            module_errors.is_empty(),
            "{name}: native request bundle module invalid: {module_errors:?}"
        );
        fixture
            .bundle
            .validate()
            .unwrap_or_else(|e| panic!("{name}: native request bundle invalid: {e:?}"));

        let json = roundtrip_native_bundle_json(name, &fixture.bundle);
        assert_or_update_text(&dir.join(format!("{name}.json")), &json);

        let msgpack = roundtrip_native_bundle_msgpack(name, &fixture.bundle);
        assert_or_update_bytes(&dir.join(format!("{name}.msgpack")), &msgpack);
    }
}

#[test]
fn vector_mask_oracle_corpus_roundtrip() {
    let fixtures = generate::build_vector_mask_oracles();
    let json = vector_mask_oracle_json(&fixtures);
    assert_vector_mask_oracle_json_schema("generated vector_mask_oracles", &json);

    let path = fixtures_dir().join("vector_mask_oracles.json");
    if !update_mode() {
        let checked_in = fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("read checked-in {}: {e}", path.display()));
        assert_vector_mask_oracle_json_schema("checked-in vector_mask_oracles", &checked_in);
    }
    assert_or_update_text(&path, &json);
}

/// Execute the `inst_vector_crosslane` fixture through the reference
/// interpreter and pin concrete lane-level results for `reduce` / `shuffle` /
/// `fma`. This is the executable counterpart to the byte-golden round-trip
/// above: it proves the wire form the corpus pins is also the form the
/// reference semantics evaluate.
#[test]
fn vector_crosslane_fixture_executes_with_concrete_lane_results() {
    let module = generate::build_inst_vector_crosslane();
    let errors = trust_ir_build::validate_module(&module);
    assert!(
        errors.is_empty(),
        "inst_vector_crosslane fixture must validate cleanly: {errors:?}"
    );

    fn i32_lane(v: i32) -> InterpretValue {
        InterpretValue::int(Ty::I32, i128::from(v)).expect("i32 lane")
    }
    fn i64_lane(v: i64) -> InterpretValue {
        InterpretValue::int(Ty::I64, i128::from(v)).expect("i64 lane")
    }
    fn f32_lane(v: f32) -> InterpretValue {
        InterpretValue {
            ty: Ty::F32,
            kind: InterpretValueKind::FloatBits(u64::from(v.to_bits())),
        }
    }
    fn f64_lane(v: f64) -> InterpretValue {
        InterpretValue {
            ty: Ty::F64,
            kind: InterpretValueKind::FloatBits(v.to_bits()),
        }
    }
    fn vec_val(ty: Ty, lanes: Vec<InterpretValue>) -> InterpretValue {
        InterpretValue {
            ty,
            kind: InterpretValueKind::Vector(lanes),
        }
    }

    let v4 = vec_val(
        Ty::v4_i32(),
        vec![i32_lane(1), i32_lane(-2), i32_lane(30), i32_lane(4)],
    );
    let v2 = vec_val(Ty::v2_i64(), vec![i64_lane(0b0011), i64_lane(0b1100)]);
    let v4f = vec_val(
        Ty::v4_f32(),
        vec![f32_lane(1.0), f32_lane(2.0), f32_lane(3.0), f32_lane(4.0)],
    );
    let v2f = vec_val(Ty::v2_f64(), vec![f64_lane(1.5), f64_lane(2.0)]);

    let outcome = Interpreter::with_module(&module)
        .execute_func(FuncId::new(0), [v4, v2, v4f, v2f])
        .expect("vector crosslane fixture executes");

    let int_of =
        |value: &InterpretValue| -> i128 { value.as_int().expect("integer result").as_signed() };
    let lanes_i128 = |value: &InterpretValue| -> Vec<i128> {
        match &value.kind {
            InterpretValueKind::Vector(lanes) => lanes
                .iter()
                .map(|lane| lane.as_int().expect("integer lane").as_signed())
                .collect(),
            other => panic!("expected vector, got {other:?}"),
        }
    };
    let lanes_f64 = |value: &InterpretValue| -> Vec<f64> {
        match &value.kind {
            InterpretValueKind::Vector(lanes) => lanes
                .iter()
                .map(|lane| match (&lane.ty, &lane.kind) {
                    (Ty::F32, InterpretValueKind::FloatBits(bits)) => {
                        f32::from_bits(*bits as u32) as f64
                    }
                    (Ty::F64, InterpretValueKind::FloatBits(bits)) => f64::from_bits(*bits),
                    other => panic!("expected float lane, got {other:?}"),
                })
                .collect(),
            other => panic!("expected vector, got {other:?}"),
        }
    };

    // reduce-add over [1, -2, 30, 4] = 33.
    assert_eq!(int_of(&outcome.returns[0]), 33);
    // reduce-or over [0b0011, 0b1100] = 0b1111 = 15.
    assert_eq!(
        outcome.returns[1].as_int().expect("i64").as_unsigned(),
        0b1111
    );
    // shuffle [3, 2, 1, 0] reverses the source lanes.
    assert_eq!(lanes_i128(&outcome.returns[2]), vec![4, 30, -2, 1]);
    // shuffle [1, 1] broadcasts source lane 1 into both result lanes.
    assert_eq!(lanes_i128(&outcome.returns[3]), vec![0b1100, 0b1100]);
    // fma a*a + a per lane over [1, 2, 3, 4] = [2, 6, 12, 20].
    assert_eq!(lanes_f64(&outcome.returns[4]), vec![2.0, 6.0, 12.0, 20.0]);
    // fma a*a + a per lane over [1.5, 2.0] = [3.75, 6.0].
    assert_eq!(lanes_f64(&outcome.returns[5]), vec![3.75, 6.0]);
}

#[test]
fn vector_dialect_mask_oracle_fixtures_execute_and_match_lean() {
    let lean_path = executable_fixtures_lean_path();
    let lean_source = fs::read_to_string(&lean_path)
        .unwrap_or_else(|e| panic!("read Lean executable fixtures {}: {e}", lean_path.display()));

    let fixtures = generate::build_vector_mask_oracles();
    let mut saw_v16 = false;
    let mut saw_v8 = false;
    let mut saw_v4 = false;
    let mut saw_v2 = false;
    let mut saw_v16_i8_compare = false;
    let mut saw_v8_i16_compare = false;

    for oracle in fixtures {
        assert_vector_mask_oracle_metadata(&oracle);
        assert!(
            lean_source.contains(oracle.lean_theorem),
            "{}: Lean cross-check theorem {} is missing",
            oracle.name,
            oracle.lean_theorem
        );
        assert!(
            lean_source.contains(oracle.expected_lean_output),
            "{}: Lean cross-check expected output {} is missing",
            oracle.name,
            oracle.expected_lean_output
        );

        let expected_value_atom = match oracle.result_ty {
            Ty::I32 => format!("int32:{}", oracle.expected_compacted_integer),
            Ty::I64 => format!("int64:{}", oracle.expected_compacted_integer),
            ref other => panic!("{}: unsupported oracle result type {other}", oracle.name),
        };
        assert!(
            oracle.expected_rust_output.contains(&expected_value_atom),
            "{}: Rust expected output must include {expected_value_atom}",
            oracle.name
        );
        assert!(
            oracle.expected_lean_output.ends_with(&expected_value_atom),
            "{}: Lean expected output must agree with {expected_value_atom}",
            oracle.name
        );

        let module = build_vector_mask_oracle_module(&oracle);
        let errors = trust_ir_build::validate_module(&module);
        assert!(
            errors.is_empty(),
            "{}: vector mask oracle module must validate cleanly: {errors:?}",
            oracle.name
        );
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .unwrap_or_else(|e| panic!("{}: Rust interpreter failed: {e}", oracle.name));
        let stable_output = stable_interpret_returns(&outcome.returns);
        assert_eq!(
            stable_output, oracle.expected_rust_output,
            "{}: Rust interpreter output drifted",
            oracle.name
        );

        match &oracle.case {
            generate::VectorMaskOracleCase::LogicalMask { .. } => {
                assert_eq!(
                    outcome.returns.len(),
                    1,
                    "{}: logical mask oracle returns compacted bits only",
                    oracle.name
                );
                assert_eq!(
                    interpret_unsigned_int(&outcome.returns[0]),
                    oracle.expected_compacted_integer,
                    "{}: compacted mask integer mismatch",
                    oracle.name
                );
            }
            generate::VectorMaskOracleCase::CompareMask {
                compare_ty,
                expected_mask_lanes,
                ..
            } => {
                assert_eq!(
                    outcome.returns.len(),
                    2,
                    "{}: compare-mask oracle returns logical mask and compacted bits",
                    oracle.name
                );
                assert_eq!(
                    interpret_bool_vector(&outcome.returns[0]),
                    *expected_mask_lanes,
                    "{}: logical compare mask lanes mismatch",
                    oracle.name
                );
                assert_eq!(
                    interpret_unsigned_int(&outcome.returns[1]),
                    oracle.expected_compacted_integer,
                    "{}: compacted compare-mask integer mismatch",
                    oracle.name
                );
                match compare_ty {
                    Ty::Vector(elem, 16) if **elem == Ty::I8 => saw_v16_i8_compare = true,
                    Ty::Vector(elem, 8) if **elem == Ty::I16 => saw_v8_i16_compare = true,
                    _ => {}
                }
            }
        }

        match mask_ty_lanes(&oracle.mask_ty) {
            16 => saw_v16 = true,
            8 => saw_v8 = true,
            4 => saw_v4 = true,
            2 => saw_v2 = true,
            lanes => panic!("{}: unexpected mask lane count {lanes}", oracle.name),
        }
    }

    assert!(saw_v16, "missing <16 x bool> mask_to_bits oracle");
    assert!(saw_v8, "missing <8 x bool> mask_to_bits oracle");
    assert!(saw_v4, "missing <4 x bool> mask_to_bits oracle");
    assert!(saw_v2, "missing <2 x bool> mask_to_bits oracle");
    assert!(saw_v16_i8_compare, "missing <16 x i8> compare-mask oracle");
    assert!(saw_v8_i16_compare, "missing <8 x i16> compare-mask oracle");
}

#[test]
fn vector_dialect_fixture_covers_portable_ops() {
    use trust_ir::dialect::{self, AttrValue, DialectInst};
    use trust_ir::inst::Inst;
    use trust_ir::ty::Ty;

    let module = generate::build_inst_vector_dialect();
    let errors = trust_ir_build::validate_module(&module);
    assert!(
        errors.is_empty(),
        "inst_vector_dialect fixture must validate cleanly: {errors:?}"
    );

    let vector_ops: Vec<&DialectInst> = module
        .functions
        .iter()
        .flat_map(|function| function.blocks.iter())
        .flat_map(|block| block.body.iter())
        .filter_map(|node| match &node.inst {
            Inst::DialectOp(op) if op.dialect == dialect::vector::DIALECT => Some(op.as_ref()),
            _ => None,
        })
        .collect();

    assert_eq!(
        vector_ops.len(),
        10,
        "fixture should cover pack/extract/insert for two lane shapes plus four masks"
    );

    fn attr_schema(op: &DialectInst) -> Vec<(&str, &'static str)> {
        op.attrs
            .iter()
            .map(|attr| {
                let kind = match &attr.value {
                    AttrValue::I64(_) => "i64",
                    AttrValue::U64(_) => "u64",
                    AttrValue::F64(_) => "f64",
                    AttrValue::Bool(_) => "bool",
                    AttrValue::Str(_) => "str",
                    AttrValue::Bytes(_) => "bytes",
                    AttrValue::Ty(_) => "ty",
                };
                (attr.name.as_str(), kind)
            })
            .collect::<Vec<_>>()
    }
    let observed_schema = vector_ops
        .iter()
        .map(|op| (op.op.as_str(), attr_schema(op)))
        .collect::<Vec<_>>();
    assert_eq!(
        observed_schema,
        vec![
            (dialect::vector::PACK_LANES_OP, vec![]),
            (
                dialect::vector::EXTRACT_LANE_OP,
                vec![("vector_ty", "ty"), ("lane", "u64")]
            ),
            (dialect::vector::INSERT_LANE_OP, vec![("lane", "u64")]),
            (dialect::vector::PACK_LANES_OP, vec![]),
            (
                dialect::vector::EXTRACT_LANE_OP,
                vec![("vector_ty", "ty"), ("lane", "u64")]
            ),
            (dialect::vector::INSERT_LANE_OP, vec![("lane", "u64")]),
            (
                dialect::vector::MASK_TO_BITS_OP,
                vec![("mask_ty", "ty"), ("bit_order", "str")]
            ),
            (
                dialect::vector::MASK_TO_BITS_OP,
                vec![("mask_ty", "ty"), ("bit_order", "str")]
            ),
            (
                dialect::vector::MASK_TO_BITS_OP,
                vec![("mask_ty", "ty"), ("bit_order", "str")]
            ),
            (
                dialect::vector::MASK_TO_BITS_OP,
                vec![("mask_ty", "ty"), ("bit_order", "str")]
            ),
        ],
        "portable vector fixture op and attr spellings must stay stable"
    );

    assert!(
        vector_ops
            .iter()
            .any(|op| op.op == dialect::vector::PACK_LANES_OP
                && op.operands.len() == 4
                && op.result_tys == [Ty::v4_i32()]),
        "missing <4 x i32> vector.pack_lanes"
    );
    assert!(
        vector_ops
            .iter()
            .any(|op| op.op == dialect::vector::PACK_LANES_OP
                && op.operands.len() == 2
                && op.result_tys == [Ty::v2_i64()]),
        "missing <2 x i64> vector.pack_lanes"
    );
    assert!(
        vector_ops
            .iter()
            .any(|op| op.op == dialect::vector::EXTRACT_LANE_OP
                && op.attr("vector_ty") == Some(&AttrValue::Ty(Ty::v4_i32()))
                && op.attr("lane") == Some(&AttrValue::U64(2))
                && op.result_tys == [Ty::I32]),
        "missing <4 x i32> vector.extract_lane with Ty/U64 attrs"
    );
    assert!(
        vector_ops
            .iter()
            .any(|op| op.op == dialect::vector::EXTRACT_LANE_OP
                && op.attr("vector_ty") == Some(&AttrValue::Ty(Ty::v2_i64()))
                && op.attr("lane") == Some(&AttrValue::U64(1))
                && op.result_tys == [Ty::I64]),
        "missing <2 x i64> vector.extract_lane with Ty/U64 attrs"
    );
    assert!(
        vector_ops
            .iter()
            .any(|op| op.op == dialect::vector::INSERT_LANE_OP
                && op.attr("lane") == Some(&AttrValue::U64(1))
                && op.result_tys == [Ty::v4_i32()]),
        "missing <4 x i32> vector.insert_lane with lane attr"
    );
    assert!(
        vector_ops
            .iter()
            .any(|op| op.op == dialect::vector::INSERT_LANE_OP
                && op.attr("lane") == Some(&AttrValue::U64(0))
                && op.result_tys == [Ty::v2_i64()]),
        "missing <2 x i64> vector.insert_lane with lane attr"
    );
    assert!(
        vector_ops
            .iter()
            .any(|op| op.op == dialect::vector::MASK_TO_BITS_OP
                && op.attr("mask_ty") == Some(&AttrValue::Ty(Ty::v4_bool()))
                && op.attr("bit_order") == Some(&AttrValue::Str("lsb_lane0".to_string()))
                && op.result_tys == [Ty::I32]),
        "missing <4 x bool> vector.mask_to_bits with mask_ty/bit_order attrs"
    );
    assert!(
        vector_ops
            .iter()
            .any(|op| op.op == dialect::vector::MASK_TO_BITS_OP
                && op.attr("mask_ty") == Some(&AttrValue::Ty(Ty::v2_bool()))
                && op.attr("bit_order") == Some(&AttrValue::Str("lsb_lane0".to_string()))
                && op.result_tys == [Ty::I64]),
        "missing <2 x bool> vector.mask_to_bits with mask_ty/bit_order attrs"
    );
    assert!(
        vector_ops
            .iter()
            .any(|op| op.op == dialect::vector::MASK_TO_BITS_OP
                && op.attr("mask_ty") == Some(&AttrValue::Ty(Ty::v8_bool()))
                && op.attr("bit_order") == Some(&AttrValue::Str("lsb_lane0".to_string()))
                && op.result_tys == [Ty::I32]),
        "missing <8 x bool> vector.mask_to_bits with mask_ty/bit_order attrs"
    );
    assert!(
        vector_ops
            .iter()
            .any(|op| op.op == dialect::vector::MASK_TO_BITS_OP
                && op.attr("mask_ty") == Some(&AttrValue::Ty(Ty::v16_bool()))
                && op.attr("bit_order") == Some(&AttrValue::Str("lsb_lane0".to_string()))
                && op.result_tys == [Ty::I32]),
        "missing <16 x bool> vector.mask_to_bits with mask_ty/bit_order attrs"
    );
}

fn nth_vector_dialect_op_mut<'a>(
    module: &'a mut Module,
    op_name: &str,
    ordinal: usize,
) -> &'a mut trust_ir::dialect::DialectInst {
    let mut seen = 0;
    for function in &mut module.functions {
        for block in &mut function.blocks {
            for node in &mut block.body {
                let trust_ir::inst::Inst::DialectOp(op) = &mut node.inst else {
                    continue;
                };
                if op.dialect == trust_ir::dialect::vector::DIALECT && op.op == op_name {
                    if seen == ordinal {
                        return op.as_mut();
                    }
                    seen += 1;
                }
            }
        }
    }
    panic!("missing vector dialect op {op_name:?} at ordinal {ordinal}");
}

fn nth_vector_dialect_result(module: &Module, op_name: &str, ordinal: usize) -> ValueId {
    let mut seen = 0;
    for function in &module.functions {
        for block in &function.blocks {
            for node in &block.body {
                let trust_ir::inst::Inst::DialectOp(op) = &node.inst else {
                    continue;
                };
                if op.dialect == trust_ir::dialect::vector::DIALECT && op.op == op_name {
                    if seen == ordinal {
                        return node.results[0];
                    }
                    seen += 1;
                }
            }
        }
    }
    panic!("missing vector dialect result for op {op_name:?} at ordinal {ordinal}");
}

fn assert_invalid_vector_dialect_fixture(name: &str, module: Module, expected_fragments: &[&str]) {
    let errors = trust_ir_build::validate_module(&module);
    let rendered = errors
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join("\n");
    assert!(
        errors.iter().any(|error| matches!(
            error,
            trust_ir_build::validate::ValidationError::InvalidVectorDialectOp { .. }
        )),
        "{name}: expected InvalidVectorDialectOp, got:\n{rendered}"
    );
    for expected in expected_fragments {
        assert!(
            rendered.contains(expected),
            "{name}: expected diagnostic fragment {expected:?}, got:\n{rendered}"
        );
    }
}

#[derive(Debug, PartialEq)]
struct VectorDialectPayload {
    op: String,
    operands: Vec<u32>,
    results: Vec<u32>,
    result_tys: Vec<trust_ir::ty::Ty>,
    attrs: Vec<(String, trust_ir::dialect::AttrValue)>,
}

fn vector_dialect_payloads(module: &Module) -> Vec<VectorDialectPayload> {
    module
        .functions
        .iter()
        .flat_map(|function| function.blocks.iter())
        .flat_map(|block| block.body.iter())
        .filter_map(|node| match &node.inst {
            trust_ir::inst::Inst::DialectOp(op)
                if op.dialect == trust_ir::dialect::vector::DIALECT =>
            {
                Some(VectorDialectPayload {
                    op: op.op.clone(),
                    operands: op.operands.iter().map(|operand| operand.index()).collect(),
                    results: node.results.iter().map(|result| result.index()).collect(),
                    result_tys: op.result_tys.clone(),
                    attrs: op
                        .attrs
                        .iter()
                        .map(|attr| (attr.name.clone(), attr.value.clone()))
                        .collect(),
                })
            }
            _ => None,
        })
        .collect()
}

fn assert_vector_dialect_payloads_match(
    name: &str,
    module: &Module,
    expected: &[VectorDialectPayload],
) {
    let errors = trust_ir_build::validate_module(module);
    assert!(
        errors.is_empty(),
        "{name}: vector dialect fixture must validate cleanly: {errors:?}"
    );
    assert_eq!(
        vector_dialect_payloads(module),
        expected,
        "{name}: vector dialect op names, lane shapes, attrs, operands, results, or mask bit order drifted"
    );
}

#[test]
fn vector_dialect_roundtrip_fixtures_preserve_payload_schema() {
    let module = generate::build_inst_vector_dialect();
    let expected = vector_dialect_payloads(&module);
    assert_eq!(
        expected.len(),
        10,
        "fixture covers pack/extract/insert for two lane shapes plus four masks"
    );
    assert!(
        expected.iter().any(|payload| payload.op == "mask_to_bits"
            && payload.attrs.iter().any(|(name, value)| name == "bit_order"
                && value == &trust_ir::dialect::AttrValue::Str("lsb_lane0".to_string()))),
        "fixture must pin mask bit-order semantics"
    );
    assert_vector_dialect_payloads_match("generated", &module, &expected);

    let text = roundtrip_text("inst_vector_dialect", &module);
    let parsed =
        trust_ir::parser::parse_module(&text).expect("parse generated vector dialect text");
    assert_vector_dialect_payloads_match("generated text roundtrip", &parsed, &expected);

    let bytes = roundtrip_binary("inst_vector_dialect", &module);
    let decoded = trust_ir::binary::deserialize_module(&bytes)
        .expect("decode generated vector dialect binary");
    assert_vector_dialect_payloads_match("generated binary roundtrip", &decoded, &expected);

    let dir = fixtures_dir();
    let fixture_text = fs::read_to_string(dir.join("inst_vector_dialect.trust_ir"))
        .expect("read checked-in vector dialect text fixture");
    let fixture_from_text =
        trust_ir::parser::parse_module(&fixture_text).expect("parse vector dialect text fixture");
    assert_vector_dialect_payloads_match("checked-in text fixture", &fixture_from_text, &expected);

    let fixture_bytes =
        fs::read(dir.join("inst_vector_dialect.tmbc")).expect("read vector dialect binary fixture");
    let fixture_from_binary = trust_ir::binary::deserialize_module(&fixture_bytes)
        .expect("decode vector dialect binary fixture");
    assert_vector_dialect_payloads_match(
        "checked-in binary fixture",
        &fixture_from_binary,
        &expected,
    );
}

#[test]
fn malformed_vector_dialect_roundtrip_fixture_rejects_schema_before_interpretation() {
    let mut malformed = generate::build_inst_vector_dialect();
    nth_vector_dialect_op_mut(
        &mut malformed,
        trust_ir::dialect::vector::MASK_TO_BITS_OP,
        0,
    )
    .attrs
    .iter_mut()
    .find(|attr| attr.name == "bit_order")
    .expect("fixture mask_to_bits carries bit_order attr")
    .value = trust_ir::dialect::AttrValue::Str("msb_lane0".to_string());

    let text = trust_ir::format::canonical(&malformed);
    let parsed = trust_ir::parser::parse_module(&text).expect("malformed vector text still parses");
    assert_invalid_vector_dialect_fixture(
        "malformed bit_order text roundtrip",
        parsed,
        &[
            "invalid vector.mask_to_bits",
            "unsupported bit_order \"msb_lane0\"",
        ],
    );

    let bytes = trust_ir::binary::serialize_module(&malformed);
    let decoded = trust_ir::binary::deserialize_module(&bytes)
        .expect("malformed vector binary still decodes");
    assert_invalid_vector_dialect_fixture(
        "malformed bit_order binary roundtrip",
        decoded,
        &[
            "invalid vector.mask_to_bits",
            "unsupported bit_order \"msb_lane0\"",
        ],
    );
}

#[test]
fn vector_dialect_negative_fixtures_reject_malformed_ops() {
    use trust_ir::dialect::{self, AttrValue};
    use trust_ir::ty::Ty;

    let mut misspelled_op = generate::build_inst_vector_dialect();
    nth_vector_dialect_op_mut(&mut misspelled_op, dialect::vector::PACK_LANES_OP, 0).op =
        "pack_lane".to_string();
    assert_invalid_vector_dialect_fixture(
        "misspelled op name",
        misspelled_op,
        &[
            "invalid vector.pack_lane",
            "unknown vector op \"pack_lane\"",
        ],
    );

    let mut invalid_lane = generate::build_inst_vector_dialect();
    nth_vector_dialect_op_mut(&mut invalid_lane, dialect::vector::EXTRACT_LANE_OP, 0)
        .attrs
        .iter_mut()
        .find(|attr| attr.name == "lane")
        .expect("fixture extract carries lane attr")
        .value = AttrValue::U64(4);
    assert_invalid_vector_dialect_fixture(
        "invalid lane index",
        invalid_lane,
        &[
            "invalid vector.extract_lane",
            "lane 4 is out of range for 4 lane vector",
        ],
    );

    let mut wrong_operand_shape = generate::build_inst_vector_dialect();
    nth_vector_dialect_op_mut(&mut wrong_operand_shape, dialect::vector::PACK_LANES_OP, 0)
        .operands
        .pop();
    assert_invalid_vector_dialect_fixture(
        "wrong operand shape",
        wrong_operand_shape,
        &[
            "invalid vector.pack_lanes",
            "expects 4 lane operand(s), got 3",
        ],
    );

    let mut wrong_result_shape = generate::build_inst_vector_dialect();
    nth_vector_dialect_op_mut(&mut wrong_result_shape, dialect::vector::MASK_TO_BITS_OP, 0)
        .result_tys[0] = Ty::I64;
    assert_invalid_vector_dialect_fixture(
        "wrong result shape",
        wrong_result_shape,
        &[
            "invalid vector.mask_to_bits",
            "<4 x bool> mask_to_bits result must be i32",
        ],
    );

    let mut missing_attr = generate::build_inst_vector_dialect();
    nth_vector_dialect_op_mut(&mut missing_attr, dialect::vector::EXTRACT_LANE_OP, 0)
        .attrs
        .retain(|attr| attr.name != "vector_ty");
    assert_invalid_vector_dialect_fixture(
        "missing vector_ty attr",
        missing_attr,
        &[
            "invalid vector.extract_lane",
            "requires Ty attribute \"vector_ty\"",
        ],
    );

    let mut malformed_vector_ty = generate::build_inst_vector_dialect();
    nth_vector_dialect_op_mut(
        &mut malformed_vector_ty,
        dialect::vector::EXTRACT_LANE_OP,
        0,
    )
    .attrs
    .iter_mut()
    .find(|attr| attr.name == "vector_ty")
    .expect("fixture extract carries vector_ty attr")
    .value = AttrValue::Str("<4 x i32>".to_string());
    assert_invalid_vector_dialect_fixture(
        "malformed vector_ty attr",
        malformed_vector_ty,
        &[
            "invalid vector.extract_lane",
            "requires Ty attribute \"vector_ty\"",
        ],
    );

    let mut malformed_attr = generate::build_inst_vector_dialect();
    nth_vector_dialect_op_mut(&mut malformed_attr, dialect::vector::INSERT_LANE_OP, 0)
        .attrs
        .iter_mut()
        .find(|attr| attr.name == "lane")
        .expect("fixture insert carries lane attr")
        .value = AttrValue::Bool(true);
    assert_invalid_vector_dialect_fixture(
        "malformed lane attr",
        malformed_attr,
        &[
            "invalid vector.insert_lane",
            "requires U64 attribute \"lane\"",
        ],
    );

    let mut malformed_mask_ty = generate::build_inst_vector_dialect();
    nth_vector_dialect_op_mut(&mut malformed_mask_ty, dialect::vector::MASK_TO_BITS_OP, 0)
        .attrs
        .iter_mut()
        .find(|attr| attr.name == "mask_ty")
        .expect("fixture mask_to_bits carries mask_ty attr")
        .value = AttrValue::Str("<4 x bool>".to_string());
    assert_invalid_vector_dialect_fixture(
        "malformed mask_ty attr",
        malformed_mask_ty,
        &[
            "invalid vector.mask_to_bits",
            "requires Ty attribute \"mask_ty\"",
        ],
    );

    let mut malformed_bit_order = generate::build_inst_vector_dialect();
    nth_vector_dialect_op_mut(
        &mut malformed_bit_order,
        dialect::vector::MASK_TO_BITS_OP,
        0,
    )
    .attrs
    .iter_mut()
    .find(|attr| attr.name == "bit_order")
    .expect("fixture mask_to_bits carries bit_order attr")
    .value = AttrValue::Bool(true);
    assert_invalid_vector_dialect_fixture(
        "malformed bit_order attr",
        malformed_bit_order,
        &[
            "invalid vector.mask_to_bits",
            "requires Str attribute \"bit_order\"",
        ],
    );

    let mut non_bool_mask = generate::build_inst_vector_dialect();
    let inserted_v4 = nth_vector_dialect_result(&non_bool_mask, dialect::vector::INSERT_LANE_OP, 0);
    nth_vector_dialect_op_mut(&mut non_bool_mask, dialect::vector::MASK_TO_BITS_OP, 0).operands
        [0] = inserted_v4;
    assert_invalid_vector_dialect_fixture(
        "non-bool mask input",
        non_bool_mask,
        &[
            "invalid vector.mask_to_bits",
            "mask operand 0",
            "type <4 x i32>",
            "does not match expected <4 x bool>",
        ],
    );
}

#[test]
fn native_request_bundle_contract_pins_trust_verifier_modes() {
    let fixture = generate::build_trust_native_request_bundle();
    let bundle = fixture.bundle;
    let mut has_trust_mc_chc = false;
    let mut has_trust_mc_pdr = false;
    let mut has_trust_wp_wp = false;
    let mut has_trust_wp_sp = false;
    let mut has_trust_wp_abduction = false;

    assert_eq!(
        bundle.schema_version,
        trust_ir::NATIVE_VERIFICATION_BUNDLE_SCHEMA_VERSION
    );
    assert_eq!(
        bundle.evidence_bundles.len(),
        bundle.requests.len(),
        "native bundle must carry one typed result evidence bundle for each request"
    );
    for evidence in &bundle.evidence_bundles {
        let request = bundle
            .requests
            .iter()
            .find(|request| request.id() == evidence.request())
            .expect("evidence request binding");
        assert_eq!(
            evidence.verifier_suite(),
            request.verifier_suite(),
            "evidence bundle must bind the same verifier suite as request {}",
            request.id()
        );
        assert_eq!(
            evidence.trust_ir_module_digest(),
            bundle.trust_ir_module_digest,
            "evidence bundle must bind the TrustIr module digest for request {}",
            request.id()
        );
        assert_eq!(
            evidence.request_digest(),
            request.stable_digest(),
            "evidence bundle must bind the stable request digest for request {}",
            request.id()
        );
        assert_eq!(
            evidence.obligations(),
            request.obligations(),
            "evidence bundle must bind the requested obligations for request {}",
            request.id()
        );
        assert!(
            !evidence.artifacts().is_empty(),
            "evidence bundle must carry digest-bound artifacts for request {}",
            request.id()
        );
    }
    assert!(
        !bundle.compiler_facts.adt_layouts.is_empty(),
        "native bundle must carry ADT layout facts"
    );
    assert!(
        !bundle.compiler_facts.fat_pointers.is_empty(),
        "native bundle must carry fat pointer metadata facts"
    );
    assert!(
        bundle.compiler_facts.casts.iter().any(|fact| {
            fact.op == trust_ir::CastOp::Transmute
                && matches!(fact.evidence, CastLayoutEvidence::SameSize { .. })
        }),
        "native bundle must carry typed transmute layout evidence"
    );
    assert!(
        !bundle.compiler_facts.monomorphizations.is_empty(),
        "native bundle must carry monomorphization identity facts"
    );
    assert!(
        bundle
            .compiler_facts
            .obligation_sources
            .iter()
            .any(|source| source.cause == NativeObligationCause::CastCheck
                && source
                    .facts
                    .iter()
                    .any(|fact| matches!(fact, NativeCompilerFactRef::Cast(_)))),
        "native bundle must map obligations to typed cast facts"
    );
    assert_eq!(
        bundle.obligations_for_assertion(NativeAssertionId::new(0)),
        vec![ProofId::new(2)],
        "native bundle must expose source assertion ids for downstream diagnostics"
    );
    assert!(
        bundle
            .obligation_source(ProofId::new(2))
            .is_some_and(
                |source| source.assertion_id == Some(NativeAssertionId::new(0))
                    && source.cause == NativeObligationCause::Assert
            ),
        "native bundle must map assertion obligations back to first-class assertion ids"
    );
    for compiler_source in &bundle.compiler_facts.obligation_sources {
        let embedded = bundle
            .module
            .proof_obligation_source(compiler_source.obligation)
            .expect("every native compiler source has an embedded source identity");
        let public = embedded
            .public
            .as_ref()
            .expect("every native requested obligation has an atomic public identity");
        assert_eq!(
            public.obligation_id, compiler_source.public_obligation_id,
            "embedded and compiler public obligation ids must agree"
        );
        assert!(
            !public.semantic_digest.is_zero(),
            "public obligation semantic digests must be nonzero"
        );
        if let Some(span) = compiler_source.span {
            let range = embedded
                .range
                .expect("located native compiler sources retain an exact embedded range");
            assert_eq!(
                (range.file, range.start_line, range.start_col),
                (span.file, span.line, span.col),
                "embedded ranges must reconcile with native compiler source starts"
            );
            assert!(
                (range.end_line, range.end_col) >= (range.start_line, range.start_col),
                "embedded ranges must retain a non-reversed endpoint"
            );
        }
    }

    for request in &bundle.requests {
        assert_eq!(
            request.provenance().verifier_suite,
            request.verifier_suite(),
            "native bundle must carry structured verifier-suite identity for request {}",
            request.id()
        );
        assert!(
            !request.provenance().expected_verifier.name.is_empty(),
            "native bundle must carry structured verifier tool identity for request {}",
            request.id()
        );
        assert!(
            !request.solver_identities().is_empty(),
            "native bundle must carry structured solver/prover identities for request {}",
            request.id()
        );
        assert!(
            request
                .provenance()
                .replay_identity()
                .is_some_and(|replay| replay.transcript_digest.is_some()),
            "native bundle must carry replay identity and transcript digest for request {}",
            request.id()
        );
        match request {
            NativeVerificationRequest::TrustVc(request) => {
                assert_eq!(
                    request.mode,
                    TrustVcVerificationMode::ImportProofCertificates
                );
                assert_eq!(
                    request.provenance.verifier_suite,
                    NativeVerifierSuite::TrustVc
                );
                assert!(
                    !request.obligations.is_empty(),
                    "TrustVc request must bind obligations"
                );
                for obligation in &request.obligations {
                    assert!(
                        request.certificates.iter().any(|cert| {
                            cert.obligation == *obligation
                                && !cert.prover.is_empty()
                                && !cert.evidence_digest.is_zero()
                        }),
                        "TrustVc request must carry per-obligation evidence for {obligation}"
                    );
                }
            }
            NativeVerificationRequest::TrustMc(request) => match request.mode {
                TrustMcVerificationMode::BoundedModelCheck => {}
                TrustMcVerificationMode::Chc => {
                    has_trust_mc_chc = true;
                    assert_eq!(
                        request.provenance.verifier_suite,
                        NativeVerifierSuite::TrustMc
                    );
                    assert_eq!(request.options.chc.engine, TrustMcChcEngine::Spacer);
                    assert!(request.options.chc.emit_horn_clauses);
                    assert!(request.options.chc.pdr.enabled);
                    assert!(
                        request
                            .options
                            .chc
                            .pdr
                            .max_frames
                            .is_some_and(|frames| frames > 0)
                    );
                    assert_eq!(
                        request.options.chc.pdr.generalization,
                        TrustMcPdrGeneralization::Cubes
                    );
                }
                TrustMcVerificationMode::Pdr => {
                    has_trust_mc_pdr = true;
                    assert_eq!(
                        request.provenance.verifier_suite,
                        NativeVerifierSuite::TrustMc
                    );
                    assert_eq!(request.options.chc.engine, TrustMcChcEngine::NativePdr);
                    assert!(request.options.chc.emit_horn_clauses);
                    assert!(request.options.chc.pdr.enabled);
                    assert!(
                        request
                            .options
                            .chc
                            .pdr
                            .max_frames
                            .is_some_and(|frames| frames > 0)
                    );
                    assert_eq!(
                        request.options.chc.pdr.generalization,
                        TrustMcPdrGeneralization::Interpolants
                    );
                }
            },
            NativeVerificationRequest::TrustWp(request) => {
                assert_eq!(
                    request.provenance.verifier_suite,
                    NativeVerifierSuite::TrustWp
                );
                assert!(request.options.emit_verification_conditions);
                match request.mode {
                    TrustWpVerificationMode::WeakestPrecondition => has_trust_wp_wp = true,
                    TrustWpVerificationMode::StrongestPostcondition => {
                        has_trust_wp_sp = true;
                        assert!(
                            request.provenance.replay_context.atoms.iter().any(|atom| {
                                atom.kind == NativeReplayAtomKind::Assumption
                                    && !atom.payload_digest.is_zero()
                            }),
                            "TrustWp SP request must carry assumption replay atoms"
                        );
                        assert!(
                            request.provenance.replay_context.atoms.iter().any(|atom| {
                                atom.kind == NativeReplayAtomKind::Assertion
                                    && atom.assertion_id == Some(NativeAssertionId::new(0))
                                    && !atom.payload_digest.is_zero()
                            }),
                            "TrustWp SP request must carry assertion replay atoms with assertion ids"
                        );
                    }
                    TrustWpVerificationMode::Abduction => {
                        has_trust_wp_abduction = true;
                        assert!(request.options.max_abduced_preconditions > 0);
                    }
                }
            }
        }
        for obligation in request.obligations() {
            assert!(
                bundle
                    .compiler_facts
                    .obligation_sources
                    .iter()
                    .any(|source| source.obligation == *obligation
                        && request
                            .function()
                            .is_none_or(|function| source.function == Some(function))
                        && source.span.is_some()),
                "native bundle must carry source span mapping for request {}/{}",
                request.id(),
                obligation
            );
        }
    }

    assert!(
        has_trust_mc_chc,
        "native bundle must pin a TrustMc CHC request"
    );
    assert!(
        has_trust_mc_pdr,
        "native bundle must pin a TrustMc PDR request"
    );
    assert!(
        has_trust_wp_wp,
        "native bundle must pin a TrustWp WP request"
    );
    assert!(
        has_trust_wp_sp,
        "native bundle must pin a TrustWp SP request"
    );
    assert!(
        has_trust_wp_abduction,
        "native bundle must pin a TrustWp abduction request"
    );

    let json = serde_json::to_value(&bundle).expect("native bundle JSON value");
    let requests = json["requests"].as_array().expect("requests array");
    let evidence_bundles = json["evidence_bundles"]
        .as_array()
        .expect("evidence bundles array");
    assert!(
        evidence_bundles.iter().any(|evidence| {
            evidence.get("TrustVc").is_some_and(|trust_vc| {
                trust_vc["request"].as_u64() == Some(0)
                    && trust_vc["request_digest"].get("bytes").is_some()
                    && trust_vc["artifacts"].as_array().is_some_and(|artifacts| {
                        artifacts.iter().any(|artifact| {
                            artifact["kind"].as_str() == Some("TrustVcCertificateImport")
                                && artifact["digest"].get("bytes").is_some()
                        })
                    })
            })
        }),
        "native bundle JSON must carry typed TrustVc result artifacts"
    );
    assert!(
        evidence_bundles.iter().any(|evidence| {
            evidence.get("TrustMc").is_some_and(|trust_mc| {
                trust_mc["mode"].as_str() == Some("Pdr")
                    && trust_mc["request_digest"].get("bytes").is_some()
                    && trust_mc["artifacts"].as_array().is_some_and(|artifacts| {
                        artifacts.iter().any(|artifact| {
                            artifact["kind"].as_str() == Some("TrustMcPdrTrace")
                                && artifact["digest"].get("bytes").is_some()
                        })
                    })
            })
        }),
        "native bundle JSON must carry typed TrustMc PDR result artifacts"
    );
    assert!(
        evidence_bundles.iter().any(|evidence| {
            evidence.get("TrustWp").is_some_and(|trust_wp| {
                trust_wp["mode"].as_str() == Some("Abduction")
                    && trust_wp["request_digest"].get("bytes").is_some()
                    && trust_wp["artifacts"].as_array().is_some_and(|artifacts| {
                        artifacts.iter().any(|artifact| {
                            artifact["kind"].as_str() == Some("TrustWpAbducedPrecondition")
                                && artifact["digest"].get("bytes").is_some()
                        })
                    })
            })
        }),
        "native bundle JSON must carry typed TrustWp abduction result artifacts"
    );
    let obligation_sources = json["compiler_facts"]["obligation_sources"]
        .as_array()
        .expect("obligation sources array");
    assert!(
        obligation_sources.iter().any(|source| {
            source["obligation"].as_u64() == Some(2)
                && source["assertion_id"].as_u64() == Some(0)
                && source["cause"].as_str() == Some("Assert")
        }),
        "native bundle JSON must carry first-class assertion ids"
    );
    assert!(
        requests.iter().any(|request| {
            request.get("TrustMc").is_some_and(|trust_mc| {
                trust_mc["provenance"]["verifier_suite"].as_str() == Some("TrustMc")
                    && trust_mc["provenance"]["replay"]["transcript_digest"]
                        .get("bytes")
                        .is_some()
                    && trust_mc["provenance"]["solvers"]
                        .as_array()
                        .is_some_and(|solvers| {
                            solvers.iter().any(|solver| {
                                solver["name"].as_str() == Some("z3-spacer")
                                    && solver["version"].as_str() == Some("4.13.0")
                            })
                        })
            })
        }),
        "native bundle JSON must carry structured verifier-suite and solver identity"
    );
    assert!(
        requests.iter().any(|request| {
            request.get("TrustWp").is_some_and(|trust_wp| {
                trust_wp["mode"].as_str() == Some("StrongestPostcondition")
                    && trust_wp["provenance"]["replay_context"]["atoms"]
                        .as_array()
                        .is_some_and(|atoms| {
                            atoms.iter().any(|atom| {
                                atom["kind"].as_str() == Some("Assumption")
                                    && atom["payload_digest"].get("bytes").is_some()
                            }) && atoms.iter().any(|atom| {
                                atom["kind"].as_str() == Some("Assertion")
                                    && atom["assertion_id"].as_u64() == Some(0)
                                    && atom["payload_digest"].get("bytes").is_some()
                            })
                        })
            })
        }),
        "native bundle JSON must carry typed TrustWp SP replay atoms"
    );
    let trust_vc = requests
        .iter()
        .find_map(|request| request.get("TrustVc"))
        .expect("TrustVc request in JSON");
    let trust_vc_obligations = trust_vc["obligations"]
        .as_array()
        .expect("TrustVc obligations array");
    let trust_vc_certificates = trust_vc["certificates"]
        .as_array()
        .expect("TrustVc certificates array");
    for obligation in trust_vc_obligations {
        let obligation = obligation.as_u64().expect("numeric obligation id");
        assert!(
            trust_vc_certificates.iter().any(|cert| {
                cert["obligation"].as_u64() == Some(obligation)
                    && cert.get("prover").is_some()
                    && cert.get("evidence_digest").is_some()
                    && cert["evidence_digest"]["bytes"]
                        .as_array()
                        .is_some_and(|bytes| bytes.len() == 32)
            }),
            "TrustVc JSON must carry obligation/prover/evidence_digest for {obligation}"
        );
    }
}

#[test]
fn native_request_bundle_contract_fails_closed_for_missing_evidence() {
    let mut bundle = generate::build_trust_native_request_bundle().bundle;
    let trust_vc = bundle
        .requests
        .iter_mut()
        .find_map(|request| match request {
            NativeVerificationRequest::TrustVc(request) => Some(request),
            _ => None,
        })
        .expect("TrustVc request");
    trust_vc.obligations.push(ProofId::new(1));

    expect_native_bundle_error(
        bundle,
        |err| {
            matches!(
                err,
                NativeVerificationBundleError::MissingTrustVcEvidenceForObligation {
                    request: trust_ir::NativeRequestId(0),
                    obligation: ProofId(1)
                }
            )
        },
        "TrustVc request without per-obligation evidence",
    );
}

#[test]
fn native_request_bundle_contract_fails_closed_for_pending_trust_vc_certificate() {
    let mut bundle = generate::build_trust_native_request_bundle().bundle;
    let pending_cert = ProofCertificate {
        obligation: ProofId::new(1),
        prover: "trust_vc".to_string(),
        evidence: ProofEvidence::LeanProof("exact stale_pending_certificate".to_string()),
    };
    let pending_ref = pending_cert.lineage_ref();
    bundle.module.proof_certificates.push(pending_cert);
    bundle.lineage.nodes[0]
        .certificates
        .push(pending_ref.clone());

    let trust_vc = bundle
        .requests
        .iter_mut()
        .find_map(|request| match request {
            NativeVerificationRequest::TrustVc(request) => Some(request),
            _ => None,
        })
        .expect("TrustVc request");
    trust_vc.obligations.push(ProofId::new(1));
    trust_vc.certificates.push(pending_ref);

    expect_native_bundle_error(
        bundle,
        |err| {
            matches!(
                err,
                NativeVerificationBundleError::TrustVcCertificateNotDischarged {
                    request: trust_ir::NativeRequestId(0),
                    obligation: ProofId(1),
                    prover,
                    status: ProofStatus::Pending,
                } if prover == "trust_vc"
            )
        },
        "TrustVc request with certificate evidence for a pending obligation",
    );
}

#[test]
fn native_request_bundle_contract_fails_closed_for_missing_solver_identity() {
    let mut bundle = generate::build_trust_native_request_bundle().bundle;
    let trust_mc = bundle
        .requests
        .iter_mut()
        .find_map(|request| match request {
            NativeVerificationRequest::TrustMc(request) => Some(request),
            _ => None,
        })
        .expect("TrustMc request");
    trust_mc.provenance.solvers.clear();

    expect_native_bundle_error(
        bundle,
        |err| {
            matches!(
                err,
                NativeVerificationBundleError::EmptyProvenanceField("request.provenance.solvers")
            )
        },
        "native request without structured solver/prover identity",
    );
}

#[test]
fn native_request_bundle_contract_fails_closed_for_cross_suite_verifier_identity() {
    let mut bundle = generate::build_trust_native_request_bundle().bundle;
    let trust_mc = bundle
        .requests
        .iter_mut()
        .find_map(|request| match request {
            NativeVerificationRequest::TrustMc(request) => Some(request),
            _ => None,
        })
        .expect("TrustMc request");
    trust_mc.provenance.expected_verifier.name = "trust_vc".to_string();

    expect_native_bundle_error(
        bundle,
        |err| {
            matches!(
                err,
                NativeVerificationBundleError::ExpectedVerifierIdentityMismatch {
                    request: trust_ir::NativeRequestId(1),
                    suite: NativeVerifierSuite::TrustMc,
                    verifier,
                    canonical,
                } if verifier == "trust_vc" && canonical == "trust_vc"
            )
        },
        "native request with cross-suite expected verifier identity",
    );
}

#[test]
fn native_request_bundle_contract_fails_closed_for_cross_suite_replay_engine() {
    let mut bundle = generate::build_trust_native_request_bundle().bundle;
    let trust_mc = bundle
        .requests
        .iter_mut()
        .find_map(|request| match request {
            NativeVerificationRequest::TrustMc(request) => Some(request),
            _ => None,
        })
        .expect("TrustMc request");
    trust_mc.provenance.replay.as_mut().expect("replay").engine = "trust_vc-import".to_string();

    expect_native_bundle_error(
        bundle,
        |err| {
            matches!(
                err,
                NativeVerificationBundleError::ReplayIdentityVerifierSuiteMismatch {
                    request: trust_ir::NativeRequestId(1),
                    expected: NativeVerifierSuite::TrustMc,
                    engine,
                    canonical,
                } if engine == "trust_vc-import" && canonical == "trust_vc-import"
            )
        },
        "native request with cross-suite replay engine",
    );
}

#[test]
fn native_request_bundle_contract_fails_closed_for_missing_replay_transcript() {
    let mut bundle = generate::build_trust_native_request_bundle().bundle;
    let trust_mc = bundle
        .requests
        .iter_mut()
        .find_map(|request| match request {
            NativeVerificationRequest::TrustMc(request) => Some(request),
            _ => None,
        })
        .expect("TrustMc request");
    trust_mc
        .provenance
        .replay
        .as_mut()
        .expect("replay")
        .transcript_digest = None;

    expect_native_bundle_error(
        bundle,
        |err| {
            matches!(
                err,
                NativeVerificationBundleError::MissingReplayTranscriptDigest(
                    trust_ir::NativeRequestId(1)
                )
            )
        },
        "native request without replay transcript digest",
    );
}

#[test]
fn native_request_bundle_contract_fails_closed_for_missing_trust_wp_sp_context() {
    let mut bundle = generate::build_trust_native_request_bundle().bundle;
    let trust_wp_sp = bundle
        .requests
        .iter_mut()
        .find_map(|request| match request {
            NativeVerificationRequest::TrustWp(request)
                if request.mode == TrustWpVerificationMode::StrongestPostcondition =>
            {
                Some(request)
            }
            _ => None,
        })
        .expect("TrustWp SP request");
    trust_wp_sp.provenance.replay_context.atoms.clear();

    expect_native_bundle_error(
        bundle,
        |err| {
            matches!(
                err,
                NativeVerificationBundleError::MissingTrustWpStrongestPostconditionContext(
                    trust_ir::NativeRequestId(4)
                )
            )
        },
        "TrustWp SP request without typed replay atoms",
    );
}

#[test]
fn native_request_bundle_contract_fails_closed_for_replay_atom_assertion_mismatch() {
    let mut bundle = generate::build_trust_native_request_bundle().bundle;
    let trust_wp_sp = bundle
        .requests
        .iter_mut()
        .find_map(|request| match request {
            NativeVerificationRequest::TrustWp(request)
                if request.mode == TrustWpVerificationMode::StrongestPostcondition =>
            {
                Some(request)
            }
            _ => None,
        })
        .expect("TrustWp SP request");
    trust_wp_sp
        .provenance
        .replay_context
        .atoms
        .iter_mut()
        .find(|atom| atom.kind == NativeReplayAtomKind::Assertion)
        .expect("assertion replay atom")
        .assertion_id = Some(NativeAssertionId::new(99));

    expect_native_bundle_error(
        bundle,
        |err| {
            matches!(
                err,
                NativeVerificationBundleError::ReplayAtomAssertionMismatch {
                    request: trust_ir::NativeRequestId(4),
                    atom,
                    obligation: ProofId(2),
                    expected: Some(NativeAssertionId(0)),
                    actual: NativeAssertionId(99),
                } if *atom == trust_ir::NativeReplayAtomId(2)
            )
        },
        "TrustWp SP replay atom with mismatched assertion id",
    );
}

#[test]
fn native_request_bundle_contract_fails_closed_for_replay_atom_digest_mismatch() {
    let mut bundle = generate::build_trust_native_request_bundle().bundle;
    let trust_wp_sp = bundle
        .requests
        .iter_mut()
        .find_map(|request| match request {
            NativeVerificationRequest::TrustWp(request)
                if request.mode == TrustWpVerificationMode::StrongestPostcondition =>
            {
                Some(request)
            }
            _ => None,
        })
        .expect("TrustWp SP request");
    trust_wp_sp.provenance.replay_context.atoms[0].payload_digest = ProofDigest::sha256([0x42; 32]);

    expect_native_bundle_error(
        bundle,
        |err| {
            matches!(
                err,
                NativeVerificationBundleError::ReplayAtomDigestMismatch {
                    request: trust_ir::NativeRequestId(4),
                    atom: trust_ir::NativeReplayAtomId(0),
                    expected: _,
                    actual,
                } if *actual == ProofDigest::sha256([0x42; 32])
            )
        },
        "TrustWp SP replay atom with stale payload digest",
    );
}

#[test]
fn native_request_bundle_contract_fails_closed_for_unsupported_mode_reason() {
    let mut bundle = generate::build_trust_native_request_bundle().bundle;
    let trust_mc = bundle
        .requests
        .iter_mut()
        .find_map(|request| match request {
            NativeVerificationRequest::TrustMc(request) => Some(request),
            _ => None,
        })
        .expect("TrustMc request");
    trust_mc
        .provenance
        .replay_context
        .unsupported_modes
        .push(NativeUnsupportedMode::new(
            NativeUnsupportedModeReason::UnsupportedFormulaSchema,
            "trust-types.Formula@future",
        ));

    expect_native_bundle_error(
        bundle,
        |err| {
            matches!(
                err,
                NativeVerificationBundleError::UnsupportedNativeRequestMode {
                    request: trust_ir::NativeRequestId(1),
                    reason: NativeUnsupportedModeReason::UnsupportedFormulaSchema,
                    detail,
                } if detail == "trust-types.Formula@future"
            )
        },
        "native request with typed unsupported-mode reason",
    );
}

#[test]
fn native_request_bundle_contract_fails_closed_for_stale_evidence_bundle() {
    let mut bundle = generate::build_trust_native_request_bundle().bundle;
    let trust_mc_pdr = bundle
        .evidence_bundles
        .iter_mut()
        .find_map(|evidence| match evidence {
            NativeEvidenceBundle::TrustMc(evidence)
                if evidence.mode == TrustMcVerificationMode::Pdr =>
            {
                Some(evidence)
            }
            _ => None,
        })
        .expect("TrustMc PDR evidence");
    trust_mc_pdr.request_digest = ProofDigest::sha256([0x51; 32]);

    expect_native_bundle_error(
        bundle,
        |err| {
            matches!(
                err,
                NativeVerificationBundleError::EvidenceRequestDigestMismatch {
                    request: trust_ir::NativeRequestId(2),
                    expected: _,
                    actual,
                } if *actual == ProofDigest::sha256([0x51; 32])
            )
        },
        "native evidence bundle with stale request digest",
    );
}

#[test]
fn native_request_bundle_contract_fails_closed_for_cross_suite_evidence_artifact() {
    let mut bundle = generate::build_trust_native_request_bundle().bundle;
    let trust_mc_chc = bundle
        .evidence_bundles
        .iter_mut()
        .find_map(|evidence| match evidence {
            NativeEvidenceBundle::TrustMc(evidence)
                if evidence.mode == TrustMcVerificationMode::Chc =>
            {
                Some(evidence)
            }
            _ => None,
        })
        .expect("TrustMc CHC evidence");
    trust_mc_chc.artifacts[0].kind = NativeEvidenceArtifactKind::TrustWpVerificationCondition;

    expect_native_bundle_error(
        bundle,
        |err| {
            matches!(
                err,
                NativeVerificationBundleError::EvidenceArtifactSuiteMismatch {
                    request: trust_ir::NativeRequestId(1),
                    suite: NativeVerifierSuite::TrustMc,
                    kind: NativeEvidenceArtifactKind::TrustWpVerificationCondition,
                }
            )
        },
        "native evidence bundle with cross-suite artifact kind",
    );
}

#[test]
fn native_request_bundle_contract_fails_closed_for_cross_suite_certificate_attachment() {
    let mut bundle = generate::build_trust_native_request_bundle().bundle;
    bundle.module.proof_certificates[0].prover = "trust_mc".to_string();
    let trust_mc_ref = bundle.module.proof_certificates[0].lineage_ref();
    bundle.lineage.nodes[0].certificates[0] = trust_mc_ref.clone();
    let trust_vc = bundle
        .requests
        .iter_mut()
        .find_map(|request| match request {
            NativeVerificationRequest::TrustVc(request) => Some(request),
            _ => None,
        })
        .expect("TrustVc request");
    trust_vc.certificates[0] = trust_mc_ref;

    expect_native_bundle_error(
        bundle,
        |err| {
            matches!(
                err,
                NativeVerificationBundleError::CertificateVerifierSuiteMismatch {
                    request: trust_ir::NativeRequestId(0),
                    expected: NativeVerifierSuite::TrustVc,
                    obligation: ProofId(0),
                    prover,
                    canonical,
                } if prover == "trust_mc" && canonical == "trust_mc"
            )
        },
        "TrustVc request with cross-suite certificate attachment",
    );
}

#[test]
fn native_request_bundle_contract_fails_closed_for_ambiguous_lineage_certificate_identity() {
    let mut bundle = generate::build_trust_native_request_bundle().bundle;
    let mut stale_ref = bundle.module.proof_certificates[0].lineage_ref();
    stale_ref.evidence_digest = ProofDigest::sha256([0xAB; 32]);
    bundle.lineage.nodes[0].certificates.push(stale_ref);

    expect_native_bundle_error(
        bundle,
        |err| {
            matches!(
                err,
                NativeVerificationBundleError::Lineage(lineage_errors)
                    if lineage_errors.iter().any(|lineage_err| matches!(
                        lineage_err,
                        ProofLineageError::DuplicateCertificateIdentity {
                            node: ProofLineageId(0),
                            obligation: ProofId(0),
                            prover,
                        } if prover == "trust_vc-clean-kernel"
                    ))
            )
        },
        "native request lineage with multiple evidence digests for one certificate identity",
    );
}

#[test]
fn native_request_bundle_contract_fails_closed_for_stale_request_lineage_root() {
    let mut bundle = generate::build_trust_native_request_bundle().bundle;
    let current_trust_ir = bundle.trust_ir_module_digest;
    let mut current_root = bundle.lineage.nodes[0].clone();
    current_root.id = ProofLineageId::new(1);
    bundle.lineage.nodes[0].target_module = bundle.lineage.nodes[0].source_module;
    bundle.lineage.nodes.push(current_root);
    bundle.lineage.roots.push(ProofLineageId::new(1));

    expect_native_bundle_error(
        bundle,
        |err| {
            matches!(
                err,
                NativeVerificationBundleError::RequestLineageRootTargetMismatch {
                    request: trust_ir::NativeRequestId(0),
                    root: ProofLineageId(0),
                    expected,
                    actual: _,
                } if *expected == current_trust_ir
            )
        },
        "native request rooted in stale lineage target",
    );
}

#[test]
fn native_request_bundle_contract_fails_closed_for_duplicate_request_lineage_roots() {
    let mut bundle = generate::build_trust_native_request_bundle().bundle;
    let trust_vc = bundle
        .requests
        .iter_mut()
        .find_map(|request| match request {
            NativeVerificationRequest::TrustVc(request) => Some(request),
            _ => None,
        })
        .expect("TrustVc request");
    trust_vc.lineage_roots.push(ProofLineageId::new(0));

    expect_native_bundle_error(
        bundle,
        |err| {
            matches!(
                err,
                NativeVerificationBundleError::DuplicateRequestLineageRoot {
                    request: trust_ir::NativeRequestId(0),
                    root: ProofLineageId(0),
                }
            )
        },
        "native request with duplicate lineage roots",
    );
}

#[test]
fn native_request_bundle_contract_fails_closed_for_malformed_provenance() {
    let mut bundle = generate::build_trust_native_request_bundle().bundle;
    let trust_mc = bundle
        .requests
        .iter_mut()
        .find_map(|request| match request {
            NativeVerificationRequest::TrustMc(request) => Some(request),
            _ => None,
        })
        .expect("TrustMc request");
    trust_mc.provenance.expected_verifier.name = " ".to_string();
    trust_mc.provenance.solvers[0].version = Some("".to_string());
    trust_mc.provenance.replay.as_mut().expect("replay").engine = "".to_string();

    let errors = bundle
        .validate()
        .expect_err("native fixture with malformed provenance rejected");
    assert!(
        errors.iter().any(|err| matches!(
            err,
            NativeVerificationBundleError::EmptyProvenanceField(
                "request.provenance.expected_verifier"
            )
        )),
        "blank verifier identity was not rejected: {errors:?}"
    );
    assert!(
        errors.iter().any(|err| matches!(
            err,
            NativeVerificationBundleError::InvalidToolIdentityField {
                field: "request.provenance.solvers",
                component: "version"
            }
        )),
        "blank solver version was not rejected: {errors:?}"
    );
    assert!(
        errors.iter().any(|err| matches!(
            err,
            NativeVerificationBundleError::InvalidReplayIdentity {
                request: trust_ir::NativeRequestId(1),
                field: "engine"
            }
        )),
        "blank replay engine was not rejected: {errors:?}"
    );
}

#[test]
fn native_request_bundle_contract_fails_closed_for_diagnostic_suppression() {
    let mut bundle = generate::build_trust_native_request_bundle().bundle;
    bundle.diagnostics.include_lineage = false;
    let trust_wp = bundle
        .requests
        .iter_mut()
        .find_map(|request| match request {
            NativeVerificationRequest::TrustWp(request) => Some(request),
            _ => None,
        })
        .expect("TrustWp request");
    trust_wp.diagnostics.include_source_spans = false;
    trust_wp.diagnostics.include_lineage = false;
    let missing_source = trust_wp.obligations[0];
    bundle
        .compiler_facts
        .obligation_sources
        .retain(|source| source.obligation != missing_source);

    let errors = bundle
        .validate()
        .expect_err("native fixture with diagnostic suppression rejected");
    assert!(
        errors.iter().any(|err| matches!(
            err,
            NativeVerificationBundleError::InvalidBundleDiagnosticsPolicy {
                field: "include_lineage"
            }
        )),
        "bundle-level lineage suppression was not rejected: {errors:?}"
    );
    assert!(
        errors.iter().any(|err| matches!(
            err,
            NativeVerificationBundleError::InvalidDiagnosticsPolicy {
                request: trust_ir::NativeRequestId(3),
                field: "include_source_spans"
            }
        )),
        "request source-span suppression was not rejected: {errors:?}"
    );
    assert!(
        errors.iter().any(|err| matches!(
            err,
            NativeVerificationBundleError::InvalidDiagnosticsPolicy {
                request: trust_ir::NativeRequestId(3),
                field: "include_lineage"
            }
        )),
        "request lineage suppression was not rejected: {errors:?}"
    );
    assert!(
        errors.iter().any(|err| matches!(
            err,
            NativeVerificationBundleError::MissingObligationSource {
                request: trust_ir::NativeRequestId(3),
                obligation,
            } if *obligation == missing_source
        )),
        "request obligation source omission was not rejected: {errors:?}"
    );
}

#[test]
fn native_request_bundle_contract_fails_closed_for_spanless_source_map() {
    let mut bundle = generate::build_trust_native_request_bundle().bundle;
    bundle
        .compiler_facts
        .obligation_sources
        .iter_mut()
        .find(|source| source.obligation == ProofId::new(2))
        .expect("assertion obligation source")
        .span = None;

    expect_native_bundle_error(
        bundle,
        |err| {
            matches!(
                err,
                NativeVerificationBundleError::MissingObligationSourceSpan {
                    request: trust_ir::NativeRequestId(1),
                    obligation: ProofId(2),
                }
            )
        },
        "native request with spanless source mapping",
    );
}

#[test]
fn native_request_bundle_contract_fails_closed_for_assertionless_source_map() {
    let mut bundle = generate::build_trust_native_request_bundle().bundle;
    bundle
        .compiler_facts
        .obligation_sources
        .iter_mut()
        .find(|source| source.obligation == ProofId::new(2))
        .expect("assertion obligation source")
        .assertion_id = None;

    expect_native_bundle_error(
        bundle,
        |err| {
            matches!(
                err,
                NativeVerificationBundleError::MissingObligationSourceAssertion {
                    request: trust_ir::NativeRequestId(1),
                    obligation: ProofId(2),
                }
            )
        },
        "native request with assertionless source mapping",
    );
}

#[test]
fn native_request_bundle_contract_fails_closed_for_unbound_source_map_cast_fact() {
    let mut bundle = generate::build_trust_native_request_bundle().bundle;
    bundle
        .compiler_facts
        .obligation_sources
        .iter_mut()
        .find(|source| source.obligation == ProofId::new(2))
        .expect("assertion obligation source")
        .facts
        .push(NativeCompilerFactRef::Cast(NativeCompilerFactId::new(4)));

    expect_native_bundle_error(
        bundle,
        |err| {
            matches!(
                err,
                NativeVerificationBundleError::ObligationSourceFactObligationMismatch {
                    obligation: ProofId(2),
                    fact: NativeCompilerFactRef::Cast(NativeCompilerFactId(4)),
                }
            )
        },
        "native request source map citing a cast fact for another obligation",
    );
}

#[test]
fn native_request_bundle_contract_fails_closed_for_cast_check_without_cast_fact() {
    let mut bundle = generate::build_trust_native_request_bundle().bundle;
    bundle
        .compiler_facts
        .obligation_sources
        .iter_mut()
        .find(|source| source.obligation == ProofId::new(1))
        .expect("cast-check obligation source")
        .facts
        .retain(|fact| !matches!(fact, NativeCompilerFactRef::Cast(_)));

    expect_native_bundle_error(
        bundle,
        |err| {
            matches!(
                err,
                NativeVerificationBundleError::MissingObligationSourceCastFact {
                    obligation: ProofId(1),
                }
            )
        },
        "native request cast-check source map without a bound cast fact",
    );
}

#[test]
fn native_request_bundle_contract_fails_closed_for_functionless_scoped_source_map() {
    let mut bundle = generate::build_trust_native_request_bundle().bundle;
    bundle.requests.truncate(1);
    bundle
        .compiler_facts
        .obligation_sources
        .iter_mut()
        .find(|source| source.obligation == ProofId::new(0))
        .expect("TrustVc obligation source")
        .function = None;

    expect_native_bundle_error(
        bundle,
        |err| {
            matches!(
                err,
                NativeVerificationBundleError::ObligationSourceFactFunctionMismatch {
                    obligation: ProofId(0),
                    fact: NativeCompilerFactRef::Monomorphization(NativeMonomorphizationId(0)),
                    expected: None,
                    actual: Some(FuncId(0)),
                }
            )
        },
        "native request source map omitting function for a function-scoped compiler fact",
    );
}

#[test]
fn native_request_bundle_contract_fails_closed_for_mismatched_source_map_monomorphization() {
    let mut bundle = generate::build_trust_native_request_bundle().bundle;
    let mut alternate = bundle.compiler_facts.monomorphizations[0].clone();
    alternate.id = NativeMonomorphizationId::new(1);
    alternate.symbol.push_str(".alt");
    alternate.stable_digest =
        ProofDigest::trust_ir_stable("trust.monomorphization", b"checked_add::<PairU64, 2>#alt");
    bundle.compiler_facts.monomorphizations.push(alternate);
    bundle
        .compiler_facts
        .obligation_sources
        .iter_mut()
        .find(|source| source.obligation == ProofId::new(2))
        .expect("assertion obligation source")
        .facts
        .push(NativeCompilerFactRef::Monomorphization(
            NativeMonomorphizationId::new(1),
        ));

    expect_native_bundle_error(
        bundle,
        |err| {
            matches!(
                err,
                NativeVerificationBundleError::ObligationSourceFactMonomorphizationMismatch {
                    obligation: ProofId(2),
                    expected: NativeMonomorphizationId(0),
                    actual: NativeMonomorphizationId(1),
                }
            )
        },
        "native request source map citing a different monomorphization fact",
    );
}

#[test]
fn native_request_bundle_contract_fails_closed_for_unmatched_source_map_cast_result() {
    let mut bundle = generate::build_trust_native_request_bundle().bundle;
    bundle.compiler_facts.casts[0].result = Some(ValueId::new(999));

    expect_native_bundle_error(
        bundle,
        |err| {
            matches!(
                err,
                NativeVerificationBundleError::InvalidCompilerFact {
                    fact: NativeCompilerFactRef::Cast(NativeCompilerFactId(4)),
                    field: "result",
                }
            )
        },
        "native request source map cast fact with unmatched result value",
    );
}

#[test]
fn native_request_bundle_fixture_fails_closed_for_schema_policy_drift() {
    let mut bundle = read_native_bundle_fixture("native_request_trust_bundle");
    bundle.schema_version = NativeVerificationBundle::SCHEMA_VERSION + 1;
    bundle.serialization.schema_version = NativeVerificationBundle::SCHEMA_VERSION + 1;
    bundle.serialization.unknown_fields = NativeUnknownFieldPolicy::Ignore;

    let errors = bundle
        .validate()
        .expect_err("native fixture with schema policy drift rejected");
    assert!(
        errors.iter().any(|err| matches!(
            err,
            NativeVerificationBundleError::UnsupportedSchemaVersion(version)
                if *version == NativeVerificationBundle::SCHEMA_VERSION + 1
        )),
        "schema version drift was not rejected: {errors:?}"
    );
    assert!(
        errors.iter().any(|err| matches!(
            err,
            NativeVerificationBundleError::UnsupportedSerializationSchemaVersion(version)
                if *version == NativeVerificationBundle::SCHEMA_VERSION + 1
        )),
        "serialization schema version drift was not rejected: {errors:?}"
    );
    assert!(
        errors.iter().any(|err| matches!(
            err,
            NativeVerificationBundleError::NonCanonicalSerialization(
                "serialization.unknown_fields"
            )
        )),
        "non-reject unknown-field policy was not rejected: {errors:?}"
    );
}

#[test]
fn native_request_bundle_contract_fails_closed_for_trust_mc_chc_pdr() {
    let mut bundle = generate::build_trust_native_request_bundle().bundle;
    let trust_mc_chc = bundle
        .requests
        .iter_mut()
        .find_map(|request| match request {
            NativeVerificationRequest::TrustMc(request)
                if request.mode == TrustMcVerificationMode::Chc =>
            {
                Some(request)
            }
            _ => None,
        })
        .expect("TrustMc CHC request");
    trust_mc_chc.options.chc.emit_horn_clauses = false;
    expect_native_bundle_error(
        bundle,
        |err| {
            matches!(
                err,
                NativeVerificationBundleError::InvalidTrustMcChcOptions {
                    request: trust_ir::NativeRequestId(1),
                    field: "chc.emit_horn_clauses"
                }
            )
        },
        "TrustMc CHC request without Horn-clause evidence",
    );

    let mut bundle = generate::build_trust_native_request_bundle().bundle;
    let trust_mc_pdr = bundle
        .requests
        .iter_mut()
        .find_map(|request| match request {
            NativeVerificationRequest::TrustMc(request)
                if request.mode == TrustMcVerificationMode::Pdr =>
            {
                Some(request)
            }
            _ => None,
        })
        .expect("TrustMc PDR request");
    trust_mc_pdr.options.chc.pdr.enabled = false;
    expect_native_bundle_error(
        bundle,
        |err| {
            matches!(
                err,
                NativeVerificationBundleError::InvalidTrustMcChcOptions {
                    request: trust_ir::NativeRequestId(2),
                    field: "chc.pdr.enabled"
                }
            )
        },
        "TrustMc PDR request with PDR disabled",
    );
}

#[test]
fn native_request_bundle_contract_fails_closed_for_trust_wp_modes() {
    for (mode, request_id) in [
        (TrustWpVerificationMode::WeakestPrecondition, 3),
        (TrustWpVerificationMode::StrongestPostcondition, 4),
        (TrustWpVerificationMode::Abduction, 5),
    ] {
        let mut bundle = generate::build_trust_native_request_bundle().bundle;
        let trust_wp = bundle
            .requests
            .iter_mut()
            .find_map(|request| match request {
                NativeVerificationRequest::TrustWp(request) if request.mode == mode => {
                    Some(request)
                }
                _ => None,
            })
            .expect("TrustWp request");
        trust_wp.options.emit_verification_conditions = false;

        expect_native_bundle_error(
            bundle,
            |err| {
                matches!(
                    err,
                    NativeVerificationBundleError::InvalidTrustWpOptions {
                        request,
                        field: "emit_verification_conditions"
                    } if *request == trust_ir::NativeRequestId(request_id)
                )
            },
            "TrustWp request without emitted verification conditions",
        );
    }

    let mut bundle = generate::build_trust_native_request_bundle().bundle;
    let trust_wp = bundle
        .requests
        .iter_mut()
        .find_map(|request| match request {
            NativeVerificationRequest::TrustWp(request)
                if request.mode == TrustWpVerificationMode::Abduction =>
            {
                Some(request)
            }
            _ => None,
        })
        .expect("TrustWp abduction request");
    trust_wp.options.max_abduced_preconditions = 0;

    expect_native_bundle_error(
        bundle,
        |err| {
            matches!(
                err,
                NativeVerificationBundleError::InvalidTrustWpOptions {
                    request: trust_ir::NativeRequestId(5),
                    field: "max_abduced_preconditions"
                }
            )
        },
        "TrustWp abduction request without abduced precondition budget",
    );
}

fn expect_native_bundle_error(
    bundle: NativeVerificationBundle,
    matches_error: impl Fn(&NativeVerificationBundleError) -> bool,
    context: &str,
) {
    let errors = bundle
        .validate()
        .expect_err(&format!("{context}: expected validation failure"));
    assert!(
        errors.iter().any(matches_error),
        "{context}: unexpected validation errors: {errors:?}"
    );
}

// ============================================================
// Coverage enforcement
// ============================================================

/// Walks every fixture and verifies that every `Ty`, `Inst`, and
/// `ProofAnnotation` discriminant appears at least once across the
/// corpus. Prevents quiet coverage regressions when new IR variants
/// are added without matching fixture updates.
#[test]
fn coverage() {
    let mut ty_seen = std::collections::HashSet::new();
    let mut inst_seen = std::collections::HashSet::new();
    let mut proof_seen = std::collections::HashSet::new();
    let mut source_identity_seen = false;
    let mut exact_source_range_seen = false;
    let mut public_identity_seen = false;

    for Fixture { build, .. } in corpus() {
        let m = build();
        walk_module(&m, &mut ty_seen, &mut inst_seen, &mut proof_seen);
        for obligation in &m.proof_obligations {
            let Some(source) = &obligation.source else {
                continue;
            };
            source_identity_seen = true;
            exact_source_range_seen |= source.range.is_some_and(|range| {
                (range.end_line, range.end_col) >= (range.start_line, range.start_col)
            });
            public_identity_seen |= source.public.is_some();
        }
    }

    // The strings below are the discriminants we require. This is a
    // deliberately manual list so that `cargo test` catches a missing
    // fixture before the golden-file diff does.
    // v25: Isize/Usize/Char covered by the b1_scalars fixture. Ty::Error is
    // deliberately ABSENT — it is producer-internal and unencodable (the
    // writer panics on it), so no serialized fixture can ever carry it.
    let required_ty = [
        "I8", "I16", "I32", "I64", "I128", "U8", "U16", "U32", "U64", "U128", "F16", "F32", "F64",
        "Bool", "Ptr", "FatPtr", "Unit", "Never", "Array", "Tuple", "Struct", "Enum", "Func",
        "Sequence", "Set", "Record", "Closure", "Ref", "RefMut", "PtrConst", "PtrMut", "Rc",
        "Vector", "Isize", "Usize", "Char",
    ];
    let required_inst = [
        "BinOp",
        "SeqMapAddK",
        "SeqMapNot",
        "SeqMap",
        "UnOp",
        "Overflow",
        "ICmp",
        "FCmp",
        "Cast",
        "Load",
        "Store",
        "Alloca",
        "HeapAlloc",
        "GEP",
        "Dealloc",
        "AtomicLoad",
        "AtomicStore",
        "AtomicRMW",
        "CmpXchg",
        "Fence",
        "Borrow",
        "BorrowMut",
        "EndBorrow",
        "Retain",
        "Release",
        "IsUnique",
        "Br",
        "CondBr",
        "Switch",
        "Return",
        "Unreachable",
        "Call",
        "CallIndirect",
        "ExtractField",
        "InsertField",
        "ExtractElement",
        "InsertElement",
        "Const",
        "NullPtr",
        "GlobalAddr",
        "Undef",
        "Assume",
        "Assert",
        "Copy",
        "Select",
        "PtrData",
        "PtrMetadata",
        "PtrFromParts",
        "OpenFrame",
        "BindSlot",
        "LoadSlot",
        "CloseFrame",
        "DialectOp",
    ];
    let required_proof = [
        "InBounds",
        "NotNull",
        "ValidBorrow",
        "UniqueBorrow",
        "SharedBorrow",
        "ValidDealloc",
        "NoOverflow",
        "NoWrap",
        "DivNonZero",
        "ShiftInRange",
        "Wrapping",
        "Pure",
        "Terminates",
        "Deterministic",
        "Associative",
        "Commutative",
        "DataRaceFree",
        "AtomicOrdering",
        "BoundedOutput",
        "Monotonic",
        "NoAlias",
        "Aligned",
        "NoPanic",
        "NoUndef",
        "ReadonlyTable",
        "AppendOnlyBuffer",
        "AtomicSetInsert",
        "ParallelMap",
        "BoundedLoop",
        "DivergenceClass",
        "Custom",
        "ProofRef",
        "ValueRange",
        "KnownBits",
        "BranchWeights",
    ];
    for v in required_ty {
        assert!(
            ty_seen.contains(v),
            "Ty variant `{v}` not covered by corpus"
        );
    }
    for v in required_inst {
        assert!(
            inst_seen.contains(v),
            "Inst variant `{v}` not covered by corpus"
        );
    }
    for v in required_proof {
        assert!(
            proof_seen.contains(v),
            "ProofAnnotation variant `{v}` not covered by corpus"
        );
    }
    assert!(
        source_identity_seen,
        "embedded proof-obligation source identity not covered by corpus"
    );
    assert!(
        exact_source_range_seen,
        "exact proof-obligation source range not covered by corpus"
    );
    assert!(
        public_identity_seen,
        "atomic public proof-obligation identity not covered by corpus"
    );
}

/// Recursively tag every `Ty` discriminant found in `ty`.
fn tag_ty(ty: &trust_ir::ty::Ty, out: &mut std::collections::HashSet<&'static str>) {
    use trust_ir::ty::Ty::*;
    match ty {
        I8 => {
            out.insert("I8");
        }
        // v25 B1 scalars. `Error` is tagged but NEVER required: it is
        // producer-internal and unencodable, so no fixture can carry it.
        Isize => {
            out.insert("Isize");
        }
        Usize => {
            out.insert("Usize");
        }
        Char => {
            out.insert("Char");
        }
        Error => {
            out.insert("Error");
        }
        I16 => {
            out.insert("I16");
        }
        I32 => {
            out.insert("I32");
        }
        I64 => {
            out.insert("I64");
        }
        I128 => {
            out.insert("I128");
        }
        U8 => {
            out.insert("U8");
        }
        U16 => {
            out.insert("U16");
        }
        U32 => {
            out.insert("U32");
        }
        U64 => {
            out.insert("U64");
        }
        U128 => {
            out.insert("U128");
        }
        F16 => {
            out.insert("F16");
        }
        F32 => {
            out.insert("F32");
        }
        F64 => {
            out.insert("F64");
        }
        Bool => {
            out.insert("Bool");
        }
        Ptr => {
            out.insert("Ptr");
        }
        FatPtr(_) => {
            out.insert("FatPtr");
        }
        Unit => {
            out.insert("Unit");
        }
        Never => {
            out.insert("Never");
        }
        Array(_, _) => {
            out.insert("Array");
        }
        Vector(inner, _) => {
            out.insert("Vector");
            tag_ty(inner, out);
        }
        Tuple(xs) => {
            out.insert("Tuple");
            for x in xs {
                tag_ty(x, out);
            }
        }
        Struct(_) => {
            out.insert("Struct");
        }
        Enum(_) => {
            out.insert("Enum");
        }
        Func(_) => {
            out.insert("Func");
        }
        Sequence(_) => {
            out.insert("Sequence");
        }
        Set(_, _) => {
            out.insert("Set");
        }
        Record(_) => {
            out.insert("Record");
        }
        Closure(_) => {
            out.insert("Closure");
        }
        Ref(inner) => {
            out.insert("Ref");
            tag_ty(inner, out);
        }
        RefMut(inner) => {
            out.insert("RefMut");
            tag_ty(inner, out);
        }
        PtrConst(inner) => {
            out.insert("PtrConst");
            tag_ty(inner, out);
        }
        PtrMut(inner) => {
            out.insert("PtrMut");
            tag_ty(inner, out);
        }
        Rc(inner) => {
            out.insert("Rc");
            tag_ty(inner, out);
        }
        // v30 typed value model. The base type lives in the module `types`
        // table (walked separately), so there is no inline surface to recurse
        // into here.
        Refine(_, _) => {
            out.insert("Refine");
        }
    }
}

fn tag_inst(inst: &trust_ir::inst::Inst, out: &mut std::collections::HashSet<&'static str>) {
    use trust_ir::inst::Inst::*;
    let tag = match inst {
        BinOp { .. } => "BinOp",
        SeqMapAddK { .. } => "SeqMapAddK",
        SeqMapNot { .. } => "SeqMapNot",
        SeqMap { .. } => "SeqMap",
        UnOp { .. } => "UnOp",
        Overflow { .. } => "Overflow",
        ICmp { .. } => "ICmp",
        FCmp { .. } => "FCmp",
        Cast { .. } => "Cast",
        Load { .. } => "Load",
        Store { .. } => "Store",
        Alloca { .. } => "Alloca",
        HeapAlloc { .. } => "HeapAlloc",
        GEP { .. } => "GEP",
        Dealloc { .. } => "Dealloc",
        AtomicLoad { .. } => "AtomicLoad",
        AtomicStore { .. } => "AtomicStore",
        AtomicRMW { .. } => "AtomicRMW",
        CmpXchg { .. } => "CmpXchg",
        Fence { .. } => "Fence",
        Borrow { .. } => "Borrow",
        BorrowMut { .. } => "BorrowMut",
        EndBorrow { .. } => "EndBorrow",
        Retain { .. } => "Retain",
        Release { .. } => "Release",
        IsUnique { .. } => "IsUnique",
        Br { .. } => "Br",
        CondBr { .. } => "CondBr",
        Switch { .. } => "Switch",
        Return { .. } => "Return",
        Unreachable => "Unreachable",
        Call { .. } => "Call",
        CallIndirect { .. } => "CallIndirect",
        ExtractField { .. } => "ExtractField",
        InsertField { .. } => "InsertField",
        ExtractElement { .. } => "ExtractElement",
        InsertElement { .. } => "InsertElement",
        Const { .. } => "Const",
        NullPtr => "NullPtr",
        GlobalAddr { .. } => "GlobalAddr",
        Undef { .. } => "Undef",
        Assume { .. } => "Assume",
        Assert { .. } => "Assert",
        Copy { .. } => "Copy",
        Select { .. } => "Select",
        PtrData { .. } => "PtrData",
        PtrMetadata { .. } => "PtrMetadata",
        PtrFromParts { .. } => "PtrFromParts",
        OpenFrame { .. } => "OpenFrame",
        BindSlot { .. } => "BindSlot",
        LoadSlot { .. } => "LoadSlot",
        CloseFrame { .. } => "CloseFrame",
        DialectOp(_) => "DialectOp",
        CoroSuspend { .. } => "CoroSuspend",
        Invoke { .. } => "Invoke",
        LandingPad { .. } => "LandingPad",
        Resume { .. } => "Resume",
    };
    out.insert(tag);
}

fn tag_proof(p: &ProofAnnotation, out: &mut std::collections::HashSet<&'static str>) {
    // Delegates to the core exhaustive `kind_name()` (crates/trust-ir/src/
    // proof/annotations.rs): the new-variant forcing function lives THERE,
    // where feature-gated arms carry their native cfg and stay correct under
    // every feature unification — no wildcard, no local drift.
    out.insert(p.kind_name());
}

fn walk_module(
    m: &Module,
    ty: &mut std::collections::HashSet<&'static str>,
    inst: &mut std::collections::HashSet<&'static str>,
    proof: &mut std::collections::HashSet<&'static str>,
) {
    // Walk interned module tables.
    for t in &m.types {
        tag_ty(t, ty);
    }
    for ft in &m.func_types {
        for p in &ft.params {
            tag_ty(p, ty);
        }
        for r in &ft.returns {
            tag_ty(r, ty);
        }
    }
    for sd in &m.structs {
        for f in &sd.fields {
            tag_ty(&f.ty, ty);
        }
    }
    for ed in &m.enums {
        for v in &ed.variants {
            for t in &v.fields {
                tag_ty(t, ty);
            }
        }
    }
    for rd in &m.records {
        for f in &rd.fields {
            tag_ty(&f.ty, ty);
        }
    }
    for ct in &m.closure_types {
        for c in &ct.captures {
            tag_ty(c, ty);
        }
    }
    for g in &m.globals {
        tag_ty(&g.ty, ty);
    }
    for f in &m.functions {
        walk_function(f, ty, inst, proof);
    }
}

fn walk_function(
    f: &Function,
    ty: &mut std::collections::HashSet<&'static str>,
    inst: &mut std::collections::HashSet<&'static str>,
    proof: &mut std::collections::HashSet<&'static str>,
) {
    for b in &f.blocks {
        for (_, t) in &b.params {
            tag_ty(t, ty);
        }
        for node in &b.body {
            tag_inst(&node.inst, inst);
            for p in &node.proofs {
                tag_proof(p, proof);
            }
            walk_inst_types(&node.inst, ty);
        }
    }
    for p in &f.proofs {
        tag_proof(p, proof);
    }
}

fn walk_inst_types(i: &trust_ir::inst::Inst, out: &mut std::collections::HashSet<&'static str>) {
    use trust_ir::inst::Inst::*;
    match i {
        BinOp { ty, .. }
        | UnOp { ty, .. }
        | Overflow { ty, .. }
        | ICmp { ty, .. }
        | FCmp { ty, .. }
        | Load { ty, .. }
        | Store { ty, .. }
        | AtomicLoad { ty, .. }
        | AtomicStore { ty, .. }
        | AtomicRMW { ty, .. }
        | CmpXchg { ty, .. }
        | ExtractField { ty, .. }
        | InsertField { ty, .. }
        | ExtractElement { ty, .. }
        | InsertElement { ty, .. }
        | Const { ty, .. }
        | Undef { ty }
        | Copy { ty, .. }
        | Select { ty, .. }
        | LoadSlot { ty, .. } => tag_ty(ty, out),
        Cast { src_ty, dst_ty, .. } => {
            tag_ty(src_ty, out);
            tag_ty(dst_ty, out);
        }
        PtrData { ptr_ty, .. } => tag_ty(ptr_ty, out),
        PtrMetadata {
            ptr_ty,
            metadata_ty,
            ..
        }
        | PtrFromParts {
            ptr_ty,
            metadata_ty,
            ..
        } => {
            tag_ty(ptr_ty, out);
            tag_ty(metadata_ty, out);
        }
        Alloca { ty, .. } => tag_ty(ty, out),
        GEP { pointee_ty, .. } => tag_ty(pointee_ty, out),
        DialectOp(d) => {
            for t in &d.result_tys {
                tag_ty(t, out);
            }
        }
        _ => {}
    }
}
