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
//   targo --unverified test -p trust-ir-conformance --test conformance
//
// Regenerating goldens after an intentional format change:
//   TRUST_IR_UPDATE_FIXTURES=1 targo --unverified test -p trust-ir-conformance --test conformance
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
//   (the writer selects the header per module, up to
//   `binary::FORMAT_VERSION`; v23 is MIN_READ_VERSION; readers accept v23–v25
//   and v29 through `binary::FORMAT_VERSION`, and reject ambiguous v26–v28).
//   The per-section tag layout is documented in `docs/binary-format.md` (the
//   TrustIr#65 freeze doc, normative for the wire format).
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

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

use trust_ir::format::{TextLoss, TextLossKind};
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

// The fixture generators (tests/generate.rs), compiled once as the library's
// `fixtures` module rather than again inside every test binary.
use trust_ir_conformance::fixtures as generate;

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
            "missing fixture {}: {}. Run `TRUST_IR_UPDATE_FIXTURES=1 targo --unverified test -p trust-ir-conformance --test conformance` to generate.",
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
            "missing fixture {}: {}. Run `TRUST_IR_UPDATE_FIXTURES=1 targo --unverified test -p trust-ir-conformance --test conformance` to generate.",
            path.display(),
            e
        )
    });
    if expected != got {
        // Keep diagnostics bounded while exposing the first actual mismatch.
        let first_difference = expected
            .lines()
            .zip(got.lines())
            .enumerate()
            .find(|(_, (expected, got))| expected != got)
            .map(|(line, (expected, got))| {
                format!("line {}: expected {expected:?}; got {got:?}", line + 1)
            })
            .unwrap_or_else(|| "different trailing lines or newline".into());
        panic!(
            "text mismatch for fixture {}: got {} lines, expected {} lines. {first_difference}\n\
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
    build: fn() -> Result<Module, generate::FixtureError>,
    text_supported: bool,
    text_skip_reason: &'static str,
}

/// The fixtures are intentionally ordered by the prompt layout
/// (ty → inst → proof) so a directory listing reads top-to-bottom.
fn corpus() -> Vec<Fixture> {
    vec![
        Fixture {
            name: "single_inhabited_enums",
            build: generate::build_single_inhabited_enums,
            text_supported: true,
            text_skip_reason: "",
        },
        Fixture {
            name: "declared_tuple_v42",
            build: generate::build_declared_tuple_v42,
            text_supported: true,
            text_skip_reason: "",
        },
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
        // v44 import-identity scheme (WS4.10): a mixed V2 + V3 import table.
        // The ONLY golden whose header word is 44.
        Fixture {
            name: "import_scheme",
            build: generate::build_import_scheme,
            text_supported: true,
            text_skip_reason: "",
        },
        // v45 function symbol attributes (WS3.10): visibility / section /
        // retention on a definition and a declaration.
        Fixture {
            name: "abi_function_symbol",
            build: generate::build_abi_function_symbol,
            text_supported: true,
            text_skip_reason: "",
        },
        // v45 per-slot ABI facts (WS3.11): every PassMode tag and the
        // return slot.
        Fixture {
            name: "abi_param_facts",
            build: generate::build_abi_param_facts,
            text_supported: true,
            text_skip_reason: "",
        },
        // v45 128-bit enum tag reprs (WS3.14(b)).
        Fixture {
            name: "abi_enum_tag_repr",
            build: generate::build_abi_enum_tag_repr,
            text_supported: true,
            text_skip_reason: "",
        },
        // v45 calling conventions (WS3.12).
        Fixture {
            name: "abi_calling_conv",
            build: generate::build_abi_calling_conv,
            text_supported: true,
            text_skip_reason: "",
        },
        // v46 typed spec carrier (WS4.14): sorts, typed invariants, temporal
        // properties, a clean-theorem binding and an obligation spec backref.
        // The ONLY golden whose header word is 46.
        Fixture {
            name: "spec_carrier",
            build: generate::build_spec_carrier,
            text_supported: true,
            text_skip_reason: "",
        },
        // v58 declared closure environment frames (WS3.13): a rustc-reordered
        // two-capture frame plus the application it makes lowerable.
        Fixture {
            name: "closure_layout",
            build: generate::build_closure_layout,
            text_supported: true,
            text_skip_reason: "",
        },
        Fixture {
            name: "closure_frame_origin",
            build: generate::build_closure_frame_origin,
            text_supported: true,
            text_skip_reason: "",
        },
        Fixture {
            name: "storage_only",
            build: generate::build_storage_only,
            text_supported: true,
            text_skip_reason: "",
        },
        // v74: a Box deref carrying its validity fact.
        Fixture {
            name: "box_deref",
            build: generate::build_box_deref,
            text_supported: true,
            text_skip_reason: "",
        },
        // v63 runtime captures, distinct from the older static-closure golden.
        Fixture {
            name: "make_closure",
            build: generate::build_make_closure,
            text_supported: true,
            text_skip_reason: "",
        },
        // The tensor region's first slice (PKG-U13a): `Ty::Tensor` in a
        // signature and `Inst::TensorContract` (an integer matmul). The ONLY
        // golden whose header word is TENSOR_FORMAT_VERSION.
        Fixture {
            name: "tensor_contract",
            build: generate::build_tensor_contract,
            text_supported: true,
            text_skip_reason: "",
        },
        // The tensor region's map, reduce and view (PKG-U13c), chained. The
        // ONLY golden whose header word is
        // TENSOR_MAP_REDUCE_VIEW_FORMAT_VERSION.
        Fixture {
            name: "tensor_map_reduce_view",
            build: generate::build_tensor_map_reduce_view,
            text_supported: true,
            text_skip_reason: "",
        },
        // Its gather and scatter (PKG-U13d), chained. The ONLY golden whose
        // header word is TENSOR_GATHER_SCATTER_FORMAT_VERSION.
        Fixture {
            name: "tensor_gather_scatter",
            build: generate::build_tensor_gather_scatter,
            text_supported: true,
            text_skip_reason: "",
        },
        // Content-addressed weight blobs (PKG-U13e): one row named at two
        // element types, an empty row, a blob as a contraction operand. The
        // ONLY golden whose header word is TENSOR_BLOB_FORMAT_VERSION.
        Fixture {
            name: "tensor_weight_blob",
            build: generate::build_tensor_weight_blob,
            text_supported: true,
            text_skip_reason: "",
        },
        // v58 nominal identity (WS3.9): both `TypeOrigin` spellings plus an
        // unkeyed definition. With `closure_layout` above, one of the two
        // goldens whose header word is 58.
        Fixture {
            name: "nominal_type_origin",
            build: generate::build_nominal_type_origin,
            text_supported: true,
            text_skip_reason: "",
        },
        // v59 typed effect summaries and world epochs (WS1.14): a writer, a
        // pure function and a havoc caller, plus a WorldPre/WorldPost clause.
        // The ONLY golden whose header word is the effect-summary version.
        Fixture {
            name: "effect_summaries",
            build: generate::build_effect_summaries,
            // Text carries the whole summary (the `; #effects:` directive)
            // and the `world_pre` / `world_post` places, so this fixture is
            // lossless in all four formats.
            text_supported: true,
            text_skip_reason: "",
        },
        // v60 source-to-lowered signature placement. This is a structurally
        // valid wire control; it grants no native ABI or proof authority.
        Fixture {
            name: "typed_signature_abi",
            build: generate::build_typed_signature_abi,
            text_supported: true,
            text_skip_reason: "",
        },
        // The proof-surface identity carrier (the wire half WS1.12
        // deferred, roadmap WS6.7(b)): two bound clean_backend_tv
        // certificates with every binding field but the WS1.13 island
        // populated (see `build_certificate_binding`), and evidenced
        // licenses. The ONLY golden whose header word is
        // CERTIFICATE_BINDING_FORMAT_VERSION.
        Fixture {
            name: "certificate_binding",
            build: generate::build_certificate_binding,
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
        // contract. The canonical text form does not yet render the
        // verifier-facing contract, so its golden is `#lossy`-marked and
        // refused by the parser (WS4.2); binary / JSON / MessagePack guard it
        // losslessly. (`summary` is positionally-safe in
        // MessagePack — always emitted, declared before the single trailing
        // optional `attrs` — so this round-trips through every format.)
        // WS4.2: the loss-free golden that spells every directive of the
        // shared text vocabulary no other loss-free fixture spells.
        Fixture {
            name: "text_directives",
            build: generate::build_text_directives,
            text_supported: true,
            text_skip_reason: "",
        },
        // WS4.4: the proof surface text carries — every summary clause kind
        // and function place, a `backed_by` citation, one obligation per v41
        // kind, one certificate per `CoverageBound`.
        Fixture {
            name: "proof_surface",
            build: generate::build_proof_surface,
            text_supported: true,
            text_skip_reason: "",
        },
        Fixture {
            name: "composition",
            build: generate::build_composition,
            // WS4.4: text CARRIES the contract (`; #summary:` block with its
            // `#ensures` clauses and the `#backed-by` citation), so the golden
            // is a loss-free text that round-trips EXACTLY. (WS4.2 made it a
            // refused `#lossy` dump until then.)
            text_supported: true,
            text_skip_reason: "",
        },
        // v23 producer provenance: every `Producer` wire tag (including the
        // `Other` string escape) plus an untagged function, emitted through
        // the ModuleBuilder default + FunctionBuilder override surface. The
        // `.trust_ir` golden additionally pins the `; #producer:` header
        // clause in canonical text.
        // v41 codegen license: all three `body_gate` states in one module
        // (`None` = no claim, `Ungated` = must-refuse, `Gated{authority}`),
        // plus a `display_path` whose generics force the quoted text form.
        Fixture {
            name: "body_gate",
            build: generate::build_body_gate,
            text_supported: true,
            text_skip_reason: "",
        },
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
        // v50 constant-size uniform array: Constant::Splat (tag 16) as
        // global initializers (nested, u64-scale lengths) and in a body, and
        // Inst::ArraySplat (tag 59) — the only goldens at header 50.
        Fixture {
            name: "array_splat",
            build: generate::build_array_splat,
            text_supported: true,
            text_skip_reason: "",
        },
        // v51, the INST wire batch: Inst::MakeAggregate / MemCopy / MemSet
        // (tags 60-62) and the WS3.20 sub-ops (BinOp 23-25, UnOp 9-12) — the
        // only goldens at header 51.
        Fixture {
            name: "inst_wire_batch",
            build: generate::build_inst_wire_batch,
            text_supported: true,
            text_skip_reason: "",
        },
        // Plan item P (wire v52): Inst::Assert of every AssertKind (tag 63)
        // beside a kindless one (tag 29) — the only goldens at header 52.
        Fixture {
            name: "assert_kind",
            build: generate::build_assert_kind,
            text_supported: true,
            text_skip_reason: "",
        },
        Fixture {
            name: "call_unwind_boundary",
            build: generate::build_call_unwind_boundary,
            text_supported: true,
            text_skip_reason: "",
        },
        // Amendment P (wire v54): sited asserts (Inst tag 66) of every
        // location spelling, inside the subset, and an `AssertInvoke`
        // (Inst tag 67), outside it — the only goldens at header 54.
        Fixture {
            name: "assert_panic_site",
            build: generate::build_assert_panic_site,
            text_supported: true,
            text_skip_reason: "",
        },
        Fixture {
            name: "assert_invoke",
            build: generate::build_assert_invoke,
            text_supported: true,
            text_skip_reason: "",
        },
        // Amendment D (wire v55): the drop-glue table and `DropInvoke`
        // (Inst tag 68) — the only golden at header 55.
        Fixture {
            name: "drop_glue",
            build: generate::build_drop_glue,
            text_supported: true,
            text_skip_reason: "",
        },
        // Amendment D, Part 2 (wire v56): `InvokeIndirect` (Inst tag 69) —
        // the only golden at header 56.
        Fixture {
            name: "unwind_twins",
            build: generate::build_unwind_twins,
            text_supported: true,
            text_skip_reason: "",
        },
        // Roadmap DG-63 (wire v62): the entry-state pointee clause place
        // (`ClausePlace::ParamPointeeEntry`, clause-place tag 10) on a
        // summary clause and on obligation formulas — the only golden at
        // header 62.
        Fixture {
            name: "param_pointee_place",
            build: generate::build_param_pointee_place,
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
        // v40 container-tail fat pointers: `FatPtrKind::ContainerVtable`
        // (sub-tag 4) beside v38's `ContainerLen` (sub-tag 3) on a struct,
        // a function type, and block parameters. This is the ONLY golden
        // whose header word is 40 — every other `.tmbc` keeps its minimum
        // lossless writer version (back_compat.rs pins that per file).
        Fixture {
            name: "ty_container_vtable",
            build: generate::build_ty_container_vtable,
            text_supported: true,
            text_skip_reason: "",
        },
        // v39 nominal dialect type on a signature, a block parameter and a
        // Copy: the ONLY golden whose header word is 39.
        Fixture {
            name: "ty_dialect_v39",
            build: generate::build_ty_dialect,
            text_supported: true,
            text_skip_reason: "",
        },
        // v43 nominal opaque runtime handle: the four pinned
        // `trust_bignum::Nat` C declarations (type tag 38 on their
        // signatures, `display_path` def-paths) plus a `pred(H) -> H`
        // transport body. The ONLY golden whose header word is 43; the
        // `.trust_ir` golden additionally pins the quoted
        // `handle<"Nat", "trust_bignum::Nat">` text spelling.
        Fixture {
            name: "ty_handle",
            build: generate::build_ty_handle,
            text_supported: true,
            text_skip_reason: "",
        },
        // WS4.15: the Lean library envelope (`trust.lean.ir-library/v1`) with
        // every load-bearing fact in its in-format home
        // (docs/SPEC_RATIFICATIONS.md §9): a `Gated{"clean-kernel-tv"}` Clean
        // body, its Certified `TranslationValidation` obligation with a
        // kernel-re-checked `CleanCic` certificate, and a kernel-only theorem
        // as a `trust.proof_item` reference. The acceptance / refusal tests
        // are `lean_library_envelope_*` below and the `b3.envelope.*` rows.
        Fixture {
            name: "lean_library_envelope",
            build: generate::build_lean_library_envelope,
            // WS4.4 (F-070, F-071): text carries the `custom("..", "..")`
            // theorem-reference kind and the `CleanCic` kernel re-check
            // directive, so the kernel-Certified envelope travels through
            // text and re-certifies (the `b3.envelope.text_*` rows).
            text_supported: true,
            text_skip_reason: "",
        },
    ]
}

struct LineageFixture {
    name: &'static str,
    build: fn() -> Result<generate::ProofLineageFixture, generate::FixtureError>,
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
    build: fn() -> Result<generate::NativeBundleFixture, generate::FixtureError>,
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
    let func_ty = module
        .add_func_type(FuncTy {
            params: Vec::new(),
            returns,
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
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
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
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
        InterpretValueKind::FnItem(func) => format!("fnitem:{}", func.index()),
        InterpretValueKind::PhantomData => "phantom_data".to_string(),
        InterpretValueKind::NullPtr => "null".to_string(),
        InterpretValueKind::Unit => "unit".to_string(),
        InterpretValueKind::Frame { lineage, .. } => format!("frame:{lineage}"),
        InterpretValueKind::PartialBytes(bytes) => format!("partial_bytes({})", bytes.len()),
        // Crystal lane (E3b): an unwritten struct/tuple lane.
        InterpretValueKind::Uninit => "uninit".to_string(),
        InterpretValueKind::DanglingPtr(addr) => format!("dangling_ptr:{addr}"),
        // WS2.12: host-minted runtime handles. No golden carries one (a handle
        // exists only in a host-assisted run).
        InterpretValueKind::Handle { id } => format!("handle:{id}"),
        // PKG-U13a: a tensor's runtime shape and its element count.
        InterpretValueKind::Tensor { dims, elems } => {
            format!("tensor({dims:?};{})", elems.len())
        }
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

#[test]
fn stable_interpret_value_spells_a_tensor_by_its_shape_and_count() {
    assert_eq!(
        stable_interpret_value(&i32_matrix([2, 3], &[1, 2, 3, 4, 5, 6])),
        "tensor([2, 3];6)"
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
    let bytes = trust_ir::binary::serialize_module(module).expect("serialize_module: test fixture");
    let back = trust_ir::binary::deserialize_module(&bytes)
        .unwrap_or_else(|e| panic!("{name}: binary deserialize failed: {e:?}"));
    let bytes2 = trust_ir::binary::serialize_module(&back).expect("serialize_module: test fixture");
    assert_eq!(
        bytes, bytes2,
        "{name}: binary serialize is not idempotent across a round-trip"
    );
    bytes
}

/// Roadmap WS4.2 text-loss ratchet: per corpus fixture, the EXACT set of
/// [`TextLossKind`]s `format::text_losses` reports on its canonical form,
/// measured at landing. A fixture NOT listed here must print through
/// `format::canonical_checked` with `Ok` (and then round-trip EXACTLY).
///
/// Each row only SHRINKS. WS4.4 removed the proof-surface kinds and WS4.5
/// carried the whole layout and linkage surface (struct names/offsets, enum
/// layouts and variant field names, global attributes, `global_asm`, the
/// switch exhaustiveness hint), so the table is EMPTY and stays as the guard
/// for the next field. A row that grows — or a fixture that newly becomes
/// lossy — fails `text_loss_ratchet_is_exact`.
const TEXT_LOSS_RATCHET: &[(&str, &[TextLossKind])] = &[
    // The `composition` (FunctionSummary), `spec_carrier` (ClauseBindings,
    // SpecCarrier) and `lean_library_envelope` (KernelRecheck,
    // ObligationKind) rows are GONE as of WS4.4: text carries the proof
    // surface, so those fixtures have no losses left.
    //
    // The `func_param_abi`, `ty_composite` and `ty_container_vtable` rows are
    // GONE as of WS4.5 (struct half): struct field names and offsets are
    // carried, so those fixtures have no losses left and the ratchet requires
    // an empty row to be deleted rather than kept at zero.
    //
    // The table is EMPTY: every corpus fixture prints through
    // `canonical_checked`. It stays as the guard for the next field — a
    // fixture that becomes lossy must be added here, in the increment that
    // makes it lossy, and fails `text_loss_ratchet_is_exact` until it is.
];

fn ratchet_row(name: &str) -> BTreeSet<TextLossKind> {
    TEXT_LOSS_RATCHET
        .iter()
        .find(|(fixture, _)| *fixture == name)
        .map(|(_, kinds)| kinds.iter().copied().collect())
        .unwrap_or_default()
}

/// Set `module`'s value for every reported loss to what the text parser
/// rebuilds for it. Test-only: it models "the text grammar dropped exactly
/// these fields", so `erase(canonicalize(m)) == parse(strip_marker(print(m)))`
/// proves the loss list is COMPLETE for `m` (a field the grammar drops
/// without a `TextLoss` arm leaves the two sides unequal).
fn erase_text_losses(module: &mut Module, losses: &[TextLoss]) {
    for loss in losses {
        match loss {
            TextLoss::EnumLayout { enum_id } => {
                for e in module.enums.iter_mut().filter(|e| e.id == *enum_id) {
                    e.layout = None;
                }
            }
            TextLoss::EnumFieldNames { enum_id } => {
                for e in module.enums.iter_mut().filter(|e| e.id == *enum_id) {
                    for v in &mut e.variants {
                        v.field_names.clear();
                    }
                }
            }
            TextLoss::EnumDiscriminantsTail { enum_id } => {
                for e in module.enums.iter_mut().filter(|e| e.id == *enum_id) {
                    while e.discriminants.last().is_some_and(Option::is_none) {
                        e.discriminants.pop();
                    }
                }
            }
            TextLoss::StructFieldNames { struct_id } => {
                for sd in module.structs.iter_mut().filter(|sd| sd.id == *struct_id) {
                    for field in &mut sd.fields {
                        field.name.clear();
                    }
                }
            }
            TextLoss::StructFieldOffsets { struct_id } => {
                for sd in module.structs.iter_mut().filter(|sd| sd.id == *struct_id) {
                    for field in &mut sd.fields {
                        field.offset = None;
                    }
                }
            }
            TextLoss::RecordFieldOffsets { record_id } => {
                for rd in module.records.iter_mut().filter(|rd| rd.id == *record_id) {
                    for field in &mut rd.fields {
                        field.offset = None;
                    }
                }
            }
            TextLoss::GlobalAttrs { global } => {
                let g = &mut module.globals[global.index() as usize];
                g.section = None;
                g.visibility = Default::default();
                g.retained = false;
            }
            TextLoss::GlobalAsm { .. } => module.global_asm.clear(),
            TextLoss::SwitchExhaustive { func, block } => {
                for f in module.functions.iter_mut().filter(|f| f.id == *func) {
                    for b in f.blocks.iter_mut().filter(|b| b.id == *block) {
                        for node in &mut b.body {
                            if let Inst::Switch {
                                exhaustive_enum_unreachable,
                                ..
                            } = &mut node.inst
                            {
                                *exhaustive_enum_unreachable = false;
                            }
                        }
                    }
                }
            }
            TextLoss::ParamAttrsTail { func } => {
                for f in module.functions.iter_mut().filter(|f| f.id == *func) {
                    while f.attrs.params.last().is_some_and(|p| p.is_empty()) {
                        f.attrs.params.pop();
                    }
                }
            }
            // These make the text UNPARSEABLE even without the marker (an
            // unreadable name, or — the proof-surface residue since WS4.4 — a
            // clause sort deeper than the reader's cap behind a
            // `FunctionSummary` / `ClauseBindings` / `SpecCarrier` loss) or
            // renumber references; no corpus fixture carries one, so the
            // complete-loss check has no model. `CertificateAssurance`,
            // `KernelRecheck` and `ObligationKind` are no longer reported.
            other => panic!("erase_text_losses: no parse model for {other:?}"),
        }
    }
}

/// Test-only: drop the `; #lossy:` marker line — what a human editing the
/// text would do. The marker is a tripwire, not integrity (see
/// `trust_ir::text_loss`); this models exactly that edit.
fn strip_lossy_marker(text: &str) -> String {
    text.lines()
        .filter(|line| !line.starts_with("; #lossy:"))
        .map(|line| format!("{line}\n"))
        .collect()
}

/// Canonical text: format, compare, re-parse, re-format.
///
/// Roadmap WS4.2: the text grammar is now TOTAL-OR-REFUSED.
///
/// * A loss-free fixture (`format::canonical_checked` is `Ok`) must round-trip
///   EXACTLY: `parse(canonical(m)) == canonicalize(m)` with NO field
///   normalization — the strongest form of findings A-G, and the evidence
///   that `text_losses` misses nothing on this fixture.
/// * A lossy fixture prints with a `; #lossy:` marker that the parser
///   refuses; its `text_losses` kinds must equal its `TEXT_LOSS_RATCHET` row
///   exactly; and with the marker stripped (test-only), the parsed module
///   equals `canonicalize(m)` with exactly the reported losses erased — so
///   the loss list is COMPLETE, not merely non-empty.
///
/// We compare against `canonicalize(m)` rather than `m` because canonical
/// text renumbers SSA values densely.
fn roundtrip_text(name: &str, module: &Module) -> String {
    let text = trust_ir::format::canonical(module);
    let canon = trust_ir::format::canonicalize(module);
    let losses = trust_ir::format::text_losses(&canon);
    let kinds: BTreeSet<TextLossKind> = losses.iter().map(TextLoss::kind).collect();
    assert_eq!(
        kinds,
        ratchet_row(name),
        "{name}: text_losses kinds differ from its TEXT_LOSS_RATCHET row ({losses:?})"
    );
    match trust_ir::format::canonical_checked(module) {
        Ok(checked) => {
            assert!(losses.is_empty());
            assert_eq!(checked, text, "{name}: canonical_checked != canonical");
            let back = trust_ir::parser::parse_module(&text)
                .unwrap_or_else(|e| panic!("{name}: text parse failed: {e:?}"));
            assert_eq!(
                trust_ir::format::canonical(&back),
                text,
                "{name}: canonical text is not idempotent across a round-trip"
            );
            assert_eq!(
                back, canon,
                "{name}: text round-trip lost module structure although text_losses is empty"
            );
        }
        Err(error) => {
            assert_eq!(error.losses, losses, "{name}: canonical_checked losses");
            assert!(
                text.lines()
                    .nth(1)
                    .is_some_and(|line| line.starts_with("; #lossy: ")),
                "{name}: a lossy canonical text must carry the marker after the header"
            );
            let refusal = trust_ir::parser::parse_module(&text)
                .expect_err("a #lossy canonical text must not parse");
            assert!(
                refusal.message.contains("this text was printed LOSSILY ("),
                "{name}: {refusal}"
            );
            let stripped = strip_lossy_marker(&text);
            let back = trust_ir::parser::parse_module(&stripped)
                .unwrap_or_else(|e| panic!("{name}: marker-stripped text parse failed: {e:?}"));
            let mut expected = canon;
            erase_text_losses(&mut expected, &losses);
            assert_eq!(
                back, expected,
                "{name}: the text grammar drops a field text_losses does not report"
            );
            assert!(
                trust_ir::format::text_losses(&back).is_empty(),
                "{name}: the erased module must itself be loss-free"
            );
        }
    }
    text
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

/// Retained AF control: a quoted generic display path belongs to an ungated
/// body as well as a gated one. Keep the frozen corpus bytes unchanged.
#[test]
fn ungated_generic_display_path_preserves_body_gate_states_across_formats() {
    let mut module = generate::build_body_gate().expect("body-gate fixture");
    let ungated = module
        .functions
        .iter_mut()
        .find(|f| f.name == "ungated_body")
        .expect("ungated fixture body");
    assert_eq!(ungated.body_gate, Some(trust_ir::BodyGate::Ungated));
    ungated.display_path = Some("core::mem::drop::<T>".into());

    let bytes = roundtrip_binary("ungated display path", &module);
    assert_eq!(&bytes[..8], b"TRUST_IR");
    assert_eq!(
        u32::from_le_bytes(bytes[8..12].try_into().unwrap()),
        41,
        "body-gate metadata keeps its minimum lossless format"
    );
    let from_binary = trust_ir::binary::deserialize_module(&bytes).expect("binary round-trip");
    assert_eq!(from_binary, module);

    let text = roundtrip_text("body_gate", &module);
    let from_text = trust_ir::parser::parse_module(&text).expect("text round-trip");
    for (format, decoded) in [("binary", from_binary), ("text", from_text)] {
        for expected in &module.functions {
            let actual = decoded
                .functions
                .iter()
                .find(|f| f.name == expected.name)
                .expect("decoded fixture body");
            assert_eq!(actual.body_gate, expected.body_gate, "{format}");
            assert_eq!(actual.display_path, expected.display_path, "{format}");
        }
    }
    roundtrip_json("ungated display path", &module);
    roundtrip_msgpack("ungated display path", &module);
}

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
        let module = build().expect("the fixture builds");

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

/// Roadmap WS4.2: `TEXT_LOSS_RATCHET` is EXACT over the whole corpus — every
/// row names a real fixture, every fixture's measured loss kinds equal its row
/// (absent = loss-free), and no row is empty. Reports every mismatch at once
/// so a re-measurement is one run.
#[test]
fn text_loss_ratchet_is_exact() {
    let fixtures = corpus();
    let mut mismatches = Vec::new();
    for (name, kinds) in TEXT_LOSS_RATCHET {
        assert!(
            !kinds.is_empty(),
            "{name}: an empty ratchet row must be deleted"
        );
        assert!(
            fixtures.iter().any(|f| f.name == *name),
            "{name}: ratchet row names no corpus fixture"
        );
    }
    for fixture in &fixtures {
        let canon = trust_ir::format::canonicalize(&(fixture.build)().expect("the fixture builds"));
        let measured: BTreeSet<TextLossKind> = trust_ir::format::text_losses(&canon)
            .iter()
            .map(TextLoss::kind)
            .collect();
        let recorded = ratchet_row(fixture.name);
        if measured != recorded {
            mismatches.push(format!(
                "    (\"{}\", &[{}]),  // recorded {recorded:?}",
                fixture.name,
                measured
                    .iter()
                    .map(|k| format!("TextLossKind::{k:?}"))
                    .collect::<Vec<_>>()
                    .join(", ")
            ));
        }
    }
    assert!(
        mismatches.is_empty(),
        "TEXT_LOSS_RATCHET drifted (a row may only SHRINK, in the increment that carries \
         the field):\n{}",
        mismatches.join("\n")
    );
}

/// Roadmap WS4.2 step 5: every entry of the ONE directive vocabulary
/// (`trust_ir::text_directives::TEXT_DIRECTIVES`) round-trips through at least
/// one loss-free corpus golden, so a printer-only directive (one without a
/// parser arm) cannot be added: the golden that spells it would fail to parse
/// in `corpus_roundtrip`, and a directive no golden spells fails here.
#[test]
fn every_text_directive_round_trips_through_the_corpus() {
    use trust_ir::text_directives::{LOSSY, TEXT_DIRECTIVES};
    let dir = fixtures_dir();
    let mut seen = BTreeSet::new();
    for fixture in corpus() {
        let module = (fixture.build)().expect("the fixture builds");
        let Ok(text) = trust_ir::format::canonical_checked(&module) else {
            continue;
        };
        let golden = fs::read_to_string(dir.join(format!("{}.trust_ir", fixture.name)))
            .expect("loss-free fixture has a text golden");
        assert_eq!(golden, text, "{}: golden drift", fixture.name);
        let back = trust_ir::parser::parse_module(&golden).expect("golden parses");
        assert_eq!(back, trust_ir::format::canonicalize(&module));
        for directive in TEXT_DIRECTIVES {
            if golden.contains(&format!("; {directive}")) {
                seen.insert(*directive);
            }
        }
        assert!(!golden.contains(LOSSY), "{}", fixture.name);
    }
    let missing: Vec<_> = TEXT_DIRECTIVES
        .iter()
        .filter(|d| !seen.contains(*d))
        .collect();
    assert!(
        missing.is_empty(),
        "text directives no loss-free corpus golden round-trips: {missing:?}"
    );
}

/// Proof-lineage sidecar corpus. These fixtures deliberately live beside the
/// module fixtures but use standalone `.trust_irpl` binary files rather than the
/// module `.tmbc` codec, so Trust can pin proof persistence without forcing a
/// module binary-format bump.
#[test]
fn proof_lineage_corpus_roundtrip() {
    let dir = fixtures_dir();
    for LineageFixture { name, build } in lineage_corpus() {
        let fixture = build().expect("the fixture builds");
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
fn native_request_type_identity_distinguishes_refinement_from_scalar_boundaries() {
    let mut bundle = generate::build_trust_native_request_bundle()
        .expect("the fixture builds")
        .bundle;
    // Request-only transport needs no claimed certificate authority. Keep the
    // genuinely valid module and exact references, not an oversized/malformed
    // synthetic encoding which public admission would reject independently.
    bundle.evidence_bundles.clear();
    bundle
        .requests
        .retain(|request| matches!(request, NativeVerificationRequest::TrustMc(_)));
    bundle.module.proof_certificates.clear();
    for obligation in &mut bundle.module.proof_obligations {
        obligation.status = ProofStatus::Pending;
    }
    for function in &mut bundle.module.functions {
        function.proofs.clear();
        for block in &mut function.blocks {
            for node in &mut block.body {
                node.proofs.clear();
                node.proof_context = None;
            }
        }
    }
    for node in &mut bundle.lineage.nodes {
        node.certificates.clear();
    }
    bundle.module.types.resize(34, Ty::U8);
    let predicate = bundle
        .module
        .intern_pred(trust_ir::pred::Pred::Interval { lo: 0, hi: 1 })
        .expect("Module::intern_pred: test fixture")
        .expect("closed interval predicate");
    assert_eq!(predicate, trust_ir::PredId::new(0));
    // In compiler-facts v4 both tuples had the SAME ARITY and byte encoding:
    // Tuple(2), 33, 33, 0, 0, 0, 0, 0, 0, 0, 0. The Refine payload in A
    // swallowed Isize and the beginning of Refine in B. Length framing alone
    // did not help; variant tags must be disjoint.
    let a = Ty::Tuple(vec![Ty::Refine(trust_ir::TyId::new(33), predicate), Ty::I8]);
    let b = Ty::Tuple(vec![
        Ty::Isize,
        Ty::Refine(trust_ir::TyId::new(0), predicate),
    ]);
    bundle.module.types.extend([a.clone(), b.clone()]);
    let digest = bundle.module.stable_digest();
    bundle.trust_ir_module_digest = digest;
    for node in &mut bundle.lineage.nodes {
        if bundle.lineage.roots.contains(&node.id) {
            node.target_module = digest;
        }
    }
    let errors = trust_ir_build::validate_module(&bundle.module);
    assert!(errors.is_empty(), "valid collision fixture: {errors:?}");
    bundle.compiler_facts.monomorphizations[0].generic_args =
        vec![trust_ir::NativeGenericArg::Ty(a)];
    bundle.validate().expect("valid A bundle");
    let facts_a = bundle.compiler_facts.stable_digest();
    let digest_a = bundle.stable_digest();
    let transport_a = bundle.transport_identity();
    // Exercise the real post-mint mutation detector on the same live owner.
    // This test calls the TCB issuer deliberately; it does not claim source
    // generation correctness or demonstrate a forged kernel proof.
    let authority = trust_ir::SourceGenerationAuthority::mint_from_live_lowering(&mut bundle)
        .expect("mint once for valid fixture");
    assert!(authority.authorizes_bundle(&bundle));
    bundle.compiler_facts.monomorphizations[0].generic_args =
        vec![trust_ir::NativeGenericArg::Ty(b)];
    bundle.validate().expect("valid B bundle");
    assert_ne!(facts_a, bundle.compiler_facts.stable_digest());
    assert_ne!(digest_a, bundle.stable_digest());
    assert_ne!(transport_a, bundle.transport_identity());
    assert!(!authority.authorizes_bundle(&bundle));
}

#[test]
fn native_request_bundle_corpus_roundtrip() {
    let dir = fixtures_dir();
    for NativeBundleFixture { name, build } in native_bundle_corpus() {
        let fixture = build().expect("the fixture builds");
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
    let fixtures = generate::build_vector_mask_oracles().expect("the fixture builds");
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

/// The `certificate_binding` fixture validates cleanly on every layer — the bound
/// and evidence policies included, so every binding digest the validator
/// re-derives (environment, statement, callees) and every license evidence it
/// carries matches what the validator computes; `origin_module` and `source`
/// are CARRIED (the first is authenticated only on the linked walk, the second
/// is checked only against an island, which this fixture has none of) — and
/// selects exactly
/// `CERTIFICATE_BINDING_FORMAT_VERSION`, and the two carriers are the only reason:
/// the same module with every binding stripped (lineages re-keyed to the
/// unbound v8 form) and every license's evidence dropped is written below
/// that version.
#[test]
fn certificate_binding_fixture_validates_under_every_policy_and_is_the_only_reason_for_its_version()
{
    use trust_ir::binary::CERTIFICATE_BINDING_FORMAT_VERSION;
    use trust_ir::proof::{ProofEvidence, clean_cic_lineage_digest_v8, module_symbol_resolver};
    use trust_ir_build::{ValidationConfig, validate_module_with_config};

    let module = generate::build_certificate_binding().expect("the fixture builds");
    assert_eq!(trust_ir_build::validate_module(&module), vec![]);
    assert_eq!(trust_ir_build::validate_module_for_codegen(&module), vec![]);
    let strict = ValidationConfig::pinned()
        .with_codegen(true)
        .with_bound_certificates(true)
        .with_gate_evidence(true);
    assert_eq!(
        validate_module_with_config(&module, &strict).into_errors(),
        vec![]
    );
    let bytes =
        trust_ir::binary::serialize_module(&module).expect("serialize_module: test fixture");
    assert_eq!(
        u32::from_le_bytes(bytes[8..12].try_into().unwrap()),
        CERTIFICATE_BINDING_FORMAT_VERSION
    );

    let mut stripped = module.clone();
    let obligations = stripped.proof_obligations.clone();
    let resolver_module = stripped.clone();
    let resolve = module_symbol_resolver(&resolver_module);
    for certificate in &mut stripped.proof_certificates {
        if let ProofEvidence::CleanCic {
            lineage,
            kernel_recheck: Some(recheck),
            ..
        } = &mut certificate.evidence
        {
            recheck.binding = None;
            let obligation = obligations
                .iter()
                .find(|o| o.id == certificate.obligation)
                .expect("scoped");
            *lineage = clean_cic_lineage_digest_v8(obligation, &resolve, None).expect("keyed");
        }
    }
    for function in &mut stripped.functions {
        if let Some(trust_ir::BodyGate::Gated { evidence, .. }) = &mut function.body_gate {
            *evidence = None;
        }
    }
    assert_eq!(trust_ir_build::validate_module(&stripped), vec![]);
    let bytes =
        trust_ir::binary::serialize_module(&stripped).expect("serialize_module: test fixture");
    assert!(
        u32::from_le_bytes(bytes[8..12].try_into().unwrap()) < CERTIFICATE_BINDING_FORMAT_VERSION
    );
}

/// Regenerate this environment-bound positive alone with
/// `TRUST_IR_UPDATE_FIXTURES=1 ... certificate_binding_goldens_replay`.
/// The ordinary run compares the canonical bytes and replays the stored
/// certificates, so changing Clean cannot silently leave downstream goldens
/// bound to an environment the current validator no longer recognizes.
#[test]
fn certificate_binding_goldens_replay() {
    use trust_ir_build::{ValidationConfig, validate_module_with_config};

    let name = "certificate_binding";
    let module = generate::build_certificate_binding().expect("the fixture builds");
    let dir = fixtures_dir();
    assert_or_update_bytes(
        &dir.join(format!("{name}.tmbc")),
        &roundtrip_binary(name, &module),
    );
    assert_or_update_text(
        &dir.join(format!("{name}.trust_ir")),
        &roundtrip_text(name, &module),
    );
    assert_or_update_text(
        &dir.join(format!("{name}.json")),
        &roundtrip_json(name, &module),
    );
    assert_or_update_bytes(
        &dir.join(format!("{name}.msgpack")),
        &roundtrip_msgpack(name, &module),
    );

    let strict = ValidationConfig::pinned()
        .with_codegen(true)
        .with_bound_certificates(true)
        .with_gate_evidence(true);
    let binary = trust_ir::binary::deserialize_module(
        &fs::read(dir.join(format!("{name}.tmbc"))).expect("binary golden"),
    )
    .expect("binary golden decodes");
    let json = serde_json::from_slice::<Module>(
        &fs::read(dir.join(format!("{name}.json"))).expect("JSON golden"),
    )
    .expect("JSON golden decodes");
    let msgpack = rmp_serde::from_slice::<Module>(
        &fs::read(dir.join(format!("{name}.msgpack"))).expect("MessagePack golden"),
    )
    .expect("MessagePack golden decodes");
    let text = trust_ir::parser::parse_module(
        &fs::read_to_string(dir.join(format!("{name}.trust_ir"))).expect("text golden"),
    )
    .expect("text golden decodes without discarding proof fields");
    for (format, stored) in [
        ("binary", binary),
        ("JSON", json),
        ("MessagePack", msgpack),
        ("text", text),
    ] {
        let report = validate_module_with_config(&stored, &strict);
        assert!(report.is_ok(), "{format}: {:?}", report.errors());
        assert_eq!(
            report.replayed_certificate_refs().map(BTreeSet::len),
            Some(2),
            "{format}: both stored TV certificates must be kernel-replayed"
        );
    }
}

/// The v46 `spec_carrier` fixture validates cleanly (the S4 rules and the
/// obligation `spec` backref both pass on it), selects exactly v46, and every
/// one of its carrier features is the reason: stripping all of them drops the
/// header back below 46.
#[test]
fn spec_carrier_fixture_validates_and_is_the_only_reason_for_v46() {
    let module = generate::build_spec_carrier().expect("the fixture builds");
    let errors = trust_ir_build::validate_module(&module);
    assert!(
        errors.is_empty(),
        "spec_carrier fixture must validate cleanly: {errors:?}"
    );
    let bytes =
        trust_ir::binary::serialize_module(&module).expect("serialize_module: test fixture");
    assert_eq!(u32::from_le_bytes(bytes[8..12].try_into().unwrap()), 46);

    let mut stripped = module;
    for machine in &mut stripped.spec_modules {
        for v in &mut machine.vars {
            v.sort = None;
        }
        for inv in &mut machine.invariants {
            inv.typed = None;
        }
        machine.temporal.clear();
        for proof in &mut machine.proofs {
            proof.kind = trust_ir::ProofKind::Kani;
        }
    }
    for obligation in &mut stripped.proof_obligations {
        obligation.spec = None;
        if let Some(formula) = &mut obligation.formula {
            formula.bindings.clear();
        }
    }
    let bytes =
        trust_ir::binary::serialize_module(&stripped).expect("serialize_module: test fixture");
    assert!(u32::from_le_bytes(bytes[8..12].try_into().unwrap()) < 46);
}

/// Roadmap DG-63 (wire v62): the `param_pointee_place` golden decodes at
/// exactly the pointee-place version, is refused one version down (clause-
/// place tag 10 is read-gated), validates cleanly, spells the place
/// `pointee_entry(N)` in text, and the place is the ONLY reason for its
/// version: re-binding every entry pointee as the parameter itself drops the
/// header below 62.
#[test]
fn param_pointee_place_golden_is_read_gated_valid_and_the_only_reason_for_its_version() {
    use trust_ir::binary::{BinaryError, PARAM_POINTEE_PLACE_FORMAT_VERSION};
    use trust_ir::proof::ClausePlace;

    let bytes = fs::read(fixtures_dir().join("param_pointee_place.tmbc")).expect("golden present");
    let (module, version) =
        trust_ir::binary::deserialize_module_with_wire_version(&bytes).expect("decodes");
    assert_eq!(version.get(), PARAM_POINTEE_PLACE_FORMAT_VERSION);
    assert_eq!(
        module,
        generate::build_param_pointee_place().expect("param_pointee_place builds")
    );
    let mut forged = bytes.clone();
    forged[8..12].copy_from_slice(&(PARAM_POINTEE_PLACE_FORMAT_VERSION - 1).to_le_bytes());
    assert_eq!(
        trust_ir::binary::deserialize_module(&forged),
        Err(BinaryError::InvalidTag(10))
    );
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "{errors:?}");
    let text = fs::read_to_string(fixtures_dir().join("param_pointee_place.trust_ir"))
        .expect("text golden present");
    assert!(text.contains("pointee_entry(0)") && text.contains("pointee_entry(1)"));

    let mut stripped = module;
    let rebind = |formula: &mut trust_ir::proof::ProofFormula| {
        for (_, binding) in &mut formula.bindings {
            if let ClausePlace::ParamPointeeEntry { index } = binding.place {
                binding.place = ClausePlace::Param { index };
            }
        }
    };
    for function in &mut stripped.functions {
        if let Some(summary) = &mut function.summary {
            summary.requires.iter_mut().for_each(rebind);
            summary.ensures.iter_mut().for_each(rebind);
        }
    }
    for obligation in &mut stripped.proof_obligations {
        if let Some(formula) = &mut obligation.formula {
            rebind(formula);
        }
    }
    let bytes =
        trust_ir::binary::serialize_module(&stripped).expect("serialize_module: test fixture");
    assert!(
        u32::from_le_bytes(bytes[8..12].try_into().unwrap()) < PARAM_POINTEE_PLACE_FORMAT_VERSION
    );
}

/// The v59 `effect_summaries` fixture validates cleanly (every body honours
/// its effect summary), selects exactly the effect-summary version, and the
/// effect summaries and world epochs are the only reason: stripping both drops
/// the header below it.
#[test]
fn effect_summaries_fixture_validates_and_is_the_only_reason_for_its_version() {
    let module = generate::build_effect_summaries().expect("the fixture builds");
    let errors = trust_ir_build::validate_module(&module);
    assert!(
        errors.is_empty(),
        "effect_summaries fixture must validate cleanly: {errors:?}"
    );
    let version = |m: &trust_ir::Module| {
        let bytes = trust_ir::binary::serialize_module(m).expect("serialize_module: test fixture");
        u32::from_le_bytes(bytes[8..12].try_into().unwrap())
    };
    assert_eq!(
        version(&module),
        trust_ir::binary::EFFECT_SUMMARY_FORMAT_VERSION
    );
    let mut stripped = module;
    for function in &mut stripped.functions {
        if let Some(summary) = &mut function.summary {
            summary.effects = None;
            for clause in &mut summary.ensures {
                clause.bindings.clear();
            }
        }
    }
    assert!(version(&stripped) < trust_ir::binary::EFFECT_SUMMARY_FORMAT_VERSION);
}

/// Execute the `inst_vector_crosslane` fixture through the reference
/// interpreter and pin concrete lane-level results for `reduce` / `shuffle` /
/// `fma`. This is the executable counterpart to the byte-golden round-trip
/// above: it proves the wire form the corpus pins is also the form the
/// reference semantics evaluate.
#[test]
fn vector_crosslane_fixture_executes_with_concrete_lane_results() {
    let module = generate::build_inst_vector_crosslane().expect("the fixture builds");
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
            kind: InterpretValueKind::Vector(lanes.into()),
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

    let fixtures = generate::build_vector_mask_oracles().expect("the fixture builds");
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

    let module = generate::build_inst_vector_dialect().expect("the fixture builds");
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
    let module = generate::build_inst_vector_dialect().expect("the fixture builds");
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
    let mut malformed = generate::build_inst_vector_dialect().expect("the fixture builds");
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

    let bytes =
        trust_ir::binary::serialize_module(&malformed).expect("serialize_module: test fixture");
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

    let mut misspelled_op = generate::build_inst_vector_dialect().expect("the fixture builds");
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

    let mut invalid_lane = generate::build_inst_vector_dialect().expect("the fixture builds");
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

    let mut wrong_operand_shape =
        generate::build_inst_vector_dialect().expect("the fixture builds");
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

    let mut wrong_result_shape = generate::build_inst_vector_dialect().expect("the fixture builds");
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

    let mut missing_attr = generate::build_inst_vector_dialect().expect("the fixture builds");
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

    let mut malformed_vector_ty =
        generate::build_inst_vector_dialect().expect("the fixture builds");
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

    let mut malformed_attr = generate::build_inst_vector_dialect().expect("the fixture builds");
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

    let mut malformed_mask_ty = generate::build_inst_vector_dialect().expect("the fixture builds");
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

    let mut malformed_bit_order =
        generate::build_inst_vector_dialect().expect("the fixture builds");
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

    let mut non_bool_mask = generate::build_inst_vector_dialect().expect("the fixture builds");
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
    let fixture = generate::build_trust_native_request_bundle().expect("the fixture builds");
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
    let mut bundle = generate::build_trust_native_request_bundle()
        .expect("the fixture builds")
        .bundle;
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
    let mut bundle = generate::build_trust_native_request_bundle()
        .expect("the fixture builds")
        .bundle;
    let pending_cert = ProofCertificate {
        obligation: ProofId::new(1),
        prover: "trust_vc".to_string(),
        evidence: ProofEvidence::LeanProof("exact stale_pending_certificate".to_string()),
        assurance: None,
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
    let mut bundle = generate::build_trust_native_request_bundle()
        .expect("the fixture builds")
        .bundle;
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
    let mut bundle = generate::build_trust_native_request_bundle()
        .expect("the fixture builds")
        .bundle;
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
    let mut bundle = generate::build_trust_native_request_bundle()
        .expect("the fixture builds")
        .bundle;
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
    let mut bundle = generate::build_trust_native_request_bundle()
        .expect("the fixture builds")
        .bundle;
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
    let mut bundle = generate::build_trust_native_request_bundle()
        .expect("the fixture builds")
        .bundle;
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
    let mut bundle = generate::build_trust_native_request_bundle()
        .expect("the fixture builds")
        .bundle;
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
    let mut bundle = generate::build_trust_native_request_bundle()
        .expect("the fixture builds")
        .bundle;
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
    let mut bundle = generate::build_trust_native_request_bundle()
        .expect("the fixture builds")
        .bundle;
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
    let mut bundle = generate::build_trust_native_request_bundle()
        .expect("the fixture builds")
        .bundle;
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
    let mut bundle = generate::build_trust_native_request_bundle()
        .expect("the fixture builds")
        .bundle;
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
    let mut bundle = generate::build_trust_native_request_bundle()
        .expect("the fixture builds")
        .bundle;
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
    let mut bundle = generate::build_trust_native_request_bundle()
        .expect("the fixture builds")
        .bundle;
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
    let mut bundle = generate::build_trust_native_request_bundle()
        .expect("the fixture builds")
        .bundle;
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
    let mut bundle = generate::build_trust_native_request_bundle()
        .expect("the fixture builds")
        .bundle;
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
    let mut bundle = generate::build_trust_native_request_bundle()
        .expect("the fixture builds")
        .bundle;
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
    let mut bundle = generate::build_trust_native_request_bundle()
        .expect("the fixture builds")
        .bundle;
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
    let mut bundle = generate::build_trust_native_request_bundle()
        .expect("the fixture builds")
        .bundle;
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
    let mut bundle = generate::build_trust_native_request_bundle()
        .expect("the fixture builds")
        .bundle;
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
    let mut bundle = generate::build_trust_native_request_bundle()
        .expect("the fixture builds")
        .bundle;
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
    let mut bundle = generate::build_trust_native_request_bundle()
        .expect("the fixture builds")
        .bundle;
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
    let mut bundle = generate::build_trust_native_request_bundle()
        .expect("the fixture builds")
        .bundle;
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
    let mut bundle = generate::build_trust_native_request_bundle()
        .expect("the fixture builds")
        .bundle;
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
    let mut bundle = generate::build_trust_native_request_bundle()
        .expect("the fixture builds")
        .bundle;
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
    let mut bundle = generate::build_trust_native_request_bundle()
        .expect("the fixture builds")
        .bundle;
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

    let mut bundle = generate::build_trust_native_request_bundle()
        .expect("the fixture builds")
        .bundle;
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
        let mut bundle = generate::build_trust_native_request_bundle()
            .expect("the fixture builds")
            .bundle;
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

    let mut bundle = generate::build_trust_native_request_bundle()
        .expect("the fixture builds")
        .bundle;
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
        let m = build().expect("the fixture builds");
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
    // v39/v43: Dialect and Handle are covered by the ty_dialect_v39 and
    // ty_handle fixtures (the only goldens at headers 39 and 43).
    // v51: `Inst::MakeAggregate` (WS3.5) and the WS3.20 `MemCopy` / `MemSet`
    // were absent from `required_inst` until the INST wire batch gave them
    // binary tags (the writer panicked on them); the `inst_wire_batch` golden
    // carries all three since.
    let required_ty = [
        "I8", "I16", "I32", "I64", "I128", "U8", "U16", "U32", "U64", "U128", "F16", "F32", "F64",
        "Bool", "Ptr", "FatPtr", "Unit", "Never", "Array", "Tuple", "Struct", "Enum", "Func",
        "Sequence", "Set", "Record", "Closure", "Ref", "RefMut", "PtrConst", "PtrMut", "Rc",
        "Vector", "Isize", "Usize", "Char", "Dialect", "Handle",
        // The tensor region: carried by the `tensor_contract` golden.
        "Tensor",
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
        "CallCannotUnwind",
        "CallIndirectCannotUnwind",
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
        // v50: carried by the `array_splat` golden.
        "ArraySplat",
        // v63: runtime capture construction, not a static closure constant.
        "MakeClosure",
        // v74: carried by the `box_deref` golden.
        "BoxDeref",
        // v51: carried by the `inst_wire_batch` golden.
        "MakeAggregate",
        "MemCopy",
        "MemSet",
        // v54 (amendment P): carried by the `assert_invoke` golden.
        "AssertInvoke",
        // v55 (amendment D): carried by the `drop_glue` golden.
        "Drop",
        "DropInvoke",
        // v56 (amendment D, Part 2): carried by the `unwind_twins` golden.
        "InvokeIndirect",
        // The tensor region: carried by the `tensor_contract` golden.
        "TensorContract",
        // Its map, reduce and view: carried by the `tensor_map_reduce_view`
        // golden.
        "TensorMap",
        "TensorReduce",
        "TensorView",
        // Its gather and scatter: carried by the `tensor_gather_scatter`
        // golden.
        "TensorGather",
        "TensorScatter",
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
    use trust_ir::ty::TyG::*;
    match ty {
        Dialect(_) => {
            out.insert("Dialect");
        }
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
        FnItem(_) => {
            out.insert("FnItem");
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
        // v43 nominal opaque runtime handle: the pair is the whole identity.
        Handle(_) => {
            out.insert("Handle");
        }
        Storage(_) => {
            out.insert("Storage");
        }
        // PKG-U13a: the element is an inline child, as a vector's lane is.
        Tensor(elem, _) => {
            out.insert("Tensor");
            tag_ty(elem, out);
        }
        Ty::Ext(e) => e.unreachable(),
    }
}

fn tag_inst(inst: &trust_ir::inst::Inst, out: &mut std::collections::HashSet<&'static str>) {
    use trust_ir::inst::InstG::*;
    let tag = match inst {
        // Crystal lane (wave-DS): outside the lowering-target subset.
        Drop { .. } => "Drop",
        // Amendment D (wire v55): the unwinding twin of a drop.
        DropInvoke { .. } => "DropInvoke",
        // Amendment D, Part 2 (wire v56): the unwinding twin of an indirect
        // call, carried by the `unwind_twins` golden.
        InvokeIndirect { .. } => "InvokeIndirect",
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
        CallCannotUnwind { .. } => "CallCannotUnwind",
        CallIndirectCannotUnwind { .. } => "CallIndirectCannotUnwind",
        ExtractField { .. } => "ExtractField",
        InsertField { .. } => "InsertField",
        MakeAggregate { .. } => "MakeAggregate",
        ArraySplat { .. } => "ArraySplat",
        MakeClosure { .. } => "MakeClosure",
        // The tensor region (wire v67): carried by the `tensor_contract`
        // golden.
        TensorContract { .. } => "TensorContract",
        // The tensor region's map, reduce and view (wire v68): carried by
        // the `tensor_map_reduce_view` golden.
        TensorMap { .. } => "TensorMap",
        TensorReduce { .. } => "TensorReduce",
        TensorView { .. } => "TensorView",
        // The tensor region's gather and scatter (wire v69): carried by the
        // `tensor_gather_scatter` golden.
        TensorGather { .. } => "TensorGather",
        TensorScatter { .. } => "TensorScatter",
        // Box dereference validity facts (wire v74): carried by the
        // `box_deref` golden.
        BoxDeref { .. } => "BoxDeref",
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
        // Amendment P (wire v54): carried by the `assert_invoke` golden.
        AssertInvoke { .. } => "AssertInvoke",
        // WS3.20 (F-057): in `required_inst` since the v51 INST wire batch,
        // carried by the `inst_wire_batch` golden.
        MemCopy { .. } => "MemCopy",
        MemSet { .. } => "MemSet",
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
    use trust_ir::inst::InstG::*;
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
        | LoadSlot { ty, .. }
        | TensorContract { ty, .. }
        | TensorMap { ty, .. }
        | TensorReduce { ty, .. }
        | TensorView { ty, .. }
        | TensorGather { ty, .. }
        | TensorScatter { ty, .. } => tag_ty(ty, out),
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

/// Legacy roster names whose live corpus fixture has since been RENAMED to a
/// feature name (`wire-allocations.toml`: names, not numbers). The roster
/// (`v41-reader-compat/module-names.txt`) and the files beside it are a frozen
/// snapshot with recorded SHA-256s (`ORIGIN.json`), so they keep their
/// historical spelling and the mapping lives here.
const LEGACY_ROSTER_RENAMES: &[(&str, &str)] = &[("body_gate_v41", "body_gate")];

/// Goldens in `tests/fixtures/` that a dedicated test owns, not a corpus row.
const STANDALONE_GOLDENS: &[(&str, &[&str])] = &[("vector_mask_oracles", &["json"])];

/// THE CORPUS CENSUS — deliberately WITHOUT a count.
///
/// This used to be `assert_eq!(fixtures.len(), names.len() + 3)` inside the
/// v41 legacy-roster test below: a single line that EVERY new golden had to
/// edit, so any two lines of work that each added a fixture conflicted
/// textually on it (measured: `+ 1` -> `+ 3` was a forced hand-merge in
/// 01349fd). What the count was FOR is kept, per fixture instead of in one
/// shared number:
///
///   * corpus names are unique, so the roster lookup below cannot be shadowed
///     by a second fixture reusing a legacy name;
///   * every registered fixture has exactly its goldens on disk; and
///   * every golden on disk belongs to a registered fixture — so a fixture
///     cannot silently drop out of the corpus while its goldens stay behind,
///     and a stray golden cannot sit unchecked.
///
/// WHAT THE COUNT CAUGHT AND THIS DOES NOT: a SYMMETRIC removal — a fixture's
/// `corpus()` row and its golden files deleted in the same commit. Both sides
/// of every assertion below lose the name together, so the corpus can shrink
/// with this test green. (The old count's comment named that purpose: "raise
/// it when a fixture is added, never to paper over a removal".) Nothing
/// mechanical replaces it: a count is exactly the shared line this census
/// exists to remove. Deleting four goldens is a visible diff, and review owns
/// it; the v41 roster below and `coverage()` catch the removals that would
/// drop a frozen name or the sole cover of a variant.
///
/// Two parallel additions touch disjoint files and disjoint corpus rows.
#[test]
fn every_golden_on_disk_is_registered_and_every_registration_has_its_goldens() {
    use std::collections::{BTreeMap, BTreeSet};

    let mut registered: BTreeMap<String, BTreeSet<&str>> = BTreeMap::new();
    let mut register = |name: &str, extensions: &[&'static str]| {
        let fresh = registered
            .insert(name.to_owned(), extensions.iter().copied().collect())
            .is_none();
        assert!(fresh, "fixture name `{name}` is registered twice");
    };
    for fixture in corpus() {
        if fixture.text_supported {
            register(fixture.name, &["json", "msgpack", "tmbc", "trust_ir"]);
        } else {
            register(fixture.name, &["json", "msgpack", "tmbc"]);
        }
    }
    for fixture in lineage_corpus() {
        register(fixture.name, &["json", "msgpack", "trust_irpl"]);
    }
    for fixture in native_bundle_corpus() {
        register(fixture.name, &["json", "msgpack"]);
    }
    for (name, extensions) in STANDALONE_GOLDENS {
        register(name, extensions);
    }

    let mut on_disk: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for entry in fs::read_dir(fixtures_dir()).expect("read fixtures dir") {
        let path = entry.expect("fixture entry").path();
        if path.is_dir() {
            continue; // `compat/` and `v41-reader-compat/` are pinned history
        }
        let stem = path
            .file_stem()
            .expect("stem")
            .to_string_lossy()
            .into_owned();
        let extension = path
            .extension()
            .expect("every golden has an extension")
            .to_string_lossy()
            .into_owned();
        on_disk.entry(stem).or_default().insert(extension);
    }

    for (name, extensions) in &registered {
        let found = on_disk.get(name).cloned().unwrap_or_default();
        let expected: BTreeSet<String> = extensions.iter().map(|e| (*e).to_owned()).collect();
        assert_eq!(
            found, expected,
            "fixture `{name}`: goldens on disk do not match its registration"
        );
    }
    for stem in on_disk.keys() {
        assert!(
            registered.contains_key(stem),
            "golden `{stem}.*` is on disk but no corpus row registers it — a fixture was \
             removed from the corpus without its goldens, or a golden was added unregistered"
        );
    }
}

/// Public v41 serde inputs keep their exact meanings after the trailing field
/// moves. This fixed historical roster is checked alongside the entire current
/// corpus; no legacy row is replaced by a post-v41 fixture.
///
/// A legacy row going missing fails at the `expect` below. There is
/// deliberately NO corpus-size count here any more — see
/// `every_golden_on_disk_is_registered_and_every_registration_has_its_goldens`
/// for what it guarded and why a shared number was the wrong place for it.
#[test]
fn published_v41_module_serde_inputs_keep_their_meanings() {
    let names: Vec<_> = include_str!("fixtures/v41-reader-compat/module-names.txt")
        .lines()
        .collect();
    assert_eq!(names.len(), 30);
    let fixtures = corpus();
    let dir = fixtures_dir().join("v41-reader-compat");
    for name in names {
        // The roster keeps its frozen spelling; the live fixture may have
        // been renamed to a feature name.
        let live = LEGACY_ROSTER_RENAMES
            .iter()
            .find(|(legacy, _)| *legacy == name)
            .map_or(name, |(_, renamed)| *renamed);
        let fixture = fixtures
            .iter()
            .find(|fixture| fixture.name == live)
            .expect("legacy fixture removed");
        let expected = (fixture.build)().expect("the fixture builds");
        let json = fs::read(dir.join(format!("{name}.json"))).unwrap();
        let msgpack = fs::read(dir.join(format!("{name}.msgpack"))).unwrap();
        assert_eq!(
            serde_json::from_slice::<Module>(&json).unwrap(),
            expected,
            "legacy JSON {name}"
        );
        assert_eq!(
            rmp_serde::from_slice::<Module>(&msgpack).unwrap(),
            expected,
            "legacy MessagePack {name}"
        );
    }
}

/// The published v41 bundle was minted when `Module::stable_digest` was the
/// V2 identity and the bundle schema was 7. WS4.10 made the digest the
/// portable V3 identity; WS4.16 (F-080) made the bundle STATE its language
/// set at schema 8; concrete THIR input advanced the schema to 9. The RustMir
/// bundle the generator mints today differs from the
/// published one in EXACTLY this ledger, and nothing else:
///
/// 1. the module digest (`trust_ir_module_digest`, the lineage node's
///    `target_module`, every evidence bundle's copy), V2 there and V3 here;
/// 2. `schema_version` and `serialization.schema_version`, 7 there, 9 here;
/// 3. `provenance.source_languages`, ABSENT there (which decodes to the
///    empty set — never a wildcard) and `{Rust}` here;
/// 4. the fixture function's v23 producer stamp, `null` there (the golden
///    predates the stamp) and `TRust` here — what the shipping tRust
///    producer stamps, and what lets `{Rust}` cover the module at all.
///
/// Everything else keeps its meaning byte for byte; the legacy bundle still
/// decodes, its digest is its OWN module's V2 identity (so it is the same
/// bundle, re-minted), and validation refuses it closed on every one of the
/// four rows above — the V2 digest, the schema, and the empty language set —
/// rather than admitting a v7 bundle as the current schema.
#[test]
fn published_v41_native_bundle_serde_inputs_keep_their_meanings() {
    assert_eq!(NativeVerificationBundle::SCHEMA_VERSION, 9);
    let dir = fixtures_dir().join("v41-reader-compat");
    let expected = generate::build_trust_native_request_bundle()
        .expect("the fixture builds")
        .bundle;
    expected
        .validate()
        .expect("current schema9 producer positive");
    let json = fs::read(dir.join("native_request_trust_bundle.json")).unwrap();
    let msgpack = fs::read(dir.join("native_request_trust_bundle.msgpack")).unwrap();
    let from_json = serde_json::from_slice::<NativeVerificationBundle>(&json).unwrap();
    let from_msgpack = rmp_serde::from_slice::<NativeVerificationBundle>(&msgpack).unwrap();
    assert_eq!(from_json, from_msgpack);

    // Row 1: the published digest is the V2 identity of the module it
    // carries (which is today's module minus row 4's stamp).
    let v2 = from_json
        .module
        .stable_digest_under(trust_ir::IdentityScheme::V2);
    let v3 = expected.module.stable_digest();
    assert_eq!(expected.trust_ir_module_digest, v3);
    assert_eq!(from_json.trust_ir_module_digest, v2, "minted under V2");
    // Rows 2-4 as published.
    assert_eq!(from_json.schema_version, 7);
    assert_eq!(from_json.serialization.schema_version, 7);
    assert!(from_json.provenance.source_languages.is_empty());
    assert_eq!(from_json.module.functions.len(), 1);
    assert_eq!(from_json.module.functions[0].producer, None);
    assert_eq!(
        expected.module.functions[0].producer,
        Some(trust_ir::Producer::TRust)
    );

    // Re-mint the published bundle at today's schema: substitute exactly the
    // four rows of the ledger.
    fn swap(value: &mut serde_json::Value, from: &serde_json::Value, to: &serde_json::Value) {
        if value == from {
            *value = to.clone();
            return;
        }
        match value {
            serde_json::Value::Array(items) => items.iter_mut().for_each(|v| swap(v, from, to)),
            serde_json::Value::Object(map) => map.values_mut().for_each(|v| swap(v, from, to)),
            _ => {}
        }
    }
    let mut legacy = serde_json::to_value(&from_json).unwrap();
    swap(
        &mut legacy,
        &serde_json::to_value(v2).unwrap(),
        &serde_json::to_value(v3).unwrap(),
    );
    legacy["schema_version"] = serde_json::json!(NativeVerificationBundle::SCHEMA_VERSION);
    legacy["serialization"]["schema_version"] =
        serde_json::json!(NativeVerificationBundle::SCHEMA_VERSION);
    legacy["provenance"]["source_languages"] = serde_json::json!(["Rust"]);
    legacy["module"]["functions"][0]["producer"] = serde_json::json!("Trust");
    assert_eq!(
        serde_json::from_value::<NativeVerificationBundle>(legacy).unwrap(),
        expected,
        "the published bundle differs from today's in the four ledger rows ONLY"
    );
    let refused = from_json
        .validate()
        .expect_err("a V2-minted, schema-7 bundle is refused");
    for expected_refusal in [
        // row 1
        |e: &trust_ir::NativeVerificationBundleError| {
            matches!(
                e,
                trust_ir::NativeVerificationBundleError::TrustIrModuleDigestMismatch { .. }
            )
        },
        // row 2
        |e: &trust_ir::NativeVerificationBundleError| {
            *e == trust_ir::NativeVerificationBundleError::UnsupportedSchemaVersion(7)
        },
        // rows 3 + 4: the empty set covers neither the primary nor the
        // unstamped function
        |e: &trust_ir::NativeVerificationBundleError| {
            matches!(
                e,
                trust_ir::NativeVerificationBundleError::BundlePrimaryLanguageUncovered { .. }
            )
        },
        |e: &trust_ir::NativeVerificationBundleError| {
            matches!(
                e,
                trust_ir::NativeVerificationBundleError::BundleLanguageUncovered {
                    producer: None,
                    ..
                }
            )
        },
    ] {
        assert!(refused.iter().any(expected_refusal), "{refused:?}");
    }
}

/// Preserve the complete former current-schema8 population beside the current
/// producer positive. Decoding preserves old metadata; admission refuses it.
#[test]
fn pre_thir_schema8_native_bundle_keeps_every_field_and_refuses_admission() {
    assert_eq!(NativeVerificationBundle::SCHEMA_VERSION, 9);
    let expected = generate::build_trust_native_request_bundle()
        .expect("the original RustMir fixture builds")
        .bundle;
    expected
        .validate()
        .expect("current schema9 producer positive");
    let current_json =
        serde_json::from_slice::<NativeVerificationBundle>(&serde_json::to_vec(&expected).unwrap())
            .unwrap();
    let current_msgpack = rmp_serde::from_slice::<NativeVerificationBundle>(
        &rmp_serde::to_vec_named(&expected).unwrap(),
    )
    .unwrap();
    for current in [&current_json, &current_msgpack] {
        assert_eq!(current, &expected);
        current.validate().expect("current reader positive");
    }

    let dir = fixtures_dir().join("compat");
    let json = fs::read(dir.join("pre_thir_native_request_trust_bundle.json")).unwrap();
    let msgpack = fs::read(dir.join("pre_thir_native_request_trust_bundle.msgpack")).unwrap();
    let from_json = serde_json::from_slice::<NativeVerificationBundle>(&json).unwrap();
    let from_msgpack = rmp_serde::from_slice::<NativeVerificationBundle>(&msgpack).unwrap();
    assert_eq!(from_json, from_msgpack);
    let mut historical_expected = expected.clone();
    historical_expected.schema_version = 8;
    historical_expected.serialization.schema_version = 8;
    assert_eq!(
        from_json, historical_expected,
        "only the two schema fields change"
    );
    for old in [&from_json, &from_msgpack] {
        let refused = old
            .validate()
            .expect_err("schema8 admission remains unsupported");
        assert!(
            refused.contains(&trust_ir::NativeVerificationBundleError::UnsupportedSchemaVersion(8))
        );
        assert!(refused.contains(
            &trust_ir::NativeVerificationBundleError::UnsupportedSerializationSchemaVersion(8)
        ));
    }
}

/// v51: the `inst_wire_batch` golden decodes at exactly the INST wire batch
/// version, is refused under any older header (every one of its tags is
/// read-gated), validates, and its bit and copySign bodies compute what Rust's
/// own intrinsics compute.
#[test]
fn inst_wire_batch_golden_is_read_gated_valid_and_executes() {
    let bytes = fs::read(fixtures_dir().join("inst_wire_batch.tmbc")).expect("golden present");
    let (module, version) =
        trust_ir::binary::deserialize_module_with_wire_version(&bytes).expect("decodes");
    assert_eq!(
        version.get(),
        trust_ir::binary::INST_WIRE_BATCH_FORMAT_VERSION
    );
    assert_eq!(
        module,
        generate::build_inst_wire_batch().expect("the fixture builds")
    );
    for older in [
        trust_ir::binary::INST_WIRE_BATCH_FORMAT_VERSION - 1,
        trust_ir::binary::BASE_FORMAT_VERSION,
    ] {
        let mut forged = bytes.clone();
        forged[8..12].copy_from_slice(&older.to_le_bytes());
        assert!(
            matches!(
                trust_ir::binary::deserialize_module(&forged),
                Err(trust_ir::binary::BinaryError::InvalidTag(_))
            ),
            "a v{older} header must not carry a batch tag"
        );
    }
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "{errors:?}");

    let interpreter = Interpreter::with_module(&module);
    let (x, k) = (0x0000_00F0_u32, 3_u32);
    let bits = interpreter
        .execute_func(
            FuncId::new(2),
            [
                InterpretValue::int(Ty::U32, i128::from(x)).expect("u32"),
                InterpretValue::int(Ty::U32, i128::from(k)).expect("u32"),
            ],
        )
        .expect("bits runs");
    let expected = x
        .leading_zeros()
        .trailing_zeros()
        .swap_bytes()
        .reverse_bits()
        .rotate_left(k)
        .rotate_right(k);
    assert_eq!(
        bits.returns[0].as_int().expect("u32").as_unsigned(),
        u128::from(expected)
    );
    let float = |value: f64| InterpretValue {
        ty: Ty::F64,
        kind: InterpretValueKind::FloatBits(value.to_bits()),
    };
    let sign = interpreter
        .execute_func(FuncId::new(3), [float(2.5), float(-0.0)])
        .expect("sign runs");
    assert_eq!(sign.returns[0], float(2.5_f64.copysign(-0.0)));
}

/// Amendment P (wire v54): the `assert_panic_site` golden decodes at exactly
/// the panic-site version, is refused under any older header (tag 66 is
/// read-gated), validates, and every failing check panics with its kind's
/// message AND its site — the entry and the resolved location, a
/// `#[track_caller]` forward through `caller` included — while every
/// passing check returns.
#[test]
fn assert_panic_site_golden_is_read_gated_valid_and_panics_with_its_site() {
    use trust_ir::interpret::{InterpretPanicSite, PanicLocationValue};
    use trust_ir::value::GlobalId;

    let bytes = fs::read(fixtures_dir().join("assert_panic_site.tmbc")).expect("golden present");
    let (module, version) =
        trust_ir::binary::deserialize_module_with_wire_version(&bytes).expect("decodes");
    assert_eq!(version.get(), trust_ir::binary::PANIC_SITE_FORMAT_VERSION);
    assert_eq!(
        module,
        generate::build_assert_panic_site().expect("assert_panic_site builds")
    );
    // The last header before the site existed reads every other construct
    // of this golden, so it is refused exactly at the sited assert's tag.
    let mut forged = bytes.clone();
    forged[8..12].copy_from_slice(&(trust_ir::binary::PANIC_SITE_FORMAT_VERSION - 1).to_le_bytes());
    assert!(
        matches!(
            trust_ir::binary::deserialize_module(&forged),
            Err(trust_ir::binary::BinaryError::InvalidTag(66))
        ),
        "a pre-site header must not carry a sited assert"
    );
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "{errors:?}");

    let by_name = |name: &str| {
        module
            .functions
            .iter()
            .find(|f| f.name == name)
            .map(|f| f.id)
            .expect("function present")
    };
    let interpreter = Interpreter::with_module(&module);
    let int = |ty: Ty, v: i128| InterpretValue::int(ty, v).expect("in range");
    let at_loc = |entry: &str| InterpretPanicSite {
        entry: by_name(entry),
        location: PanicLocationValue::Global {
            global: GlobalId::new(0),
            offset: 0,
        },
    };
    let panic_of = |func: &str, args: Vec<InterpretValue>| {
        let error = interpreter
            .execute_func(by_name(func), args)
            .expect_err("the check fails");
        assert_eq!(
            error.code,
            trust_ir::interpret::InterpretErrorCode::Panic,
            "{error}"
        );
        let site = error.panic().and_then(|panic| panic.site);
        (error.message, site)
    };
    assert_eq!(
        panic_of("bounds", vec![int(Ty::Usize, 5), int(Ty::Usize, 3)]),
        (
            "index out of bounds: the len is 3 but the index is 5".to_string(),
            Some(at_loc("panic_bounds_check"))
        )
    );
    assert_eq!(
        panic_of("add", vec![int(Ty::U8, 255)]),
        (
            "attempt to add with overflow".to_string(),
            Some(at_loc("panic_const_add_overflow"))
        )
    );
    assert_eq!(
        panic_of("resumed", vec![InterpretValue::bool(false)]),
        (
            "assertion failed".to_string(),
            Some(at_loc("panic_resumed"))
        )
    );
    // `#[track_caller]`: the location is the caller's, resolved through the
    // global it materialized.
    assert_eq!(
        panic_of("caller", vec![int(Ty::Usize, 9), int(Ty::Usize, 2)]),
        (
            "index out of bounds: the len is 2 but the index is 9".to_string(),
            Some(at_loc("panic_bounds_check"))
        )
    );
    let returns = |func: &str, args: Vec<InterpretValue>| {
        interpreter
            .execute_func(by_name(func), args)
            .expect("the check holds")
            .returns
    };
    assert_eq!(
        returns("bounds", vec![int(Ty::Usize, 2), int(Ty::Usize, 3)]).len(),
        1
    );
    assert_eq!(returns("add", vec![int(Ty::U8, 7)]).len(), 1);
    assert_eq!(
        returns("resumed", vec![InterpretValue::bool(true)]).len(),
        1
    );
    assert_eq!(
        returns("caller", vec![int(Ty::Usize, 1), int(Ty::Usize, 2)]).len(),
        1
    );
}

/// Amendment P (wire v54): the `assert_invoke` golden decodes at exactly the
/// panic-site version, is refused under any older header (tag 67 is
/// read-gated), validates, takes its normal edge when the check holds and
/// is the sited panic (never its pad) when it fails.
#[test]
fn assert_invoke_golden_is_read_gated_and_valid() {
    let bytes = fs::read(fixtures_dir().join("assert_invoke.tmbc")).expect("golden present");
    let (module, version) =
        trust_ir::binary::deserialize_module_with_wire_version(&bytes).expect("decodes");
    assert_eq!(version.get(), trust_ir::binary::PANIC_SITE_FORMAT_VERSION);
    assert_eq!(
        module,
        generate::build_assert_invoke().expect("assert_invoke builds")
    );
    let mut forged = bytes.clone();
    forged[8..12].copy_from_slice(&(trust_ir::binary::PANIC_SITE_FORMAT_VERSION - 1).to_le_bytes());
    assert!(matches!(
        trust_ir::binary::deserialize_module(&forged),
        Err(trust_ir::binary::BinaryError::InvalidTag(67))
    ));
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "{errors:?}");
    let report = trust_ir_build::validate::validate_module_report(&module);
    assert_eq!(report.unwind_surface(), vec![FuncId::new(1)]);
    let interpreter = Interpreter::with_module(&module);
    let x = InterpretValue::int(Ty::Usize, 42).expect("usize");
    let outcome = interpreter
        .execute_func(FuncId::new(1), vec![InterpretValue::bool(true), x.clone()])
        .expect("the normal edge");
    assert_eq!(outcome.returns, vec![x.clone()]);
    let error = interpreter
        .execute_func(FuncId::new(1), vec![InterpretValue::bool(false), x])
        .expect_err("the sited panic");
    assert_eq!(error.code, trust_ir::interpret::InterpretErrorCode::Panic);
    assert_eq!(error.message, "attempt to divide by zero");
    assert_eq!(
        error
            .panic()
            .and_then(|panic| panic.site)
            .map(|site| site.entry),
        Some(FuncId::new(0))
    );
}

/// Amendment D (wire v55): the `drop_glue` golden decodes at exactly the
/// drop-glue version, is refused under any older header (tag 68 is
/// read-gated), validates with every drop resolved, and executes its normal
/// paths: nested, recursive and flagged drops run their glue, and the
/// `DropInvoke` takes its normal edge.
#[test]
fn drop_glue_golden_is_read_gated_valid_and_executes() {
    let bytes = fs::read(fixtures_dir().join("drop_glue.tmbc")).expect("golden present");
    let (module, version) =
        trust_ir::binary::deserialize_module_with_wire_version(&bytes).expect("decodes");
    assert_eq!(version.get(), trust_ir::binary::DROP_GLUE_FORMAT_VERSION);
    assert_eq!(
        module,
        generate::build_drop_glue().expect("drop_glue builds")
    );
    assert_eq!(module.drop_glue.len(), 3);
    let mut forged = bytes.clone();
    forged[8..12].copy_from_slice(&(trust_ir::binary::DROP_GLUE_FORMAT_VERSION - 1).to_le_bytes());
    assert!(matches!(
        trust_ir::binary::deserialize_module(&forged),
        Err(trust_ir::binary::BinaryError::InvalidTag(68))
    ));
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "{errors:?}");
    let report = trust_ir_build::validate::validate_module_report(&module);
    assert!(report.unresolved_drops().is_empty());
    let run = module
        .functions
        .iter()
        .find(|f| f.name == "run")
        .expect("run")
        .id;
    let run_list = module
        .functions
        .iter()
        .find(|f| f.name == "run_list")
        .expect("run_list")
        .id;
    assert_eq!(report.unwind_surface(), vec![run]);
    let interpreter = Interpreter::with_module(&module);
    for (flag, expected) in [(true, 4), (false, 3)] {
        let outcome = interpreter
            .execute_func(run, vec![InterpretValue::bool(flag)])
            .expect("the normal paths execute");
        assert_eq!(
            outcome.returns[0].as_int().expect("i64").as_signed(),
            expected,
            "flag {flag}"
        );
    }
    let outcome = interpreter
        .execute_func(run_list, vec![])
        .expect("recursion through the table");
    assert_eq!(outcome.returns[0].as_int().expect("i64").as_signed(), 0);
}

/// Amendment D, Part 2 (wire v56): the `unwind_twins` golden decodes at
/// exactly the unwind-twins version, is refused under any older header (tag
/// 69 is read-gated), validates, puts both runners on the unwind surface,
/// and executes under the default `PanicStrategy::Abort`: `run_ok` takes the
/// twin's normal edge and returns 7, and `run_boom`'s failed check is the
/// terminal `div_by_zero` panic (the unwind edge is never taken); under
/// `PanicStrategy::Unwind` `run_boom`'s raise enters the catch-all pad (-1).
#[test]
fn unwind_twins_golden_is_read_gated_valid_and_executes() {
    let bytes = fs::read(fixtures_dir().join("unwind_twins.tmbc")).expect("golden present");
    let (module, version) =
        trust_ir::binary::deserialize_module_with_wire_version(&bytes).expect("decodes");
    assert_eq!(version.get(), trust_ir::binary::UNWIND_TWINS_FORMAT_VERSION);
    assert_eq!(
        module,
        generate::build_unwind_twins().expect("unwind_twins builds")
    );
    let mut forged = bytes.clone();
    forged[8..12]
        .copy_from_slice(&(trust_ir::binary::UNWIND_TWINS_FORMAT_VERSION - 1).to_le_bytes());
    assert!(matches!(
        trust_ir::binary::deserialize_module(&forged),
        Err(trust_ir::binary::BinaryError::InvalidTag(69))
    ));
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "{errors:?}");
    let id = |name: &str| {
        module
            .functions
            .iter()
            .find(|f| f.name == name)
            .unwrap_or_else(|| panic!("{name}"))
            .id
    };
    let report = trust_ir_build::validate::validate_module_report(&module);
    assert_eq!(report.unwind_surface(), vec![id("run_ok"), id("run_boom")]);
    let interpreter = Interpreter::with_module(&module);
    let outcome = interpreter
        .execute_func(id("run_ok"), vec![])
        .expect("the normal edge");
    assert_eq!(outcome.returns[0].as_int().expect("i64").as_signed(), 7);
    let panic = interpreter
        .execute_func(id("run_boom"), vec![])
        .expect_err("the panic=abort projection");
    assert_eq!(panic.code, trust_ir::interpret::InterpretErrorCode::Panic);
    assert_eq!(panic.message, "attempt to divide by zero");
    // Under `PanicStrategy::Unwind` (§21) the raise is caught by the twin's
    // catch-all pad, and the normal path is unchanged.
    let unwinding =
        Interpreter::with_module(&module).with_options(trust_ir::interpret::InterpretOptions {
            panic_strategy: trust_ir::interpret::PanicStrategy::Unwind,
            ..trust_ir::interpret::InterpretOptions::default()
        });
    for (name, expected) in [("run_ok", 7), ("run_boom", -1)] {
        let outcome = unwinding
            .execute_func(id(name), vec![])
            .unwrap_or_else(|e| panic!("{name} under Unwind: {e}"));
        assert_eq!(
            outcome.returns[0].as_int().expect("i64").as_signed(),
            expected,
            "{name} under Unwind"
        );
    }
}

/// Amendment D: every golden written below the drop-glue version decodes
/// with an EMPTY table (there is nothing to carry), so its drops keep their
/// v47 standing, and it re-serializes byte for byte.
#[test]
fn every_pre_drop_glue_golden_decodes_with_an_empty_table() {
    let mut checked = 0usize;
    let mut files: Vec<PathBuf> = fs::read_dir(fixtures_dir())
        .expect("fixture dir")
        .map(|entry| entry.expect("entry").path())
        .filter(|path| path.extension().is_some_and(|e| e == "tmbc"))
        .collect();
    files.sort();
    for path in files {
        let bytes = fs::read(&path).expect("read golden");
        let Ok((module, version)) = trust_ir::binary::deserialize_module_with_wire_version(&bytes)
        else {
            continue;
        };
        if version.get() >= trust_ir::binary::DROP_GLUE_FORMAT_VERSION {
            continue;
        }
        assert!(module.drop_glue.is_empty(), "{}", path.display());
        assert_eq!(
            trust_ir::binary::serialize_module(&module).expect("serialize_module: test fixture"),
            bytes,
            "{} re-serializes byte for byte",
            path.display()
        );
        checked += 1;
    }
    assert!(checked > 10, "the corpus is not vacuous ({checked})");
}

/// PKG-U13e: every golden written below the blob version decodes with an
/// empty blob table and re-serializes byte for byte, so the table rewrote no
/// module that names no blob.
#[test]
fn every_pre_blob_golden_decodes_with_an_empty_blob_table() {
    let mut checked = 0usize;
    let mut files: Vec<PathBuf> = fs::read_dir(fixtures_dir())
        .expect("fixture dir")
        .map(|entry| entry.expect("entry").path())
        .filter(|path| path.extension().is_some_and(|e| e == "tmbc"))
        .collect();
    files.sort();
    for path in files {
        let bytes = fs::read(&path).expect("read golden");
        let Ok((module, version)) = trust_ir::binary::deserialize_module_with_wire_version(&bytes)
        else {
            continue;
        };
        if version.get() >= trust_ir::binary::TENSOR_BLOB_FORMAT_VERSION {
            continue;
        }
        assert!(module.blobs.is_empty(), "{}", path.display());
        assert_eq!(
            trust_ir::binary::serialize_module(&module).expect("serialize_module: test fixture"),
            bytes,
            "{} re-serializes byte for byte",
            path.display()
        );
        checked += 1;
    }
    assert!(checked > 10, "the corpus is not vacuous ({checked})");
}

/// Amendment P: every golden written below the panic-site version keeps its
/// binary bytes — it decodes with no site and re-serializes byte for byte —
/// so the amendment rewrote no siteless module. Not vacuous: assert-bearing
/// goldens are among them.
#[test]
fn every_pre_panic_site_golden_keeps_its_bytes() {
    let mut checked = 0usize;
    let mut asserts = 0usize;
    let mut files: Vec<PathBuf> = fs::read_dir(fixtures_dir())
        .expect("fixture dir")
        .map(|entry| entry.expect("entry").path())
        .filter(|path| path.extension().is_some_and(|e| e == "tmbc"))
        .collect();
    files.sort();
    for path in files {
        let bytes = fs::read(&path).expect("read golden");
        let Ok((module, version)) = trust_ir::binary::deserialize_module_with_wire_version(&bytes)
        else {
            continue;
        };
        if version.get() >= trust_ir::binary::PANIC_SITE_FORMAT_VERSION {
            continue;
        }
        for node in module
            .functions
            .iter()
            .flat_map(|f| &f.blocks)
            .flat_map(|b| &b.body)
        {
            assert!(
                node.inst.panic_site().is_none(),
                "{}: a pre-v54 golden carries no site",
                path.display()
            );
            asserts += usize::from(matches!(node.inst, trust_ir::Inst::Assert { .. }));
        }
        assert_eq!(
            trust_ir::binary::serialize_module(&module).expect("serialize_module: test fixture"),
            bytes,
            "{} (v{}) re-serializes byte for byte",
            path.display(),
            version.get()
        );
        checked += 1;
    }
    assert!(
        checked > 10 && asserts > 0,
        "{checked} goldens, {asserts} asserts"
    );
}

/// Plan item P (wire v52): the `assert_kind` golden decodes at exactly the
/// assert-kind version, is refused under any older header (tag 63 is
/// read-gated), validates, and every function panics with its kind's
/// message — and returns when its check holds.
#[test]
fn assert_kind_golden_is_read_gated_valid_and_panics_by_kind() {
    let bytes = fs::read(fixtures_dir().join("assert_kind.tmbc")).expect("golden present");
    let (module, version) =
        trust_ir::binary::deserialize_module_with_wire_version(&bytes).expect("decodes");
    assert_eq!(version.get(), trust_ir::binary::ASSERT_KIND_FORMAT_VERSION);
    assert_eq!(
        module,
        generate::build_assert_kind().expect("assert_kind builds")
    );
    for older in [
        trust_ir::binary::ASSERT_KIND_FORMAT_VERSION - 1,
        trust_ir::binary::BASE_FORMAT_VERSION,
    ] {
        let mut forged = bytes.clone();
        forged[8..12].copy_from_slice(&older.to_le_bytes());
        assert!(
            matches!(
                trust_ir::binary::deserialize_module(&forged),
                Err(trust_ir::binary::BinaryError::InvalidTag(63))
            ),
            "a v{older} header must not carry a kinded assert"
        );
    }
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "{errors:?}");

    let interpreter = Interpreter::with_module(&module);
    let int = |ty: Ty, v: i128| InterpretValue::int(ty, v).expect("in range");
    let panic_of = |func: u32, args: Vec<InterpretValue>| {
        let error = interpreter
            .execute_func(FuncId::new(func), args)
            .expect_err("the check fails");
        assert_eq!(
            error.code,
            trust_ir::interpret::InterpretErrorCode::Panic,
            "{error}"
        );
        error.message
    };
    assert_eq!(
        panic_of(0, vec![int(Ty::Usize, 5), int(Ty::Usize, 3)]),
        "index out of bounds: the len is 3 but the index is 5"
    );
    assert_eq!(
        panic_of(1, vec![int(Ty::Usize, 4097), int(Ty::Usize, 8)]),
        "misaligned pointer dereference: address must be a multiple of 0x8 but is 0x1001"
    );
    assert_eq!(
        panic_of(2, vec![int(Ty::U32, 7), int(Ty::U32, 0)]),
        "attempt to divide by zero"
    );
    assert_eq!(
        panic_of(3, vec![int(Ty::U32, 7), int(Ty::U32, 0)]),
        "attempt to calculate the remainder with a divisor of zero"
    );
    assert_eq!(
        panic_of(4, vec![int(Ty::Usize, 0)]),
        "null pointer dereference occurred"
    );
    for (k, message) in [
        "attempt to add with overflow",
        "attempt to subtract with overflow",
        "attempt to multiply with overflow",
        "attempt to divide with overflow",
        "attempt to calculate the remainder with overflow",
        "attempt to shift left with overflow",
        "attempt to shift right with overflow",
        "attempt to negate with overflow",
    ]
    .into_iter()
    .enumerate()
    {
        assert_eq!(panic_of(5, vec![int(Ty::U8, k as i128)]), message);
    }
    assert_eq!(
        panic_of(6, vec![InterpretValue::bool(false)]),
        "assertion failed"
    );
    // The negative twins: every check that holds returns its input.
    let returns = |func: u32, args: Vec<InterpretValue>| {
        interpreter
            .execute_func(FuncId::new(func), args)
            .expect("the check holds")
            .returns
    };
    assert_eq!(
        returns(0, vec![int(Ty::Usize, 2), int(Ty::Usize, 3)]).len(),
        1
    );
    assert_eq!(returns(2, vec![int(Ty::U32, 7), int(Ty::U32, 2)]).len(), 1);
    assert_eq!(returns(5, vec![int(Ty::U8, 8)]).len(), 1);
    assert_eq!(returns(6, vec![InterpretValue::bool(true)]).len(), 1);
}

/// Plan item P: every assert in a golden written BEFORE the kind existed
/// (header below v52 — bytes checked in by older writers, never rewritten)
/// decodes as `AssertKind::Unspecified`. Not vacuous: at least one such
/// golden carries an assert (`inst_control`).
#[test]
fn every_pre_assert_kind_golden_assert_decodes_as_unspecified() {
    let mut seen = 0usize;
    let mut dirs = vec![fixtures_dir(), fixtures_dir().join("compat")];
    let mut files = Vec::new();
    while let Some(dir) = dirs.pop() {
        for entry in fs::read_dir(&dir).expect("fixture dir") {
            let path = entry.expect("entry").path();
            if path.extension().is_some_and(|e| e == "tmbc") {
                files.push(path);
            }
        }
    }
    files.sort();
    for path in files {
        let bytes = fs::read(&path).expect("read golden");
        let Ok((module, version)) = trust_ir::binary::deserialize_module_with_wire_version(&bytes)
        else {
            continue;
        };
        if version.get() >= trust_ir::binary::ASSERT_KIND_FORMAT_VERSION {
            continue;
        }
        for node in module
            .functions
            .iter()
            .flat_map(|f| &f.blocks)
            .flat_map(|b| &b.body)
        {
            if let trust_ir::Inst::Assert { kind, .. } = &node.inst {
                assert_eq!(
                    *kind,
                    trust_ir::AssertKind::Unspecified,
                    "{} (v{})",
                    path.display(),
                    version.get()
                );
                seen += 1;
            }
        }
    }
    assert!(seen > 0, "no pre-v52 golden carries an assert");
}

#[test]
fn declared_tuple_golden_has_valid_ir_and_uses_its_declared_byte_image() {
    let module = generate::build_declared_tuple_v42().expect("the fixture builds");
    assert!(trust_ir_build::validate_module(&module).is_empty());
    let result = Interpreter::with_module(&module)
        .execute_func(FuncId::new(0), [])
        .unwrap();
    assert_eq!(
        result.returns[0].as_int().unwrap().as_unsigned(),
        0x1122334455667788
    );
    let bytes =
        trust_ir::binary::serialize_module(&module).expect("serialize_module: test fixture");
    assert_eq!(u32::from_le_bytes(bytes[8..12].try_into().unwrap()), 42);
}

/// WS2.3 (F-031) differential property, gate 8: the validator and the layout
/// authority share ONE coherence rule for declared struct layouts. For every
/// struct of every conformance module — the generated corpus, the
/// native-bundle module, and every binary golden on disk (plus the pinned
/// back-compat blobs that still decode) — a module `validate_module` accepts
/// has no struct that `Module::ty_layout_shape` refuses, except as
/// `MissingStructSize` / `MissingStructAlign` (no declared layout to judge)
/// or `MissingFieldOffset` (a partial layout, deliberately not a validation
/// error in WS2.3 — it stays refused at use time). Before WS2.3 a target-free
/// or target-pinned `Pair { a @ 0, b @ 0 }` validated while `shape` refused it.
#[test]
fn struct_layout_validator_agrees_with_shape() {
    use trust_ir::LayoutError;

    let mut modules: Vec<(String, Module)> = Vec::new();
    for fixture in corpus() {
        modules.push((
            fixture.name.to_string(),
            (fixture.build)().expect("the fixture builds"),
        ));
    }
    for fixture in native_bundle_corpus() {
        modules.push((
            fixture.name.to_string(),
            (fixture.build)().expect("the fixture builds").bundle.module,
        ));
    }
    for dir in [fixtures_dir(), fixtures_dir().join("compat")] {
        let mut paths: Vec<PathBuf> = fs::read_dir(&dir)
            .unwrap_or_else(|e| panic!("read {}: {e}", dir.display()))
            .map(|entry| entry.expect("fixture dir entry").path())
            .filter(|path| path.extension().is_some_and(|ext| ext == "tmbc"))
            .collect();
        paths.sort();
        for path in paths {
            let bytes = fs::read(&path).expect("read golden");
            // A compat blob below the read floor is refused by design
            // (back_compat.rs owns that); it has no module to compare.
            if let Ok(module) = trust_ir::binary::deserialize_module(&bytes) {
                modules.push((path.display().to_string(), module));
            }
        }
    }

    let mut judged_declared = 0usize;
    for (name, module) in &modules {
        if !trust_ir_build::validate_module(module).is_empty() {
            continue;
        }
        for sd in &module.structs {
            let shape = module.ty_layout_shape(&Ty::Struct(sd.id));
            match &shape {
                Ok(_) => {
                    if sd.size.is_some() && sd.align.is_some() {
                        judged_declared += 1;
                    }
                }
                Err(
                    LayoutError::MissingStructSize(_)
                    | LayoutError::MissingStructAlign(_)
                    | LayoutError::MissingFieldOffset { .. },
                ) => {}
                Err(other) => panic!(
                    "{name}: struct #{} validates but the layout authority refuses it: {other:?}",
                    sd.id.index()
                ),
            }
        }
    }
    assert!(
        judged_declared > 0,
        "the property must be non-vacuous: no validated conformance module declares a struct layout"
    );

    // Mutation control: the property is not vacuous in the refusing
    // direction either — the one-mutation overlap twin of a coherent pair is
    // refused by BOTH authorities, target-free and pinned.
    for pin in [false, true] {
        let mut m = Module::new("ws2_3_twin");
        m.add_struct(trust_ir::ty::StructDef {
            id: trust_ir::StructId::new(0),
            name: "Pair".into(),
            fields: vec![
                trust_ir::ty::FieldDef {
                    name: "a".into(),
                    ty: Ty::U32,
                    offset: Some(0),
                },
                trust_ir::ty::FieldDef {
                    name: "b".into(),
                    ty: Ty::F32,
                    offset: Some(0),
                },
            ],
            size: Some(8),
            align: Some(4),
            repr: trust_ir::ty::StructRepr::C,
            origin: None,
        });
        if pin {
            m.target_info = Some(trust_ir::TargetInfo {
                triple: "aarch64-apple-darwin".into(),
                pointer_size: 8,
                endianness: trust_ir::Endianness::Little,
                abi: None,
                struct_passing: trust_ir::StructPassingPolicy::Unclassified,
            });
        }
        assert!(matches!(
            m.ty_layout_shape(&Ty::Struct(trust_ir::StructId::new(0))),
            Err(LayoutError::StructLayoutIncoherent(_))
        ));
        assert_eq!(
            trust_ir_build::validate_module(&m),
            vec![trust_ir_build::ValidationError::StructLayoutInconsistent {
                struct_id: 0,
                reason: "fields overlap",
            }],
            "pin={pin}"
        );
    }
}

// ============================================================
// WS4.15: the Lean library envelope has an in-format home
// ============================================================
//
// `docs/SPEC_RATIFICATIONS.md` §9 maps every load-bearing fact of the
// `trust.lean.ir-library/v1` envelope onto an existing carrier. The corpus row
// `lean_library_envelope` pins its bytes; these tests pin that the carriers
// actually carry AUTHORITY: the TV obligation is kernel-re-checked in-process,
// the license is admitted by the codegen gate, the bytes re-certify after
// every lossless transport, and each forgery is refused for its own reason.
// The rows that CANNOT hold until WS1 lands (F-006 license binding, F-008
// source-definition binding) and the text leg (F-071, then F-070) are ratchets in
// `tests/two_language/b3_kernel_certified.rs` (`b3.envelope.*`).

/// Exactly one `CertifiedCleanCicKernelRecheckFailed` for `obligation`, and it
/// is the KERNEL's own judgment on the re-derived equation (not a decode,
/// relevance or fragment refusal).
fn sole_envelope_kernel_rejection(
    errors: &[trust_ir_build::ValidationError],
    obligation: u32,
) -> bool {
    matches!(
        errors,
        [trust_ir_build::ValidationError::CertifiedCleanCicKernelRecheckFailed {
            obligation: got,
            reason,
        }] if *got == obligation
            && reason.contains(
                "in-process kernel REJECTED the translation-validation equation for 'addmul'"
            )
    )
}

fn mul_to_add_in_addmul(module: &mut Module) {
    let func = module
        .functions
        .iter_mut()
        .find(|f| f.name == "addmul")
        .expect("fixture defines addmul");
    let op = func.blocks[0]
        .body
        .iter_mut()
        .find_map(|node| match &mut node.inst {
            Inst::BinOp { op, .. } if *op == trust_ir::BinOp::Mul => Some(op),
            _ => None,
        })
        .expect("addmul has a Mul");
    *op = trust_ir::BinOp::Add;
}

#[test]
fn lean_library_envelope_validates_under_authority_and_licenses_codegen() {
    use trust_ir::proof::RejectingModuleProofAuthority;

    let module = generate::build_lean_library_envelope().expect("the fixture builds");

    // Every envelope fact sits in its home (the §9 table).
    assert!(module.name.starts_with("lean-library:"));
    assert_eq!(module.files, vec![generate::LEAN_ENVELOPE_SOURCE_PATH]);
    let addmul = module
        .functions
        .iter()
        .find(|f| f.name == "addmul")
        .expect("addmul");
    assert_eq!(addmul.producer, Some(trust_ir::Producer::Clean));
    assert_eq!(addmul.display_path.as_deref(), Some("Envelope.addmul"));
    assert_eq!(
        addmul.body_gate,
        Some(trust_ir::BodyGate::Gated {
            authority: generate::LEAN_ENVELOPE_TV_AUTHORITY.to_string(),
            evidence: None,
        })
    );
    let [theorem, tv] = module.proof_obligations.as_slice() else {
        panic!("two obligations: {:?}", module.proof_obligations);
    };
    assert_eq!(tv.kind, trust_ir::ObligationKind::TranslationValidation);
    assert_eq!(tv.status, ProofStatus::Certified);
    assert_eq!(tv.function, Some(addmul.id));
    let formula = tv.formula.as_ref().expect("carrier/method formula");
    assert_eq!(formula.schema, generate::LEAN_ENVELOPE_TV_BINDING_SCHEMA);
    assert_eq!(formula.payload, generate::LEAN_ENVELOPE_TV_BINDING_PAYLOAD);
    assert_eq!(
        theorem.kind,
        trust_ir::ObligationKind::Custom {
            namespace: "trust.proof_item".to_string(),
            name: "addmul_def".to_string(),
        }
    );
    assert_eq!(theorem.status, ProofStatus::Pending);
    assert_eq!(
        theorem.formula.as_ref().map(|f| f.schema.as_str()),
        Some(generate::LEAN_ENVELOPE_THEOREM_REF_SCHEMA)
    );
    assert!(
        theorem
            .formula
            .as_ref()
            .is_some_and(|f| f.bindings.is_empty() && f.smtlib.is_none()),
        "a theorem REFERENCE carries no bindable first-order clause"
    );

    // Accepted by every entry point that grants authority, and the kernel tier
    // actually replayed the certificate (it is not a structural pass).
    assert_eq!(trust_ir_build::validate_module(&module), vec![]);
    assert_eq!(
        trust_ir_build::validate_module_with_authority(&module, &RejectingModuleProofAuthority),
        vec![]
    );
    assert_eq!(trust_ir_build::validate_module_for_codegen(&module), vec![]);
    let report = trust_ir_build::validate_module_report(&module);
    assert_eq!(
        report.replayed_certificate_refs().map(|r| r.len()),
        Some(1),
        "the kernel tier replays the TV certificate"
    );

    // The license and the proof surface force v41; nothing later is needed.
    let bytes =
        trust_ir::binary::serialize_module(&module).expect("serialize_module: test fixture");
    assert_eq!(&bytes[..8], b"TRUST_IR");
    assert_eq!(
        u32::from_le_bytes(bytes[8..12].try_into().unwrap()),
        41,
        "body_gate / display_path / Custom kind select v41"
    );

    // The three lossless transports carry it, and the decoded module
    // RE-CERTIFIES (the kernel runs again on the decoded bytes).
    let from_bin = trust_ir::binary::deserialize_module(&bytes).expect("binary decode");
    let from_json: Module =
        serde_json::from_str(&serde_json::to_string_pretty(&module).unwrap()).unwrap();
    let from_msgpack: Module = rmp_serde::from_slice(&rmp_serde::to_vec(&module).unwrap()).unwrap();
    for (format, decoded) in [
        ("binary", from_bin),
        ("json", from_json),
        ("msgpack", from_msgpack),
    ] {
        assert_eq!(decoded, module, "{format} round trip is lossless");
        assert_eq!(
            trust_ir_build::validate_module_with_authority(
                &decoded,
                &RejectingModuleProofAuthority
            ),
            vec![],
            "{format}: decoded module re-certifies"
        );
    }
}

/// Negative twin: the envelope's body miscompiled (`a*b + a` -> `a+b + a`)
/// under the SAME certificate is refused, by the kernel, at every entry point
/// that grants authority. (The F-008 half — a certificate RE-MINTED against
/// the miscompiled body — is the `b3.envelope.gap.*` ratchet.)
#[test]
fn lean_library_envelope_mutated_body_under_the_same_certificate_is_refused() {
    use trust_ir::proof::RejectingModuleProofAuthority;

    let mut module = generate::build_lean_library_envelope().expect("the fixture builds");
    mul_to_add_in_addmul(&mut module);
    assert!(sole_envelope_kernel_rejection(
        &trust_ir_build::validate_module(&module),
        1
    ));
    assert!(sole_envelope_kernel_rejection(
        &trust_ir_build::validate_module_with_authority(&module, &RejectingModuleProofAuthority),
        1
    ));
    // The codegen entry point adds exactly one license follow-on (roadmap
    // WS1.5): `addmul` still wears `Gated{clean-kernel-tv}`, whose evidence is
    // a certificate this pass must have kernel-replayed, and it replayed none.
    let codegen = trust_ir_build::validate_module_for_codegen(&module);
    let addmul = module.function_by_name("addmul").expect("addmul").id;
    assert!(
        codegen.len() == 2
            && sole_envelope_kernel_rejection(&codegen[..1], 1)
            && matches!(
                &codegen[1],
                trust_ir_build::ValidationError::GatedWithoutEvidence { function, authority, detail }
                    if *function == addmul.index()
                        && authority == "clean-kernel-tv"
                        && detail.contains("was not kernel-replayed")
            ),
        "{codegen:?}"
    );
}

/// The reference carriers grant nothing on their own: the carrier/method
/// formula is lineage-bound (editing it voids the certificate), and the
/// kernel-only theorem reference cannot claim `Certified` without a
/// kernel-checkable certificate.
#[test]
fn lean_library_envelope_reference_carriers_grant_no_authority() {
    let honest = generate::build_lean_library_envelope().expect("the fixture builds");

    // carrier/method are bound into the TV certificate's lineage.
    let mut relabelled = honest.clone();
    relabelled.proof_obligations[1]
        .formula
        .as_mut()
        .expect("formula")
        .payload = "carrier=UInt32;method=definitional-equality".to_string();
    let errors = trust_ir_build::validate_module(&relabelled);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            trust_ir_build::ValidationError::CertifiedCleanCicLineageMismatch { obligation: 1 }
        )),
        "editing the carrier voids the lineage: {errors:?}"
    );

    // A theorem REFERENCE claiming the kernel tier with no certificate.
    let mut claimed = honest.clone();
    claimed.proof_obligations[0].status = ProofStatus::Certified;
    assert_eq!(
        trust_ir_build::validate_module(&claimed),
        vec![trust_ir_build::ValidationError::CertifiedWithoutCleanCic { obligation: 0 }]
    );
}

// ---- WS4.15 review: adversarial inputs the fixture's own tests did not write ----

/// The one `CertifiedCleanCicKernelRecheckFailed` for `obligation`, whose
/// reason contains `needle`.
fn sole_recheck_failure(
    errors: &[trust_ir_build::ValidationError],
    obligation: u32,
    needle: &str,
) -> bool {
    matches!(
        errors,
        [trust_ir_build::ValidationError::CertifiedCleanCicKernelRecheckFailed {
            obligation: got,
            reason,
        }] if *got == obligation && reason.contains(needle)
    )
}

/// The kernel-only theorem REFERENCE cannot borrow the body's certificate. A
/// `clean_backend_tv` certificate re-minted (fresh lineage) for the
/// `Custom{"trust.proof_item"}` row is refused by the anchor→kind guard; the
/// honest certificate merely re-pointed at the reference is refused by
/// lineage; and a directive-free (contract-path) `CleanCic` over the reference
/// is refused because a `clean.theorem-ref/v1` formula grounds nothing.
#[test]
fn lean_library_envelope_theorem_reference_cannot_borrow_the_tv_certificate() {
    use trust_ir::proof::RejectingModuleProofAuthority;

    let honest = generate::build_lean_library_envelope().expect("the fixture builds");

    let mut reminted = honest.clone();
    reminted.proof_obligations[0].status = ProofStatus::Certified;
    let certificate = generate::lean_envelope_tv_certificate(
        &reminted.proof_obligations[0],
        generate::lean_envelope_terms::addmul_body(),
    )
    .expect("the fixture builds");
    reminted.proof_certificates.push(certificate);
    for errors in [
        trust_ir_build::validate_module(&reminted),
        trust_ir_build::validate_module_with_authority(&reminted, &RejectingModuleProofAuthority),
    ] {
        assert!(
            sole_recheck_failure(
                &errors,
                0,
                "may only certify TranslationValidation obligations"
            ),
            "a TV certificate re-minted for the theorem reference: {errors:?}"
        );
    }

    let mut repointed = honest.clone();
    repointed.proof_obligations[0].status = ProofStatus::Certified;
    repointed.proof_obligations[1].status = ProofStatus::Pending;
    repointed.proof_certificates[0].obligation = ProofId::new(0);
    assert_eq!(
        trust_ir_build::validate_module(&repointed),
        vec![trust_ir_build::ValidationError::CertifiedCleanCicLineageMismatch { obligation: 0 }]
    );

    let mut contract_path = honest.clone();
    contract_path.proof_obligations[0].status = ProofStatus::Certified;
    let mut certificate = generate::lean_envelope_tv_certificate(
        &contract_path.proof_obligations[0],
        generate::lean_envelope_terms::addmul_body(),
    )
    .expect("the fixture builds");
    match &mut certificate.evidence {
        ProofEvidence::CleanCic { kernel_recheck, .. } => *kernel_recheck = None,
        other => panic!("CleanCic evidence expected: {other:?}"),
    }
    contract_path.proof_certificates.push(certificate);
    for errors in [
        trust_ir_build::validate_module(&contract_path),
        trust_ir_build::validate_module_with_authority(
            &contract_path,
            &RejectingModuleProofAuthority,
        ),
    ] {
        assert!(
            sole_recheck_failure(
                &errors,
                0,
                "does not pass the obligation-grounded Clean contract recheck"
            ),
            "a directive-free CleanCic over the theorem reference: {errors:?}"
        );
    }
}

/// The TV home is FUNCTION-scoped: an envelope `bodies[]` row whose obligation
/// loses its `function` (certificate re-minted over the new lineage, so this
/// is not a lineage refusal) has no LHS to re-derive and is refused.
#[test]
fn lean_library_envelope_unscoped_tv_obligation_is_refused() {
    let mut module = generate::build_lean_library_envelope().expect("the fixture builds");
    module.proof_obligations[1].function = None;
    module.proof_certificates[0] = generate::lean_envelope_tv_certificate(
        &module.proof_obligations[1],
        generate::lean_envelope_terms::addmul_body(),
    )
    .expect("the fixture builds");
    let errors = trust_ir_build::validate_module(&module);
    assert!(
        sole_recheck_failure(&errors, 1, "carries no function"),
        "{errors:?}"
    );
}

/// A certificate whose COMPARAND is honest but whose proof term proves the
/// miscompiled body's equation is refused by the kernel: the payload's two
/// halves cannot be mixed.
#[test]
fn lean_library_envelope_proof_of_another_body_is_refused() {
    let mut module = generate::build_lean_library_envelope().expect("the fixture builds");
    let (_, foreign_proof) = generate::lean_envelope_terms::comparand_and_proof(
        generate::lean_envelope_terms::add_add_body(),
    );
    match &mut module.proof_certificates[0].evidence {
        ProofEvidence::CleanCic { term, .. } => {
            *term = trust_ir::proof::encode_clean_expr_v1(&foreign_proof).expect("encodes");
        }
        other => panic!("CleanCic evidence expected: {other:?}"),
    }
    assert!(sole_envelope_kernel_rejection(
        &trust_ir_build::validate_module(&module),
        1
    ));
}

/// A multi-body envelope (the normal shape: one `bodies[]` row per compiled
/// definition) is NOT wrongly refused: a second body with its own TV row and
/// certificate certifies on every entry point. Its twin — the second body
/// miscompiled (`a*b + b`) under its own honest certificate — is refused by
/// the kernel for that body alone.
#[test]
fn lean_library_envelope_second_body_certifies_and_its_miscompile_is_refused() {
    use trust_ir::proof::RejectingModuleProofAuthority;

    let mut module = generate::build_lean_library_envelope().expect("the fixture builds");
    let mut second = module
        .functions
        .iter()
        .find(|f| f.name == "addmul")
        .expect("addmul")
        .clone();
    let second_id = FuncId::new(u32::try_from(module.functions.len()).expect("small"));
    second.id = second_id;
    second.name = "addmul2".to_string();
    second.display_path = Some("Envelope.addmul2".to_string());
    module.functions.push(second);
    let tv = generate::lean_envelope_tv_obligation(2, second_id);
    let certificate = generate::lean_envelope_tv_certificate_for(
        &tv,
        generate::lean_envelope_terms::addmul_body(),
        "addmul2",
    )
    .expect("the fixture builds");
    module.proof_obligations.push(tv);
    module.proof_certificates.push(certificate);

    assert_eq!(trust_ir_build::validate_module(&module), vec![]);
    assert_eq!(
        trust_ir_build::validate_module_with_authority(&module, &RejectingModuleProofAuthority),
        vec![]
    );
    assert_eq!(trust_ir_build::validate_module_for_codegen(&module), vec![]);
    assert_eq!(
        trust_ir_build::validate_module_report(&module)
            .replayed_certificate_refs()
            .map(|r| r.len()),
        Some(2),
        "both bodies' certificates are replayed"
    );

    let second = module
        .functions
        .iter_mut()
        .find(|f| f.name == "addmul2")
        .expect("addmul2");
    let b = second.blocks[0].params[1].0;
    let rhs = second.blocks[0]
        .body
        .iter_mut()
        .find_map(|node| match &mut node.inst {
            Inst::BinOp { op, rhs, .. } if *op == trust_ir::BinOp::Add => Some(rhs),
            _ => None,
        })
        .expect("addmul2 has an Add");
    *rhs = b;
    let errors = trust_ir_build::validate_module(&module);
    assert!(
        sole_recheck_failure(
            &errors,
            2,
            "in-process kernel REJECTED the translation-validation equation for 'addmul2'"
        ),
        "{errors:?}"
    );
}

// ---------------------------------------------------------------------------
// A Rust reference carries no permission instruction (docs/SPEC_RATIFICATIONS.md,
// the section of that name): the bundle check. `NativeVerificationBundle::validate`
// refuses `Borrow` / `BorrowMut` / `EndBorrow` in any function stamped
// `Producer::TRust`, whatever the bundle's input; minting a source-generation
// authority inherits the refusal because it validates first. The section's
// RustMir-input key is not applied until the Trust MIR bridge's respelling and
// trust-mc's alias change are on their mains (the design's landing order).
// ---------------------------------------------------------------------------

/// The `trust_native_request_bundle` fixture with one permission instruction
/// (`which`) inserted ahead of its function's return, its functions stamped
/// `producer`, its input `input`, and its module identity rebound.
fn bundle_with_permission_instruction(
    which: Option<fn(ValueId) -> Inst>,
    producer: Option<trust_ir::Producer>,
    input: trust_ir::NativeAdapterInput,
) -> NativeVerificationBundle {
    let mut bundle = generate::build_trust_native_request_bundle()
        .expect("the native request bundle fixture builds")
        .bundle;
    bundle.input = input;
    for function in &mut bundle.module.functions {
        function.producer = producer.clone();
    }
    let function = &mut bundle.module.functions[0];
    let fresh = function.max_value_id() + 1;
    let (cell, reference) = (ValueId::new(fresh), ValueId::new(fresh + 1));
    let body = &mut function.blocks[0].body;
    let at = body.len() - 1;
    body.insert(
        at,
        InstrNode::new(Inst::Alloca {
            ty: Ty::I32,
            count: None,
            align: None,
        })
        .with_result(cell),
    );
    let inst = match which {
        Some(build) => build(cell),
        // The Rust producers' spelling of the same reference.
        None => Inst::Copy {
            ty: Ty::Ptr,
            operand: cell,
        },
    };
    let mut node = InstrNode::new(inst.clone());
    if !matches!(inst, Inst::EndBorrow { .. }) {
        node = node.with_result(reference);
    }
    body.insert(at + 1, node);
    let digest = bundle.module.stable_digest();
    bundle.trust_ir_module_digest = digest;
    for node in &mut bundle.lineage.nodes {
        if bundle.lineage.roots.contains(&node.id) {
            node.target_module = digest;
        }
    }
    // Each verifier's evidence names the module it judged: rebound with it.
    for evidence in &mut bundle.evidence_bundles {
        match evidence {
            NativeEvidenceBundle::TrustVc(evidence) => evidence.trust_ir_module_digest = digest,
            NativeEvidenceBundle::TrustMc(evidence) => evidence.trust_ir_module_digest = digest,
            NativeEvidenceBundle::TrustWp(evidence) => evidence.trust_ir_module_digest = digest,
        }
    }
    bundle
}

/// A permission instruction's name and its builder over the borrowed pointer.
type PermissionInstruction = (&'static str, fn(ValueId) -> Inst);

const PERMISSION_INSTRUCTIONS: [PermissionInstruction; 3] = [
    ("borrow", |ptr| Inst::Borrow { ptr }),
    ("borrow_mut", |ptr| Inst::BorrowMut { ptr }),
    ("end_borrow", |borrow_ptr| Inst::EndBorrow { borrow_ptr }),
];

fn rust_mir_input() -> trust_ir::NativeAdapterInput {
    trust_ir::NativeAdapterInput::RustMir {
        body_digest: ProofDigest::sha256([0x31; 32]),
    }
}

fn refuses_as_rust_reference(errors: &[NativeVerificationBundleError]) -> bool {
    errors.iter().any(|error| {
        matches!(
            error,
            NativeVerificationBundleError::RustReferenceAsPermissionBorrow { location }
                if location == "function 'checked_add' bb0 #2"
        )
    })
}

/// C6, the stamp key. A bundle carrying any permission instruction in a
/// function stamped `Producer::TRust` is refused by name, whatever its input
/// (a RustMir body or a trust-ir module). Fails with the check deleted.
#[test]
fn rust_producer_bundle_refuses_a_permission_borrow() {
    for input in [
        rust_mir_input(),
        trust_ir::NativeAdapterInput::TrustIrModule,
    ] {
        for (name, build) in PERMISSION_INSTRUCTIONS {
            let bundle = bundle_with_permission_instruction(
                Some(build),
                Some(trust_ir::Producer::TRust),
                input,
            );
            let errors = bundle.validate().expect_err(name);
            assert!(
                refuses_as_rust_reference(&errors),
                "{input:?} {name}: {errors:?}"
            );
        }
        // The control: the same reference spelled as the Rust producers spell
        // it validates, so the refusal above is the instruction, not the edit.
        let control =
            bundle_with_permission_instruction(None, Some(trust_ir::Producer::TRust), input);
        assert_eq!(
            control.validate(),
            Ok(()),
            "{input:?}: Copy-spelled reference"
        );
    }
}

/// C6. Minting a source-generation authority from such a bundle is refused with
/// the same error, because `mint_from_live_lowering` validates first. Fails with
/// the check deleted (the mint succeeds).
#[test]
fn rust_producer_bundle_mint_refuses_a_permission_borrow() {
    for (name, build) in PERMISSION_INSTRUCTIONS {
        let mut bundle = bundle_with_permission_instruction(
            Some(build),
            Some(trust_ir::Producer::TRust),
            rust_mir_input(),
        );
        match trust_ir::SourceGenerationAuthority::mint_from_live_lowering(&mut bundle) {
            Err(trust_ir::SourceGenerationAuthorityMintError::InvalidBundle(errors)) => {
                assert!(refuses_as_rust_reference(&errors), "{name}: {errors:?}");
            }
            other => panic!("{name}: the mint must be refused, got {other:?}"),
        }
    }
    let mut control =
        bundle_with_permission_instruction(None, Some(trust_ir::Producer::TRust), rust_mir_input());
    let authority = trust_ir::SourceGenerationAuthority::mint_from_live_lowering(&mut control)
        .expect("a Copy-spelled reference mints");
    assert!(authority.authorizes_bundle(&control));
}

/// C6, the twin: outside the `Producer::TRust` stamp the bundle check refuses
/// nothing. The permission machine stays the format's model for non-Rust
/// producers (unstamped, `Clean`), and the MIR bridge's `TrustIr`-stamped
/// output in a RustMir bundle still carries `Borrow` / `BorrowMut` until its
/// respelling is on Trust's main, which is why the section's RustMir-input key
/// is not applied yet. Fails if the check is keyed on every input or every
/// stamp; it must change in the commit that applies the RustMir key.
#[test]
fn bundle_check_refuses_no_permission_borrow_outside_the_rust_stamp() {
    for input in [
        rust_mir_input(),
        trust_ir::NativeAdapterInput::TrustIrModule,
    ] {
        for producer in [
            None,
            Some(trust_ir::Producer::TrustIr),
            Some(trust_ir::Producer::Clean),
        ] {
            for (name, build) in PERMISSION_INSTRUCTIONS {
                let bundle =
                    bundle_with_permission_instruction(Some(build), producer.clone(), input);
                let errors = bundle.validate().err().unwrap_or_default();
                assert!(
                    !errors.iter().any(|error| matches!(
                        error,
                        NativeVerificationBundleError::RustReferenceAsPermissionBorrow { .. }
                    )),
                    "{input:?} {producer:?} {name}: {errors:?}"
                );
            }
        }
    }
}

#[test]
fn box_deref_golden_is_valid_executes_and_refuses_an_older_header() {
    let expected = generate::build_box_deref().expect("Box deref fixture");
    let bytes = fs::read(fixtures_dir().join("box_deref.tmbc")).expect("committed v74 fixture");
    let (decoded, version) = trust_ir::binary::deserialize_module_with_wire_version(&bytes)
        .expect("decode a Box deref and its validity fact");
    assert_eq!(
        version.get(),
        trust_ir::binary::BOX_DEREF_VALIDITY_FORMAT_VERSION
    );
    assert_eq!(decoded, expected);
    assert_eq!(trust_ir_build::validate_module(&decoded), vec![]);
    // The default codegen gate sets no evidence floor: the only refusal is
    // the lowering subset's, never a fact rule.
    let floor = trust_ir_build::CodegenAdmission::pinned().with_require_box_validity_evidence(
        Some(trust_ir::box_validity::BoxValidityTier::ConsumerRederived),
    );
    let below: Vec<_> = trust_ir_build::validate_module_for_codegen_with(&decoded, &floor)
        .into_iter()
        .filter(|error| {
            matches!(
                error,
                trust_ir_build::ValidationError::BoxValidityEvidenceBelowFloor { .. }
            )
        })
        .collect();
    // `fresh` and `checked` each premise all three conjuncts.
    assert_eq!(below.len(), 6, "{below:?}");
    // Both roots are in the named-premise class, so a floor there admits
    // the golden.
    let named = trust_ir_build::CodegenAdmission::pinned().with_require_box_validity_evidence(
        Some(trust_ir::box_validity::BoxValidityTier::NamedPremise),
    );
    assert!(
        !trust_ir_build::validate_module_for_codegen_with(&decoded, &named)
            .iter()
            .any(|error| matches!(
                error,
                trust_ir_build::ValidationError::BoxValidityEvidenceBelowFloor { .. }
            ))
    );
    for (function, expected) in [(0, 24), (2, 42)] {
        let actual = trust_ir::interpret::Interpreter::with_module(&decoded)
            .execute_func(FuncId::new(function), [])
            .expect("a valid Box deref is the identity on its pointer");
        assert_eq!(actual.returns.len(), 1);
        assert_eq!(actual.returns[0].as_int().unwrap().as_signed(), expected);
    }
    for body in [
        trust_ir::binary::ModuleBinaryBody::RawV38,
        trust_ir::binary::ModuleBinaryBody::CanonicalV38,
    ] {
        let options = trust_ir::binary::ModuleBinaryOptions {
            body,
            ..Default::default()
        };
        assert!(matches!(
            trust_ir::binary::ProjectedModuleBinaryPlan::try_new(&decoded, options),
            Err(trust_ir::binary::BinaryProjectionError::BoxDerefRequiresV74)
        ));
    }
    let mut old_header = bytes;
    old_header[8..12]
        .copy_from_slice(&(trust_ir::binary::BOX_DEREF_VALIDITY_FORMAT_VERSION - 1).to_le_bytes());
    assert!(matches!(
        trust_ir::binary::deserialize_module(&old_header),
        Err(trust_ir::binary::BinaryError::InvalidTag(77))
    ));
}

#[test]
fn make_closure_golden_is_valid_executes_and_refuses_an_older_header() {
    let expected = generate::build_make_closure().expect("runtime closure fixture");
    let bytes = fs::read(fixtures_dir().join("make_closure.tmbc")).expect("committed v63 fixture");
    let (decoded, version) = trust_ir::binary::deserialize_module_with_wire_version(&bytes)
        .expect("decode runtime closure construction");
    assert_eq!(version.get(), trust_ir::binary::MAKE_CLOSURE_FORMAT_VERSION);
    assert_eq!(decoded, expected);
    assert!(trust_ir_build::validate_module(&decoded).is_empty());
    let actual = trust_ir::interpret::Interpreter::with_module(&decoded)
        .execute_func(FuncId::new(1), [])
        .expect("apply the constructed two-capture closure");
    assert_eq!(actual.returns.len(), 1);
    assert_eq!(actual.returns[0].as_int().unwrap().as_signed(), 24);
    for body in [
        trust_ir::binary::ModuleBinaryBody::RawV38,
        trust_ir::binary::ModuleBinaryBody::CanonicalV38,
    ] {
        let options = trust_ir::binary::ModuleBinaryOptions {
            body,
            ..Default::default()
        };
        assert!(matches!(
            trust_ir::binary::ProjectedModuleBinaryPlan::try_new(&decoded, options),
            Err(trust_ir::binary::BinaryProjectionError::MakeClosureRequiresV63)
        ));
    }
    let mut old_header = bytes;
    old_header[8..12]
        .copy_from_slice(&(trust_ir::binary::MAKE_CLOSURE_FORMAT_VERSION - 1).to_le_bytes());
    assert!(trust_ir::binary::deserialize_module(&old_header).is_err());
}

/// A `tensor<i32, 2>` interpreter value of extents `dims` holding `elems` in
/// row-major order.
fn i32_matrix(dims: [u64; 2], elems: &[i128]) -> InterpretValue {
    InterpretValue {
        ty: Ty::Tensor(Box::new(Ty::I32), 2),
        kind: InterpretValueKind::Tensor {
            dims: dims.to_vec(),
            elems: trust_ir::ArrayValue::from_vec(
                elems
                    .iter()
                    .map(|&e| InterpretValue::int(Ty::I32, e).expect("an i32 element"))
                    .collect(),
            ),
        },
    }
}

#[test]
fn tensor_contract_golden_is_valid_executes_and_refuses_an_older_header() {
    let expected = generate::build_tensor_contract().expect("tensor contraction fixture");
    let bytes =
        fs::read(fixtures_dir().join("tensor_contract.tmbc")).expect("committed tensor fixture");
    let (decoded, version) = trust_ir::binary::deserialize_module_with_wire_version(&bytes)
        .expect("decode the tensor contraction");
    assert_eq!(version.get(), trust_ir::binary::TENSOR_FORMAT_VERSION);
    assert_eq!(decoded, expected);
    assert!(trust_ir_build::validate_module(&decoded).is_empty());
    // [[1, 2, 3], [4, 5, 6]] x [[7, 8], [9, 10], [11, 12]].
    let actual = Interpreter::with_module(&decoded)
        .execute_func(
            FuncId::new(0),
            [
                i32_matrix([2, 3], &[1, 2, 3, 4, 5, 6]),
                i32_matrix([3, 2], &[7, 8, 9, 10, 11, 12]),
            ],
        )
        .expect("multiply a 2x3 by a 3x2 integer matrix");
    assert_eq!(actual.returns.len(), 1);
    assert_eq!(actual.returns[0].ty, Ty::Tensor(Box::new(Ty::I32), 2));
    let InterpretValueKind::Tensor { dims, elems } = &actual.returns[0].kind else {
        panic!("a contraction returns a tensor: {:?}", actual.returns[0]);
    };
    assert_eq!(dims, &[2, 2]);
    let elems: Vec<i128> = elems
        .iter()
        .map(|e| e.as_int().expect("an integer element").as_signed())
        .collect();
    assert_eq!(elems, [58, 64, 139, 154]);
    // The contracted axes' extents disagree (3 against 2): shape agreement
    // is a precondition, so this is undefined behaviour, never a type error.
    let mismatch = Interpreter::with_module(&decoded)
        .execute_func(
            FuncId::new(0),
            [
                i32_matrix([2, 3], &[1, 2, 3, 4, 5, 6]),
                i32_matrix([2, 3], &[1, 2, 3, 4, 5, 6]),
            ],
        )
        .expect_err("paired axes of different extents");
    assert_eq!(
        mismatch.code,
        trust_ir::InterpretErrorCode::UndefinedBehavior
    );
    assert_eq!(
        mismatch.message,
        "tensor contraction: paired axes have different extents"
    );
    for body in [
        trust_ir::binary::ModuleBinaryBody::RawV38,
        trust_ir::binary::ModuleBinaryBody::CanonicalV38,
    ] {
        let options = trust_ir::binary::ModuleBinaryOptions {
            body,
            ..Default::default()
        };
        assert!(matches!(
            trust_ir::binary::ProjectedModuleBinaryPlan::try_new(&decoded, options),
            Err(trust_ir::binary::BinaryProjectionError::TensorRequiresV67)
        ));
    }
    let mut old_header = bytes;
    old_header[8..12].copy_from_slice(&(trust_ir::binary::TENSOR_FORMAT_VERSION - 1).to_le_bytes());
    assert!(trust_ir::binary::deserialize_module(&old_header).is_err());
}

fn i32_tensor(dims: &[u64], values: &[i128]) -> InterpretValue {
    InterpretValue {
        ty: Ty::Tensor(Box::new(Ty::I32), dims.len() as u32),
        kind: InterpretValueKind::Tensor {
            dims: dims.to_vec(),
            elems: trust_ir::ArrayValue::from_vec(
                values
                    .iter()
                    .map(|&x| InterpretValue::int(Ty::I32, x).expect("an i32 element"))
                    .collect(),
            ),
        },
    }
}

#[test]
fn tensor_map_reduce_view_golden_is_valid_executes_and_refuses_an_older_header() {
    let expected =
        generate::build_tensor_map_reduce_view().expect("tensor map/reduce/view fixture");
    let bytes = fs::read(fixtures_dir().join("tensor_map_reduce_view.tmbc"))
        .expect("committed tensor map/reduce/view fixture");
    let (decoded, version) = trust_ir::binary::deserialize_module_with_wire_version(&bytes)
        .expect("decode the tensor map/reduce/view chain");
    assert_eq!(
        version.get(),
        trust_ir::binary::TENSOR_MAP_REDUCE_VIEW_FORMAT_VERSION
    );
    assert_eq!(decoded, expected);
    assert!(trust_ir_build::validate_module(&decoded).is_empty());
    // a + b = [[3, -5, 200], [-1, -2, 0]]; negated [[-3, 5, -200], [1, 2,
    // 0]]; relu [[0, 5, 0], [1, 2, 0]]; i8 round trip unchanged; row sums
    // [5, 3]; padded by two 9s: [9, 9, 5, 3].
    let run = |a: &[i128], b: &[i128], p: i128| {
        Interpreter::with_module(&decoded).execute_func(
            FuncId::new(0),
            [
                i32_tensor(&[2, 3], a),
                i32_tensor(&[2, 3], b),
                InterpretValue::int(Ty::Usize, p).expect("a usize"),
                InterpretValue::int(Ty::I32, 9).expect("an i32"),
            ],
        )
    };
    let actual =
        run(&[1, -2, 100, 0, -1, 7], &[2, -3, 100, -1, -1, -7], 2).expect("map, reduce and pad");
    assert_eq!(actual.returns.len(), 1);
    assert_eq!(actual.returns[0].ty, Ty::Tensor(Box::new(Ty::I32), 1));
    let InterpretValueKind::Tensor { dims, elems } = &actual.returns[0].kind else {
        panic!("a view returns a tensor: {:?}", actual.returns[0]);
    };
    assert_eq!(dims, &[4]);
    let elems: Vec<i128> = elems
        .iter()
        .map(|e| e.as_int().expect("an integer element").as_signed())
        .collect();
    assert_eq!(elems, [9, 9, 5, 3]);
    // -(-200) = 200 survives the relu and wraps through i8 to -56.
    let wrapped = run(&[-100, 0, 0, 0, 0, 0], &[-100, 0, 0, 0, 0, 0], 0).expect("wrap");
    let InterpretValueKind::Tensor { elems, .. } = &wrapped.returns[0].kind else {
        panic!("a tensor");
    };
    let elems: Vec<i128> = elems
        .iter()
        .map(|e| e.as_int().expect("an integer element").as_signed())
        .collect();
    assert_eq!(elems, [-56, 0]);
    // The operands' extents disagree: a precondition, so undefined
    // behaviour, never a type error.
    let mismatch = Interpreter::with_module(&decoded)
        .execute_func(
            FuncId::new(0),
            [
                i32_tensor(&[2, 3], &[0; 6]),
                i32_tensor(&[3, 2], &[0; 6]),
                InterpretValue::int(Ty::Usize, 0).expect("a usize"),
                InterpretValue::int(Ty::I32, 0).expect("an i32"),
            ],
        )
        .expect_err("operands of different extents");
    assert_eq!(
        (mismatch.code, mismatch.message.as_str()),
        (
            trust_ir::InterpretErrorCode::UndefinedBehavior,
            "tensor map: operand extents differ"
        )
    );
    for body in [
        trust_ir::binary::ModuleBinaryBody::RawV38,
        trust_ir::binary::ModuleBinaryBody::CanonicalV38,
    ] {
        let options = trust_ir::binary::ModuleBinaryOptions {
            body,
            ..Default::default()
        };
        assert!(matches!(
            trust_ir::binary::ProjectedModuleBinaryPlan::try_new(&decoded, options),
            Err(trust_ir::binary::BinaryProjectionError::TensorMapReduceViewRequiresV68)
        ));
    }
    // One version down, the reader still knows the tensor type and refuses
    // the map at its Inst tag.
    let mut old_header = bytes;
    old_header[8..12].copy_from_slice(
        &(trust_ir::binary::TENSOR_MAP_REDUCE_VIEW_FORMAT_VERSION - 1).to_le_bytes(),
    );
    assert_eq!(
        trust_ir::binary::deserialize_module(&old_header),
        Err(trust_ir::binary::BinaryError::InvalidTag(72))
    );
}

/// An integer tensor of `elem` with extents `dims` and the row-major
/// `values`.
fn int_tensor(elem: &Ty, dims: &[u64], values: &[i128]) -> InterpretValue {
    InterpretValue {
        ty: Ty::Tensor(Box::new(elem.clone()), dims.len() as u32),
        kind: InterpretValueKind::Tensor {
            dims: dims.to_vec(),
            elems: trust_ir::ArrayValue::from_vec(
                values
                    .iter()
                    .map(|&x| InterpretValue::int(elem.clone(), x).expect("an integer element"))
                    .collect(),
            ),
        },
    }
}

#[test]
fn tensor_weight_blob_golden_is_valid_executes_and_refuses_an_older_header() {
    let expected = generate::build_tensor_weight_blob().expect("tensor weight blob fixture");
    let bytes = fs::read(fixtures_dir().join("tensor_weight_blob.tmbc"))
        .expect("committed tensor weight blob fixture");
    let (decoded, version) = trust_ir::binary::deserialize_module_with_wire_version(&bytes)
        .expect("decode the tensor weight blobs");
    assert_eq!(version.get(), trust_ir::binary::TENSOR_BLOB_FORMAT_VERSION);
    assert_eq!(decoded, expected);
    assert_eq!(decoded.blobs.len(), 2, "two functions share one row");
    assert!(trust_ir_build::validate_module(&decoded).is_empty());
    let interp = Interpreter::with_module(&decoded);
    // x · w = 3·1 + 4·2 + 5·(-1).
    let dot = interp
        .execute_func(FuncId::new(0), [int_tensor(&Ty::I32, &[3], &[3, 4, 5])])
        .expect("the dot product");
    assert_eq!(dot.returns, [int_tensor(&Ty::I32, &[], &[6])]);
    let raw = interp
        .execute_func(FuncId::new(1), [])
        .expect("the weights as bytes");
    assert_eq!(
        raw.returns,
        [int_tensor(
            &Ty::U8,
            &[12],
            &[1, 0, 0, 0, 2, 0, 0, 0, 255, 255, 255, 255]
        )]
    );
    let none = interp
        .execute_func(FuncId::new(2), [])
        .expect("no elements");
    assert_eq!(none.returns, [int_tensor(&Ty::I64, &[0], &[])]);
    // A contraction over extents that differ from the blob's is undefined
    // behaviour, never a type error.
    let mismatch = interp
        .execute_func(FuncId::new(0), [int_tensor(&Ty::I32, &[2], &[3, 4])])
        .expect_err("paired extents differ");
    assert_eq!(
        mismatch.code,
        trust_ir::InterpretErrorCode::UndefinedBehavior
    );
    for body in [
        trust_ir::binary::ModuleBinaryBody::RawV38,
        trust_ir::binary::ModuleBinaryBody::CanonicalV38,
    ] {
        let options = trust_ir::binary::ModuleBinaryOptions {
            body,
            ..Default::default()
        };
        assert!(matches!(
            trust_ir::binary::ProjectedModuleBinaryPlan::try_new(&decoded, options),
            Err(trust_ir::binary::BinaryProjectionError::TensorBlobRequiresV70)
        ));
    }
    // One version down, the reader refuses the constant at its tag.
    let mut old_header = bytes;
    old_header[8..12]
        .copy_from_slice(&(trust_ir::binary::TENSOR_BLOB_FORMAT_VERSION - 1).to_le_bytes());
    assert_eq!(
        trust_ir::binary::deserialize_module(&old_header),
        Err(trust_ir::binary::BinaryError::InvalidTag(18))
    );
}

#[test]
fn tensor_gather_scatter_golden_is_valid_executes_and_refuses_an_older_header() {
    let expected = generate::build_tensor_gather_scatter().expect("tensor gather/scatter fixture");
    let bytes = fs::read(fixtures_dir().join("tensor_gather_scatter.tmbc"))
        .expect("committed tensor gather/scatter fixture");
    let (decoded, version) = trust_ir::binary::deserialize_module_with_wire_version(&bytes)
        .expect("decode the tensor gather/scatter chain");
    assert_eq!(
        version.get(),
        trust_ir::binary::TENSOR_GATHER_SCATTER_FORMAT_VERSION
    );
    assert_eq!(decoded, expected);
    assert!(trust_ir_build::validate_module(&decoded).is_empty());
    let run = |rows: &[i128], cols: &[i128], at: &[i128]| {
        let n = rows.len() as u64;
        Interpreter::with_module(&decoded).execute_func(
            FuncId::new(0),
            [
                int_tensor(&Ty::I32, &[2, 3], &[1, 2, 3, 4, 5, 6]),
                int_tensor(&Ty::I64, &[n], rows),
                int_tensor(&Ty::U8, &[cols.len() as u64], cols),
                int_tensor(&Ty::I32, &[4], &[0, 0, 0, 0]),
                int_tensor(&Ty::Usize, &[at.len() as u64], at),
            ],
        )
    };
    // The gather reads [6, 1, 5] at (1, 2), (0, 0), (1, 1); the scatter
    // writes them at 3, 0, 3, so position 3 holds the row-major-last, 5.
    let actual = run(&[1, 0, 1], &[2, 0, 1], &[3, 0, 3]).expect("gather, then scatter");
    assert_eq!(actual.returns.len(), 1);
    assert_eq!(actual.returns[0].ty, Ty::Tensor(Box::new(Ty::I32), 1));
    let InterpretValueKind::Tensor { dims, elems } = &actual.returns[0].kind else {
        panic!("a scatter returns a tensor: {:?}", actual.returns[0]);
    };
    assert_eq!(dims, &[4]);
    let elems: Vec<i128> = elems
        .iter()
        .map(|e| e.as_int().expect("an integer element").as_signed())
        .collect();
    assert_eq!(elems, [1, 0, 0, 5]);
    // A negative row is outside its axis: a precondition, so undefined
    // behaviour, never a type error.
    let outside = run(&[-1, 0, 1], &[2, 0, 1], &[3, 0, 3]).expect_err("a negative coordinate");
    assert_eq!(
        (outside.code, outside.message.as_str()),
        (
            trust_ir::InterpretErrorCode::UndefinedBehavior,
            "tensor gather: a coordinate is outside its axis"
        )
    );
    for body in [
        trust_ir::binary::ModuleBinaryBody::RawV38,
        trust_ir::binary::ModuleBinaryBody::CanonicalV38,
    ] {
        let options = trust_ir::binary::ModuleBinaryOptions {
            body,
            ..Default::default()
        };
        assert!(matches!(
            trust_ir::binary::ProjectedModuleBinaryPlan::try_new(&decoded, options),
            Err(trust_ir::binary::BinaryProjectionError::TensorGatherScatterRequiresV69)
        ));
    }
    // One version down, the reader still knows the tensor type and refuses
    // the gather at its Inst tag.
    let mut old_header = bytes;
    old_header[8..12].copy_from_slice(
        &(trust_ir::binary::TENSOR_GATHER_SCATTER_FORMAT_VERSION - 1).to_le_bytes(),
    );
    assert_eq!(
        trust_ir::binary::deserialize_module(&old_header),
        Err(trust_ir::binary::BinaryError::InvalidTag(75))
    );
}

#[test]
fn storage_only_golden_has_exact_parent_geometry_and_no_value_authority() {
    let name = "storage_only";
    let module = generate::build_storage_only().expect("storage geometry fixture");
    let root = module
        .functions
        .iter()
        .find(|function| function.id == FuncId::new(0))
        .expect("storage fixture root");
    assert_eq!(root.body_gate, Some(trust_ir::BodyGate::Ungated));
    let dir = fixtures_dir();
    let bytes = roundtrip_binary(name, &module);
    assert_eq!(
        module.functions[0].body_gate,
        Some(trust_ir::BodyGate::Ungated)
    );
    assert!(module.proof_obligations.is_empty());
    assert!(module.proof_certificates.is_empty());
    let (decoded, wire_version) =
        trust_ir::binary::deserialize_module_with_wire_version(&bytes).unwrap();
    assert!(trust_ir_build::validate::decoded_provenance_errors(&decoded, wire_version).is_empty());
    assert_or_update_bytes(&dir.join("storage_only.tmbc"), &bytes);
    assert_or_update_text(
        &dir.join("storage_only.trust_ir"),
        &roundtrip_text(name, &module),
    );
    assert_or_update_text(
        &dir.join("storage_only.json"),
        &roundtrip_json(name, &module),
    );
    assert_or_update_bytes(
        &dir.join("storage_only.msgpack"),
        &roundtrip_msgpack(name, &module),
    );
    assert_eq!(
        u32::from_le_bytes(bytes[8..12].try_into().unwrap()),
        trust_ir::binary::STORAGE_LAYOUT_FORMAT_VERSION
    );
    assert!(trust_ir_build::validate_module(&module).is_empty());
    assert_eq!(
        module
            .struct_field_offset_bits(trust_ir::StructId::new(0), 2)
            .unwrap(),
        704
    );
    let actual = trust_ir::interpret::Interpreter::with_module(&module)
        .execute_func(FuncId::new(0), [])
        .unwrap();
    assert_eq!(actual.returns[0].as_int().unwrap().as_unsigned(), 7);
    assert_eq!(actual.host_calls, 0);
    let mut old = bytes;
    old[8..12].copy_from_slice(&63_u32.to_le_bytes());
    assert!(trust_ir::binary::deserialize_module(&old).is_err());
    for body in [
        trust_ir::binary::ModuleBinaryBody::RawV38,
        trust_ir::binary::ModuleBinaryBody::CanonicalV38,
    ] {
        let options = trust_ir::binary::ModuleBinaryOptions {
            body,
            ..Default::default()
        };
        assert!(matches!(
            trust_ir::binary::ProjectedModuleBinaryPlan::try_new(&module, options),
            Err(trust_ir::binary::BinaryProjectionError::StorageRequiresV64)
        ));
    }
    for (size, align, tail) in [(95, 8, 88), (96, 4, 88), (96, 8, 80)] {
        let mut bad = module.clone();
        bad.structs[0].size = Some(size);
        bad.structs[0].align = Some(align);
        bad.structs[0].fields[2].offset = Some(tail);
        assert!(
            bad.ty_layout_shape(&Ty::Struct(trust_ir::StructId::new(0)))
                .is_err()
        );
    }
    let mut bad = module;
    bad.func_types[0]
        .params
        .push(Ty::Struct(trust_ir::StructId::new(0)));
    assert!(bad.first_storage_violation().is_some());
}

/// Selective maintained generation writes only this new fixture's four files;
/// ordinary corpus replay still compares every old golden unchanged.
#[test]
fn closure_frame_origin_goldens_replay() {
    let name = "closure_frame_origin";
    let module = generate::build_closure_frame_origin().expect("origin fixture builds");
    assert!(trust_ir_build::validate_module(&module).is_empty());
    assert!(
        module.functions.is_empty(),
        "frame data grants no body/codegen license"
    );
    assert!(
        module
            .closure_storage_binding(trust_ir::ClosureTyId::new(0))
            .is_err(),
        "a nominal origin must not invent a callable target"
    );
    let bytes = roundtrip_binary(name, &module);
    assert_eq!(u32::from_le_bytes(bytes[8..12].try_into().unwrap()), 66);
    let dir = fixtures_dir();
    assert_or_update_bytes(&dir.join(format!("{name}.tmbc")), &bytes);
    assert_or_update_text(
        &dir.join(format!("{name}.trust_ir")),
        &roundtrip_text(name, &module),
    );
    assert_or_update_text(
        &dir.join(format!("{name}.json")),
        &roundtrip_json(name, &module),
    );
    assert_or_update_bytes(
        &dir.join(format!("{name}.msgpack")),
        &roundtrip_msgpack(name, &module),
    );
    let decoded = trust_ir::binary::deserialize_module(&bytes).expect("origin golden decodes");
    assert_eq!(decoded, module);
    assert!(trust_ir_build::validate_module(&decoded).is_empty());
    let (_, wire_version) = trust_ir::binary::deserialize_module_with_wire_version(&bytes).unwrap();
    assert!(
        trust_ir_build::validate::decoded_provenance_errors(&decoded, wire_version).is_empty(),
        "the new data-only fixture must not add a producer omission"
    );
    let mut older = bytes.clone();
    older[8..12].copy_from_slice(&65u32.to_le_bytes());
    assert!(
        trust_ir::binary::deserialize_module(&older).is_err(),
        "older header must not admit the origin tail"
    );
    let mut absent = module;
    absent.closure_layouts[0].origin = None;
    let legacy = trust_ir::binary::serialize_module(&absent).unwrap();
    assert_eq!(u32::from_le_bytes(legacy[8..12].try_into().unwrap()), 58);
    assert_eq!(
        trust_ir::binary::deserialize_module(&legacy).unwrap(),
        absent
    );
}
