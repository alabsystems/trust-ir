// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The must-refuse corpus, self-checked (KIND 4, 2026-09-24).
//!
//! `tests/fixtures/refuse/MANIFEST.tsv` lists wire artifacts a conforming
//! consumer must REFUSE, each paired with the trust-ir verdict that names why.
//! Before any consumer sees a row, this file:
//!
//! 1. BYTE-PINS every artifact row as a golden (`<row>.tmbc`, plus `.json` /
//!    `.msgpack` for a module row), through the same update harness as the
//!    round-trip corpus (`TRUST_IR_UPDATE_FIXTURES=1`, then run again);
//! 2. RUNS every pinned verdict against the real trust-ir entry point, on the
//!    module DECODED FROM THE CHECKED-IN BYTES — never on the builder's
//!    in-memory module — so a row cannot rot into an ordinary module, and a
//!    two-verdict row (accepted structurally, refused for codegen) has BOTH
//!    readings measured;
//! 3. holds the corpus EXHAUSTIVE over `ValidationError` and `BinaryError`:
//!    the variant lists are derived from the enum SOURCES (no literal count),
//!    every variant is either exhibited by a manifest verdict or listed by
//!    name in `UNCOVERED.tsv` with a class and a reason, that file is EXACTLY
//!    the uncovered set, and against the merge-base with `origin/main` it only
//!    SHRINKS. A new variant absent from the allowlist fails exactness
//!    anywhere; one ADDED to the allowlist fails the shrink rule wherever git
//!    can answer — live from the commit after the allowlist first reached
//!    `origin/main`, with a fetched `origin/main` (a stale one is an older,
//!    larger ledger: a weaker base, not a vacuous one). Where git cannot
//!    answer (no history, no `origin/main`, or the allowlist not yet on
//!    `origin/main`) the shrink half SAYS it is skipped, and the rule itself
//!    is proved on synthetic ledgers and a fake git beside it
//!    (`shrink_verdict`);
//! 4. pins the CONTROL row: the envelope every module row shares, accepted by
//!    the codegen gate under the license the runner tells a consumer to
//!    recognize and refused without it, so the runner's reason-blindness is
//!    bounded by name rather than silent
//!    (`no_module_row_is_refused_for_the_structural_license_alone`).
//!
//! What this is, on the ladder: TEST-rung evidence. The type-level rung the
//! design asked for (a wildcard-free `match` over every variant, so rustc
//! refuses an unclassified one) is NOT available from this crate:
//! `ValidationError` and `BinaryError` are `#[non_exhaustive]` (measured,
//! `validate.rs:177`, `binary.rs:578`), so a match outside their crates must
//! carry a wildcard arm and proves nothing about coverage. The source-derived
//! census plus the exact, shrink-only allowlist is the strongest mechanical
//! form this crate can give, and it is stated as such.
//!
//! What it does NOT do: it cannot check that a `structural` allowlist class is
//! true (that plain `validate_module` produces the variant) without a value of
//! it; that column is read, and the enforcement-links V census ("named by a
//! test") is the mechanical proxy beside it.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use trust_ir::Module;
use trust_ir::binary::{deserialize_module, serialize_module};
use trust_ir::format::{TextLoss, text_losses};
use trust_ir::inst::Inst;
use trust_ir::proof::{ProofAnnotation, ProofStatus, RejectingModuleProofAuthority};
use trust_ir::ty::Ty;
use trust_ir_build::validate::{
    CodegenAdmission, ValidationConfig, ValidationError, validate_module,
    validate_module_as_decoded, validate_module_complete, validate_module_for_codegen,
    validate_module_for_codegen_with, validate_module_with_authority, validate_module_with_config,
};
use trust_ir_conformance::refuse::{
    Carrier, MANIFEST, ManifestRow, Row, STRUCTURAL_LICENSE_AUTHORITY, Verdict, corpus,
    corpus_from, fixtures_dir, manifest,
};
use trust_ir_conformance::refuse_fixtures as generate;

// ---------------------------------------------------------------------------
// The builder table: one line per artifact row, kept in bijection with the
// manifest by `manifest_and_builders_agree`.
// ---------------------------------------------------------------------------

#[derive(Clone, Copy)]
enum Build {
    Module(fn() -> Result<Module, trust_ir_conformance::fixtures::FixtureError>),
    Bytes(fn() -> Result<Vec<u8>, trust_ir_conformance::fixtures::FixtureError>),
}

const ROWS: &[(&str, Build)] = &[
    (
        "make_closure_capture_count",
        Build::Module(generate::build_refuse_make_closure_capture_count),
    ),
    (
        "tensor_float_element",
        Build::Module(generate::build_refuse_tensor_float_element),
    ),
    (
        "tensor_contract_rank_mismatch",
        Build::Module(generate::build_refuse_tensor_contract_rank_mismatch),
    ),
    (
        "tensor_contract_codegen",
        Build::Module(generate::build_refuse_tensor_contract_codegen),
    ),
    (
        "blob_tensor_below_its_version",
        Build::Bytes(generate::build_refuse_bytes_blob_tensor_below_its_version),
    ),
    (
        "tensor_map_lane_out_of_scope",
        Build::Module(generate::build_refuse_tensor_map_lane_out_of_scope),
    ),
    (
        "tensor_reduce_axes_not_ascending",
        Build::Module(generate::build_refuse_tensor_reduce_axes_not_ascending),
    ),
    (
        "tensor_view_shape_reads_a_coordinate",
        Build::Module(generate::build_refuse_tensor_view_shape_reads_a_coordinate),
    ),
    (
        "tensor_map_reduce_view_codegen",
        Build::Module(generate::build_refuse_tensor_map_reduce_view_codegen),
    ),
    (
        "blob_tensor_map_reduce_view_below_its_version",
        Build::Bytes(generate::build_refuse_bytes_blob_tensor_map_reduce_view_below_its_version),
    ),
    (
        "tensor_gather_coordinate_count_is_not_the_data_rank",
        Build::Module(generate::build_refuse_tensor_gather_coordinate_count_is_not_the_data_rank),
    ),
    (
        "tensor_scatter_init_is_not_the_result_type",
        Build::Module(generate::build_refuse_tensor_scatter_init_is_not_the_result_type),
    ),
    (
        "tensor_gather_scatter_codegen",
        Build::Module(generate::build_refuse_tensor_gather_scatter_codegen),
    ),
    (
        "blob_tensor_gather_scatter_below_its_version",
        Build::Bytes(generate::build_refuse_bytes_blob_tensor_gather_scatter_below_its_version),
    ),
    (
        "tensor_blob_digest_mismatch",
        Build::Module(generate::build_refuse_tensor_blob_digest_mismatch),
    ),
    (
        "tensor_blob_missing",
        Build::Module(generate::build_refuse_tensor_blob_missing),
    ),
    (
        "tensor_blob_extents_do_not_fit_its_bytes",
        Build::Module(generate::build_refuse_tensor_blob_extents_do_not_fit_its_bytes),
    ),
    (
        "tensor_blob_codegen",
        Build::Module(generate::build_refuse_tensor_blob_codegen),
    ),
    (
        "blob_tensor_blob_below_its_version",
        Build::Bytes(generate::build_refuse_bytes_blob_tensor_blob_below_its_version),
    ),
    (
        "blob_tensor_blob_table_not_canonical",
        Build::Bytes(generate::build_refuse_bytes_blob_tensor_blob_table_not_canonical),
    ),
    (
        "signature_abi_duplicate_binding",
        Build::Module(generate::build_refuse_signature_abi_duplicate_binding),
    ),
    (
        "signature_abi_target_disagreement",
        Build::Module(generate::build_refuse_signature_abi_target_disagreement),
    ),
    (
        "signature_abi_function_attribute_disagreement",
        Build::Module(generate::build_refuse_signature_abi_function_attribute_disagreement),
    ),
    (
        "signature_abi_unknown_field",
        Build::Bytes(generate::build_refuse_bytes_signature_abi_unknown_field),
    ),
    (
        "binding_frame_analysis_incomplete",
        Build::Module(generate::build_refuse_binding_frame_analysis_incomplete),
    ),
    (
        "binding_frame_closed_edge",
        Build::Module(generate::build_refuse_binding_frame_closed_edge),
    ),
    (
        "body_gate_ungated",
        Build::Module(generate::build_refuse_body_gate_ungated),
    ),
    (
        "body_gate_omitted_at_contract_surface",
        Build::Module(generate::build_refuse_body_gate_omitted_at_contract_surface),
    ),
    (
        "body_gate_unknown_authority",
        Build::Module(generate::build_refuse_body_gate_unknown_authority),
    ),
    (
        "body_gate_kernel_tv_without_certificate",
        Build::Module(generate::build_refuse_body_gate_kernel_tv_without_certificate),
    ),
    (
        "body_gate_refuted_by_failed_tv",
        Build::Module(generate::build_refuse_body_gate_refuted_by_failed_tv),
    ),
    (
        "body_gate_evidence_stale_body_digest",
        Build::Module(generate::build_refuse_body_gate_evidence_stale_body_digest),
    ),
    (
        "body_gate_kernel_tv_evidence_unrecorded",
        Build::Module(generate::build_refuse_body_gate_kernel_tv_evidence_unrecorded),
    ),
    (
        "control_licensed_identity",
        Build::Module(generate::build_refuse_control_licensed_identity),
    ),
    (
        "global_asm_block",
        Build::Module(generate::build_refuse_global_asm_block),
    ),
    (
        "dealloc_instruction",
        Build::Module(generate::build_refuse_dealloc_instruction),
    ),
    (
        "rust_reference_as_permission_borrow",
        Build::Module(generate::build_refuse_rust_reference_as_permission_borrow),
    ),
    (
        "sequence_element_op",
        Build::Module(generate::build_refuse_sequence_element_op),
    ),
    (
        "dialect_op_foreign_namespace",
        Build::Module(generate::build_refuse_dialect_op_foreign_namespace),
    ),
    (
        "unbacked_claim_on_check",
        Build::Module(generate::build_refuse_unbacked_claim_on_check),
    ),
    (
        "assert_panic_kind_unspecified",
        Build::Module(generate::build_refuse_assert_panic_kind_unspecified),
    ),
    (
        "assert_panic_site_missing",
        Build::Module(generate::build_refuse_assert_panic_site_missing),
    ),
    (
        "assert_panic_site_entry_signature",
        Build::Module(generate::build_refuse_assert_panic_site_entry_signature),
    ),
    (
        "assert_panic_location_non_canonical",
        Build::Module(generate::build_refuse_assert_panic_location_non_canonical),
    ),
    (
        "assert_panic_location_global_mutable",
        Build::Module(generate::build_refuse_assert_panic_location_global_mutable),
    ),
    (
        "assert_invoke_unwind_dest_without_landing_pad",
        Build::Module(generate::build_refuse_assert_invoke_unwind_dest_without_landing_pad),
    ),
    // Amendment D (§20): executable drops.
    (
        "drop_unresolved",
        Build::Module(generate::build_refuse_drop_unresolved),
    ),
    (
        "drop_glue_invalid",
        Build::Module(generate::build_refuse_drop_glue_invalid),
    ),
    (
        "drop_glue_called_directly",
        Build::Module(generate::build_refuse_drop_glue_called_directly),
    ),
    (
        "drop_invoke_unwind_dest_without_landing_pad",
        Build::Module(generate::build_refuse_drop_invoke_unwind_dest_without_landing_pad),
    ),
    (
        "invoke_indirect_unwind_dest_without_landing_pad",
        Build::Module(generate::build_refuse_invoke_indirect_unwind_dest_without_landing_pad),
    ),
    (
        "import_backed_summary_unauthenticated",
        Build::Module(generate::build_refuse_import_backed_summary_unauthenticated),
    ),
    (
        "completeness_unclaimed",
        Build::Module(generate::build_refuse_completeness_unclaimed),
    ),
    (
        "tainted_value_reaches_sink",
        Build::Module(generate::build_refuse_tainted_value_reaches_sink),
    ),
    (
        "custom_obligation_unpinned_namespace",
        Build::Module(generate::build_refuse_custom_obligation_unpinned_namespace),
    ),
    (
        "formula_smtlib_rendering_disagrees",
        Build::Module(generate::build_refuse_formula_smtlib_rendering_disagrees),
    ),
    (
        "summary_clause_smtlib_rendering_disagrees",
        Build::Module(generate::build_refuse_summary_clause_smtlib_rendering_disagrees),
    ),
    (
        "summary_clause_param_pointee_of_by_value_param",
        Build::Module(generate::build_refuse_summary_clause_param_pointee_of_by_value_param),
    ),
    (
        "spec_carrier_smtlib_rendering_disagrees",
        Build::Module(generate::build_refuse_spec_carrier_smtlib_rendering_disagrees),
    ),
    (
        "pred_citation_rendering_disagrees",
        Build::Module(generate::build_refuse_pred_citation_rendering_disagrees),
    ),
    (
        "function_symbol_synthetic_shadowed",
        Build::Module(generate::build_refuse_function_symbol_synthetic_shadowed),
    ),
    (
        "enum_tag_lane_off_scalar_table",
        Build::Module(generate::build_refuse_enum_tag_lane_off_scalar_table),
    ),
    (
        "dialect_type_created_by_load",
        Build::Module(generate::build_refuse_dialect_type_created_by_load),
    ),
    (
        "storage_by_value_signature",
        Build::Module(generate::build_refuse_storage_by_value_signature),
    ),
    (
        "handle_runtime_unpinned",
        Build::Module(generate::build_refuse_handle_runtime_unpinned),
    ),
    (
        "extern_weak_direct_call",
        Build::Module(generate::build_refuse_extern_weak_direct_call),
    ),
    (
        "extern_weak_as_fn_def",
        Build::Module(generate::build_refuse_extern_weak_as_fn_def),
    ),
    (
        "certified_with_empty_kernel_term",
        Build::Module(generate::build_refuse_certified_with_empty_kernel_term),
    ),
    (
        "source_provenance_stale_body_digest",
        Build::Module(generate::build_refuse_source_provenance_stale_body_digest),
    ),
    (
        "duplicate_enum_id",
        Build::Module(generate::build_refuse_duplicate_enum_id),
    ),
    (
        "func_type_out_of_range",
        Build::Module(generate::build_refuse_func_type_out_of_range),
    ),
    (
        "ptr_data_of_non_pointer",
        Build::Module(generate::build_refuse_ptr_data_of_non_pointer),
    ),
    (
        "effect_summary_uncovered_write",
        Build::Module(generate::build_refuse_effect_summary_uncovered_write),
    ),
    (
        "trusted_status_row",
        Build::Module(generate::build_refuse_trusted_status_row),
    ),
    (
        "struct_passing_unclassified_by_value_aggregate",
        Build::Module(generate::build_refuse_struct_passing_unclassified_by_value_aggregate),
    ),
    (
        "struct_passing_always_memory_by_value_aggregate",
        Build::Module(generate::build_refuse_struct_passing_always_memory_by_value_aggregate),
    ),
    (
        "struct_passing_native_c_pass_mode_contradicts_target",
        Build::Module(generate::build_refuse_struct_passing_native_c_pass_mode_contradicts_target),
    ),
    (
        "struct_passing_unclassified_refined_aggregate",
        Build::Module(generate::build_refuse_struct_passing_unclassified_refined_aggregate),
    ),
    (
        "struct_passing_unclassified_vector_by_value",
        Build::Module(generate::build_refuse_struct_passing_unclassified_vector_by_value),
    ),
    (
        "struct_passing_unclassified_closure_by_value",
        Build::Module(generate::build_refuse_struct_passing_unclassified_closure_by_value),
    ),
    (
        "narrow_arg_ext_unrecorded_darwin",
        Build::Module(generate::build_refuse_narrow_arg_ext_unrecorded_darwin),
    ),
    (
        "calling_conv_c_unwind_definition",
        Build::Module(generate::build_refuse_calling_conv_c_unwind_definition),
    ),
    (
        "target_feature_unknown",
        Build::Module(generate::build_refuse_target_feature_unknown),
    ),
    (
        "region_havoc_store",
        Build::Module(generate::build_refuse_region_havoc_store),
    ),
    (
        "undef_fresh_havoc_feeds_assume",
        Build::Module(generate::build_refuse_undef_fresh_havoc_feeds_assume),
    ),
    (
        "array_splat_non_array_type",
        Build::Module(generate::build_refuse_array_splat_non_array_type),
    ),
    (
        "uniform_array_spelled_as_list",
        Build::Module(generate::build_refuse_uniform_array_spelled_as_list),
    ),
    (
        "switch_case_negative_at_unsigned",
        Build::Module(generate::build_refuse_switch_case_negative_at_unsigned),
    ),
    (
        "switch_case_above_signed_max",
        Build::Module(generate::build_refuse_switch_case_above_signed_max),
    ),
    (
        "switch_case_negative_at_refined_unsigned",
        Build::Module(generate::build_refuse_switch_case_negative_at_refined_unsigned),
    ),
    (
        "switch_case_usize_beyond_target_width",
        Build::Module(generate::build_refuse_switch_case_usize_beyond_target_width),
    ),
    (
        "switch_case_isize_beyond_target_width",
        Build::Module(generate::build_refuse_switch_case_isize_beyond_target_width),
    ),
    (
        "const_usize_beyond_target_width",
        Build::Module(generate::build_refuse_const_usize_beyond_target_width),
    ),
    (
        "unop_not_scalar_bool",
        Build::Module(generate::build_refuse_unop_not_scalar_bool),
    ),
    (
        "type_origin_claimed_twice",
        Build::Module(generate::build_refuse_type_origin_claimed_twice),
    ),
    (
        "blob_ambiguous_lineage_header",
        Build::Bytes(generate::build_refuse_bytes_blob_ambiguous_lineage_header),
    ),
    (
        "blob_bad_magic",
        Build::Bytes(generate::build_refuse_bytes_blob_bad_magic),
    ),
    (
        "blob_truncated",
        Build::Bytes(generate::build_refuse_bytes_blob_truncated),
    ),
    (
        "blob_trailing_bytes",
        Build::Bytes(generate::build_refuse_bytes_blob_trailing_bytes),
    ),
    (
        "blob_pool_count_exceeds_input",
        Build::Bytes(generate::build_refuse_bytes_blob_pool_count_exceeds_input),
    ),
    (
        "template_blob_is_not_a_module",
        Build::Bytes(generate::build_refuse_bytes_template_blob_is_not_a_module),
    ),
    (
        "ty_ext_tag_under_module_magic",
        Build::Bytes(generate::build_refuse_bytes_ty_ext_tag_under_module_magic),
    ),
    (
        "constant_ext_tag_under_module_magic",
        Build::Bytes(generate::build_refuse_bytes_constant_ext_tag_under_module_magic),
    ),
    (
        "blob_varint_overflow",
        Build::Bytes(generate::build_refuse_bytes_blob_varint_overflow),
    ),
    (
        "blob_string_id_out_of_pool",
        Build::Bytes(generate::build_refuse_bytes_blob_string_id_out_of_pool),
    ),
    (
        "blob_pool_string_not_utf8",
        Build::Bytes(generate::build_refuse_bytes_blob_pool_string_not_utf8),
    ),
    (
        "blob_feature_tag_below_its_version",
        Build::Bytes(generate::build_refuse_bytes_blob_feature_tag_below_its_version),
    ),
    (
        "blob_call_boundary_below_its_version",
        Build::Bytes(generate::build_refuse_bytes_blob_call_boundary_below_its_version),
    ),
    (
        "blob_indirect_call_boundary_below_its_version",
        Build::Bytes(generate::build_refuse_bytes_blob_indirect_call_boundary_below_its_version),
    ),
    (
        "blob_param_pointee_place_below_its_version",
        Build::Bytes(generate::build_refuse_bytes_blob_param_pointee_place_below_its_version),
    ),
    (
        "blob_param_flag_bit_below_its_version",
        Build::Bytes(generate::build_refuse_bytes_blob_param_flag_bit_below_its_version),
    ),
    (
        "blob_tuple_layout_incoherent",
        Build::Bytes(generate::build_refuse_bytes_blob_tuple_layout_incoherent),
    ),
    (
        "blob_panic_location_tag_unknown",
        Build::Bytes(generate::build_refuse_bytes_blob_panic_location_tag_unknown),
    ),
    (
        "blob_drop_glue_not_canonical",
        Build::Bytes(generate::build_refuse_bytes_blob_drop_glue_not_canonical),
    ),
];

// ---------------------------------------------------------------------------
// Golden harness (the same discipline as conformance.rs).
// ---------------------------------------------------------------------------

fn update_mode() -> bool {
    std::env::var("TRUST_IR_UPDATE_FIXTURES")
        .map(|v| !v.is_empty())
        .unwrap_or(false)
}

fn assert_or_update_bytes(path: &Path, got: &[u8]) {
    if update_mode() {
        fs::create_dir_all(path.parent().unwrap()).expect("create fixture dir");
        fs::write(path, got).expect("write fixture");
        return;
    }
    let expected = fs::read(path).unwrap_or_else(|e| {
        panic!(
            "missing fixture {}: {e}. Run `TRUST_IR_UPDATE_FIXTURES=1 targo --unverified test -p \
             trust-ir-conformance --test refuse_corpus`, then run again.",
            path.display()
        )
    });
    assert!(
        expected == got,
        "byte-level mismatch for refuse fixture {}: got {} bytes, expected {}. A refuse row is \
         a frozen wire artifact; if the change is intentional, regenerate with \
         `TRUST_IR_UPDATE_FIXTURES=1` and review the diff.",
        path.display(),
        got.len(),
        expected.len()
    );
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// Whether this tree is a public snapshot (no `docs/`, no `CLAUDE.md`): the
/// obligation files under `docs/` are not exported there.
fn is_public_snapshot() -> bool {
    let root = repo_root();
    !root.join("docs").exists() && !root.join("CLAUDE.md").exists()
}

/// The variant name of a `Debug`-rendered enum value: the leading identifier.
fn variant_name(value: &impl std::fmt::Debug) -> String {
    let text = format!("{value:?}");
    text.split([' ', '(', '{']).next().unwrap_or("").to_string()
}

fn manifest_by_id() -> BTreeMap<String, ManifestRow> {
    manifest()
        .expect("the must-refuse manifest parses")
        .into_iter()
        .map(|r| (r.id.clone(), r))
        .collect()
}

// ---------------------------------------------------------------------------
// 1. goldens
// ---------------------------------------------------------------------------

#[test]
fn goldens_pin_every_artifact_row() {
    let dir = fixtures_dir();
    for (id, build) in ROWS {
        match build {
            Build::Module(build) => {
                let module = build().unwrap_or_else(|e| panic!("{id}: the builder refused: {e}"));
                let bytes = serialize_module(&module).expect("serialize_module: test fixture");
                let decoded = deserialize_module(&bytes)
                    .unwrap_or_else(|e| panic!("{id}: a module row must decode: {e}"));
                assert_eq!(
                    serialize_module(&decoded).expect("serialize_module: test fixture"),
                    bytes,
                    "{id}: the decoded module must re-encode to the same bytes"
                );
                assert_or_update_bytes(&dir.join(format!("{id}.tmbc")), &bytes);
                // The serde goldens pin what a consumer DECODES, so the three
                // carriers of one row are one module.
                let json = serde_json::to_string_pretty(&decoded).unwrap();
                assert_or_update_bytes(&dir.join(format!("{id}.json")), json.as_bytes());
                let back: Module = serde_json::from_str(&json).expect("JSON round trip");
                assert_eq!(back, decoded, "{id}: JSON drift");
                let msgpack = rmp_serde::to_vec(&decoded).unwrap();
                assert_or_update_bytes(&dir.join(format!("{id}.msgpack")), &msgpack);
                let back: Module = rmp_serde::from_slice(&msgpack).expect("MessagePack round trip");
                assert_eq!(back, decoded, "{id}: MessagePack drift");
            }
            Build::Bytes(build) => {
                let bytes = build().unwrap_or_else(|e| panic!("{id}: the builder refused: {e}"));
                assert!(
                    deserialize_module(&bytes).is_err(),
                    "{id}: poisoned bytes must not decode"
                );
                assert_or_update_bytes(&dir.join(format!("{id}.tmbc")), &bytes);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// 2. the manifest and the builder table are one list; the directory is exact
// ---------------------------------------------------------------------------

#[test]
fn manifest_and_builders_agree_and_the_directory_is_exact() {
    let rows = manifest_by_id();
    let table: BTreeMap<&str, &Build> = ROWS.iter().map(|(id, b)| (*id, b)).collect();
    for (id, row) in &rows {
        match row.carrier {
            Carrier::None => assert!(
                !table.contains_key(id.as_str()),
                "{id}: a `none` row has no builder"
            ),
            Carrier::Module | Carrier::Control => assert!(
                matches!(table.get(id.as_str()), Some(Build::Module(_))),
                "{id}: a `module` / `control` row needs a `Build::Module` line in ROWS"
            ),
            Carrier::Bytes => assert!(
                matches!(table.get(id.as_str()), Some(Build::Bytes(_))),
                "{id}: a `bytes` row needs a `Build::Bytes` line in ROWS"
            ),
        }
    }
    for id in table.keys() {
        assert!(
            rows.contains_key(*id),
            "{id}: built but not in MANIFEST.tsv"
        );
    }
    if update_mode() {
        return;
    }
    // Every file in the directory belongs to a row (or is the manifest /
    // allowlist): a stray golden cannot sit unexamined beside the corpus.
    let mut stray = Vec::new();
    for entry in fs::read_dir(fixtures_dir()).expect("refuse dir") {
        let path = entry.expect("entry").path();
        let name = path.file_name().unwrap().to_string_lossy().into_owned();
        if name == "MANIFEST.tsv" || name == "UNCOVERED.tsv" {
            continue;
        }
        let (stem, ext) = name.rsplit_once('.').unwrap_or((&name, ""));
        let ok = match rows.get(stem).map(|r| r.carrier) {
            Some(Carrier::Module | Carrier::Control) => matches!(ext, "tmbc" | "json" | "msgpack"),
            Some(Carrier::Bytes) => ext == "tmbc",
            Some(Carrier::None) | None => false,
        };
        if !ok {
            stray.push(name);
        }
    }
    assert!(stray.is_empty(), "files belonging to no row: {stray:?}");
}

/// The storage subject is its by-value slot, not its geometry or license.
/// Updating this test writes only the three new row artifacts; existing
/// corpus bytes and the accepted control remain unchanged.
#[test]
fn storage_signature_row_and_pointer_twin_are_attributed() {
    let id = "storage_by_value_signature";
    let built =
        generate::build_refuse_storage_by_value_signature().expect("storage subject builds");
    let bytes = serialize_module(&built).expect("wire-representable storage subject");
    let decoded = deserialize_module(&bytes).expect("storage subject decodes");
    assert_eq!(
        u32::from_le_bytes(bytes[8..12].try_into().unwrap()),
        trust_ir::binary::STORAGE_LAYOUT_FORMAT_VERSION
    );
    let dir = fixtures_dir();
    assert_or_update_bytes(&dir.join(format!("{id}.tmbc")), &bytes);
    assert_or_update_bytes(
        &dir.join(format!("{id}.json")),
        serde_json::to_string_pretty(&decoded).unwrap().as_bytes(),
    );
    assert_or_update_bytes(
        &dir.join(format!("{id}.msgpack")),
        &rmp_serde::to_vec(&decoded).unwrap(),
    );
    let subject = deserialize_module(&fs::read(dir.join(format!("{id}.tmbc"))).unwrap())
        .expect("checked-in storage subject decodes");
    let errors = validate_module(&subject);
    assert!(
        matches!(
            errors.as_slice(),
            [ValidationError::InvalidStorageUse { .. }]
        ),
        "the by-value slot is the sole refusal: {errors:?}"
    );

    let mut twin = subject;
    assert_eq!(twin.func_types.len(), 2);
    let storage = twin.func_types[1].params[0].clone();
    assert_eq!(storage, Ty::Storage(trust_ir::StorageLayout::new(80, 8)));
    twin.func_types[1].params[0] = Ty::PtrConst(Box::new(storage));
    let twin = deserialize_module(&serialize_module(&twin).unwrap()).unwrap();
    assert!(
        validate_module(&twin).is_empty(),
        "a pointer to the same storage geometry is a value; this grants no Core/native admission"
    );

    let control = deserialize_module(
        &fs::read(dir.join("control_licensed_identity.tmbc")).expect("existing accepted control"),
    )
    .unwrap();
    assert!(validate_module(&control).is_empty());
    let recognized: BTreeSet<String> = [STRUCTURAL_LICENSE_AUTHORITY.to_string()].into();
    let admission = CodegenAdmission::pinned().with_recognized(&recognized);
    assert!(validate_module_for_codegen_with(&control, &admission).is_empty());
}

/// Amendment P: `assert_panic_site_missing`'s subject is the site ALONE. The
/// same module with the check's site stated passes the admission that
/// refuses the row (the negative twin), and the row is refused by exactly one
/// `AssertPanicSiteMissing`.
#[test]
fn assert_panic_site_row_twin_with_a_site_is_admitted() {
    let admission = CodegenAdmission::pinned().with_require_assert_panic_sites(true);
    let names = |m: &trust_ir::Module| -> Vec<String> {
        validate_module_for_codegen_with(m, &admission)
            .iter()
            .map(variant_name)
            .collect()
    };
    let row =
        generate::build_refuse_assert_panic_site_missing().expect("panic-site subject builds");
    assert_eq!(names(&row), vec!["AssertPanicSiteMissing".to_string()]);
    let twin = generate::build_panic_site_subject(generate::PanicSiteSubject::Faithful)
        .expect("refuse fixture");
    assert_eq!(names(&twin), Vec::<String>::new());
    // The default gate accepts both: a siteless assert is well-formed.
    assert_eq!(validate_module_for_codegen(&row), vec![]);
    assert_eq!(validate_module_for_codegen(&twin), vec![]);
}

/// Plan item P: `assert_panic_kind_unspecified`'s subject is the kind ALONE.
/// The same module with the check's kind stated passes the admission that
/// refuses the row (the negative twin), and the row is refused by exactly one
/// `AssertPanicKindUnspecified`.
#[test]
fn assert_panic_kind_row_twin_with_a_kind_is_admitted() {
    let admission = CodegenAdmission::pinned().with_require_assert_panic_kinds(true);
    let names = |m: &trust_ir::Module| -> Vec<String> {
        validate_module_for_codegen_with(m, &admission)
            .iter()
            .map(variant_name)
            .collect()
    };
    let row =
        generate::build_refuse_assert_panic_kind_unspecified().expect("assert-kind subject builds");
    assert_eq!(names(&row), vec!["AssertPanicKindUnspecified".to_string()]);
    let twin = generate::build_assert_kind_subject(trust_ir::AssertKind::Overflow(
        trust_ir::AssertOverflowOp::Add,
    ))
    .expect("refuse fixture");
    assert_eq!(names(&twin), Vec::<String>::new());
}

/// Every `pub fn build_refuse_<row>` / `build_refuse_bytes_<row>` in the
/// builder source is a ROWS line. The builders are `pub fn`s of a library
/// module (`refuse_fixtures`), so one nobody calls is never dead code to the
/// compiler; this scan is what keeps an orphan builder from hiding.
#[test]
fn every_refuse_builder_is_a_rows_line() {
    let source = fs::read_to_string(
        repo_root().join("crates/trust-ir-conformance/tests/generate/refuse.rs"),
    )
    .expect("generate/refuse.rs");
    let mut found = BTreeSet::new();
    for line in source.lines() {
        let Some(rest) = line.strip_prefix("pub fn build_refuse_") else {
            continue;
        };
        let name: String = rest
            .chars()
            .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
            .collect();
        found.insert(name);
    }
    let rows: BTreeSet<String> = ROWS
        .iter()
        .map(|(id, build)| match build {
            Build::Module(_) => (*id).to_string(),
            Build::Bytes(_) => format!("bytes_{id}"),
        })
        .collect();
    assert!(
        found.len() > 5,
        "the source scan found {} builders",
        found.len()
    );
    assert_eq!(
        found, rows,
        "generate/refuse.rs builders (left) and ROWS (right) are one list: an orphan builder \
         is never dead code to the compiler, so it is refused here by name"
    );
}

// ---------------------------------------------------------------------------
// 3. every pinned verdict holds, on the module decoded from the golden
// ---------------------------------------------------------------------------

/// What one entry point measured for one row.
enum Measured {
    /// Variant names of every error a `Vec<ValidationError>` lane returned.
    Errors(Vec<String>),
    /// `validate_module_complete`'s verdict, as a variant name.
    Completeness(Result<(), String>),
    /// `deserialize_module`'s verdict, as a variant name.
    Binary(Result<(), String>),
    /// The zero-`Trusted` census: true iff something is faith-stamped.
    Census(bool),
    /// The consumer lane: nothing trust-ir measures (see
    /// `consumer_rows_are_well_formed_and_carry_their_trigger`).
    Consumer,
}

fn names(errors: Vec<trust_ir_build::validate::ValidationError>) -> Measured {
    Measured::Errors(errors.iter().map(variant_name).collect())
}

/// The closed list of entry points a manifest row may name.
fn run_entry_point(entry: &str, row: &Row) -> Measured {
    let module = || {
        row.module()
            .unwrap_or_else(|| panic!("{}: `{entry}` needs a module row", row.id()))
    };
    match entry {
        "validate_module" => names(validate_module(module())),
        "validate_module_for_codegen" => names(validate_module_for_codegen(module())),
        "validate_module_for_codegen:recognizing_clean_kernel_tv" => {
            let recognized: BTreeSet<String> = ["clean-kernel-tv".to_string()].into();
            let admission = CodegenAdmission::pinned().with_recognized(&recognized);
            names(validate_module_for_codegen_with(module(), &admission))
        }
        "validate_module_for_codegen:refusing_unbacked_claims_on_checks" => {
            let admission = CodegenAdmission::pinned().with_refuse_unbacked_claims_on_checks(true);
            names(validate_module_for_codegen_with(module(), &admission))
        }
        "validate_module_for_codegen:requiring_assert_panic_kinds" => {
            let admission = CodegenAdmission::pinned().with_require_assert_panic_kinds(true);
            names(validate_module_for_codegen_with(module(), &admission))
        }
        "validate_module_for_codegen:requiring_assert_panic_sites" => {
            let admission = CodegenAdmission::pinned().with_require_assert_panic_sites(true);
            names(validate_module_for_codegen_with(module(), &admission))
        }
        // The codegen gate under the evidence policy (roadmap WS1.12(c)): a
        // license by an evidence-bound authority must record its
        // `GateEvidence` (`ValidationError::UnevidencedGate`).
        "validate_module_for_codegen:requiring_gate_evidence" => names(
            validate_module_with_config(
                module(),
                &ValidationConfig::pinned()
                    .with_codegen(true)
                    .with_gate_evidence(true),
            )
            .into_errors(),
        ),
        "validate_module_with_authority" => names(validate_module_with_authority(
            module(),
            &RejectingModuleProofAuthority,
        )),
        "validate_module_as_decoded" => {
            let version = row
                .wire_version
                .unwrap_or_else(|| panic!("{}: a module row has a wire version", row.id()));
            names(validate_module_as_decoded(module(), version))
        }
        "validate_module_complete" => {
            Measured::Completeness(validate_module_complete(module()).map_err(|e| variant_name(&e)))
        }
        "zero_trusted_census" => {
            let m = module();
            let stamped = m
                .proof_obligations
                .iter()
                .any(|o| o.status == ProofStatus::Trusted)
                || !m.trusted_evidence_census().is_empty();
            Measured::Census(stamped)
        }
        "deserialize_module" => Measured::Binary(
            deserialize_module(row.wire_bytes())
                .map(|_| ())
                .map_err(|e| variant_name(&e)),
        ),
        "consumer" => Measured::Consumer,
        other => panic!(
            "{}: `{other}` is not an entry point this harness runs; extend `run_entry_point` \
             (and the MANIFEST.tsv header) deliberately",
            row.id()
        ),
    }
}

#[test]
fn every_pinned_verdict_holds_on_the_decoded_golden() {
    if update_mode() {
        eprintln!("refuse_corpus: goldens were (re)written this run; run again to check verdicts");
        return;
    }
    let rows = corpus().expect("the must-refuse corpus loads");
    assert!(!rows.is_empty());
    // Every mismatch is collected and reported at once, so a re-measurement
    // of the manifest is one run.
    let mut failures: Vec<String> = Vec::new();
    for row in &rows {
        // Group the verdicts by entry point: a lane may name several variants.
        let mut by_entry: BTreeMap<&str, Vec<&Verdict>> = BTreeMap::new();
        for e in &row.manifest.expectations {
            by_entry
                .entry(e.entry_point.as_str())
                .or_default()
                .push(&e.verdict);
        }
        for (entry, verdicts) in by_entry {
            let id = row.id();
            let mut fail =
                |message: String| failures.push(format!("    {id}: `{entry}`: {message}"));
            let expected_names: BTreeSet<&str> = verdicts.iter().filter_map(|v| v.name()).collect();
            let accepts = verdicts.iter().any(|v| matches!(v, Verdict::Accepts));
            if accepts && !expected_names.is_empty() {
                fail("cannot both accept and refuse".into());
                continue;
            }
            match run_entry_point(entry, row) {
                Measured::Errors(produced) => {
                    if let Some(v) = verdicts
                        .iter()
                        .find(|v| !matches!(v, Verdict::Accepts | Verdict::Validation(_)))
                    {
                        fail(format!("returns ValidationErrors, not `{v}`"));
                        continue;
                    }
                    if accepts {
                        if !produced.is_empty() {
                            fail(format!("pinned `accepts` but refused: {produced:?}"));
                        }
                        continue;
                    }
                    if produced.is_empty() {
                        fail(format!("accepted a row pinned as {expected_names:?}"));
                        continue;
                    }
                    let produced_set: BTreeSet<&str> =
                        produced.iter().map(String::as_str).collect();
                    if produced_set != expected_names {
                        fail(format!(
                            "produced {produced_set:?}, pinned {expected_names:?} (a row exhibits \
                             exactly the variants it names, so a second refusal cannot hide behind \
                             the first)"
                        ));
                    }
                }
                Measured::Completeness(result) => {
                    let expected: Vec<&str> = verdicts
                        .iter()
                        .filter_map(|v| match v {
                            Verdict::Completeness(n) => Some(n.as_str()),
                            _ => None,
                        })
                        .collect();
                    if expected.len() != verdicts.len() || expected.len() != 1 {
                        fail("one `Completeness:<variant>` verdict per row".into());
                        continue;
                    }
                    if result != Err(expected[0].to_string()) {
                        fail(format!(
                            "measured {result:?}, pinned Err({:?})",
                            expected[0]
                        ));
                    }
                }
                Measured::Binary(result) => {
                    let expected: Vec<&str> = verdicts
                        .iter()
                        .filter_map(|v| match v {
                            Verdict::Binary(n) => Some(n.as_str()),
                            _ => None,
                        })
                        .collect();
                    if expected.len() != verdicts.len() || expected.len() != 1 {
                        fail("one `Binary:<variant>` verdict per row".into());
                        continue;
                    }
                    if result != Err(expected[0].to_string()) {
                        fail(format!(
                            "measured {result:?}, pinned Err({:?})",
                            expected[0]
                        ));
                    }
                }
                Measured::Census(stamped) => {
                    if verdicts.as_slice() != [&Verdict::Census("Trusted".into())] {
                        fail("the census has one verdict, `Census:Trusted`".into());
                    } else if !stamped {
                        fail("the zero-Trusted census found nothing faith-stamped".into());
                    }
                }
                Measured::Consumer => {
                    if row.is_control() {
                        if verdicts.as_slice() != [&Verdict::Accepts] {
                            fail("a control row's `consumer` verdict is exactly `accepts`".into());
                        }
                    } else if verdicts.iter().any(|v| !matches!(v, Verdict::Consumer(_))) {
                        fail("the `consumer` entry carries `Consumer:<rule>` verdicts only".into());
                    }
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "MANIFEST.tsv verdicts do not match what the entry points return:\n{}",
        failures.join("\n")
    );
}

// ---------------------------------------------------------------------------
// 4. the text lane: a lossy row is never offered as text
// ---------------------------------------------------------------------------

#[test]
fn text_losses_are_exact_per_row() {
    if update_mode() {
        return;
    }
    let mut mismatches = Vec::new();
    for row in corpus().expect("the must-refuse corpus loads") {
        let Some(module) = row.module() else {
            assert!(
                row.manifest.text_losses.is_empty(),
                "{}: poisoned bytes have no text form",
                row.id()
            );
            continue;
        };
        let measured: BTreeSet<String> = text_losses(module)
            .iter()
            .map(|l| format!("{:?}", TextLoss::kind(l)))
            .collect();
        let recorded: BTreeSet<String> = row.manifest.text_losses.iter().cloned().collect();
        if measured != recorded {
            mismatches.push(format!(
                "    {}: measured {measured:?}, manifest {recorded:?}",
                row.id()
            ));
        }
    }
    assert!(
        mismatches.is_empty(),
        "MANIFEST.tsv text_losses drifted:\n{}",
        mismatches.join("\n")
    );
}

// ---------------------------------------------------------------------------
// 5. exhaustiveness: every variant is exhibited or allowlisted, exactly
// ---------------------------------------------------------------------------

/// The variant names of `pub enum <name> {` in `source`, read off the enum
/// body (the lines indented by exactly four spaces that begin with an
/// uppercase identifier). Derived, never spelled: a variant added to the enum
/// is in this list at once.
fn enum_variants(source: &str, name: &str) -> Vec<String> {
    let header = format!("pub enum {name} {{");
    let start = source
        .find(&header)
        .unwrap_or_else(|| panic!("`{header}` not found"));
    let body = &source[start + header.len()..];
    let end = body.find("\n}\n").expect("enum body ends at column 0");
    let mut out = Vec::new();
    for line in body[..end].lines() {
        let Some(rest) = line.strip_prefix("    ") else {
            continue;
        };
        if rest.starts_with(' ') {
            continue;
        }
        let ident: String = rest
            .chars()
            .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
            .collect();
        if ident.chars().next().is_some_and(|c| c.is_ascii_uppercase()) {
            out.push(ident);
        }
    }
    assert!(
        out.len() > 5,
        "`{name}`: the source scan found {} variants",
        out.len()
    );
    out
}

fn all_variants() -> (Vec<String>, Vec<String>) {
    let root = repo_root();
    let validate = fs::read_to_string(root.join("crates/trust-ir-build/src/validate.rs"))
        .expect("validate.rs");
    let binary = fs::read_to_string(root.join("crates/trust-ir/src/binary.rs")).expect("binary.rs");
    (
        enum_variants(&validate, "ValidationError"),
        enum_variants(&binary, "BinaryError"),
    )
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Uncovered {
    variant: String,
    class: String,
    reason: String,
}

const UNCOVERED_CLASSES: [&str; 4] = ["structural", "lane", "unencodable", "unreachable"];

fn parse_uncovered(text: &str) -> Vec<Uncovered> {
    let mut out = Vec::new();
    for (index, raw) in text.lines().enumerate() {
        if raw.trim().is_empty() || raw.trim_start().starts_with('#') {
            continue;
        }
        let cells: Vec<&str> = raw.split('\t').map(str::trim).collect();
        assert_eq!(
            cells.len(),
            3,
            "UNCOVERED.tsv:{}: expected variant, class, reason",
            index + 1
        );
        let class = cells[1].split(':').next().unwrap_or("");
        assert!(
            UNCOVERED_CLASSES.contains(&class),
            "UNCOVERED.tsv:{}: class `{}` is not one of {UNCOVERED_CLASSES:?}",
            index + 1,
            cells[1]
        );
        assert!(
            class != "lane" || cells[1].len() > "lane:".len(),
            "UNCOVERED.tsv:{}: `lane:` names the lane",
            index + 1
        );
        assert!(
            !cells[2].is_empty(),
            "UNCOVERED.tsv:{}: reason required",
            index + 1
        );
        out.push(Uncovered {
            variant: cells[0].to_string(),
            class: cells[1].to_string(),
            reason: cells[2].to_string(),
        });
    }
    out
}

fn uncovered_path() -> PathBuf {
    fixtures_dir().join("UNCOVERED.tsv")
}

/// The (validation, binary) variant names some manifest verdict exhibits.
fn exhibited() -> (BTreeSet<String>, BTreeSet<String>) {
    let mut validation = BTreeSet::new();
    let mut binary = BTreeSet::new();
    for row in manifest().expect("the must-refuse manifest parses") {
        for e in &row.expectations {
            match &e.verdict {
                Verdict::Validation(n) => {
                    validation.insert(n.clone());
                }
                Verdict::Binary(n) => {
                    binary.insert(n.clone());
                }
                _ => {}
            }
        }
    }
    (validation, binary)
}

#[test]
fn every_variant_is_exhibited_by_a_row_or_allowlisted_exactly() {
    let (validation, binary) = all_variants();
    let all: BTreeSet<String> = validation.iter().chain(binary.iter()).cloned().collect();
    let (ex_validation, ex_binary) = exhibited();
    for name in &ex_validation {
        assert!(
            validation.contains(name),
            "MANIFEST.tsv names `Validation:{name}`, which is not a ValidationError variant"
        );
    }
    for name in &ex_binary {
        assert!(
            binary.contains(name),
            "MANIFEST.tsv names `Binary:{name}`, which is not a BinaryError variant"
        );
    }
    let exhibited_all: BTreeSet<String> = ex_validation.union(&ex_binary).cloned().collect();
    let listed = parse_uncovered(&fs::read_to_string(uncovered_path()).expect("UNCOVERED.tsv"));
    let listed_names: BTreeSet<String> = listed.iter().map(|u| u.variant.clone()).collect();
    assert_eq!(
        listed_names.len(),
        listed.len(),
        "UNCOVERED.tsv lists a variant twice"
    );
    let expected: BTreeSet<String> = all.difference(&exhibited_all).cloned().collect();
    if listed_names != expected {
        let missing: Vec<_> = expected.difference(&listed_names).collect();
        let stale: Vec<_> = listed_names.difference(&expected).collect();
        panic!(
            "UNCOVERED.tsv is not exactly the uncovered set.\n  variants with neither a corpus row \
             nor an allowlist line (a NEW variant lands with a row, never an allowlist line): \
             {missing:?}\n  allowlist lines whose variant now has a row (delete them), or that \
             name no variant: {stale:?}"
        );
    }
    // Non-vacuity: the corpus exhibits something on both enums, and the
    // allowlist is not the whole enum.
    assert!(!ex_validation.is_empty() && !ex_binary.is_empty());
    assert!(listed.len() < all.len());
    // `unencodable` / `unreachable` classify reader-side variants only: the
    // writer refuses to produce the bytes, or no input reaches the arm.
    for u in &listed {
        if u.class == "unencodable" || u.class == "unreachable" {
            assert!(
                binary.contains(&u.variant),
                "{}: `{}` classifies a BinaryError only",
                u.variant,
                u.class
            );
        }
    }
}

/// The variants `new` lists that `old` did not: the growth the shrink rule
/// refuses. Factored out so the rule is testable without git (below).
fn allowlist_growth(old: &str, new: &str) -> Vec<String> {
    let old: BTreeSet<String> = parse_uncovered(old)
        .into_iter()
        .map(|u| u.variant)
        .collect();
    let new: BTreeSet<String> = parse_uncovered(new)
        .into_iter()
        .map(|u| u.variant)
        .collect();
    new.difference(&old).cloned().collect()
}

/// What the git-backed shrink check concludes from what git answers.
#[derive(Debug, PartialEq, Eq)]
enum ShrinkVerdict {
    /// Compared against the allowlist at the merge-base: these variants were
    /// added since (empty = the rule holds).
    Added(Vec<String>),
    /// `origin/main` carries the allowlist but the merge-base does not: HEAD
    /// has not merged `origin/main` since the allowlist landed there, so the
    /// rule has no base — a FAILURE, not a skip.
    BaseBehindOrigin { base: String },
    /// Git cannot answer (no history, no `origin/main`), or the allowlist has
    /// not reached `origin/main` yet (its first landing): skipped, and said.
    Skipped(&'static str),
}

const UNCOVERED_REPO_PATH: &str = "crates/trust-ir-conformance/tests/fixtures/refuse/UNCOVERED.tsv";

/// The shrink check over a `git` oracle (`None` = the command failed), so
/// every branch below is testable without a repository. `head` is the
/// allowlist text at HEAD.
fn shrink_verdict(git: &dyn Fn(&[&str]) -> Option<String>, head: &str) -> ShrinkVerdict {
    let Some(base) = git(&["merge-base", "HEAD", "origin/main"]) else {
        return ShrinkVerdict::Skipped(
            "no merge-base with origin/main (no git history, or no origin/main ref)",
        );
    };
    let base = base.trim().to_string();
    let at_base = git(&["show", &format!("{base}:{UNCOVERED_REPO_PATH}")]);
    let at_origin = git(&["show", &format!("origin/main:{UNCOVERED_REPO_PATH}")]);
    match (at_base, at_origin) {
        (Some(old), _) => ShrinkVerdict::Added(allowlist_growth(&old, head)),
        (None, Some(_)) => ShrinkVerdict::BaseBehindOrigin { base },
        (None, None) => ShrinkVerdict::Skipped(
            "UNCOVERED.tsv has not reached origin/main yet (its first landing)",
        ),
    }
}

/// The shrink rule itself, on synthetic ledgers and a fake git: a deletion
/// passes, an addition is named, a rename is an addition; a merge-base
/// behind an `origin/main` that carries the allowlist is a failure, not a
/// skip; and the two states git cannot decide are skipped BY NAME. Nothing
/// here depends on the repository's state, so this is where the rule is
/// proved; the git-backed test below is its live application.
#[test]
fn the_shrink_rule_names_every_added_variant_and_admits_deletions() {
    let old = "A\tstructural\tr\nB\tstructural\tr\nC\tlane:x\tr\n";
    assert_eq!(
        allowlist_growth(old, "A\tstructural\tr\nC\tlane:x\tr\n"),
        Vec::<String>::new()
    );
    assert_eq!(allowlist_growth(old, old), Vec::<String>::new());
    let grown = "A\tstructural\tr\nB\tstructural\tr\nC\tlane:x\tr\nD\tstructural\tr\n";
    assert_eq!(allowlist_growth(old, grown), vec!["D".to_string()]);
    // A rename is a deletion plus an addition: the addition is refused.
    assert_eq!(
        allowlist_growth(old, "A\tstructural\tr\nB2\tstructural\tr\nC\tlane:x\tr\n"),
        vec!["B2".to_string()]
    );
    // The git oracle, state by state.
    let fake = |base: Option<&'static str>,
                at_base: Option<&'static str>,
                at_origin: Option<&'static str>| {
        move |args: &[&str]| -> Option<String> {
            match args {
                ["merge-base", "HEAD", "origin/main"] => base.map(str::to_string),
                ["show", spec] if spec.starts_with("origin/main:") => at_origin.map(str::to_string),
                ["show", spec] if spec.starts_with("abc:") => at_base.map(str::to_string),
                _ => None,
            }
        }
    };
    assert_eq!(
        shrink_verdict(&fake(Some("abc\n"), Some(old), Some(old)), grown),
        ShrinkVerdict::Added(vec!["D".to_string()]),
        "an addition since the merge-base is named"
    );
    assert_eq!(
        shrink_verdict(&fake(Some("abc\n"), Some(grown), Some(grown)), grown),
        ShrinkVerdict::Added(Vec::new()),
        "an unchanged allowlist holds"
    );
    assert_eq!(
        shrink_verdict(&fake(Some("abc\n"), Some(grown), Some(grown)), old),
        ShrinkVerdict::Added(Vec::new()),
        "a deletion since the merge-base holds"
    );
    assert_eq!(
        shrink_verdict(&fake(Some("abc\n"), None, Some(old)), grown),
        ShrinkVerdict::BaseBehindOrigin {
            base: "abc".to_string()
        },
        "origin/main carries the allowlist, the merge-base does not: a failure"
    );
    assert!(
        matches!(
            shrink_verdict(&fake(Some("abc\n"), None, None), grown),
            ShrinkVerdict::Skipped(reason) if reason.contains("first landing")
        ),
        "before the first landing the check says it is skipped"
    );
    assert!(
        matches!(
            shrink_verdict(&fake(None, Some(old), Some(old)), grown),
            ShrinkVerdict::Skipped(reason) if reason.contains("no merge-base")
        ),
        "without git history the check says it is skipped"
    );
}

/// Against the merge-base with `origin/main`, the allowlist only SHRINKS.
/// Live wherever `origin/main` carries the allowlist — from the commit after
/// its first landing, with a fetched `origin/main` (a stale one is an older,
/// larger base: weaker, not vacuous). A merge-base behind such an
/// `origin/main` FAILS. Only the two states git cannot decide are skipped,
/// and the skip is printed by name (`--nocapture` shows it); the rule itself
/// is proved on a fake git above.
#[test]
fn the_allowlist_only_shrinks_against_the_merge_base() {
    let root = repo_root();
    let git = |args: &[&str]| -> Option<String> {
        Command::new("git")
            .arg("-C")
            .arg(&root)
            .args(args)
            .output()
            .ok()
            .filter(|o| o.status.success())
            .map(|o| String::from_utf8_lossy(&o.stdout).into_owned())
    };
    let head = fs::read_to_string(uncovered_path()).expect("UNCOVERED.tsv at HEAD");
    match shrink_verdict(&git, &head) {
        ShrinkVerdict::Added(added) => assert!(
            added.is_empty(),
            "UNCOVERED.tsv gained {added:?} since the merge-base with origin/main; the allowlist \
             only shrinks. A new variant lands with a must-refuse corpus row."
        ),
        ShrinkVerdict::BaseBehindOrigin { base } => panic!(
            "origin/main carries UNCOVERED.tsv but the merge-base {base} does not: HEAD has not \
             merged origin/main since the allowlist landed there, so the shrink rule has no \
             base. `git merge origin/main` (never rebase) and re-run."
        ),
        ShrinkVerdict::Skipped(reason) => eprintln!(
            "refuse_corpus: SKIPPED the git-backed shrink check: {reason}. The rule is proved on \
             a fake git beside this test; this half is live only where origin/main carries the \
             allowlist."
        ),
    }
}

// ---------------------------------------------------------------------------
// 6. consumer-relative rows: well-formed here, and carrying their trigger
// ---------------------------------------------------------------------------

fn nodes(module: &Module) -> impl Iterator<Item = &trust_ir::node::InstrNode> {
    module
        .functions
        .iter()
        .flat_map(|f| f.blocks.iter())
        .flat_map(|b| b.body.iter())
}

/// The construct that makes each `Consumer:<rule>` row refusable, by rule.
fn consumer_trigger(rule: &str, m: &Module) -> bool {
    let triple = m
        .target_info
        .as_ref()
        .map(|t| t.triple.as_str())
        .unwrap_or("");
    match rule {
        "struct_passing_unclassified" => {
            m.target_info
                .as_ref()
                .is_some_and(|t| t.struct_passing == trust_ir::StructPassingPolicy::Unclassified)
                && m.functions.iter().any(|f| {
                    m.func_type(f.ty)
                        .is_some_and(|ft| ft.params.iter().any(|p| matches!(p, Ty::Struct(_))))
                })
                && nodes(m).any(|n| matches!(n.inst, Inst::Call { .. }))
        }
        // §17: a recorded `pass = indirect` on a C-convention two-`u64`
        // struct parameter on aarch64-apple-darwin, which AAPCS64 passes in
        // x0/x1 — the recorded fact contradicts the placement the consumer
        // computes under `NativeC`.
        "native_c_pass_mode_disagreement" => {
            triple == "aarch64-apple-darwin"
                && m.target_info
                    .as_ref()
                    .is_some_and(|t| t.struct_passing == trust_ir::StructPassingPolicy::NativeC)
                && m.functions.iter().any(|f| {
                    f.calling_conv == trust_ir::CallingConv::C
                        && m.func_type(f.ty).is_some_and(|ft| {
                            ft.params.iter().enumerate().any(|(i, p)| {
                                let two_words = match p {
                                    Ty::Struct(id) => m.struct_def(*id).is_some_and(|d| {
                                        d.size == Some(16)
                                            && d.fields.len() == 2
                                            && d.fields
                                                .iter()
                                                .all(|fd| matches!(fd.ty, Ty::U64 | Ty::I64))
                                    }),
                                    _ => false,
                                };
                                two_words
                                    && f.attrs.params.get(i).is_some_and(|a| {
                                        matches!(a.pass, Some(trust_ir::PassMode::Indirect { .. }))
                                    })
                            })
                        })
                })
                && nodes(m).any(|n| matches!(n.inst, Inst::Call { .. }))
        }
        // §17: `Unclassified` beside a by-value aggregate slot the old
        // Struct-only reading missed — a refined aggregate, a vector, a
        // closure. Each is a slot of the ONE predicate.
        "struct_passing_unclassified_refined"
        | "struct_passing_unclassified_vector"
        | "struct_passing_unclassified_closure" => {
            let slot_matches = |p: &Ty| match rule {
                "struct_passing_unclassified_refined" => matches!(
                    p,
                    Ty::Refine(base, _) if matches!(m.ty(*base), Some(Ty::Struct(_)))
                ),
                "struct_passing_unclassified_vector" => matches!(p, Ty::Vector(..)),
                _ => matches!(p, Ty::Closure(_)),
            };
            m.target_info
                .as_ref()
                .is_some_and(|t| t.struct_passing == trust_ir::StructPassingPolicy::Unclassified)
                && m.functions.iter().any(|f| {
                    m.func_type(f.ty)
                        .is_some_and(|ft| ft.params.iter().any(&slot_matches))
                })
                && nodes(m).any(|n| matches!(n.inst, Inst::Call { .. }))
        }
        "narrow_argument_extension_unrecorded" => {
            triple == "aarch64-apple-darwin"
                && m.functions.iter().any(|f| {
                    f.is_declaration()
                        && f.calling_conv == trust_ir::CallingConv::C
                        && m.func_type(f.ty).is_some_and(|ft| {
                            ft.params
                                .iter()
                                .any(|p| matches!(p, Ty::I8 | Ty::U8 | Ty::I16 | Ty::U16))
                                // `None` RECORDED on every slot: an absent
                                // slot is "no ABI facts at all", which this
                                // row is not about.
                                && f.attrs.params.len() == ft.params.len()
                                && f.attrs.params.iter().all(|p| {
                                    p.ext == trust_ir::ArgExt::None && p.pass.is_none()
                                })
                        })
                })
                && nodes(m).any(|n| matches!(n.inst, Inst::Call { .. }))
        }
        "c_unwind_recorded_not_lowered" => m
            .functions
            .iter()
            .any(|f| !f.is_declaration() && f.calling_conv == trust_ir::CallingConv::CUnwind),
        "target_feature_not_available" => m
            .functions
            .iter()
            .any(|f| !f.attrs.target_features.is_empty()),
        "region_havoc_store_semantics" => nodes(m).any(|n| {
            matches!(n.inst, Inst::Store { .. }) && n.has_proof(&ProofAnnotation::RegionHavocStore)
        }),
        "fresh_symbolic_havoc_narrowed" => {
            nodes(m).any(|n| {
                matches!(n.inst, Inst::Undef { .. })
                    && n.has_proof(&ProofAnnotation::FreshSymbolicHavoc)
            }) && nodes(m).any(|n| matches!(n.inst, Inst::Assume { .. }))
        }
        other => panic!("`Consumer:{other}` has no trigger predicate here; add one deliberately"),
    }
}

#[test]
fn consumer_rows_are_well_formed_and_carry_their_trigger() {
    if update_mode() {
        return;
    }
    let mut seen = 0;
    for row in corpus().expect("the must-refuse corpus loads") {
        let rules: Vec<&str> = row
            .manifest
            .expectations
            .iter()
            .filter_map(|e| match &e.verdict {
                Verdict::Consumer(r) => Some(r.as_str()),
                _ => None,
            })
            .collect();
        if rules.is_empty() {
            continue;
        }
        let module = row.module().expect("a consumer row is a module row");
        // Well-formed by every trust-ir rule, structural and codegen: the
        // refusal is the CONSUMER'S, and nothing here can stand in for it.
        assert_eq!(validate_module(module), Vec::new(), "{}", row.id());
        assert_eq!(
            validate_module_for_codegen(module),
            Vec::new(),
            "{}",
            row.id()
        );
        for rule in rules {
            assert!(
                consumer_trigger(rule, module),
                "{}: the module no longer carries the construct `{rule}` is about",
                row.id()
            );
            seen += 1;
        }
    }
    assert!(seen > 0);
}

// ---------------------------------------------------------------------------
// 6b. the control row bounds the runner's reason-blindness
// ---------------------------------------------------------------------------

/// Every `Gated` authority a module row wears is the structural license, the
/// evidence-bound `clean-kernel-tv`, or the subject of a row that pins
/// `UnrecognizedGateAuthority`; the builders spell the structural license
/// exactly as the runner exports it; under the recognized set the runner
/// tells a consumer to use, the codegen gate reports
/// `UnrecognizedGateAuthority` ONLY on rows whose subject is a foreign
/// authority, and the control row is accepted; under `{clean-kernel-tv}`
/// alone the control is refused for the license — which is what makes a
/// refused control diagnostic. The rows the license alone would mask under a
/// production set are counted and printed, never asserted as a number.
#[test]
fn no_module_row_is_refused_for_the_structural_license_alone() {
    if update_mode() {
        return;
    }
    assert_eq!(
        generate::REFUSE_STRUCTURAL_LICENSE_AUTHORITY,
        STRUCTURAL_LICENSE_AUTHORITY
    );
    let named: BTreeSet<String> = [
        "clean-kernel-tv".to_string(),
        STRUCTURAL_LICENSE_AUTHORITY.to_string(),
    ]
    .into();
    let production: BTreeSet<String> = ["clean-kernel-tv".to_string()].into();
    let is_unrecognized =
        |e: &ValidationError| matches!(e, ValidationError::UnrecognizedGateAuthority { .. });
    let mut masked = Vec::new();
    let mut controls = 0;
    for row in corpus().expect("the must-refuse corpus loads") {
        let Some(module) = row.module() else {
            continue;
        };
        let foreign: Vec<&str> = module
            .functions
            .iter()
            .filter(|f| !f.is_declaration())
            .filter_map(|f| match &f.body_gate {
                Some(trust_ir::BodyGate::Gated { authority, .. }) if !named.contains(authority) => {
                    Some(authority.as_str())
                }
                _ => None,
            })
            .collect();
        let pins_foreign =
            !row.is_control()
                && row.manifest.expectations.iter().any(|e| {
                    e.verdict == Verdict::Validation("UnrecognizedGateAuthority".to_string())
                });
        assert_eq!(
            !foreign.is_empty(),
            pins_foreign,
            "{}: wears {foreign:?}; a foreign authority is the subject of a row pinning \
             UnrecognizedGateAuthority, and of nothing else",
            row.id()
        );
        let under_named = validate_module_for_codegen_with(
            module,
            &CodegenAdmission::pinned().with_recognized(&named),
        );
        assert_eq!(
            under_named.iter().any(is_unrecognized),
            pins_foreign,
            "{}: under the recognized set the runner names, `UnrecognizedGateAuthority` appears \
             only where the manifest pins it: {under_named:?}",
            row.id()
        );
        let under_production = validate_module_for_codegen_with(
            module,
            &CodegenAdmission::pinned().with_recognized(&production),
        );
        if row.is_control() {
            controls += 1;
            assert!(
                under_named.is_empty(),
                "{}: the control is accepted under the named license: {under_named:?}",
                row.id()
            );
            assert!(
                under_production.iter().any(is_unrecognized),
                "{}: the control is refused for the license under a production set",
                row.id()
            );
        } else if !pins_foreign
            && !under_production.is_empty()
            && under_production.iter().all(is_unrecognized)
        {
            masked.push(row.id().to_string());
        }
    }
    assert!(controls > 0, "the corpus carries a control row");
    eprintln!(
        "refuse_corpus: under {{clean-kernel-tv}} alone, {} module row(s) are refused for the \
         structural license and NOTHING else: {masked:?}",
        masked.len()
    );
}

// ---------------------------------------------------------------------------
// 7. the two-way citation: the obligation file names its row back
// ---------------------------------------------------------------------------

#[test]
fn every_obligation_file_cites_its_row_back() {
    let root = repo_root();
    let snapshot = is_public_snapshot();
    let mut broken = Vec::new();
    for row in manifest().expect("the must-refuse manifest parses") {
        let path = root.join(&row.obligation);
        if !path.is_file() {
            if snapshot && row.obligation.starts_with("docs/") {
                continue; // not exported; the full tree checks it
            }
            broken.push(format!("{}: {} does not exist", row.id, row.obligation));
            continue;
        }
        let text = fs::read_to_string(&path).expect("read obligation file");
        let token = format!("refuse/{}", row.id);
        // At a token boundary: `refuse/row_one` is not satisfied by
        // `refuse/row_one_renamed`.
        let cited = text.match_indices(&token).any(|(at, _)| {
            text[at + token.len()..]
                .chars()
                .next()
                .is_none_or(|c| !(c.is_ascii_alphanumeric() || c == '_'))
        });
        if !cited {
            broken.push(format!(
                "{}: {} does not cite `{token}` (the sentence stating the obligation names its \
                 corpus row, or says the corpus cannot express it)",
                row.id, row.obligation
            ));
        }
    }
    assert!(broken.is_empty(), "\n{}", broken.join("\n"));
}

// ---------------------------------------------------------------------------
// 8. the manifest ↔ corpus loader agree, from the checked-in bytes
// ---------------------------------------------------------------------------

#[test]
fn the_runner_loads_every_artifact_row_from_the_checked_in_bytes() {
    if update_mode() {
        return;
    }
    let rows = corpus_from(&fixtures_dir(), MANIFEST).expect("corpus loads");
    let artifact_rows = manifest()
        .expect("the must-refuse manifest parses")
        .iter()
        .filter(|r| r.has_artifact())
        .count();
    assert_eq!(rows.len(), artifact_rows);
    assert_eq!(rows.len(), ROWS.len());
    assert!(rows.iter().any(Row::is_control));
    for row in &rows {
        match row.manifest.carrier {
            Carrier::Module | Carrier::Control => {
                assert!(row.module().is_some() && row.wire_version.is_some());
            }
            Carrier::Bytes => assert!(row.module().is_none()),
            Carrier::None => unreachable!(),
        }
        assert!(!row.wire_bytes().is_empty());
    }
}
