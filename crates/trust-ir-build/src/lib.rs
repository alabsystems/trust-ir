// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
#![forbid(unsafe_code)]
// The execution core passes every operand of a step as an explicit parameter; six of its
// functions take 8-12 arguments by design (main's own code, unchanged by the v40 merge).
// The sealed tippy's `too_many_arguments` fires on them under the workspace's
// `-D warnings` lane, which main last passed under an older clippy. Allowed for the crate
// with this reason rather than restructuring the calling convention in a format merge.
#![allow(clippy::too_many_arguments)]
pub mod ay_batch;
pub mod builder;
#[cfg(feature = "source-value-operational")]
pub mod bytev1_clean_uint32;
#[cfg(feature = "source-value-operational")]
pub mod clean_u32_boxed_helper_cic;
/// Source-bound tagged-UInt32 prefix observations; no execution-proof authority.
#[cfg(feature = "source-value-operational")]
pub mod clean_u32_boxed_prefix;
/// Closed CIC mathematics for the explicitly distinct tagged-prefix profile.
#[cfg(feature = "source-value-operational")]
pub mod clean_u32_boxed_prefix_cic;
pub mod contracts;
#[cfg(any(feature = "clean-tv-anchor", feature = "source-identity-data"))]
pub mod core_execution;
#[cfg(any(feature = "clean-tv-anchor", feature = "source-identity-data"))]
pub mod core_reflection;
pub mod coverage;
pub mod demo;
pub mod host;
pub mod linked;
pub mod loop_cut;
pub mod loop_cut_image;
pub mod loop_entry_cut;
pub mod merge;
pub mod proof_assembly;
pub mod proof_components;
pub mod satcert;
pub mod scoped_local;
pub mod semantic_evaluation;
#[cfg(feature = "source-value-operational")]
pub mod source_call_operational;
#[cfg(feature = "source-value-operational")]
pub mod source_readonly_calls;
#[cfg(feature = "source-value-operational")]
pub mod source_value_operational;
pub mod template;
pub mod term_scope;
#[cfg(feature = "clean-tv-anchor")]
pub mod translation;
pub mod validate;

/// Test plumbing, not a supported API: the `clean-kernel` crate this crate
/// already links (unconditionally) for its in-process CleanCic re-checker, at
/// the ONE rev the workspace pins. The two-language ratchets
/// (`trust-ir-conformance` target `two_language_b3`) build non-identity kernel
/// comparands (`clean_kernel::Expr`) through this path, so they take no
/// `clean-kernel` dependency of their own and add no pin leg
/// (`scripts/pin_rewrite.py`). The 0.x line promises no stability either way.
#[doc(hidden)]
pub use clean_kernel;

pub use ay_batch::AYBatchBuilder;
// Import authentication: the closure walk that re-earns every proof-bearing
// cross-crate row against the dependency module's stable digest. Re-exported
// beside `validate_module` for the same reason the codegen interlock is — a
// consumer acting on a `backed_by` or a cross-crate inheritance must run THIS,
// and the stricter gate must not be harder to find than the faith floor.
pub use builder::{
    AddObligationError, BuildError, BuilderError, DialectResultArityError, FunctionBuilder,
    FunctionDefinitionError, HandleDeclError, HandleRuntimeDecls, ModuleBuilder, PtrExtent,
    ReservedBlockParamAttachFailure, ReservedBlockParamError, ReservedBlockParamFunctionBuilder,
};
pub use contracts::mint_summary_obligations;
// Consumer-derived input coverage (supersedes the deprecated
// `coverage_assurance_report`): coverage is a verdict the consumer derives
// from a kernel-replayed claim (basis K) or a re-verified solver result cited
// by a sealed attestation (basis R), never from a producer-written row.
pub use coverage::{
    CertificateCoverage, CoverageBasis, CoverageEstablishmentReport, CoverageInputs,
    CoverageUndeterminedReason, MachineSemanticsDivergence, ModeStrengthMismatch,
    ObligationCoverage, VerifiedSolverResult, bound_established_by_kernel_claim,
    bound_established_by_replayed_result, coverage_establishment_report,
    request_machine_semantics_divergence,
};
pub use linked::{
    AuthenticatedImports, ImportResolver, LinkedValidationReport, MAX_IMPORT_DEPTH, ModuleSet,
    UnboundDeclaration, coverage_supports, validate_linked_module, validate_linked_module_with,
    validate_linked_module_with_config,
};
// WS4.11 (F-069): the ONE module merge / id remap, so producers and consumers
// stop re-teaching every id-bearing table to a private remapper.
pub use merge::{
    DuplicateDecl, DuplicateDef, MergeError, MergePolicy, Remap, RetainedImage, StrippedProofState,
    merge_into,
};
// The codegen interlock (`validate_module_for_codegen` and its composed
// `_with(CodegenAdmission)` lane, `codegen_license_errors`,
// `EVIDENCE_BOUND_GATE_AUTHORITIES`, `TRUST_INTERNAL_SPEC_PREFIX`, `RESERVED_TRUST_INTERNAL_SPEC_MODULES`) is
// re-exported here beside `validate_module` DELIBERATELY: it is the stricter
// gate a backend must run instead of `validate_module`, and a safety interlock
// that is harder to import than the check it supersedes does not get used.
// The v43 handle-runtime registry (`HandleRegistry`, `TRUSTED_HANDLE_RUNTIMES`,
// `HandleRuntimePin`, `HandleEntryPoint`, `PinnedTy`, `HandlePinError`,
// `validate_module_with_handle_registry`) is re-exported for the same reason:
// a producer declaring a runtime through `ModuleBuilder::declare_handle_runtime`
// takes its row from here, and an audit that wants to see what the validator
// trusts must not have to dig for it. The WS3.21 RC-runtime table
// (`TRUSTED_RC_RUNTIMES`, `RcRuntimePin`, `RcEntryPoint`, `rc_entry_for_symbol`)
// is re-exported beside it: a backend routing `Retain` / `Release` / `IsUnique`
// reads the pinned symbols from here rather than from a convention. The
// WS2.13 reference host model of both tables (`PinnedHandleHost`) is
// re-exported so an interpreter consumer installs the model the validator's
// tables key, not a re-typed copy. The WS3.22 release table
// (`PinnedReleaseEntry`, `PinnedReleaseSubject`, `pinned_release_entry_points`,
// `pinned_release_entry_for_symbol`) is the ONE place the release entry points
// of both tables are named (F-060): a host model deciding that a bodyless call
// is a free keys on it, and `PinnedHandleHost` does.
pub use host::PinnedHandleHost;
pub use validate::{
    ADMITTED_OBLIGATION_NAMESPACES, BoxDerefValidationRule, CheckedConsumption, CodegenAdmission,
    CompletenessError, ConsumptionRole, CoverageAssuranceReport, EVIDENCE_BOUND_GATE_AUTHORITIES,
    GateEvidenceRule, GiveBackReport, HandleEntryPoint, HandlePinError, HandleRegistry,
    HandleRuntimePin, ModuleValidationReport, PinnedReleaseEntry, PinnedReleaseSubject, PinnedTy,
    PointerConstantRefusal, RESERVED_TRUST_INTERNAL_SPEC_MODULES, RcEntryPoint, RcRuntimePin,
    SourceBoundCallCertificates, SourceToSiliconClaim, SourceToSiliconError,
    TRUST_INTERNAL_SPEC_PREFIX, TRUSTED_HANDLE_RUNTIMES, TRUSTED_RC_RUNTIMES, UnlicensedBodyPolicy,
    ValidationConfig, ValidationError, certify_identity_lineage_rung,
    certify_identity_lineage_rung_bound, certify_identity_lineage_rung_island_bound,
    certify_island_theorem, certify_module_give_backs, certify_source_bound_call_family,
    certify_source_bound_readonly_call_family, codegen_global_asm_errors, codegen_license_errors,
    codegen_license_errors_with, codegen_lowerability_errors, codegen_lowerability_errors_in,
    codegen_switch_case_literal_errors, codegen_switch_case_literal_errors_observed,
    consumption_role, gate_evidence_rule, is_admitted_obligation_namespace,
    kernel_certified_theorems, lineage_closed_with_validated_authority,
    pinned_release_entry_for_symbol, pinned_release_entry_points, rc_entry_for_symbol,
    validate_changed, validate_function, validate_module, validate_module_complete,
    validate_module_for_codegen, validate_module_for_codegen_with, validate_module_report,
    validate_module_report_with_authority, validate_module_report_with_authority_and_registry,
    validate_module_report_with_observed_catalog, validate_module_with_authority,
    validate_module_with_bundle, validate_module_with_bundle_with_authority,
    validate_module_with_config, validate_module_with_dialect_schemas,
    validate_module_with_handle_registry, validate_spec_anchor_functions,
    validate_spec_module_semantics, verify_source_to_silicon, wire_identity_blocker,
};
#[cfg(feature = "clean-tv-anchor")]
pub use validate::{
    CheckedScalarSourceValueEquation, CheckedSourceValueEquation, SourceValueEquationError,
    check_scalar_source_value_equation, check_uint_source_value_equation,
};
// Deprecated (false provenance), kept only while trust-vc and Trust still call
// it; `coverage_establishment_report` supersedes it.
#[allow(deprecated)]
pub use validate::coverage_assurance_report;
// The decoded-provenance lane: the v41 producer rule read against the header
// version a binary blob declared. `binary` only — nothing else can mint the
// `trust_ir::binary::WireVersion` it takes.
#[cfg(feature = "binary")]
pub use validate::{decoded_provenance_errors, validate_module_as_decoded};

#[cfg(feature = "source-addition-data")]
pub mod source_addition_data;
/// Actual-module custody for closed scalar source/IR mathematics, no admission.
#[cfg(feature = "source-identity-data")]
pub mod source_identity_data;

#[cfg(feature = "source-value-operational")]
pub use source_value_operational::{
    CheckedSourceValueOperational, SourceValueOperationalError,
    check_u32_straight_line_source_value,
    check_u32_straight_line_source_value_with_runtime_signature_descriptors,
    check_u32_straight_line_source_value_with_validated_runtime_context,
    check_u64_straight_line_source_value,
};

pub mod cps_image_replay;
pub mod projected_equality_replay;
