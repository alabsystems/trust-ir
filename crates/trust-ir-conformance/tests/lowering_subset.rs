// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Lowering-target conformance subset gate (v2).
//
// `lowering-target-subset.md` (repo root) pins the exact `Inst` / `Ty` /
// `ProofAnnotation` (+ `CastOp` / dialect-op) surface a frontend may emit on
// the "perfectly proven" path; `trust_ir_conformance::subset` is its
// machine-readable mirror. This gate (mirroring the B3 schema-parity gate
// pattern) walks every module fixture in the conformance corpus and asserts,
// TWO-SIDED:
//
//   1. every fixture NOT on the exemption list stays inside the subset, and
//   2. every fixture ON the exemption list really does use an out-of-subset
//      construct — a stale exemption fails the gate, so the list can never
//      silently over-claim.
//
// The exemption list exists because the corpus's job is WIRE-FORMAT coverage
// of the full IR surface, which is deliberately broader than the proven
// subset. Exempt fixtures are not "wrong" — they document exactly which
// coverage is wire-format-only rather than proven-path.
//
// A third check keeps the spec doc and the machine constants in lockstep:
// every allowlisted name (and every documented exclusion) must appear
// verbatim in lowering-target-subset.md (repo root), alongside the version
// marker.

use std::path::{Path, PathBuf};

use trust_ir_conformance::subset::{
    CASTOP_ALLOWLIST_V5, DIALECT_OP_ALLOWLIST_V5, INST_ALLOWLIST_V5, PROOF_ALLOWLIST_V5,
    SUBSET_VERSION, TY_ALLOWLIST_V5, module_subset_violations,
};

// Fixture generators live in a sibling file and are included directly so
// this gate walks the exact modules the byte-golden corpus pins. (dead_code
// allowed: the lineage/oracle builders are only used by conformance.rs.)
// The fixture generators (tests/generate.rs), compiled once as the library's
// `fixtures` module rather than again inside every test binary.
use trust_ir_conformance::fixtures as generate;

type ModuleFixture = (
    &'static str,
    fn() -> Result<trust_ir::Module, generate::FixtureError>,
);

/// One corpus row: fixture name + builder (kept in sync with
/// `conformance.rs::corpus()` by the `gate_walks_every_corpus_fixture`
/// cross-check below).
const MODULE_FIXTURES: &[ModuleFixture] = &[
    ("ty_primitives", generate::build_ty_primitives),
    ("ty_composite", generate::build_ty_composite),
    ("declared_tuple_v42", generate::build_declared_tuple_v42),
    ("spec_carrier", generate::build_spec_carrier),
    // v59 effect summaries and world epochs (WS1.14) are summary METADATA;
    // the bodies are stores, a global address, an add and a direct call —
    // expected subset-clean.
    ("effect_summaries", generate::build_effect_summaries),
    ("certificate_binding", generate::build_certificate_binding),
    ("inst_arithmetic", generate::build_inst_arithmetic),
    ("inst_seq_map", generate::build_inst_seq_map),
    ("inst_seq_map_not", generate::build_inst_seq_map_not),
    ("inst_seq_map_general", generate::build_inst_seq_map_general),
    ("inst_vector", generate::build_inst_vector),
    ("inst_vector_dialect", generate::build_inst_vector_dialect),
    (
        "inst_vector_crosslane",
        generate::build_inst_vector_crosslane,
    ),
    ("inst_memory", generate::build_inst_memory),
    ("inst_control", generate::build_inst_control),
    ("inst_atomic", generate::build_inst_atomic),
    ("inst_borrow_arc", generate::build_inst_borrow_arc),
    ("inst_binding_frames", generate::build_inst_binding_frames),
    ("inst_dialect", generate::build_inst_dialect),
    ("proof_annotations", generate::build_proof_annotations),
    ("proof_diagnostics", generate::build_proof_diagnostics),
    ("func_param_abi", generate::build_func_param_abi),
    ("chc_batch", generate::build_chc_batch_fixture),
    (
        "frontend_emission_subset",
        generate::build_frontend_emission_subset,
    ),
    // Panic-class obligations are module-level proof METADATA; they add no
    // instruction or type, so this fixture must stay subset-clean.
    (
        "frontend_panic_obligations",
        generate::build_frontend_panic_obligations,
    ),
    // WS4.4: the proof surface text carries — summaries with every clause
    // kind and place, a `backed_by` citation, one obligation per v41 kind,
    // one certificate per `CoverageBound`. All of it is module-level proof
    // METADATA over a plain body plus a body-less `External` declaration, so
    // the fixture must stay subset-clean.
    ("proof_surface", generate::build_proof_surface),
    ("composition", generate::build_composition),
    // WS4.2 text-directive coverage: function/node metadata plus a plain
    // call and branches — expected subset-clean.
    ("text_directives", generate::build_text_directives),
    // v23 producer provenance tags. Provenance is function metadata (like
    // calling_conv/linkage); the subset constrains instructions and types,
    // so a fully-tagged module is expected subset-clean.
    ("body_gate", generate::build_body_gate),
    ("producer_provenance", generate::build_producer_provenance),
    // v32/v33 debug metadata is claim-style function/node metadata. Its
    // sparse value IDs, scope tree, and source spans do not broaden the
    // executable lowering surface, so this fixture must remain subset-clean.
    ("debug_metadata_v33", generate::build_debug_metadata_v33),
    // v24 128-bit-faithful integer carrier (`Constant::U128`, wire tag 13).
    // Ty::U128 is IN the lowering subset and the subset constrains types and
    // instructions, so the fixture is expected subset-clean.
    ("u128_constants", generate::build_u128_constants),
    // v25 byte-array carrier: types are [u8; N] arrays (in-subset).
    ("bytes_constants", generate::build_bytes_constants),
    ("b1_scalars", generate::build_b1_scalars),
    // WS3-M1 mixed-producer seed: cross-producer calls in both directions
    // over subset-only arithmetic bodies — expected subset-clean, no
    // exemption (tests/mixed_producer.rs holds its acceptance tests).
    (
        "mixed_producer_module",
        generate::build_mixed_producer_module,
    ),
    // v40 container-tail fat pointers (ContainerVtable + ContainerLen) on the
    // default 64-bit little-endian target: FatPtr is in subset v2 regardless
    // of kind, so the fixture is expected subset-clean.
    ("ty_container_vtable", generate::build_ty_container_vtable),
    // v44 import-identity scheme: a mixed V2/V3 import table over a
    // one-instruction i32 identity body — expected subset-clean (the scheme
    // is identity metadata, not a construct a backend lowers).
    ("import_scheme", generate::build_import_scheme),
    // v39 nominal dialect type and v43 nominal opaque runtime handle: both
    // are excluded types (exact-typed transport only, no proven lowering),
    // so both fixtures are documented exemptions.
    ("ty_dialect_v39", generate::build_ty_dialect),
    ("ty_handle", generate::build_ty_handle),
    // v50 constant-size uniform array: a documented exemption (no trust-cg
    // lowering yet).
    ("array_splat", generate::build_array_splat),
    // v51 INST wire batch: MakeAggregate / MemCopy / MemSet are excluded
    // (no trust-cg lowering), so a documented exemption.
    ("inst_wire_batch", generate::build_inst_wire_batch),
    // Plan item P (wire v52): an assert's kind changes only its panic, so a
    // kinded `Assert` stays in subset; expected subset-clean.
    ("assert_kind", generate::build_assert_kind),
    ("call_unwind_boundary", generate::build_call_unwind_boundary),
    // Amendment P (wire v54): a site changes which panic a failed check is,
    // never whether it fails, so a sited `Assert` stays in subset;
    // expected subset-clean. `AssertInvoke` is excluded by name until a
    // consumer lowers its unwind edge: a documented exemption.
    ("assert_panic_site", generate::build_assert_panic_site),
    ("assert_invoke", generate::build_assert_invoke),
    // Amendment D (wire v55): `Drop` / `DropInvoke` are excluded by name
    // until a backend lowers them (the v5 expansion): a documented
    // exemption.
    ("drop_glue", generate::build_drop_glue),
    // Amendment D, Part 2 (wire v56): `InvokeIndirect` is excluded by name
    // until a backend lowers it (the v5 expansion): a documented exemption.
    ("unwind_twins", generate::build_unwind_twins),
    // Roadmap DG-63 (wire v62): the entry-state pointee clause place is
    // summary / obligation METADATA over a load-add-store body on `&u64` /
    // `&mut u64` — expected subset-clean.
    ("param_pointee_place", generate::build_param_pointee_place),
    // v45 function symbol attributes (WS3.10): visibility / section /
    // retention are function METADATA, like linkage and producer — the
    // subset constrains instructions and types — so this fixture is
    // expected subset-clean.
    ("abi_function_symbol", generate::build_abi_function_symbol),
    // v45 foreign calling conventions (WS3.12): a convention is an ABI fact
    // on a function or a call site, not an instruction or a type, so this
    // fixture is expected subset-clean too.
    ("abi_calling_conv", generate::build_abi_calling_conv),
    // v60 checked source ABI placement: a placement record is an ABI fact on
    // a function signature, not an instruction or a type, so this fixture is
    // expected subset-clean.
    ("typed_signature_abi", generate::build_typed_signature_abi),
    // v45 128-bit enum tag lanes (WS3.14(b)): `Ty::Enum` is in the subset
    // and a tag repr is a LAYOUT hint on the enum definition, not an
    // instruction or a type — expected subset-clean.
    ("abi_enum_tag_repr", generate::build_abi_enum_tag_repr),
    // v45 per-slot ABI facts (WS3.11): ABI claims on function metadata, not
    // instructions or types — expected subset-clean.
    ("abi_param_facts", generate::build_abi_param_facts),
    // WS4.15: the Lean library envelope — subset arithmetic plus module-level
    // proof metadata, so it is expected subset-clean.
    (
        "lean_library_envelope",
        generate::build_lean_library_envelope,
    ),
    // v58 (WS3.13): a declared closure environment frame plus the
    // application it makes lowerable for codegen. The APPLICATION is outside
    // the subset (structural condition 4: no Lean closure-application rule),
    // so the fixture is on the exemption list below.
    ("closure_layout", generate::build_closure_layout),
    ("make_closure", generate::build_make_closure),
    ("storage_only", generate::build_storage_only),
    // The tensor region (PKG-U13a): `Ty::Tensor` and `Inst::TensorContract`
    // have no machine lowering, so the fixture is on the exemption list below.
    ("tensor_contract", generate::build_tensor_contract),
    // Its map, reduce and view (PKG-U13c): no machine lowering either, so
    // the fixture is on the exemption list below.
    (
        "tensor_map_reduce_view",
        generate::build_tensor_map_reduce_view,
    ),
    // Its gather and scatter (PKG-U13d): no machine lowering either, so the
    // fixture is on the exemption list below.
    (
        "tensor_gather_scatter",
        generate::build_tensor_gather_scatter,
    ),
    // Its content-addressed weights (PKG-U13e): no machine lowering either,
    // so the fixture is on the exemption list below.
    ("tensor_weight_blob", generate::build_tensor_weight_blob),
    // v58 (WS3.9): nominal type-origin keys on a struct and an enum over a
    // one-constant u32 body — expected subset-clean (the key is identity
    // metadata, not a construct a backend lowers).
    ("nominal_type_origin", generate::build_nominal_type_origin),
];

/// Fixtures that INTENTIONALLY exercise out-of-subset constructs, with the
/// specific construct(s) they exist to wire-format-cover. Two-sided: a
/// listed fixture with zero violations fails the gate (remove the stale
/// entry); an unlisted fixture with violations fails the gate (either fix
/// the fixture or document the exemption here AND in the spec doc).
const SUBSET_EXEMPT_FIXTURES: &[(&str, &str)] = &[
    (
        "call_unwind_boundary",
        "Inst::CallCannotUnwind / CallIndirectCannotUnwind — typed wire-only no-crossing boundaries; executable and proof-subset host-unwind semantics are not modeled",
    ),
    (
        "inst_memory",
        "Inst::Dealloc — wire coverage of the full memory-instruction surface; the format \
         states neither the AllocOrigin nor the layout a correct free needs, so no conforming \
         backend can consume it (G18-1)",
    ),
    (
        "ty_primitives",
        "Ty::F16 — wire coverage of the full primitive-type surface; F16 has no Lean \
         binary16 semantics (B3 depth ledger), so it stays out of the subset although the \
         reference interpreter executes it since WS2.15",
    ),
    (
        "inst_vector_crosslane",
        "vector.fma — carried without a trust-ir lowering by ratified fast-4 policy, so it has \
         no in-repo refinement proof",
    ),
    (
        "inst_dialect",
        "verif.bfs_step — opaque dialect payload exercising every AttrValue variant; wire \
         round-trip coverage only, no proven lowering",
    ),
    (
        "proof_annotations",
        "ProofAnnotation::Custom — wire coverage of every annotation variant; Custom's meaning \
         is producer-defined and cannot be pinned",
    ),
    (
        "chc_batch",
        "ProofAnnotation::Custom — the ay CHC batch protocol tags ride the unpinned Custom \
         escape hatch",
    ),
    (
        "ty_dialect_v39",
        "Ty::Dialect — v39 nominal dialect type wire coverage (the only golden with header \
         39); exact-typed transport only, no legalization, so excluded as emitted",
    ),
    (
        "ty_handle",
        "Ty::Handle — v43 nominal opaque runtime handle wire coverage (the only golden with \
         header 43); the pinned trust_bignum::Nat declarations plus a transport body, \
         runtime-opaque with no interpreter or Lean origin, so excluded as emitted",
    ),
    (
        "array_splat",
        "Inst::ArraySplat / Constant::Splat — v50 uniform-array wire coverage (the only golden \
         with header 50) at u64-scale lengths; wire tags, Lean semantics and the lazy \
         interpreter value landed, a trust-cg lowering did not, so excluded until a subset bump",
    ),
    (
        "inst_wire_batch",
        "Inst::MakeAggregate / MemCopy / MemSet — v51 INST wire batch coverage (the only golden \
         with header 51) beside the in-subset WS3.20 sub-ops; the three instructions have wire \
         tags and semantics but no trust-cg lowering, so excluded until their admission bumps",
    ),
    (
        "assert_invoke",
        "Inst::AssertInvoke / LandingPad / Resume — amendment P wire coverage of the sited check \
         with an unwind edge (Inst tag 67); both engines execute it as the panic=abort \
         projection, but no consumer lowers its unwind edge, so excluded by name until a \
         subset bump admits it with the lowering",
    ),
    (
        "drop_glue",
        "Inst::Drop / DropInvoke / LandingPad / Resume — amendment D wire coverage of the \
         drop-glue table and the unwinding drop (Inst tag 68); both engines execute a resolved \
         drop as a call of its glue, but no backend lowers a drop yet, so excluded by name \
         until the v5 expansion admits Drop and DropInvoke with the lowering",
    ),
    (
        "unwind_twins",
        "Inst::InvokeIndirect / LandingPad — amendment D Part 2 wire coverage of the unwinding \
         indirect call (Inst tag 69); both engines execute it (its unwind edge under \
         PanicStrategy::Unwind), but no backend lowers it, so excluded by name until the v5 \
         expansion admits it with the lowering",
    ),
    (
        "closure_layout",
        "closure application (CallIndirect over a Ty::Closure callee) — v58 declared-closure-frame \
         wire coverage that applies the closure its row declares; structural condition 4 keeps \
         the application outside the subset (the Lean model has no closure-application rule)",
    ),
    (
        "storage_only",
        "possibly-uninitialized storage geometry; no by-value Core lowering or initialized-value authority",
    ),
    (
        "make_closure",
        "Inst::MakeClosure and closure application — runtime capture wire coverage, \
         still refused by the lowering-target subset; no native/provider proof admission",
    ),
    (
        "tensor_contract",
        "Ty::Tensor / Inst::TensorContract — the tensor region's wire coverage (an integer \
         matrix multiply); both engines execute it, but a tensor has no memory layout and no \
         backend lowers a contraction, so excluded by name until a subset bump admits them",
    ),
    (
        "tensor_map_reduce_view",
        "Ty::Tensor / Inst::TensorMap / Inst::TensorReduce / Inst::TensorView — the tensor \
         region's map, reduce and view wire coverage, chained; both engines execute them, but a \
         tensor has no memory layout and no backend lowers them, so excluded by name until a \
         subset bump admits them",
    ),
    (
        "tensor_gather_scatter",
        "Ty::Tensor / Inst::TensorGather / Inst::TensorScatter — the tensor region's gather and \
         scatter wire coverage, chained; both engines execute them, but a tensor has no memory \
         layout and no backend lowers them, so excluded by name until a subset bump admits them",
    ),
    (
        "tensor_weight_blob",
        "Ty::Tensor / Constant::TensorBlob — content-addressed weight blobs named at two element \
         types and fed to a contraction; both engines read them, but a tensor has no memory \
         layout and no backend lowers a blob constant, so excluded by its tensor type until a \
         subset bump admits it",
    ),
];

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crates dir")
        .parent()
        .expect("repo root")
        .to_path_buf()
}

fn exemption_reason(name: &str) -> Option<&'static str> {
    SUBSET_EXEMPT_FIXTURES
        .iter()
        .find(|(n, _)| *n == name)
        .map(|(_, why)| *why)
}

/// The gate: every corpus module fixture is either subset-clean or an
/// explicitly documented exemption — in both directions.
#[test]
fn corpus_fixtures_respect_the_lowering_target_subset() {
    for (name, build) in MODULE_FIXTURES {
        let module = build().expect("the fixture builds");
        let violations = module_subset_violations(&module);
        match exemption_reason(name) {
            None => assert!(
                violations.is_empty(),
                "fixture `{name}` uses out-of-subset constructs but is not on the exemption \
                 list — either keep it inside lowering-target subset v{SUBSET_VERSION} or record \
                 the exemption in SUBSET_EXEMPT_FIXTURES (this test) and in \
                 lowering-target-subset.md:\n  {}",
                violations.join("\n  ")
            ),
            Some(why) => assert!(
                !violations.is_empty(),
                "fixture `{name}` is on the exemption list (\"{why}\") but produced ZERO subset \
                 violations — the exemption is stale; delete it so the gate keeps enforcing the \
                 subset"
            ),
        }
    }
}

/// The exemption list may only name fixtures the gate actually walks.
#[test]
fn exemption_list_names_only_known_fixtures() {
    for (name, _) in SUBSET_EXEMPT_FIXTURES {
        assert!(
            MODULE_FIXTURES.iter().any(|(n, _)| n == name),
            "SUBSET_EXEMPT_FIXTURES names unknown fixture `{name}`"
        );
    }
}

/// Keep this gate's fixture table in lockstep with `conformance.rs::corpus()`
/// — a fixture registered there but not walked here (or vice versa) fails.
/// Parsed textually so the two test binaries need no shared crate surface.
#[test]
fn gate_walks_every_corpus_fixture() {
    let conformance_src = std::fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests")
            .join("conformance.rs"),
    )
    .expect("read conformance.rs");
    // Fixture registrations look like: name: "ty_primitives",
    let mut corpus_names = Vec::new();
    for line in conformance_src.lines() {
        let trimmed = line.trim_start();
        if let Some(rest) = trimmed.strip_prefix("name: \"")
            && let Some(name) = rest.strip_suffix("\",")
        {
            corpus_names.push(name.to_string());
        }
    }
    for (name, _) in MODULE_FIXTURES {
        assert!(
            corpus_names.iter().any(|n| n == name),
            "gate walks `{name}` but conformance.rs::corpus() does not register it"
        );
    }
    for name in &corpus_names {
        // Lineage / native-bundle fixtures are not Module fixtures; skip them.
        if name.starts_with("proof_lineage") || name.starts_with("native_request") {
            continue;
        }
        assert!(
            MODULE_FIXTURES.iter().any(|(n, _)| n == name),
            "conformance.rs::corpus() registers `{name}` but this gate does not walk it — add \
             it to MODULE_FIXTURES (and, if intentionally out-of-subset, to \
             SUBSET_EXEMPT_FIXTURES + lowering-target-subset.md)"
        );
    }
}

/// The native verification-request bundle carries a module too; the module
/// side of that handoff must stay inside the subset (its out-of-subset
/// surface lives in the compiler-facts sidecar, which is verification
/// metadata, not emitted IR).
#[test]
fn native_bundle_module_respects_the_subset() {
    let fixture = generate::build_trust_native_request_bundle().expect("the fixture builds");
    let violations = module_subset_violations(&fixture.bundle.module);
    assert!(
        violations.is_empty(),
        "native_request_trust_bundle module uses out-of-subset constructs:\n  {}",
        violations.join("\n  ")
    );
}

/// The spec doc and the machine-readable constants must not drift: every
/// allowlisted name, every documented exclusion, and the version marker must
/// appear verbatim (backticked) in lowering-target-subset.md (repo root).
#[test]
fn spec_doc_matches_machine_readable_subset() {
    let doc_path = repo_root().join("lowering-target-subset.md");
    let doc = std::fs::read_to_string(&doc_path)
        .unwrap_or_else(|e| panic!("read {}: {e}", doc_path.display()));

    assert!(
        doc.contains(&format!("**Version:** v{SUBSET_VERSION}")),
        "spec doc must carry the version marker `**Version:** v{SUBSET_VERSION}`"
    );

    // Placement-aware lockstep: an allowlisted name must appear backticked in
    // its axis section OUTSIDE the "Excluded:" table, and each documented
    // exclusion must appear INSIDE that table — so a doc edit that moves a
    // construct between the allowed and excluded regions fails this gate, not
    // just a wholesale deletion.
    fn axis_section<'d>(doc: &'d str, heading: &str) -> &'d str {
        let start = doc
            .find(heading)
            .unwrap_or_else(|| panic!("spec doc is missing the `{heading}` section"));
        let rest = &doc[start..];
        match rest[heading.len()..].find("\n## ") {
            Some(next) => &rest[..heading.len() + next],
            None => rest,
        }
    }
    /// Split a section at its `Excluded:` table: (outside, exclusion_table).
    /// The table is the run of `|`-prefixed (or blank) lines after `Excluded:`.
    fn split_excluded(section: &str) -> (String, String) {
        let Some(idx) = section.find("\nExcluded:") else {
            return (section.to_string(), String::new());
        };
        let (before, after) = section.split_at(idx);
        let mut table = String::new();
        let mut tail = String::new();
        let mut in_table = true;
        for line in after.lines().skip(2) {
            let is_row = line.trim_start().starts_with('|') || line.trim().is_empty();
            if in_table && is_row {
                table.push_str(line);
                table.push('\n');
            } else {
                in_table = false;
                tail.push_str(line);
                tail.push('\n');
            }
        }
        (format!("{before}\n{tail}"), table)
    }

    let mut missing = Vec::new();
    let mut misplaced = Vec::new();
    let mut check_axis = |heading: &str, allowed: &[&str], excluded: &[&str]| {
        let (outside, table) = split_excluded(axis_section(&doc, heading));
        for name in allowed {
            let tick = format!("`{name}`");
            if !outside.contains(&tick) {
                if table.contains(&tick) {
                    misplaced.push(format!(
                        "{name} (allowed, but only in {heading} Excluded table)"
                    ));
                } else {
                    missing.push(format!("{name} ({heading})"));
                }
            }
        }
        for name in excluded {
            let tick = format!("`{name}`");
            if !table.contains(&tick) {
                misplaced.push(format!(
                    "{name} (excluded, but not in {heading} Excluded table)"
                ));
            }
        }
    };
    check_axis(
        "## Instructions",
        INST_ALLOWLIST_V5,
        // `Dealloc` left the subset in G18-1 (2026-09-01): the format cannot
        // state the allocator origin or the layout a correct free needs.
        // `MakeAggregate` (WS3.5, 2026-09-19) landed after v3 was cut without
        // its wire tag or a backend lowering; a v3 addendum records it as
        // excluded (see the doc's history).
        &[
            "Dealloc",
            "CoroSuspend",
            "LandingPad",
            "Resume",
            "MakeAggregate",
            // WS3.20: semantics landed, admission is a subset-contract bump.
            "MemCopy",
            "MemSet",
            // Crystal lane (wave-DS): no destructor model in either executable model.
            "Drop",
            // v50: wire tags and semantics landed, no backend lowering yet.
            "ArraySplat",
            // Amendment P (v54): no consumer lowers its unwind edge yet.
            "AssertInvoke",
            // Amendment D Part 2 (v56): no backend lowers it yet.
            "InvokeIndirect",
            // The tensor region (PKG-U13a): no backend lowers a contraction.
            "TensorContract",
            // Its map, reduce and view (PKG-U13c): no backend lowers them.
            "TensorMap",
            "TensorReduce",
            "TensorView",
            // Its gather and scatter (PKG-U13d): likewise.
            "TensorGather",
            "TensorScatter",
        ],
    );
    check_axis(
        "## Types",
        TY_ALLOWLIST_V5,
        // v4 (WS2.17) promoted `Isize` / `Usize` / `Char` out of this table.
        // The tensor region (PKG-U13a): `Tensor` has no memory layout.
        &[
            "F16", "Error", "Refine", "Dialect", "Handle", "Storage", "Tensor",
        ],
    );
    check_axis(
        "## Casts",
        CASTOP_ALLOWLIST_V5,
        &["ReifyFnPointer", "FPToSISat", "FPToUISat"],
    );
    check_axis("## Dialect ops", DIALECT_OP_ALLOWLIST_V5, &["vector.fma"]);
    check_axis(
        "## Proof annotations",
        PROOF_ALLOWLIST_V5,
        // Both havoc markers are wire-encodable, NOT feature-gated, and were
        // never ratified into the subset — `proof_annotation_excluded`
        // (trust-ir::bridge) and `PROOF_ALLOWLIST_V5` both fail closed on
        // them, so the doc must carry them in its Excluded table too.
        &["Custom", "FreshSymbolicHavoc", "RegionHavocStore"],
    );
    // Every exempt fixture must be listed in the doc's exemption table.
    for (name, _) in SUBSET_EXEMPT_FIXTURES {
        if !doc.contains(&format!("`{name}`")) {
            missing.push(format!("{name} (exempt fixture)"));
        }
    }
    assert!(
        missing.is_empty() && misplaced.is_empty(),
        "lowering-target-subset.md and trust_ir_conformance::subset must stay \
         in lockstep — missing: {missing:?}; misplaced (wrong side of an Excluded \
         table): {misplaced:?}"
    );
}

/// The worked example (integration-frontend-emission): a two-function module
/// emitted through the subset with spans — validated end-to-end.
#[test]
fn worked_example_is_subset_clean_validated_and_span_covered() {
    let module = generate::build_frontend_emission_subset().expect("the fixture builds");

    // 1. Well-formed.
    let errors = trust_ir_build::validate_module(&module);
    assert!(
        errors.is_empty(),
        "worked example must validate: {errors:?}"
    );

    // 2. Inside the subset (also enforced corpus-wide above; restated here
    //    so the worked example's contract is self-contained).
    let violations = module_subset_violations(&module);
    assert!(
        violations.is_empty(),
        "worked example must stay inside subset v{SUBSET_VERSION}:\n  {}",
        violations.join("\n  ")
    );

    // 3. Two functions, emitted with provenance: every instruction carries a
    //    span, and the function-level ABI came through the builder.
    assert_eq!(module.functions.len(), 2, "worked example is two functions");
    assert_eq!(module.files.len(), 1, "one interned source file");
    for func in &module.functions {
        assert_eq!(
            func.calling_conv,
            trust_ir::CallingConv::Rust,
            "fn `{}`: calling conv set through the builder",
            func.name
        );
        for block in &func.blocks {
            for (i, node) in block.body.iter().enumerate() {
                assert!(
                    node.span.is_some(),
                    "fn `{}` bb{} inst #{i} lost its span",
                    func.name,
                    block.id.index()
                );
            }
        }
    }
    assert!(
        module.functions[0].attrs.inlinehint,
        "checked_add carries the inlinehint attr set through the builder"
    );

    // 4. Executable end-to-end: sum3(x) == x + 3 through the reference
    //    interpreter (callee included).
    let outcome = trust_ir::Interpreter::with_module(&module)
        .execute_func(
            module.functions[1].id,
            [trust_ir::InterpretValue::int(trust_ir::Ty::I32, 39).expect("i32 arg")],
        )
        .expect("worked example executes");
    let got = outcome.returns[0].as_int().expect("i32 result").as_signed();
    assert_eq!(got, 42, "sum3(39) == 42");
}

/// v2 admitted the fat-pointer trio with canonical metadata on the 64-bit
/// little-endian target only; v3 keeps the metadata condition and lifts the
/// target condition to the whole module (structural condition 5), so a
/// non-64-bit or big-endian module fails ONCE, module-wide, whether or not it
/// carries a fat pointer.
#[test]
fn fat_pointer_is_canonical_and_the_module_target_is_pinned() {
    let module = generate::build_inst_arithmetic().expect("the fixture builds");
    let violations = module_subset_violations(&module);
    assert!(
        violations.is_empty(),
        "the canonical U64 str metadata trio must be admitted: {violations:?}"
    );

    let mut wrong_metadata = module.clone();
    let mut changed = false;
    'outer: for function in &mut wrong_metadata.functions {
        for block in &mut function.blocks {
            for node in &mut block.body {
                if let trust_ir::Inst::PtrMetadata { metadata_ty, .. } = &mut node.inst {
                    *metadata_ty = trust_ir::Ty::U32;
                    changed = true;
                    break 'outer;
                }
            }
        }
    }
    assert!(changed, "fixture must contain PtrMetadata");
    let violations = module_subset_violations(&wrong_metadata);
    assert!(
        violations
            .iter()
            .any(|violation| violation.contains("does not match canonical")),
        "non-canonical metadata must fail closed: {violations:?}"
    );

    let mut narrow = module;
    narrow.target_info = Some(trust_ir::TargetInfo {
        triple: "i686-unknown-linux-gnu".into(),
        pointer_size: 4,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    // Condition 5 is reported exactly once, first, module-wide. On a 4-byte
    // target the canonical-metadata condition (2) ALSO fires against the
    // fixture's `u64` lanes (canonical is `u32` there) — an independent,
    // correct finding, so it is not counted against the module-level row.
    let violations = module_subset_violations(&narrow);
    assert_eq!(
        violations
            .iter()
            .filter(|violation| violation.contains("structural condition 5"))
            .count(),
        1,
        "{violations:?}"
    );
    assert!(
        violations[0].contains("structural condition 5")
            && violations[0].contains("4-byte pointers"),
        "32-bit module must fail closed on condition 5 first: {violations:?}"
    );
    assert!(
        violations[1..]
            .iter()
            .all(|violation| violation.contains("does not match canonical")),
        "{violations:?}"
    );

    narrow.target_info.as_mut().expect("target").pointer_size = 8;
    narrow.target_info.as_mut().expect("target").endianness = trust_ir::Endianness::Big;
    let violations = module_subset_violations(&narrow);
    assert_eq!(
        violations.len(),
        1,
        "one module-wide violation: {violations:?}"
    );
    assert!(
        violations[0].contains("structural condition 5") && violations[0].contains("big-endian"),
        "big-endian module must fail closed on condition 5: {violations:?}"
    );

    // Mutation control: an explicit 64-bit little-endian pin is admitted
    // exactly like the unpinned module — the condition names ONE byte
    // model, it does not refuse every pinned target.
    narrow.target_info.as_mut().expect("target").endianness = trust_ir::Endianness::Little;
    let violations = module_subset_violations(&narrow);
    assert!(
        violations.is_empty(),
        "an explicit 64-bit little-endian target is the pinned byte model: {violations:?}"
    );
}

/// Amendment D (wire v55): `Drop` and `DropInvoke` stay OUTSIDE subset v4,
/// excluded BY NAME in both spellings (the core classifier and the mirror),
/// though both engines now execute a resolved drop as a call of its glue:
/// admitting an opcode no backend lowers is not admission (the v5
/// expansion, with structural condition 9: every drop resolves).
#[test]
fn drop_and_drop_invoke_stay_outside_subset_v4() {
    let module = generate::build_drop_glue().expect("the fixture builds");
    let violations = module_subset_violations(&module).join("\n");
    for name in ["Inst::Drop ", "Inst::DropInvoke "] {
        assert!(
            violations.contains(name),
            "{name} must be named:\n{violations}"
        );
    }
    let mut seen = 0;
    for node in module
        .functions
        .iter()
        .flat_map(|f| &f.blocks)
        .flat_map(|b| &b.body)
    {
        if matches!(
            node.inst,
            trust_ir::Inst::Drop { .. } | trust_ir::Inst::DropInvoke { .. }
        ) {
            seen += 1;
            assert!(
                trust_ir::ConformanceSubset::inst_excluded(&node.inst)
                    .is_some_and(|why| why.contains("Drop")),
                "the core classifier excludes {:?} by name",
                node.inst
            );
        }
    }
    assert!(seen >= 5, "the golden carries both spellings ({seen})");
}

/// Amendment D, Part 2 (wire v56): `InvokeIndirect` is outside subset v4,
/// named by both spellings of the subset (the mirror and the core
/// classifier), with the `LandingPad` its unwind edge enters.
#[test]
fn invoke_indirect_stays_outside_subset_v4() {
    let module = generate::build_unwind_twins().expect("the fixture builds");
    let violations = module_subset_violations(&module).join("\n");
    for name in ["Inst::InvokeIndirect ", "Inst::LandingPad "] {
        assert!(
            violations.contains(name),
            "{name} must be named:\n{violations}"
        );
    }
    let mut seen = 0;
    for node in module
        .functions
        .iter()
        .flat_map(|f| &f.blocks)
        .flat_map(|b| &b.body)
    {
        if matches!(node.inst, trust_ir::Inst::InvokeIndirect { .. }) {
            seen += 1;
            assert!(
                trust_ir::ConformanceSubset::inst_excluded(&node.inst)
                    .is_some_and(|why| why.contains("InvokeIndirect")),
                "the core classifier excludes {:?} by name",
                node.inst
            );
        }
    }
    assert_eq!(seen, 2, "the golden carries one twin per runner");
}

/// Amendment P (wire v54): a site changes WHICH panic a failed check is,
/// never whether it fails, so every sited `Assert` of the `assert_panic_site`
/// golden is inside the subset, while `AssertInvoke` is excluded BY NAME
/// (both spellings of the subset), with `LandingPad` and `Resume` beside it.
#[test]
fn a_sited_assert_is_inside_the_subset_and_assert_invoke_is_excluded_by_name() {
    let sited = generate::build_assert_panic_site().expect("the fixture builds");
    assert!(
        sited
            .functions
            .iter()
            .flat_map(|f| &f.blocks)
            .flat_map(|b| &b.body)
            .any(|node| node.inst.panic_site().is_some()),
        "the golden carries sited asserts"
    );
    assert_eq!(module_subset_violations(&sited), Vec::<String>::new());
    let invoke = generate::build_assert_invoke().expect("the fixture builds");
    let violations = module_subset_violations(&invoke).join("\n");
    for name in ["AssertInvoke", "LandingPad", "Resume"] {
        assert!(
            violations.contains(name),
            "{name} must be named:\n{violations}"
        );
    }
    for node in invoke
        .functions
        .iter()
        .flat_map(|f| &f.blocks)
        .flat_map(|b| &b.body)
    {
        if matches!(node.inst, trust_ir::Inst::AssertInvoke { .. }) {
            assert!(
                trust_ir::ConformanceSubset::inst_excluded(&node.inst)
                    .is_some_and(|why| why.contains("AssertInvoke")),
                "the core classifier excludes it by name"
            );
        }
    }
}
