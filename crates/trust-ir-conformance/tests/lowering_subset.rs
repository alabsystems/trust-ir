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
    CASTOP_ALLOWLIST_V2, DIALECT_OP_ALLOWLIST_V2, INST_ALLOWLIST_V2, PROOF_ALLOWLIST_V2,
    SUBSET_VERSION, TY_ALLOWLIST_V2, module_subset_violations,
};

// Fixture generators live in a sibling file and are included directly so
// this gate walks the exact modules the byte-golden corpus pins. (dead_code
// allowed: the lineage/oracle builders are only used by conformance.rs.)
#[allow(dead_code)]
#[path = "generate.rs"]
mod generate;

type ModuleFixture = (&'static str, fn() -> trust_ir::Module);

/// One corpus row: fixture name + builder (kept in sync with
/// `conformance.rs::corpus()` by the `gate_walks_every_corpus_fixture`
/// cross-check below).
const MODULE_FIXTURES: &[ModuleFixture] = &[
    ("ty_primitives", generate::build_ty_primitives),
    ("ty_composite", generate::build_ty_composite),
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
    ("composition", generate::build_composition),
    // v23 producer provenance tags. Provenance is function metadata (like
    // calling_conv/linkage); the subset constrains instructions and types,
    // so a fully-tagged module is expected subset-clean.
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
];

/// Fixtures that INTENTIONALLY exercise out-of-subset constructs, with the
/// specific construct(s) they exist to wire-format-cover. Two-sided: a
/// listed fixture with zero violations fails the gate (remove the stale
/// entry); an unlisted fixture with violations fails the gate (either fix
/// the fixture or document the exemption here AND in the spec doc).
const SUBSET_EXEMPT_FIXTURES: &[(&str, &str)] = &[
    (
        "b1_scalars",
        "Ty::Isize/Usize/Char — v25 B1 scalar wire coverage; trust-cg has no pointer-width-int \
         or char lowering yet (B1 adoption wave)",
    ),
    (
        "ty_primitives",
        "Ty::F16 — wire coverage of the full primitive-type surface; F16 has no executable \
         binary16 semantics (B3 depth ledger)",
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
        let module = build();
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
    let fixture = generate::build_trust_native_request_bundle();
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
        INST_ALLOWLIST_V2,
        &["CoroSuspend", "LandingPad", "Resume"],
    );
    check_axis(
        "## Types",
        TY_ALLOWLIST_V2,
        &["F16", "Isize", "Usize", "Char", "Error"],
    );
    check_axis(
        "## Casts",
        CASTOP_ALLOWLIST_V2,
        &["ReifyFnPointer", "FPToSISat", "FPToUISat"],
    );
    check_axis("## Dialect ops", DIALECT_OP_ALLOWLIST_V2, &["vector.fma"]);
    check_axis("## Proof annotations", PROOF_ALLOWLIST_V2, &["Custom"]);
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
    let module = generate::build_frontend_emission_subset();

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

#[test]
fn fat_pointer_v2_is_canonical_and_64_bit_only() {
    let module = generate::build_inst_arithmetic();
    let violations = module_subset_violations(&module);
    assert!(
        violations.is_empty(),
        "the canonical U64 str metadata trio must be admitted in v2: {violations:?}"
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
    let violations = module_subset_violations(&narrow);
    assert!(
        violations
            .iter()
            .any(|violation| violation.contains("pinned 64-bit little-endian target")),
        "32-bit FatPtr must fail closed: {violations:?}"
    );

    narrow.target_info.as_mut().expect("target").pointer_size = 8;
    narrow.target_info.as_mut().expect("target").endianness = trust_ir::Endianness::Big;
    let violations = module_subset_violations(&narrow);
    assert!(
        violations
            .iter()
            .any(|violation| violation.contains("got 64-bit big-endian")),
        "big-endian FatPtr must fail closed: {violations:?}"
    );
}
