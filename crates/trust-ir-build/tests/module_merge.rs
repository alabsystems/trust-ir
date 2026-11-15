// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// WS4.11 (F-069) — the library module merge / id remap, `merge_into`.
//
// Layout:
// * positive — the identity law over the conformance corpus (merging `m` into
//   the merge's identity element gives `m` back, byte for byte), and the
//   corpus merged pairwise: every merged image's validation verdict is drawn
//   from the union of the two inputs' verdicts (no new error class), and a
//   refused pair is refused only for a reason the JOIN owns (two symbols that
//   are not one definition, two targets);
// * negative twins — two bodies for one symbol (`ConflictingDefinition`
//   naming `blocks`), identical bodies under different codegen licenses
//   (`ConflictingDefinition` naming `body_gate`), a dangling `TyId`
//   (`Dangling { table: "types" }`), an obligation scoped to a superseded
//   declaration, a carried `backed_by` without carried imports, a refused
//   merge leaving `dst` untouched;
// * nominal identity — two `Ty::Handle`s with one name and two runtimes stay
//   two types, and a declaration/definition pair that crosses them is never
//   joined; a self-referential struct dedups coinductively; an equally named
//   but different struct stays a second struct;
// * the v42 tuple-layout fixture merged behind a non-empty type table keeps
//   its descriptor pointing at its own tuple (a merger that skipped
//   `tuple_layouts[i].tuple_type` fails it through `TupleLayoutInconsistent`);
// * the ported proof-program rows, named after the rows:
//   `design_0827_functy_interning` and
//   `exec_log_and_tcb_module_merge_and_id_remap`.
//
// Mutation controls, and the test that kills each:
// * a new `Module` field fails to compile `merge_into` (the exhaustive
//   destructure). MEASURED on the 2026-10-07 rebase: main's amendment D
//   `Module::drop_glue`, a new `Assert` field (`site`), four new `Inst`
//   variants and the level-R `Ext` arms were each a compile error here
//   (E0027 / E0063 / E0004) until merged;
// * dedup of `Ty::Handle` by name alone turns
//   `handles_with_one_name_and_two_runtimes_stay_distinct` into a join;
// * dedup of functions on body equality alone turns the `body_gate` twin
//   (and `ws4_11_review_claims_are_part_of_definition_identity`) into a join;
// * skipping the tuple-type remap fails the tuple-layout fixture;
// * comparing signature ids instead of content fails
//   `ws4_11_review_aliased_signatures_are_one_signature` (the pre-review
//   merger compared ids: the defect the review fixed);
// * copying a panic site verbatim fails
//   `ws4_11_review_panic_sites_follow_the_remap`;
// * WS1.14 (wire v59) effect summaries: a new `EffectSummary` field or
//   `EffectSet` / `EffectPlace` variant fails to compile `merge_into` (the
//   same exhaustive destructure; MEASURED on the 2026-10-07 rebase, where
//   `FunctionSummary.effects` was E0027 / E0063 until merged). Copying an
//   effect place verbatim fails `ws1_14_effect_summaries_follow_the_global_remap`
//   and `ws1_14_merged_effect_places_keep_the_one_spelling`; mapping without
//   re-sorting fails the latter; keeping the later (or wider, or a filled-in)
//   declaration's effects fails
//   `ws1_14_two_declarations_differing_only_in_effects`; canonicalizing a
//   non-canonical `src` set fails
//   `ws1_14_a_dangling_or_non_canonical_effect_set_is_refused`.
// * WS6.7 (wire v61) license evidence: copying a `src` function's
//   `GateEvidence` verbatim fails
//   `ws6_7_merge_drops_license_evidence_and_keeps_the_license` (and the
//   identity law's count); dropping the license with it, or turning
//   `Ungated` into anything else, fails the same test's controls; comparing
//   licenses WITH their evidence fails
//   `ws6_7_identical_evidenced_definitions_dedup_and_dst_evidence_stands`, and
//   comparing them without their AUTHORITY fails its negative twin.
// The runtime mutants are by construction, not measured runs: each named
// test asserts exactly the outcome its mutant flips.

use std::collections::BTreeSet;

use trust_ir::constant::Constant;
use trust_ir::inst::Inst;
use trust_ir::node::InstrNode;
use trust_ir::proof::{ObligationKind, ProofObligation, ProofStatus};
use trust_ir::ty::{FieldDef, FuncTy, HandleTy, StructDef, Ty};
use trust_ir::value::{BlockId, FuncId, ProofId, StructId, TyId, ValueId};
use trust_ir::{
    Block, BodyGate, EffectPlace, EffectSet, EffectSummary, Endianness, ExternRef, Function,
    FunctionSummary, Linkage, Module, ModuleCompleteness, ModuleImport, Producer, SourceSpan,
    TargetInfo, UnloweredRow,
};
use trust_ir_build::{
    DuplicateDecl, DuplicateDef, MergeError, MergePolicy, ModuleBuilder, ValidationError,
    merge_into, validate_module,
};

#[path = "../../trust-ir-conformance/tests/generate.rs"]
#[allow(dead_code)]
mod generate;

// ── helpers ─────────────────────────────────────────────────────────────────

type Builder = fn() -> Result<Module, generate::FixtureError>;

/// `(builder name, builder)` rows, named by the builder itself so the
/// coverage test below can hold the list to the generator's source.
macro_rules! corpus {
    ($($builder:ident),* $(,)?) => {
        &[$((stringify!($builder), generate::$builder as Builder)),*]
    };
}

/// Every module fixture of the conformance generator
/// (`every_module_fixture_of_the_generator_is_in_the_corpus` holds it).
const CORPUS: &[(&str, Builder)] = corpus![
    build_ty_primitives,
    build_ty_container_vtable,
    build_ty_dialect,
    build_import_scheme,
    build_abi_function_symbol,
    build_abi_calling_conv,
    build_abi_enum_tag_repr,
    build_abi_param_facts,
    build_effect_summaries,
    build_spec_carrier,
    build_ty_handle,
    build_ty_composite,
    build_inst_seq_map,
    build_inst_seq_map_not,
    build_inst_seq_map_general,
    build_inst_arithmetic,
    build_inst_vector,
    build_inst_vector_dialect,
    build_inst_vector_crosslane,
    build_inst_memory,
    build_inst_control,
    build_inst_atomic,
    build_inst_borrow_arc,
    build_inst_binding_frames,
    build_inst_dialect,
    build_proof_annotations,
    build_proof_diagnostics,
    build_func_param_abi,
    build_text_directives,
    build_composition,
    build_proof_surface,
    build_chc_batch_fixture,
    build_frontend_emission_subset,
    build_frontend_panic_obligations,
    build_body_gate,
    build_producer_provenance,
    build_debug_metadata_v33,
    build_u128_constants,
    build_bytes_constants,
    build_array_splat,
    build_assert_kind,
    build_inst_wire_batch,
    build_b1_scalars,
    build_mixed_producer_module,
    build_mixed_producer_cross_functy_mismatch,
    build_declared_tuple_v42,
    build_lean_library_envelope,
    build_assert_panic_site,
    build_assert_invoke,
    build_drop_glue,
    build_unwind_twins,
    build_call_unwind_boundary,
    build_typed_signature_abi,
    build_closure_layout,
    build_make_closure,
    build_tensor_contract,
    build_tensor_map_reduce_view,
    build_tensor_gather_scatter,
    build_tensor_weight_blob,
    build_nominal_type_origin,
    build_certificate_binding,
    build_param_pointee_place,
];

fn corpus() -> Vec<(&'static str, Module)> {
    CORPUS
        .iter()
        .map(|(name, build)| {
            (
                *name,
                build().unwrap_or_else(|e| panic!("fixture {name} builds: {e}")),
            )
        })
        .collect()
}

/// The corpus is EVERY module fixture: each `pub fn build_*() ->
/// Result<Module, FixtureError>` of the generator (and of the submodules it
/// includes by `#[path]`) is a `CORPUS` row, so a fixture the format gains is
/// merged pairwise from the day it lands.
#[test]
fn every_module_fixture_of_the_generator_is_in_the_corpus() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/../trust-ir-conformance/tests");
    let root = std::fs::read_to_string(format!("{dir}/generate.rs")).expect("generator source");
    let mut sources = vec![root.clone()];
    for line in root.lines() {
        if let Some(rest) = line.trim().strip_prefix("#[path = \"") {
            let path = rest.split('"').next().expect("a quoted path");
            sources.push(std::fs::read_to_string(format!("{dir}/{path}")).expect("submodule"));
        }
    }
    let listed: BTreeSet<&str> = CORPUS.iter().map(|(name, _)| *name).collect();
    let mut missing = Vec::new();
    let mut found = 0;
    for source in &sources {
        for line in source.lines() {
            let Some(rest) = line.strip_prefix("pub fn build_") else {
                continue;
            };
            if !rest.contains("-> Result<Module, FixtureError>") {
                continue;
            }
            found += 1;
            let name = format!("build_{}", rest.split('(').next().expect("a name"));
            if !listed.contains(name.as_str()) {
                missing.push(name);
            }
        }
    }
    assert!(found > 0, "the scan found no module fixture builder");
    assert!(
        missing.is_empty(),
        "module fixtures missing from CORPUS: {missing:?}"
    );
}

/// The merge's identity element for `m`: an empty module named like `m` that
/// claims completeness (vacuously true), since `None` — no claim — absorbs.
fn identity_for(m: &Module) -> Module {
    let mut unit = Module::new(m.name.clone());
    unit.completeness = Some(ModuleCompleteness::Complete);
    unit
}

/// A `ValidationError`'s variant name: the error CLASS.
fn class(error: &ValidationError) -> String {
    let debug = format!("{error:?}");
    debug
        .split([' ', '(', '{'])
        .next()
        .unwrap_or_default()
        .to_string()
}

fn classes(module: &Module) -> BTreeSet<String> {
    validate_module(module).iter().map(class).collect()
}

fn unit_ty() -> FuncTy {
    FuncTy {
        abi: None,
        params: vec![],
        returns: vec![],
        is_vararg: false,
    }
}

/// A module with one function `name: () -> ()` whose body returns, under the
/// given codegen license; `with_body: false` makes it a bodyless `External`
/// declaration.
fn one_function(module_name: &str, name: &str, with_body: bool, gate: Option<BodyGate>) -> Module {
    let mut m = Module::new(module_name);
    let ft = m
        .add_func_type(unit_ty())
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), name, ft, BlockId::new(0));
    f.linkage = Linkage::External;
    if with_body {
        let mut entry = Block::new(BlockId::new(0));
        entry
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        f.blocks.push(entry);
        f.body_gate = gate;
    }
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    m
}

/// `name: () -> i32` returning the constant `value`.
fn returns_const(module_name: &str, name: &str, value: i128) -> Module {
    let mut m = Module::new(module_name);
    let ft = m
        .add_func_type(FuncTy {
            abi: None,
            params: vec![],
            returns: vec![Ty::I32],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), name, ft, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(value),
        })
        .with_result(ValueId::new(0)),
    );
    entry.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    f.blocks.push(entry);
    f.body_gate = Some(BodyGate::Ungated);
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    m
}

fn merged(a: &Module, b: &Module, policy: &MergePolicy) -> Result<Module, MergeError> {
    let mut image = a.clone();
    merge_into(&mut image, b, policy)?;
    Ok(image)
}

// ── positive: the identity law ──────────────────────────────────────────────

/// Merging `m` into the identity element is `m` again: every carried table
/// in the same order under the same ids. Source provenance (F-078) and a
/// codegen license's v61 evidence (WS6.7) are the two fields the merge drops
/// by design, and each is counted.
#[test]
fn merging_into_the_identity_element_is_the_identity() {
    for (name, m) in corpus() {
        let mut image = identity_for(&m);
        let remap = merge_into(&mut image, &m, &MergePolicy::VERIFICATION_IMAGE)
            .unwrap_or_else(|e| panic!("{name}: the identity merge refused: {e}"));
        let mut expected = m.clone();
        let mut provenance = 0;
        let mut gate_evidence = 0;
        for f in &mut expected.functions {
            provenance += usize::from(f.source_provenance.take().is_some());
            // WS6.7 (wire v61): a license's evidence is the other field the
            // merge drops by design (it cites `src`'s ids), counted; the
            // license and its authority stay.
            if let Some(BodyGate::Gated { evidence, .. }) = &mut f.body_gate {
                gate_evidence += usize::from(evidence.take().is_some());
            }
        }
        assert_eq!(remap.dropped_provenance(), provenance, "{name}");
        assert_eq!(remap.dropped_gate_evidence(), gate_evidence, "{name}");
        assert_eq!(
            format!("{image:?}"),
            format!("{expected:?}"),
            "{name}: merge into the identity element changed the module"
        );
        // The byte half runs where `trust_ir::binary` is compiled (this
        // crate's forwarding `binary` feature: the workspace test run turns
        // it on through `trust-ir-cli` / `trust-ir-conformance`); the
        // structural equality above holds in every build.
        #[cfg(feature = "binary")]
        if trust_ir_build::wire_identity_blocker(&expected).is_none()
            && expected.completeness.is_none()
        {
            assert_eq!(
                trust_ir::binary::serialize_module(&image).expect("serialize_module: test fixture"),
                trust_ir::binary::serialize_module(&expected)
                    .expect("serialize_module: test fixture"),
                "{name}: the canonical bytes differ"
            );
        }
    }
}

/// A plain `Module::new` makes NO completeness claim, and no claim absorbs.
#[test]
fn no_completeness_claim_absorbs_a_claim() {
    let mut claimed = one_function("c", "f", true, Some(BodyGate::Ungated));
    claimed.completeness = Some(ModuleCompleteness::Complete);
    let mut image = Module::new("image");
    merge_into(&mut image, &claimed, &MergePolicy::VERIFICATION_IMAGE).expect("merges");
    assert_eq!(image.completeness, None);
}

// ── positive: the corpus merged pairwise ────────────────────────────────────

/// The one error class the format attaches to a JOIN of valid inputs: a
/// carried `Certified` row whose CleanCic lineage is INDEX-keyed (v5..v7:
/// obligation and function indices) no longer binds once those indices
/// move, and the validator's re-check in the merged image refuses it — the
/// merge never re-earns a certificate (the symbol-keyed v8 lineage is the
/// relocatable one). Admitted only when proof state is carried and an input
/// actually carries a CleanCic certificate.
///
/// That refusal has one consequence the join owns with it. The validator's
/// kernel authority is all-or-nothing (`validated_authority_refs`: one failed
/// `Certified` re-check empties it, so a malformed certificate cannot hide
/// behind a valid one), so every `InheritedFromCallee` row of the image loses
/// its ground and reports `InheritedProofNotDischarged`, even one whose own
/// inherited row still re-checks. It is admitted only as exactly that: the
/// image must report the join-owned mismatch, and demoting exactly the
/// mismatched rows to `Pending` (taking them out of the kernel tier, so the
/// authority is no longer emptied) must leave no `InheritedProofNotDischarged`
/// — an inheritance that does not ground even then is a new class, refused.
fn join_owned_class(
    class: &str,
    policy: &MergePolicy,
    a: &Module,
    b: &Module,
    image: &Module,
) -> bool {
    let carries_clean_cic = |m: &Module| {
        m.proof_certificates
            .iter()
            .any(|c| matches!(c.evidence, trust_ir::proof::ProofEvidence::CleanCic { .. }))
    };
    let lineage_owned = policy.carry_proof_state && (carries_clean_cic(a) || carries_clean_cic(b));
    match class {
        "CertifiedCleanCicLineageMismatch" => lineage_owned,
        "InheritedProofNotDischarged" if lineage_owned => {
            let mismatched: BTreeSet<u32> = validate_module(image)
                .iter()
                .filter_map(|error| match error {
                    ValidationError::CertifiedCleanCicLineageMismatch { obligation } => {
                        Some(*obligation)
                    }
                    _ => None,
                })
                .collect();
            if mismatched.is_empty() {
                return false;
            }
            let mut demoted = image.clone();
            for row in &mut demoted.proof_obligations {
                if mismatched.contains(&row.id.index()) {
                    row.status = ProofStatus::Pending;
                }
            }
            !classes(&demoted).contains("InheritedProofNotDischarged")
        }
        _ => false,
    }
}

/// Every pair of conformance fixtures, both orders, under both policies:
/// a merged image's verdict is drawn from the union of the inputs' verdicts
/// (each input merged alone under the same policy, and judged under the
/// merged image's target), and a refused merge is refused for a reason the
/// join owns.
///
/// The target is the one join-owned input to a verdict: a target-free input
/// joined to a target-pinned one ADOPTS the target (only two different pinned
/// targets are refused), and some typing rules read it — a `MemCopy` count is
/// exactly `Usize`, or `U64` only with no target info. So each input's verdict
/// is taken under the target the image carries; the merge itself never
/// re-types a lane.
#[test]
fn the_corpus_merged_pairwise_adds_no_error_class() {
    let corpus = corpus();
    for policy in [
        MergePolicy::EXECUTION_IMAGE,
        MergePolicy::VERIFICATION_IMAGE,
    ] {
        let mut alone: std::collections::HashMap<(usize, String), BTreeSet<String>> =
            std::collections::HashMap::new();
        let mut alone_under = |k: usize, target: &Option<TargetInfo>| {
            alone
                .entry((k, format!("{target:?}")))
                .or_insert_with(|| {
                    let m = &corpus[k].1;
                    let mut image = identity_for(m);
                    merge_into(&mut image, m, &policy).expect("an input merges alone");
                    image.target_info = target.clone();
                    classes(&image)
                })
                .clone()
        };
        for (i, (a_name, a)) in corpus.iter().enumerate() {
            for (j, (b_name, b)) in corpus.iter().enumerate() {
                if i == j {
                    continue;
                }
                let mut image = identity_for(a);
                merge_into(&mut image, a, &policy).expect("an input merges alone");
                match merge_into(&mut image, b, &policy) {
                    Ok(_) => {
                        let union: BTreeSet<String> = alone_under(i, &image.target_info)
                            .union(&alone_under(j, &image.target_info))
                            .cloned()
                            .collect();
                        let new: Vec<String> = classes(&image)
                            .difference(&union)
                            .filter(|class| !join_owned_class(class, &policy, a, b, &image))
                            .cloned()
                            .collect();
                        assert!(
                            new.is_empty(),
                            "{a_name} <- {b_name} ({policy:?}): new error classes {new:?}"
                        );
                    }
                    Err(
                        MergeError::ConflictingDefinition { .. }
                        | MergeError::DuplicateDefinition { .. }
                        | MergeError::DropGlueConflict { .. }
                        | MergeError::UnrelocatableDisclosure { .. }
                        | MergeError::TargetMismatch { .. },
                    ) => {}
                    Err(other) => {
                        panic!("{a_name} <- {b_name} ({policy:?}): refused for {other}")
                    }
                }
            }
        }
    }
}

// ── negative twins: definitions ─────────────────────────────────────────────

#[test]
fn identical_definitions_dedup_and_different_bodies_conflict() {
    let a = returns_const("a", "f", 1);
    let same = returns_const("b", "f", 1);
    let image = merged(&a, &same, &MergePolicy::VERIFICATION_IMAGE).expect("identical dedups");
    assert_eq!(image.functions.len(), 1);

    let other = returns_const("b", "f", 2);
    assert_eq!(
        merged(&a, &other, &MergePolicy::VERIFICATION_IMAGE),
        Err(MergeError::ConflictingDefinition {
            symbol: "f".into(),
            field: "blocks",
        })
    );

    let refuse = MergePolicy {
        on_duplicate_definition: DuplicateDef::Refuse,
        ..MergePolicy::VERIFICATION_IMAGE
    };
    assert_eq!(
        merged(&a, &same, &refuse),
        Err(MergeError::DuplicateDefinition { symbol: "f".into() })
    );
}

/// REVIEW (roadmap): `DedupIdentical` is FULL equality. Identical bodies
/// under two codegen licenses are a conflict naming `body_gate`, in both
/// input orders — never "keep the first", which would let input order pick
/// the license.
#[test]
fn identical_bodies_with_different_codegen_licenses_conflict_on_body_gate() {
    let ungated = one_function("a", "f", true, Some(BodyGate::Ungated));
    let gated = one_function(
        "b",
        "f",
        true,
        Some(BodyGate::Gated {
            authority: "clean-kernel-tv".into(),
            evidence: None,
        }),
    );
    for (x, y) in [(&ungated, &gated), (&gated, &ungated)] {
        assert_eq!(
            merged(x, y, &MergePolicy::EXECUTION_IMAGE),
            Err(MergeError::ConflictingDefinition {
                symbol: "f".into(),
                field: "body_gate",
            })
        );
    }
    // Positive twin: the same license twice dedups.
    let image = merged(&ungated, &ungated, &MergePolicy::EXECUTION_IMAGE).expect("dedups");
    assert_eq!(image.functions.len(), 1);
    assert_eq!(image.functions[0].body_gate, Some(BodyGate::Ungated));
}

fn evidenced(authority: &str, digest_byte: u8) -> BodyGate {
    BodyGate::Gated {
        authority: authority.into(),
        evidence: Some(trust_ir::GateEvidence {
            obligation: ProofId::new(0),
            body_digest: trust_ir::proof::ProofDigest::sha256([digest_byte; 32]),
        }),
    }
}

/// WS6.7 (wire v61): a `src` license's `GateEvidence` cites `src`'s
/// obligation id and the digest of a body the merge renumbers, so the merge
/// drops it (counted) and keeps the license and its authority. It never
/// re-stamps it, and never moves a function to another licensing state.
#[test]
fn ws6_7_merge_drops_license_evidence_and_keeps_the_license() {
    for policy in [
        MergePolicy::EXECUTION_IMAGE,
        MergePolicy::VERIFICATION_IMAGE,
    ] {
        let src = one_function("a", "f", true, Some(evidenced("clean-kernel-tv", 7)));
        let mut image = Module::new("image");
        let remap = merge_into(&mut image, &src, &policy).expect("merges");
        assert_eq!(
            image.functions[0].body_gate,
            Some(BodyGate::gated("clean-kernel-tv")),
            "{policy:?}"
        );
        assert_eq!(remap.dropped_gate_evidence(), 1, "{policy:?}");
        // Controls: no evidence to drop, and no licensing state is changed.
        for gate in [
            None,
            Some(BodyGate::Ungated),
            Some(BodyGate::gated("clean-kernel-tv")),
        ] {
            let src = one_function("a", "f", true, gate.clone());
            let mut image = Module::new("image");
            let remap = merge_into(&mut image, &src, &policy).expect("merges");
            assert_eq!(image.functions[0].body_gate, gate, "{policy:?}");
            assert_eq!(remap.dropped_gate_evidence(), 0, "{policy:?}");
        }
    }
}

/// WS6.7: licenses are compared WITHOUT their evidence for the duplicate
/// rules, so an identical definition that carries evidence on either side
/// (or different evidence on both) dedups and `dst`'s copy stands, evidence
/// included, for the validator to recompute in the image. The AUTHORITY is
/// still part of the definition: another authority under the same evidence
/// is a `body_gate` conflict in both orders.
#[test]
fn ws6_7_identical_evidenced_definitions_dedup_and_dst_evidence_stands() {
    let dst = one_function("a", "f", true, Some(evidenced("clean-kernel-tv", 7)));
    for src_gate in [
        evidenced("clean-kernel-tv", 7),
        evidenced("clean-kernel-tv", 9),
        BodyGate::gated("clean-kernel-tv"),
    ] {
        let src = one_function("b", "f", true, Some(src_gate.clone()));
        let image = merged(&dst, &src, &MergePolicy::VERIFICATION_IMAGE)
            .unwrap_or_else(|e| panic!("{src_gate:?}: identical definitions dedup: {e}"));
        assert_eq!(image.functions.len(), 1);
        assert_eq!(image.functions[0].body_gate, dst.functions[0].body_gate);
        // The other order: `dst` evidence-free stays evidence-free (the
        // merge never gains a claim from `src`).
        let image = merged(&src, &dst, &MergePolicy::VERIFICATION_IMAGE).expect("dedups");
        assert_eq!(image.functions[0].body_gate, Some(src_gate));
    }
    let other = one_function("b", "f", true, Some(evidenced("trust-verify", 7)));
    for (x, y) in [(&dst, &other), (&other, &dst)] {
        assert_eq!(
            merged(x, y, &MergePolicy::VERIFICATION_IMAGE),
            Err(MergeError::ConflictingDefinition {
                symbol: "f".into(),
                field: "body_gate",
            })
        );
    }
}

/// `0.0` and `-0.0` are different IR literals despite IEEE numeric equality;
/// two definitions that differ only there are a conflict.
#[test]
fn signed_zero_constants_are_not_identical_definitions() {
    let build = |module: &str, v: f64| {
        let mut m = Module::new(module);
        let ft = m
            .add_func_type(FuncTy {
                abi: None,
                params: vec![],
                returns: vec![Ty::F64],
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut f = Function::new(FuncId::new(0), "z", ft, BlockId::new(0));
        let mut entry = Block::new(BlockId::new(0));
        entry.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::F64,
                value: Constant::Float(v),
            })
            .with_result(ValueId::new(0)),
        );
        entry.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        }));
        f.blocks.push(entry);
        m.try_add_function(f)
            .expect("Module::try_add_function: test fixture");
        m
    };
    assert_eq!(
        merged(
            &build("a", 0.0),
            &build("b", -0.0),
            &MergePolicy::EXECUTION_IMAGE
        ),
        Err(MergeError::ConflictingDefinition {
            symbol: "z".into(),
            field: "blocks",
        })
    );
}

/// Float literals use an f64 carrier even for an f32 instruction/global.
/// These quiet f32 NaNs preserve both payloads through that widening; the
/// f64 cases also cover signaling NaNs without an arithmetic conversion.
fn float_identity_cases() -> [(Ty, f64, f64); 5] {
    let f32_nan = |bits: u32| {
        let value = f64::from(f32::from_bits(bits));
        assert_eq!((value as f32).to_bits(), bits, "fixture preserves f32 bits");
        value
    };
    [
        (Ty::F32, f32_nan(0x7fc0_0001), f32_nan(0x7fc0_0002)),
        (
            Ty::F64,
            f64::from_bits(0x7ff8_0000_0000_0001),
            f64::from_bits(0x7ff8_0000_0000_0002),
        ),
        (
            Ty::F64,
            f64::from_bits(0x7ff0_0000_0000_0001),
            f64::from_bits(0x7ff0_0000_0000_0002),
        ),
        (Ty::F32, 0.0, -0.0),
        (Ty::F64, 0.0, -0.0),
    ]
}

fn returns_float(module_name: &str, ty: Ty, value: f64) -> Module {
    let mut m = Module::new(module_name);
    let ft = m
        .add_func_type(FuncTy {
            abi: None,
            params: vec![],
            returns: vec![ty.clone()],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), "z", ft, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry.body.push(
        InstrNode::new(Inst::Const {
            ty,
            value: Constant::Float(value),
        })
        .with_result(ValueId::new(0)),
    );
    entry.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    f.blocks.push(entry);
    f.body_gate = Some(BodyGate::Ungated);
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    m
}

fn float_global(module_name: &str, ty: Ty, value: f64) -> Module {
    let mut m = Module::new(module_name);
    m.globals.push(trust_ir::Global {
        name: "z".into(),
        ty,
        mutable: false,
        initializer: Some(Constant::Float(value)),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    });
    m
}

fn assert_float_duplicate_identity(a: &Module, same: &Module, other: &Module, field: &'static str) {
    for input in [a, same, other] {
        assert!(
            validate_module(input).is_empty(),
            "{:?}",
            validate_module(input)
        );
    }
    for policy in [
        MergePolicy::VERIFICATION_IMAGE,
        MergePolicy::EXECUTION_IMAGE,
    ] {
        let image = merged(a, same, &policy).expect("identical literal bits dedup");
        assert_eq!(image.functions, a.functions);
        assert_eq!(image.globals, a.globals);
        assert!(
            validate_module(&image).is_empty(),
            "{:?}",
            validate_module(&image)
        );

        for (dst, src) in [(a, other), (other, a)] {
            let mut dst = dst.clone();
            let before = dst.clone();
            let before_digest = dst.stable_digest();
            assert_eq!(
                merge_into(&mut dst, src, &policy).map(|_| ()),
                Err(MergeError::ConflictingDefinition {
                    symbol: "z".into(),
                    field,
                }),
            );
            // Structural equality and the digest both retain all float bits;
            // Debug text alone cannot witness NaN-payload rollback.
            assert_eq!(dst, before, "a refused merge writes nothing");
            assert_eq!(dst.stable_digest(), before_digest);
        }
    }
}

#[test]
fn float_bodies_dedup_only_identical_nan_bits_and_signed_zero() {
    for (ty, value, other) in float_identity_cases() {
        assert_ne!(value.to_bits(), other.to_bits());
        let a = returns_float("a", ty.clone(), value);
        let same = returns_float("b", ty.clone(), value);
        let other = returns_float("b", ty, other);
        assert_float_duplicate_identity(&a, &same, &other, "blocks");
    }
}

#[test]
fn float_global_initializers_dedup_only_identical_nan_bits_and_signed_zero() {
    for (ty, value, other) in float_identity_cases() {
        assert_ne!(value.to_bits(), other.to_bits());
        let a = float_global("a", ty.clone(), value);
        let same = float_global("b", ty.clone(), value);
        let other = float_global("b", ty, other);
        assert_float_duplicate_identity(&a, &same, &other, "initializer");
    }
}

/// A declaration resolves to a definition in either order; the definition's
/// license survives.
#[test]
fn a_declaration_resolves_to_its_definition_in_either_order() {
    let decl = one_function("a", "f", false, None);
    let def = one_function("b", "f", true, Some(BodyGate::Ungated));
    for (x, y) in [(&decl, &def), (&def, &decl)] {
        let image = merged(x, y, &MergePolicy::VERIFICATION_IMAGE).expect("links");
        assert_eq!(image.functions.len(), 1);
        assert!(!image.functions[0].blocks.is_empty());
        assert_eq!(image.functions[0].body_gate, Some(BodyGate::Ungated));
        assert!(
            validate_module(&image).is_empty(),
            "{:?}",
            validate_module(&image)
        );
    }
}

#[test]
fn an_obligation_scoped_to_a_superseded_declaration_is_refused() {
    let mut decl = one_function("a", "f", false, None);
    decl.proof_obligations.push(ProofObligation {
        id: ProofId::new(0),
        kind: ObligationKind::Postcondition,
        status: ProofStatus::Pending,
        description: "about the declaration".into(),
        formula: None,
        function: Some(FuncId::new(0)),
        source: None,
        site: None,
        spec: None,
    });
    let def = one_function("b", "f", true, Some(BodyGate::Ungated));
    for (x, y) in [(&decl, &def), (&def, &decl)] {
        assert_eq!(
            merged(x, y, &MergePolicy::VERIFICATION_IMAGE),
            Err(MergeError::SupersededDeclarationScoped { symbol: "f".into() })
        );
    }
}

// ── two declarations of one symbol ───────────────────────────────────────────

/// `f: () -> ()` declared `External` (module `a`) and the same symbol as an
/// `Internal` bodyless function that is no contract-only declaration (module
/// `b`, `EmptyFunction` on its own) — the shape of `two_language_cli`'s b4
/// hollow twin.
fn external_and_hollow_declarations() -> (Module, Module) {
    let external = one_function("a", "f", false, None);
    let mut hollow = one_function("b", "f", false, None);
    hollow.functions[0].linkage = Linkage::Internal;
    (external, hollow)
}

/// Two declarations that differ outside their ABI. The verification image
/// requires them identical (a declaration's summary is a claim; input order
/// must not pick one) and names the field. The execution image keeps the
/// WS4.6 linker's rule — the earlier declaration stands — so the image holds
/// the first input's own facts, and a malformed earlier declaration is named
/// by `validate_module` AS MERGED (`EmptyFunction`), exactly as the
/// pre-WS4.11 `trust-ir run` linker left it. Mutation control: refusing the
/// pair under `FirstStands` (the pre-fix merge, which broke the b4 twin)
/// fails the `expect`; keeping the later declaration fails the linkage
/// check.
#[test]
fn two_declarations_under_each_policy() {
    let (external, hollow) = external_and_hollow_declarations();
    for (x, y) in [(&external, &hollow), (&hollow, &external)] {
        assert_eq!(
            merged(x, y, &MergePolicy::VERIFICATION_IMAGE),
            Err(MergeError::ConflictingDefinition {
                symbol: "f".into(),
                field: "linkage",
            }),
            "{} <- {}",
            x.name,
            y.name
        );
        let image = merged(x, y, &MergePolicy::EXECUTION_IMAGE)
            .unwrap_or_else(|e| panic!("{} <- {}: {e}", x.name, y.name));
        assert_eq!(image.functions.len(), 1);
        assert_eq!(image.functions[0].linkage, x.functions[0].linkage);
        assert_eq!(classes(&image), classes(x), "the earlier input's verdict");
    }
    // Control: the two inputs' verdicts differ exactly in `EmptyFunction`, so
    // "the earlier input's verdict" above tells the two orders apart.
    assert!(classes(&hollow).contains("EmptyFunction"));
    assert!(!classes(&external).contains("EmptyFunction"));
}

/// The ABI binds two declarations under BOTH policies: a different signature
/// or calling convention is refused naming the field, in both orders — the
/// earlier declaration standing never hides an ABI disagreement.
#[test]
fn two_declarations_must_agree_on_the_abi_under_each_policy() {
    let (_, hollow) = external_and_hollow_declarations();
    let mut cc = one_function("c", "f", false, None);
    cc.functions[0].calling_conv = trust_ir::CallingConv::Cold;
    let mut signature = one_function("d", "f", false, None);
    signature.func_types[0].returns = vec![Ty::I32];
    for (other, field) in [(&cc, "calling_conv"), (&signature, "ty")] {
        for (x, y) in [(&hollow, other), (other, &hollow)] {
            for policy in [
                MergePolicy::EXECUTION_IMAGE,
                MergePolicy::VERIFICATION_IMAGE,
            ] {
                assert_eq!(
                    merged(x, y, &policy),
                    Err(MergeError::ConflictingDefinition {
                        symbol: "f".into(),
                        field,
                    }),
                    "{} <- {} ({policy:?})",
                    x.name,
                    y.name
                );
            }
        }
    }
}

/// Under `FirstStands` with proof state carried, the later declaration is
/// SUPERSEDED exactly as by a definition: an obligation scoped to it would be
/// re-scoped to a declaration it was never about, so the merge is refused.
/// An obligation scoped to the declaration that STANDS is carried.
/// Mutation control: treating the later declaration as equal
/// (`KeepExisting`) drops the refusal.
#[test]
fn an_obligation_scoped_to_a_later_declaration_is_refused_when_the_first_stands() {
    let policy = MergePolicy {
        on_duplicate_declaration: DuplicateDecl::FirstStands,
        ..MergePolicy::VERIFICATION_IMAGE
    };
    let (external, mut hollow) = external_and_hollow_declarations();
    hollow.proof_obligations.push(ProofObligation {
        id: ProofId::new(0),
        kind: ObligationKind::Postcondition,
        status: ProofStatus::Pending,
        description: "about the hollow declaration".into(),
        formula: None,
        function: Some(FuncId::new(0)),
        source: None,
        site: None,
        spec: None,
    });
    assert_eq!(
        merged(&external, &hollow, &policy),
        Err(MergeError::SupersededDeclarationScoped { symbol: "f".into() })
    );
    let image = merged(&hollow, &external, &policy).expect("the scoped declaration stands");
    assert_eq!(image.proof_obligations.len(), 1);
    assert_eq!(image.proof_obligations[0].function, Some(FuncId::new(0)));
}

// ── negative twins: tables ───────────────────────────────────────────────────

#[test]
fn a_dangling_type_id_is_refused_and_leaves_dst_unchanged() {
    let mut src = Module::new("src");
    src.types.push(Ty::Array(TyId::new(41), 4));
    let mut dst = returns_const("dst", "g", 7);
    let before = format!("{dst:?}");
    assert_eq!(
        merge_into(&mut dst, &src, &MergePolicy::VERIFICATION_IMAGE).map(|_| ()),
        Err(MergeError::Dangling {
            table: "types",
            id: 41,
        })
    );
    assert_eq!(format!("{dst:?}"), before, "a refused merge writes nothing");
}

/// WS4.11 review: the dangling-id refusal holds in EVERY table a body can
/// cite, not only `types` — a signature id, an inline nominal type, a global
/// address, a carried `ProofRef` and a span's file index each name their own
/// table, and every refusal leaves `dst` byte-for-byte unchanged. A
/// `ProofRef` the execution image strips anyway is no refusal: it is never
/// carried, so it cannot dangle in the image.
#[test]
fn ws4_11_review_a_dangling_id_is_refused_in_every_cited_table() {
    use trust_ir::proof::ProofAnnotation;
    use trust_ir::value::GlobalId;

    let mut bad_signature = returns_const("src", "f", 1);
    bad_signature.functions[0].ty = trust_ir::FuncTyId::new(17);

    let mut bad_struct = returns_const("src", "f", 1);
    bad_struct.functions[0].blocks[0].body[0].inst = Inst::Const {
        ty: Ty::Struct(StructId::new(5)),
        value: Constant::Aggregate(vec![]),
    };

    let mut bad_global = returns_const("src", "f", 1);
    bad_global.functions[0].blocks[0].body.insert(
        0,
        InstrNode::new(Inst::GlobalAddr {
            global: GlobalId::new(3),
        })
        .with_result(ValueId::new(1)),
    );

    let mut bad_proof_ref = returns_const("src", "f", 1);
    bad_proof_ref.functions[0].blocks[0].body[0]
        .proofs
        .push(ProofAnnotation::ProofRef(ProofId::new(8)));

    let mut bad_file = returns_const("src", "f", 1);
    bad_file
        .intern_file("src/f.rs")
        .expect("Module::intern_file: test fixture");
    bad_file.functions[0].blocks[0].body[0].span = Some(SourceSpan {
        file: 4,
        line: 1,
        col: 1,
    });

    let cases: [(&str, &Module, &'static str, u32); 5] = [
        ("signature", &bad_signature, "func_types", 17),
        ("inline struct", &bad_struct, "structs", 5),
        ("global address", &bad_global, "globals", 3),
        ("carried ProofRef", &bad_proof_ref, "proof_obligations", 8),
        ("span file", &bad_file, "files", 4),
    ];
    for (what, src, table, id) in cases {
        let mut dst = returns_const("dst", "g", 7);
        let before = format!("{dst:?}");
        assert_eq!(
            merge_into(&mut dst, src, &MergePolicy::VERIFICATION_IMAGE).map(|_| ()),
            Err(MergeError::Dangling { table, id }),
            "{what}"
        );
        assert_eq!(
            format!("{dst:?}"),
            before,
            "{what}: a refused merge writes nothing"
        );
    }

    // The execution image strips every ProofRef before it could dangle.
    let mut dst = returns_const("dst", "g", 7);
    let remap = merge_into(&mut dst, &bad_proof_ref, &MergePolicy::EXECUTION_IMAGE)
        .expect("a stripped ProofRef is never carried, so it cannot dangle");
    assert_eq!(remap.stripped().proof_refs, 1);
    assert!(
        dst.functions
            .iter()
            .flat_map(|f| f.blocks.iter().flat_map(|b| b.body.iter()))
            .all(|n| !n
                .proofs
                .iter()
                .any(|p| matches!(p, ProofAnnotation::ProofRef(_)))),
        "no ProofRef survives the execution image"
    );
}

#[test]
fn a_carried_backed_by_without_carried_imports_is_refused() {
    let mut src = one_function("src", "ext", false, None);
    let import = src
        .intern_import(ModuleImport::new(
            "dep",
            trust_ir::proof::ProofDigest::sha256([7; 32]),
        ))
        .expect("Module::intern_import: test fixture");
    src.functions[0].summary = Some(FunctionSummary {
        backed_by: Some(ExternRef {
            module: import,
            symbol: "ext".into(),
            obligation: None,
        }),
        ..FunctionSummary::default()
    });
    let policy = MergePolicy {
        carry_imports: false,
        ..MergePolicy::VERIFICATION_IMAGE
    };
    let mut dst = Module::new("dst");
    assert!(matches!(
        merge_into(&mut dst, &src, &policy),
        Err(MergeError::ImportsNotCarried { .. })
    ));
    // Positive twin: carried, the reference is remapped into dst's table.
    let mut dst = Module::new("dst");
    dst.intern_import(ModuleImport::new(
        "other",
        trust_ir::proof::ProofDigest::sha256([1; 32]),
    ))
    .expect("Module::intern_import: test fixture");
    let remap =
        merge_into(&mut dst, &src, &MergePolicy::VERIFICATION_IMAGE).expect("carried import");
    let carried = remap.import(import).expect("the import is mapped");
    assert_eq!(carried.index(), 1);
    assert_eq!(
        dst.functions[0]
            .summary
            .as_ref()
            .unwrap()
            .backed_by
            .as_ref()
            .unwrap()
            .module,
        carried
    );
}

#[test]
fn the_execution_image_strips_claims_and_counts_them() {
    let mut src = one_function("src", "f", true, Some(BodyGate::Ungated));
    src.functions[0].summary = Some(FunctionSummary::new().proved());
    src.functions[0].proofs = vec![
        trust_ir::proof::ProofAnnotation::Pure,
        trust_ir::proof::ProofAnnotation::ProofRef(ProofId::new(0)),
    ];
    src.proof_obligations.push(ProofObligation {
        id: ProofId::new(0),
        kind: ObligationKind::Postcondition,
        status: ProofStatus::Pending,
        description: "post".into(),
        formula: None,
        function: Some(FuncId::new(0)),
        source: None,
        site: None,
        spec: None,
    });
    let mut dst = Module::new("dst");
    let remap = merge_into(&mut dst, &src, &MergePolicy::EXECUTION_IMAGE).expect("merges");
    let stripped = remap.stripped();
    assert_eq!(
        (
            stripped.summaries,
            stripped.proof_refs,
            stripped.obligations
        ),
        (1, 1, 1)
    );
    assert_eq!(dst.functions[0].summary, None);
    assert_eq!(
        dst.functions[0].proofs,
        vec![trust_ir::proof::ProofAnnotation::Pure]
    );
    assert!(dst.proof_obligations.is_empty());
    assert_eq!(remap.proof(ProofId::new(0)), None, "nothing to map to");
}

#[test]
fn carried_proof_ids_shift_past_dst_and_references_follow() {
    let build = |module: &str, name: &str| {
        let mut m = one_function(module, name, true, Some(BodyGate::Ungated));
        m.functions[0].proofs = vec![trust_ir::proof::ProofAnnotation::ProofRef(ProofId::new(0))];
        m.proof_obligations.push(ProofObligation {
            id: ProofId::new(0),
            kind: ObligationKind::Postcondition,
            status: ProofStatus::Pending,
            description: format!("post of {name}"),
            formula: None,
            function: Some(FuncId::new(0)),
            source: None,
            site: None,
            spec: None,
        });
        m
    };
    let mut image = build("a", "f");
    let remap = merge_into(
        &mut image,
        &build("b", "g"),
        &MergePolicy::VERIFICATION_IMAGE,
    )
    .expect("merges");
    let g_post = remap.proof(ProofId::new(0)).expect("mapped");
    assert_eq!(g_post, ProofId::new(1));
    let g = image.function_by_name("g").expect("g merged");
    assert_eq!(
        g.proofs,
        vec![trust_ir::proof::ProofAnnotation::ProofRef(g_post)]
    );
    let row = image
        .proof_obligations
        .iter()
        .find(|o| o.id == g_post)
        .expect("row carried");
    assert_eq!(row.function, Some(g.id));
    // A `ProofRef` validates only against a kernel-authorized certificate,
    // which this fixture does not build: each input alone is refused for
    // exactly its own `(function, obligation)` pair. The merged verdict is
    // the union with g's pair RELOCATED to (1, 1) — `missing: false`
    // proves the carried reference names the carried row.
    let verdict = |m: &Module| -> BTreeSet<String> {
        validate_module(m)
            .iter()
            .map(|e| format!("{e:?}"))
            .collect()
    };
    let pair = |function: u32, obligation: u32| -> BTreeSet<String> {
        [
            ValidationError::ProofRefUnresolved {
                function,
                obligation,
                missing: false,
            },
            ValidationError::ProofRefWithoutClaim {
                function,
                obligation,
            },
        ]
        .iter()
        .map(|e| format!("{e:?}"))
        .collect()
    };
    assert_eq!(verdict(&build("a", "f")), pair(0, 0));
    assert_eq!(verdict(&build("b", "g")), pair(0, 0));
    let expected: BTreeSet<String> = pair(0, 0).union(&pair(1, 1)).cloned().collect();
    assert_eq!(verdict(&image), expected);
}

#[test]
fn source_provenance_is_dropped_and_counted() {
    let m = generate::build_composition().expect("fixture");
    let mut src = m.clone();
    src.functions[0].source_provenance = Some(trust_ir::SourceProvenance {
        schema: 1,
        compiler_source_digest: trust_ir::proof::ProofDigest::sha256([1; 32]),
        semantic_body_digest: trust_ir::proof::ProofDigest::sha256([2; 32]),
        binding_digest: trust_ir::proof::ProofDigest::sha256([3; 32]),
        loops: vec![],
    });
    let mut image = identity_for(&src);
    let remap = merge_into(&mut image, &src, &MergePolicy::VERIFICATION_IMAGE).expect("merges");
    assert_eq!(remap.dropped_provenance(), 1);
    assert!(
        image
            .functions
            .iter()
            .all(|f| f.source_provenance.is_none())
    );
}

#[test]
fn completeness_claims_combine_and_resolved_rows_drop() {
    let row = |symbol: &str| UnloweredRow {
        symbol: symbol.into(),
        display_path: None,
        reason: "not lowered".into(),
    };
    let mut a = one_function("a", "f", true, Some(BodyGate::Ungated));
    a.completeness = Some(ModuleCompleteness::Partial(vec![row("g"), row("h")]));
    let mut b = one_function("b", "g", true, Some(BodyGate::Ungated));
    b.completeness = Some(ModuleCompleteness::Complete);
    let mut image = a.clone();
    let remap = merge_into(&mut image, &b, &MergePolicy::EXECUTION_IMAGE).expect("merges");
    assert_eq!(remap.resolved_unlowered(), 1, "b defines g");
    assert_eq!(
        image.completeness,
        Some(ModuleCompleteness::Partial(vec![row("h")]))
    );

    let mut c = one_function("c", "h", true, Some(BodyGate::Ungated));
    c.completeness = Some(ModuleCompleteness::Complete);
    merge_into(&mut image, &c, &MergePolicy::EXECUTION_IMAGE).expect("merges");
    assert_eq!(
        image.completeness,
        Some(ModuleCompleteness::Complete),
        "every row resolved is completeness (an empty Partial is refused)"
    );
}

#[test]
fn differing_targets_are_refused() {
    let target = |triple: &str| TargetInfo {
        triple: triple.into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    };
    let mut a = one_function("a", "f", true, Some(BodyGate::Ungated));
    a.target_info = Some(target("aarch64-apple-darwin"));
    let mut b = one_function("b", "g", true, Some(BodyGate::Ungated));
    b.target_info = Some(target("x86_64-unknown-linux-gnu"));
    assert!(matches!(
        merged(&a, &b, &MergePolicy::EXECUTION_IMAGE),
        Err(MergeError::TargetMismatch { .. })
    ));
    b.target_info = a.target_info.clone();
    assert!(merged(&a, &b, &MergePolicy::EXECUTION_IMAGE).is_ok());
}

#[test]
fn file_less_spans_land_on_the_placeholder_file() {
    let mut with_files = returns_const("a", "f", 1);
    let file = with_files
        .intern_file("src/a.rs")
        .expect("Module::intern_file: test fixture");
    with_files.functions[0].blocks[0].body[0].span = Some(SourceSpan {
        file,
        line: 3,
        col: 1,
    });
    let mut fileless = returns_const("b", "g", 2);
    fileless.functions[0].blocks[0].body[0].span = Some(SourceSpan {
        file: 0,
        line: 9,
        col: 1,
    });
    for (x, y) in [(&with_files, &fileless), (&fileless, &with_files)] {
        let image = merged(x, y, &MergePolicy::EXECUTION_IMAGE).expect("merges");
        let span_of = |name: &str| {
            image.function_by_name(name).unwrap().blocks[0].body[0]
                .span
                .unwrap()
        };
        assert_eq!(image.files[span_of("f").file as usize], "src/a.rs");
        assert_eq!(image.files[span_of("g").file as usize], "");
        assert!(
            validate_module(&image).is_empty(),
            "{:?}",
            validate_module(&image)
        );
    }
}

/// `name` returning a constant whose one node carries a span into `path`
/// (`None`: a file-less span, the module keeping no file table).
fn spanned_const(module: &str, name: &str, path: Option<&str>) -> Module {
    let mut m = returns_const(module, name, 1);
    let file = path.map_or(0, |path| {
        m.intern_file(path)
            .expect("Module::intern_file: test fixture")
    });
    m.functions[0].blocks[0].body[0].span = Some(SourceSpan {
        file,
        line: 3,
        col: 1,
    });
    m
}

/// `Module.files` strings are debug-only: the V3 identity blanks them, and
/// the conformance tripwire `module_files_strings_are_debug_only` refuses a
/// reader. So the merge must be a function of the tables' LENGTHS: two `src`
/// builds that differ only in a path string (one V3 identity) merge into one
/// `dst` as one V3 identity with one file remap — even when one of them
/// spells a path `dst` already holds. Mutation control: deduplicating `src`
/// rows against `dst` by path (the pre-review merge) points `same_path`'s span
/// at `dst`'s row 0 and fails the `file(0)` and digest checks.
#[test]
fn ws4_11_review_path_strings_never_steer_the_file_map() {
    let dst = spanned_const("dst", "g", Some("src/a.rs"));
    let same_path = spanned_const("src", "f", Some("src/a.rs"));
    let other_path = spanned_const("src", "f", Some("src/b.rs"));
    assert_eq!(
        same_path.stable_digest(),
        other_path.stable_digest(),
        "control: the two builds are one V3 identity"
    );
    let mut digests = Vec::new();
    for src in [&same_path, &other_path] {
        let mut image = dst.clone();
        let remap = merge_into(&mut image, src, &MergePolicy::EXECUTION_IMAGE).expect("merges");
        assert_eq!(remap.file(0), Some(1), "src's row is its own appended row");
        assert_eq!(image.files.len(), 2);
        let f = image.function_by_name("f").unwrap();
        assert_eq!(f.blocks[0].body[0].span.unwrap().file, 1);
        assert!(
            validate_module(&image).is_empty(),
            "{:?}",
            validate_module(&image)
        );
        digests.push(image.stable_digest());
    }
    assert_eq!(digests[0], digests[1]);
}

/// The placeholder twin: a file-less `src` merged into a `dst` whose table
/// already holds a `""` row gets a placeholder of its OWN, exactly as into a
/// `dst` whose row spells a real path — so the two `dst` builds (one V3
/// identity) still merge to one. Mutation control: reusing `dst`'s `""` row
/// (a lookup by string) makes the first image one row shorter.
#[test]
fn ws4_11_review_the_placeholder_is_appended_never_looked_up() {
    let blank_row = spanned_const("dst", "g", Some(""));
    let real_row = spanned_const("dst", "g", Some("src/a.rs"));
    assert_eq!(blank_row.stable_digest(), real_row.stable_digest());
    let fileless = spanned_const("src", "f", None);
    let mut digests = Vec::new();
    for dst in [&blank_row, &real_row] {
        let mut image = dst.clone();
        merge_into(&mut image, &fileless, &MergePolicy::EXECUTION_IMAGE).expect("merges");
        assert_eq!(image.files.len(), 2);
        let f = image.function_by_name("f").unwrap();
        assert_eq!(f.blocks[0].body[0].span.unwrap().file, 1);
        assert_eq!(image.files[1], "");
        assert!(
            validate_module(&image).is_empty(),
            "{:?}",
            validate_module(&image)
        );
        digests.push(image.stable_digest());
    }
    assert_eq!(digests[0], digests[1]);
}

// ── nominal identity ─────────────────────────────────────────────────────────

fn handle(runtime: &str) -> Ty {
    Ty::Handle(Box::new(HandleTy {
        name: "Nat".into(),
        runtime: runtime.into(),
    }))
}

/// REVIEW (roadmap): nominal types are never unified by name. Two handles
/// with one name and two runtimes stay two types — the merge does not refuse
/// the pair (they are two legal types) — and a declaration of `sink` over
/// one runtime is never joined to a definition of `sink` over the other.
#[test]
fn handles_with_one_name_and_two_runtimes_stay_distinct() {
    let mut a = Module::new("a");
    let ta = a
        .add_type(handle("trust_bignum::Nat"))
        .expect("Module::add_type: test fixture");
    let mut b = Module::new("b");
    let tb = b
        .add_type(handle("other::Nat"))
        .expect("Module::add_type: test fixture");
    let mut image = a.clone();
    let remap = merge_into(&mut image, &b, &MergePolicy::EXECUTION_IMAGE).expect("two types");
    assert_ne!(remap.ty(tb), Some(ta), "never unified by name");
    assert_eq!(image.types.len(), 2);

    // The crossing: `sink` defined over one runtime, declared over the other.
    let sink = |module: &str, runtime: &str, bodied: bool| {
        let mut m = Module::new(module);
        let ft = m
            .add_func_type(FuncTy {
                abi: None,
                params: vec![handle(runtime)],
                returns: vec![],
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut f = Function::new(FuncId::new(0), "sink", ft, BlockId::new(0));
        f.linkage = Linkage::External;
        if bodied {
            let mut entry = Block::new(BlockId::new(0));
            entry.params.push((ValueId::new(0), handle(runtime)));
            entry
                .body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            f.blocks.push(entry);
        }
        m.try_add_function(f)
            .expect("Module::try_add_function: test fixture");
        m
    };
    let def = sink("a", "trust_bignum::Nat", true);
    let decl = sink("b", "other::Nat", false);
    for (x, y) in [(&def, &decl), (&decl, &def)] {
        assert_eq!(
            merged(x, y, &MergePolicy::EXECUTION_IMAGE),
            Err(MergeError::ConflictingDefinition {
                symbol: "sink".into(),
                field: "ty",
            }),
            "a cross-runtime call must never be joined"
        );
    }
}

fn node_struct(id: u32, payload: Ty) -> StructDef {
    StructDef {
        id: StructId::new(id),
        name: "Node".into(),
        fields: vec![
            FieldDef {
                name: "next".into(),
                ty: Ty::PtrMut(Box::new(Ty::Struct(StructId::new(id)))),
                offset: Some(0),
            },
            FieldDef {
                name: "value".into(),
                ty: payload,
                offset: Some(8),
            },
        ],
        size: Some(16),
        align: Some(8),
        repr: Default::default(),
        origin: None,
    }
}

/// A self-referential struct dedups coinductively; an equally named struct
/// with a different payload stays a second struct.
#[test]
fn recursive_structs_dedup_only_when_identical() {
    let with = |module: &str, id: u32, payload: Ty| {
        let mut m = Module::new(module);
        // A leading unrelated struct so the ids differ across modules.
        for k in 0..id {
            m.structs.push(StructDef {
                id: StructId::new(k),
                name: format!("Pad{k}"),
                fields: vec![],
                size: Some(0),
                align: Some(1),
                repr: Default::default(),
                origin: None,
            });
        }
        m.structs.push(node_struct(id, payload));
        m.add_type(Ty::Struct(StructId::new(id)))
            .expect("Module::add_type: test fixture");
        m
    };
    let a = with("a", 0, Ty::I64);
    let same = with("b", 2, Ty::I64);
    let mut image = a.clone();
    let remap = merge_into(&mut image, &same, &MergePolicy::EXECUTION_IMAGE).expect("merges");
    assert_eq!(remap.struct_(StructId::new(2)), Some(StructId::new(0)));
    assert_eq!(remap.ty(TyId::new(0)), Some(TyId::new(0)));
    assert_eq!(
        image.structs.iter().filter(|s| s.name == "Node").count(),
        1,
        "identical recursive structs are one"
    );

    let different = with("c", 0, Ty::I32);
    let mut image = a.clone();
    let remap = merge_into(&mut image, &different, &MergePolicy::EXECUTION_IMAGE).expect("merges");
    let mapped = remap.struct_(StructId::new(0)).expect("mapped");
    assert_ne!(mapped, StructId::new(0), "never unified by name");
    assert_eq!(
        image.struct_def(mapped).unwrap().fields[0].ty,
        Ty::PtrMut(Box::new(Ty::Struct(mapped))),
        "the new struct's self-reference follows it"
    );
}

// ── the v42 tuple-layout fixture behind a non-empty type table ──────────────

#[test]
fn a_tuple_layout_keeps_naming_its_tuple_after_the_merge() {
    let tuples = generate::build_declared_tuple_v42().expect("fixture");
    let mut image = generate::build_ty_primitives().expect("fixture");
    // The subject is the type-table remap, not the target: pin both inputs
    // to the tuple fixture's target (two pinned targets are refused).
    image.target_info = tuples.target_info.clone();
    image.types.push(Ty::Tuple(vec![Ty::U8, Ty::U64, Ty::U16]));
    image.types.push(Ty::Bool);
    let before = classes(&image);
    let remap = merge_into(&mut image, &tuples, &MergePolicy::VERIFICATION_IMAGE).expect("merges");
    for layout in &tuples.tuple_layouts {
        let mapped = remap.ty(layout.tuple_type).expect("mapped");
        assert!(
            image.tuple_layouts.iter().any(|d| d.tuple_type == mapped),
            "the descriptor follows its tuple type"
        );
    }
    let after = classes(&image);
    assert!(
        !after.contains("TupleLayoutInconsistent"),
        "a descriptor names a type other than its tuple: {after:?}"
    );
    let alone = {
        let mut m = identity_for(&tuples);
        merge_into(&mut m, &tuples, &MergePolicy::VERIFICATION_IMAGE).expect("merges");
        classes(&m)
    };
    let union: BTreeSet<String> = before.union(&alone).cloned().collect();
    assert!(after.is_subset(&union), "{after:?} vs {union:?}");
}

// ── ported proof-program rows ───────────────────────────────────────────────

/// Row `design-0827/functy-interning`: "FuncTy is interned by structural
/// equality against module.func_types on append and on the general-tier
/// merge, including recursive Ty::Func id remap."
#[test]
fn design_0827_functy_interning() {
    // On append: two Clean functions with one signature into a module that
    // already holds it share one row.
    let binop = || FuncTy {
        abi: None,
        params: vec![Ty::U32, Ty::U32],
        returns: vec![Ty::U32],
        is_vararg: false,
    };
    let mut mb = ModuleBuilder::new("clean");
    let held = mb.intern_func_type(binop());
    let first = mb.intern_func_type(binop());
    let second = mb.intern_func_type(binop());
    assert_eq!((first, second), (held, held));
    assert_eq!(
        mb.build()
            .expect("ModuleBuilder::build: test fixture")
            .func_types
            .len(),
        1
    );

    // On merge: a signature that takes a callable `Ty::Func(id)` resolves to
    // dst's equal row through the recursive remap, though src numbers its
    // rows the other way round.
    let mut dst = Module::new("dst");
    let d_inner = dst
        .add_func_type(binop())
        .expect("Module::add_func_type: test fixture");
    let d_outer = dst
        .add_func_type(FuncTy {
            abi: None,
            params: vec![Ty::Func(d_inner), Ty::U32],
            returns: vec![Ty::U32],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut src = Module::new("src");
    src.func_types.push(FuncTy {
        abi: None,
        params: vec![Ty::Func(trust_ir::value::FuncTyId::new(1)), Ty::U32],
        returns: vec![Ty::U32],
        is_vararg: false,
    });
    src.func_types.push(binop());
    let mut apply = Function::new(
        FuncId::new(0),
        "apply",
        trust_ir::value::FuncTyId::new(0),
        BlockId::new(0),
    );
    apply.linkage = Linkage::External;
    apply.producer = Some(Producer::Clean);
    src.try_add_function(apply)
        .expect("Module::try_add_function: test fixture");
    let remap = merge_into(&mut dst, &src, &MergePolicy::EXECUTION_IMAGE).expect("merges");
    assert_eq!(
        remap.func_ty(trust_ir::value::FuncTyId::new(1)),
        Some(d_inner)
    );
    assert_eq!(
        remap.func_ty(trust_ir::value::FuncTyId::new(0)),
        Some(d_outer)
    );
    assert_eq!(dst.function_by_name("apply").unwrap().ty, d_outer);
}

/// Row `exec-log-and-tcb/module-merge-and-id-remap`: "Join a Clean-produced
/// module into the Rust crate module (tables remapped, claim-free channels,
/// target_info equality, name-collision and unremapped-table refusal)."
#[test]
fn exec_log_and_tcb_module_merge_and_id_remap() {
    // Module A (Rust): struct S and `f(S) -> i32`.
    let mut a = Module::new("rust_crate");
    a.structs.push(StructDef {
        id: StructId::new(0),
        name: "S".into(),
        fields: vec![FieldDef {
            name: "x".into(),
            ty: Ty::I32,
            offset: Some(0),
        }],
        size: Some(4),
        align: Some(4),
        repr: Default::default(),
        origin: None,
    });
    let f_ty = a
        .add_func_type(FuncTy {
            abi: None,
            params: vec![Ty::Struct(StructId::new(0))],
            returns: vec![Ty::I32],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), "f", f_ty, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry
        .params
        .push((ValueId::new(0), Ty::Struct(StructId::new(0))));
    entry.body.push(
        // `ExtractField.ty` is the FIELD (result) type (WS2.2).
        InstrNode::new(Inst::ExtractField {
            ty: Ty::I32,
            aggregate: ValueId::new(0),
            field: 0,
        })
        .with_result(ValueId::new(1)),
    );
    entry.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(1)],
    }));
    f.blocks.push(entry);
    f.producer = Some(Producer::TRust);
    f.body_gate = Some(BodyGate::Ungated);
    a.try_add_function(f)
        .expect("Module::try_add_function: test fixture");

    // Module B (Clean): its own tables, `g() -> i32` calling `h`.
    let mut b = Module::new("clean_unit");
    b.add_type(Ty::Bool)
        .expect("Module::add_type: test fixture");
    let unit = b
        .add_func_type(unit_ty())
        .expect("Module::add_func_type: test fixture");
    let i32_ty = b
        .add_func_type(FuncTy {
            abi: None,
            params: vec![],
            returns: vec![Ty::I32],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let _ = unit;
    let mut h = Function::new(FuncId::new(0), "h", i32_ty, BlockId::new(0));
    let mut h_entry = Block::new(BlockId::new(0));
    h_entry.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(41),
        })
        .with_result(ValueId::new(0)),
    );
    h_entry.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    h.blocks.push(h_entry);
    h.producer = Some(Producer::Clean);
    h.body_gate = Some(BodyGate::Ungated);
    b.try_add_function(h)
        .expect("Module::try_add_function: test fixture");
    let mut g = Function::new(FuncId::new(1), "g", i32_ty, BlockId::new(0));
    let mut g_entry = Block::new(BlockId::new(0));
    g_entry.body.push(
        InstrNode::new(Inst::Call {
            callee: FuncId::new(0),
            args: vec![],
        })
        .with_result(ValueId::new(0)),
    );
    g_entry.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    g.blocks.push(g_entry);
    g.producer = Some(Producer::Clean);
    g.body_gate = Some(BodyGate::Ungated);
    b.try_add_function(g)
        .expect("Module::try_add_function: test fixture");

    assert!(validate_module(&a).is_empty(), "{:?}", validate_module(&a));
    assert!(validate_module(&b).is_empty(), "{:?}", validate_module(&b));
    let mut image = a.clone();
    let remap = merge_into(&mut image, &b, &MergePolicy::VERIFICATION_IMAGE).expect("joins");
    assert!(
        validate_module(&image).is_empty(),
        "the joined module validates: {:?}",
        validate_module(&image)
    );
    // B's ids were remapped past A's.
    let g_id = remap.func(FuncId::new(1)).expect("g mapped");
    let h_id = remap.func(FuncId::new(0)).expect("h mapped");
    assert_eq!((h_id, g_id), (FuncId::new(1), FuncId::new(2)));
    let g = image.function_by_id(g_id).expect("g present");
    assert!(matches!(
        g.blocks[0].body[0].inst,
        Inst::Call { callee, .. } if callee == h_id
    ));
    assert_eq!(
        remap.func_ty(trust_ir::value::FuncTyId::new(1)),
        Some(image.function_by_id(g_id).unwrap().ty)
    );
    // A name collision with a different body is refused by name.
    let mut collide = b.clone();
    collide.functions[1].name = "f".into();
    assert!(matches!(
        merged(&a, &collide, &MergePolicy::VERIFICATION_IMAGE),
        Err(MergeError::ConflictingDefinition { ref symbol, .. }) if symbol == "f"
    ));
    // Differing targets are refused.
    let mut targeted = b.clone();
    targeted.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    let mut other = a.clone();
    other.target_info = Some(TargetInfo {
        triple: "x86_64-unknown-linux-gnu".into(),
        ..targeted.target_info.clone().unwrap()
    });
    assert!(matches!(
        merged(&other, &targeted, &MergePolicy::VERIFICATION_IMAGE),
        Err(MergeError::TargetMismatch { .. })
    ));
    // The unremapped-table refusal: a dangling id is refused by name, never
    // carried stale.
    let mut dangling = b.clone();
    dangling.functions[1].blocks[0].body[0].inst = Inst::Call {
        callee: FuncId::new(9),
        args: vec![],
    };
    assert_eq!(
        merged(&a, &dangling, &MergePolicy::VERIFICATION_IMAGE),
        Err(MergeError::Dangling {
            table: "functions",
            id: 9,
        })
    );
}

// ── WS4.11 review: adversarial inputs per rule ───────────────────────────────

/// `name: () -> ()` defined (returning) or declared, whose signature is row
/// `alias` of a table holding `rows` equal `() -> ()` rows.
fn aliased_signature_function(module: &str, rows: u32, alias: u32, defined: bool) -> Module {
    let mut m = Module::new(module);
    for _ in 0..rows {
        m.add_func_type(unit_ty())
            .expect("Module::add_func_type: test fixture");
    }
    let mut f = Function::new(
        FuncId::new(0),
        "f",
        trust_ir::value::FuncTyId::new(alias),
        BlockId::new(0),
    );
    f.linkage = Linkage::External;
    if defined {
        let mut entry = Block::new(BlockId::new(0));
        entry
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        f.blocks.push(entry);
        f.body_gate = Some(BodyGate::Ungated);
    }
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    m
}

/// The signature table is positional and NOT interned (`add_func_type`
/// appends), so one signature routinely sits at two ids. A `src` reference
/// lands on the FIRST equal `dst` row; `dst`'s function may name an alias.
/// Signatures compare by content: an identical definition dedups and a
/// declaration resolves, over the alias, in both orders.
#[test]
fn ws4_11_review_aliased_signatures_are_one_signature() {
    let def_on_alias = aliased_signature_function("a", 2, 1, true);
    let def_on_first = aliased_signature_function("b", 1, 0, true);
    let decl_on_first = aliased_signature_function("c", 1, 0, false);
    for (x, y) in [
        (&def_on_alias, &def_on_first),
        (&def_on_first, &def_on_alias),
        (&def_on_alias, &decl_on_first),
        (&decl_on_first, &def_on_alias),
        (&def_on_alias, &def_on_alias),
    ] {
        let image = merged(x, y, &MergePolicy::EXECUTION_IMAGE)
            .unwrap_or_else(|e| panic!("{} <- {}: {e}", x.name, y.name));
        assert_eq!(image.functions.len(), 1);
        assert!(!image.functions[0].blocks.is_empty());
        assert!(
            validate_module(&image).is_empty(),
            "{:?}",
            validate_module(&image)
        );
    }
}

/// The negative twins of the content comparison: a different signature (a
/// return lane), a different variadic flag and a different calling
/// convention stay conflicts, whichever row each side names.
#[test]
fn ws4_11_review_different_signatures_still_conflict() {
    let def = aliased_signature_function("a", 2, 1, true);
    let mut returns = aliased_signature_function("b", 1, 0, false);
    returns.func_types[0].returns = vec![Ty::I32];
    let mut vararg = aliased_signature_function("c", 1, 0, false);
    vararg.func_types[0].is_vararg = true;
    let mut cc = aliased_signature_function("d", 1, 0, false);
    cc.functions[0].calling_conv = trust_ir::CallingConv::Cold;
    let mut body = aliased_signature_function("e", 1, 0, true);
    body.func_types[0].params = vec![Ty::I64];
    for (other, field) in [
        (&returns, "ty"),
        (&vararg, "ty"),
        (&cc, "calling_conv"),
        (&body, "ty"),
    ] {
        for (x, y) in [(&def, other), (other, &def)] {
            assert_eq!(
                merged(x, y, &MergePolicy::EXECUTION_IMAGE),
                Err(MergeError::ConflictingDefinition {
                    symbol: "f".into(),
                    field,
                }),
                "{} <- {}",
                x.name,
                y.name
            );
        }
    }
}

/// Two definitions that differ only in their claims are a conflict under the
/// verification image (input order must not pick a proof claim), naming the
/// field; the execution image strips both claims first, so they dedup.
#[test]
fn ws4_11_review_claims_are_part_of_definition_identity() {
    let plain = one_function("a", "f", true, Some(BodyGate::Ungated));
    let mut proved = plain.clone();
    proved.name = "b".into();
    proved.functions[0].summary = Some(FunctionSummary::new().proved());
    let mut annotated = plain.clone();
    annotated.name = "c".into();
    annotated.functions[0].proofs = vec![trust_ir::proof::ProofAnnotation::Pure];
    let mut other_producer = plain.clone();
    other_producer.name = "d".into();
    other_producer.functions[0].producer = Some(Producer::Clean);
    for (other, field) in [
        (&proved, "summary"),
        (&annotated, "proofs"),
        (&other_producer, "producer"),
    ] {
        for (x, y) in [(&plain, other), (other, &plain)] {
            assert_eq!(
                merged(x, y, &MergePolicy::VERIFICATION_IMAGE),
                Err(MergeError::ConflictingDefinition {
                    symbol: "f".into(),
                    field,
                }),
                "{} <- {}",
                x.name,
                y.name
            );
        }
    }
    let image =
        merged(&plain, &proved, &MergePolicy::EXECUTION_IMAGE).expect("claims stripped first");
    assert_eq!(image.functions[0].summary, None);
}

/// A refused empty `Partial` (`EmptyPartialClaim`) claims partiality without
/// naming what is missing. The merge keeps exactly that spelling — never the
/// other side's rows, never `Complete` — so the merged image is refused for
/// the same reason the input was; `None` (no claim) still absorbs it.
#[test]
fn ws4_11_review_an_empty_partial_claim_is_never_upgraded() {
    let row = UnloweredRow {
        symbol: "h".into(),
        display_path: None,
        reason: "not lowered".into(),
    };
    let mut empty = one_function("a", "f", true, Some(BodyGate::Ungated));
    empty.completeness = Some(ModuleCompleteness::Partial(vec![]));
    let mut rows = one_function("b", "g", true, Some(BodyGate::Ungated));
    rows.completeness = Some(ModuleCompleteness::Partial(vec![row]));
    let mut complete = one_function("c", "h", true, Some(BodyGate::Ungated));
    complete.completeness = Some(ModuleCompleteness::Complete);
    for other in [&rows, &complete] {
        for (x, y) in [(&empty, other), (other, &empty)] {
            let image = merged(x, y, &MergePolicy::EXECUTION_IMAGE).expect("merges");
            assert_eq!(
                image.completeness,
                Some(ModuleCompleteness::Partial(vec![])),
                "{} <- {}",
                x.name,
                y.name
            );
            assert!(
                classes(&image).contains("EmptyPartialClaim"),
                "{:?}",
                classes(&image)
            );
        }
    }
    let mut none = one_function("d", "k", true, Some(BodyGate::Ungated));
    none.completeness = None;
    assert_eq!(
        merged(&empty, &none, &MergePolicy::EXECUTION_IMAGE)
            .expect("merges")
            .completeness,
        None
    );
}

/// Amendment D (§20): a module dropping struct `Owned` through glue `glue`,
/// defined or only declared. Function 0 is the glue, function 1 the user.
fn drop_glue_module(module: &str, glue: &str, owned_field: Ty, defined: bool) -> Module {
    let mut m = Module::new(module);
    let owned = Ty::Struct(m.add_struct(StructDef {
        id: StructId::new(0),
        name: "Owned".into(),
        fields: vec![FieldDef {
            name: "data".into(),
            ty: owned_field,
            offset: None,
        }],
        size: None,
        align: None,
        repr: Default::default(),
        origin: None,
    }));
    let sig = m
        .add_func_type(FuncTy {
            abi: None,
            params: vec![Ty::Ptr],
            returns: vec![],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut glue_fn = Function::new(FuncId::new(0), glue, sig, BlockId::new(0));
    glue_fn.linkage = Linkage::External;
    if defined {
        let mut block = Block::new(BlockId::new(0));
        block.params.push((ValueId::new(0), Ty::Ptr));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        glue_fn.blocks.push(block);
        glue_fn.body_gate = Some(BodyGate::Ungated);
    }
    m.functions.push(glue_fn);
    let mut user = Function::new(
        FuncId::new(1),
        format!("user_{module}"),
        sig,
        BlockId::new(0),
    );
    let mut block = Block::new(BlockId::new(0));
    block.params.push((ValueId::new(0), Ty::Ptr));
    block.body.push(InstrNode::new(Inst::Drop {
        ty: owned.clone(),
        ptr: ValueId::new(0),
    }));
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    user.blocks.push(block);
    user.body_gate = Some(BodyGate::Ungated);
    m.functions.push(user);
    m.set_drop_glue(owned, FuncId::new(0)).expect("one row");
    m
}

/// The drop-glue table is CARRIED (dropping it would turn every resolved
/// drop into an unresolved one): a declaration's row and the definition's
/// row are one row naming the one merged glue and the one merged `Owned`,
/// in either order, and the table stays canonical.
#[test]
fn ws4_11_review_drop_glue_rows_are_carried_and_restated_rows_collapse() {
    let def = drop_glue_module("a", "drop_owned", Ty::Ptr, true);
    let decl = drop_glue_module("b", "drop_owned", Ty::Ptr, false);
    for (x, y) in [(&def, &decl), (&decl, &def)] {
        let mut image = Module::new("image");
        merge_into(&mut image, x, &MergePolicy::EXECUTION_IMAGE).expect("first");
        let remap = merge_into(&mut image, y, &MergePolicy::EXECUTION_IMAGE).expect("second");
        let glue = image.function_by_name("drop_owned").expect("glue").id;
        assert_eq!(remap.func(FuncId::new(0)), Some(glue));
        assert_eq!(
            image.drop_glue,
            vec![trust_ir::DropGlueEntry {
                glue,
                ty: Ty::Struct(StructId::new(0)),
            }],
            "{} <- {}",
            x.name,
            y.name
        );
        assert_eq!(
            image.drop_glue_for(&Ty::Struct(StructId::new(0))),
            trust_ir::DropResolution::Resolved(glue)
        );
        let report = trust_ir_build::validate::validate_module_report(&image);
        assert!(report.errors().is_empty(), "{:?}", report.errors());
        assert!(
            report.unresolved_drops().is_empty(),
            "every merged drop resolves"
        );
    }
    // Into the identity element the table is the input's, byte for byte.
    let mut image = Module::new("a");
    merge_into(&mut image, &def, &MergePolicy::EXECUTION_IMAGE).expect("identity");
    assert_eq!(image.drop_glue, def.drop_glue);
}

/// Input order never chooses a destructor: two glues for one type, and one
/// glue for two (structurally distinct) types, are refused, `dst` unchanged.
#[test]
fn ws4_11_review_contradictory_drop_glue_is_refused() {
    let a = drop_glue_module("a", "drop_owned", Ty::Ptr, true);
    let other_glue = drop_glue_module("b", "drop_owned_too", Ty::Ptr, true);
    // Same glue symbol and body, but `Owned` with another field type: the
    // nominal struct does not dedup, so one glue would destroy two types.
    let other_type = drop_glue_module("c", "drop_owned", Ty::U64, true);
    for (other, type_has_glue) in [(&other_glue, true), (&other_type, false)] {
        for (x, y) in [(&a, other), (other, &a)] {
            let mut image = x.clone();
            let before = format!("{image:?}");
            let error = merge_into(&mut image, y, &MergePolicy::EXECUTION_IMAGE)
                .map(|_| ())
                .expect_err("contradictory drop glue");
            match &error {
                MergeError::DropGlueConflict { conflict, .. } => assert_eq!(
                    matches!(conflict, trust_ir::DropGlueConflict::TypeHasGlue { .. }),
                    type_has_glue,
                    "{error}"
                ),
                other => panic!("{} <- {}: {other}", x.name, y.name),
            }
            assert!(error.to_string().contains("drop_glue row"), "{error}");
            assert_eq!(
                format!("{image:?}"),
                before,
                "a refused merge writes nothing"
            );
        }
    }
}

/// Amendment P: a panic site names a function (its entry) and, for a static
/// location, a global. Both are module ids and follow the remap; a merger
/// that copied them verbatim would point the site at `dst`'s first function
/// and first global.
#[test]
fn ws4_11_review_panic_sites_follow_the_remap() {
    let global = |name: &str| trust_ir::Global {
        name: name.into(),
        ty: Ty::U64,
        mutable: false,
        initializer: Some(Constant::Int(7)),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    };
    let mut src = Module::new("src");
    let unit = src
        .add_func_type(unit_ty())
        .expect("Module::add_func_type: test fixture");
    let bool_in = src
        .add_func_type(FuncTy {
            abi: None,
            params: vec![Ty::Bool],
            returns: vec![],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    src.globals.push(global("loc"));
    let mut entry_fn = Function::new(FuncId::new(0), "panic_entry", unit, BlockId::new(0));
    entry_fn.linkage = Linkage::External;
    src.functions.push(entry_fn);
    let mut check = Function::new(FuncId::new(1), "check", bool_in, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.params.push((ValueId::new(0), Ty::Bool));
    block.body.push(InstrNode::new(Inst::Assert {
        cond: ValueId::new(0),
        kind: Default::default(),
        site: Some(trust_ir::PanicSite {
            entry: FuncId::new(0),
            location: trust_ir::PanicLocation::Global(trust_ir::value::GlobalId::new(0)),
        }),
    }));
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    check.blocks.push(block);
    check.body_gate = Some(BodyGate::Ungated);
    src.functions.push(check);

    let mut dst = returns_const("dst", "unrelated", 3);
    dst.globals.push(global("first"));
    dst.globals.push(global("second"));
    let remap = merge_into(&mut dst, &src, &MergePolicy::EXECUTION_IMAGE).expect("merges");
    let check = dst.function_by_name("check").expect("merged");
    let Inst::Assert {
        site: Some(site), ..
    } = &check.blocks[0].body[0].inst
    else {
        panic!("the assert keeps its site");
    };
    let entry = dst.function_by_name("panic_entry").expect("merged").id;
    assert_eq!(site.entry, entry);
    assert_eq!(remap.func(FuncId::new(0)), Some(entry));
    let trust_ir::PanicLocation::Global(loc) = site.location else {
        panic!("a static location");
    };
    assert_eq!(dst.globals[loc.as_usize()].name, "loc");
    assert_eq!(remap.global(trust_ir::value::GlobalId::new(0)), Some(loc));
}

const CLEAN_ORIGIN: &str = "@trust-internal::clean-origin-disclosure-v1";
const DEFERRED: &str = "@trust-internal::deferred-verification-disclosure-v1";

fn disclosure(name: &str, keys: &[&str]) -> trust_ir::SpecModule {
    let mut spec = trust_ir::SpecModule::new(name);
    for key in keys {
        spec.invariants
            .push(trust_ir::SpecInvariant::new(*key, "{\"schema\":\"row\"}"));
    }
    spec
}

/// Every reserved Trust disclosure is either known id-free or guarded: the
/// allowlist names only reserved modules, so a reserved name added later is
/// id-binding (refused across a relocation) until someone shows otherwise.
#[test]
fn ws4_11_review_id_free_disclosures_are_reserved_names() {
    for name in trust_ir_build::merge::ID_FREE_DISCLOSURES {
        assert!(
            trust_ir_build::validate::RESERVED_TRUST_INTERNAL_SPEC_MODULES.contains(name),
            "{name}"
        );
    }
    assert!(
        trust_ir_build::validate::RESERVED_TRUST_INTERNAL_SPEC_MODULES
            .iter()
            .any(|name| !trust_ir_build::merge::ID_FREE_DISCLOSURES.contains(name)),
        "some reserved disclosure binds function ids"
    );
}

/// A `src` clean-origin disclosure keys its rows `fn:<FuncId index>` in
/// opaque text the merge cannot rewrite. Into a module with functions the
/// row would name whatever the image keeps at that index — refused, `dst`
/// unchanged. Into the identity element nothing moves and it is carried;
/// the execution image strips it (counted) instead.
#[test]
fn ws4_11_review_a_src_id_binding_disclosure_is_never_relocated() {
    let mut src = returns_const("src", "f", 1);
    src.spec_modules.push(disclosure(CLEAN_ORIGIN, &["fn:0"]));
    // dst functions: one unrelated, and one with f's symbol (dedup) — both
    // are relocations of the key's meaning or of its neighbours.
    for dst_fn in ["unrelated", "f"] {
        let mut dst = returns_const("dst", dst_fn, 1);
        let before = format!("{dst:?}");
        assert_eq!(
            merge_into(&mut dst, &src, &MergePolicy::VERIFICATION_IMAGE).map(|_| ()),
            Err(MergeError::UnrelocatableDisclosure {
                name: CLEAN_ORIGIN.into()
            }),
            "into a dst defining {dst_fn}"
        );
        assert_eq!(format!("{dst:?}"), before, "a refused merge writes nothing");
    }
    let mut image = identity_for(&src);
    merge_into(&mut image, &src, &MergePolicy::VERIFICATION_IMAGE).expect("nothing moves");
    assert_eq!(image.spec_modules, src.spec_modules);
    let mut image = returns_const("dst", "unrelated", 1);
    let remap = merge_into(&mut image, &src, &MergePolicy::EXECUTION_IMAGE).expect("stripped");
    assert_eq!(remap.stripped().spec_modules, 1);
    assert!(image.spec_modules.is_empty());
}

/// A `dst` disclosure keeps its ids (`dst` ids never move): a merge that
/// only appends unrelated functions keeps it. It is refused when the merge
/// replaces the function a key names (a declaration's row would describe
/// the definition), or when a key dangles or does not parse (an appended
/// function could land on it).
#[test]
fn ws4_11_review_a_dst_id_binding_disclosure_is_never_retargeted() {
    let unrelated = returns_const("src", "g", 2);
    let mut dst = returns_const("dst", "f", 1);
    dst.spec_modules.push(disclosure(CLEAN_ORIGIN, &["fn:0"]));
    let image = merged(&dst, &unrelated, &MergePolicy::VERIFICATION_IMAGE).expect("appends only");
    assert_eq!(image.spec_modules, dst.spec_modules);

    for key in ["fn:5", "fn:00", "fn:x", "row"] {
        let mut dangling = returns_const("dst", "f", 1);
        dangling
            .spec_modules
            .push(disclosure(CLEAN_ORIGIN, &["fn:0", key]));
        assert_eq!(
            merged(&dangling, &unrelated, &MergePolicy::VERIFICATION_IMAGE),
            Err(MergeError::UnrelocatableDisclosure {
                name: CLEAN_ORIGIN.into()
            }),
            "key {key}"
        );
        // Nothing changes when nothing is added: the same disclosure stays.
        let mut empty = Module::new("empty");
        empty.completeness = None;
        assert!(merged(&dangling, &empty, &MergePolicy::VERIFICATION_IMAGE).is_ok());
    }

    let mut declared = one_function("dst", "f", false, None);
    declared
        .spec_modules
        .push(disclosure(CLEAN_ORIGIN, &["fn:0"]));
    let definition = one_function("src", "f", true, Some(BodyGate::Ungated));
    assert_eq!(
        merged(&declared, &definition, &MergePolicy::EXECUTION_IMAGE),
        Err(MergeError::UnrelocatableDisclosure {
            name: CLEAN_ORIGIN.into()
        })
    );
}

/// The deferred-verification notice binds no id ("MUST NOT be treated as
/// borrow-checked"); it is carried across a relocation — dropping it would
/// lose the caveat — in either direction.
#[test]
fn ws4_11_review_the_id_free_deferred_notice_is_carried() {
    let mut noticed = returns_const("a", "f", 1);
    noticed
        .spec_modules
        .push(disclosure(DEFERRED, &["disclosure"]));
    let other = returns_const("b", "g", 2);
    for (x, y) in [(&noticed, &other), (&other, &noticed)] {
        let image = merged(x, y, &MergePolicy::VERIFICATION_IMAGE).expect("carried");
        assert_eq!(image.spec_modules, noticed.spec_modules);
    }
}

// ── closure layouts and nominal origin (wire v58, WS3.9) ─────────────────────

/// A closure-layout row follows its closure type's remap. Merged after a
/// module that already holds a closure type, `build_closure_layout`'s type
/// moves to a new id and its row must move with it (an unremapped row would
/// lay out the OTHER closure, `ClosureLayoutIncoherent`). Merged with itself
/// the type is one type and the identical row one row; a row that disagrees
/// with the row the merged image already holds for that type is a conflict
/// naming the field, in both orders — never "keep the first".
#[test]
fn closure_layout_rows_follow_their_closure_type() {
    let laid_out = generate::build_closure_layout().expect("fixture");
    let mut other = Module::new("other");
    let unary = other
        .add_func_type(FuncTy {
            abi: None,
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    other
        .add_closure_type(trust_ir::ClosureTy {
            func: unary,
            captures: vec![Ty::I32],
        })
        .expect("Module::add_closure_type: test fixture");
    let mut image = other.clone();
    let remap = merge_into(&mut image, &laid_out, &MergePolicy::EXECUTION_IMAGE).expect("merges");
    let moved = remap
        .closure(laid_out.closure_layouts[0].closure)
        .expect("mapped");
    assert_ne!(moved, laid_out.closure_layouts[0].closure, "the type moved");
    assert_eq!(image.closure_layouts.len(), 1);
    assert_eq!(image.closure_layouts[0].closure, moved);
    assert_eq!(
        classes(&image),
        classes(&laid_out),
        "{:?}",
        validate_module(&image)
    );

    let twice = merged(&laid_out, &laid_out, &MergePolicy::EXECUTION_IMAGE).expect("dedups");
    assert_eq!(twice.closure_layouts.len(), 1);

    let mut skewed = laid_out.clone();
    skewed.name = "skewed".into();
    skewed.closure_layouts[0].capture_offsets = vec![0, 8];
    for (x, y) in [(&laid_out, &skewed), (&skewed, &laid_out)] {
        assert!(
            matches!(
                merged(x, y, &MergePolicy::EXECUTION_IMAGE),
                Err(MergeError::ConflictingDefinition {
                    field: "capture_offsets",
                    ..
                })
            ),
            "{} <- {}",
            x.name,
            y.name
        );
    }
    // The layout table itself, without a body to collide on.
    let mut bare = laid_out.clone();
    bare.functions.clear();
    let mut bare_skewed = skewed.clone();
    bare_skewed.functions.clear();
    assert_eq!(
        merged(&bare, &bare_skewed, &MergePolicy::EXECUTION_IMAGE),
        Err(MergeError::ConflictingDefinition {
            symbol: format!(
                "closure layout closure.{}",
                bare.closure_layouts[0].closure.index()
            ),
            field: "capture_offsets",
        })
    );
}

/// A nominal `origin` is part of a definition's identity in the merge: the
/// fixture merged with itself is one set of types, and the same definitions
/// with their origins erased stay SECOND types (fresh ids), never unified by
/// name or shape. Mutation control: a struct / enum row that drops `origin`
/// in the remap stops the fixture deduping with itself (the `twice` counts);
/// one that ignores `origin` in the `dst` match unifies the erased twin.
#[test]
fn nominal_origin_is_part_of_definition_identity() {
    let stamped = generate::build_nominal_type_origin().expect("fixture");
    let stamped_structs = stamped
        .structs
        .iter()
        .filter(|d| d.origin.is_some())
        .count();
    let stamped_enums = stamped.enums.iter().filter(|d| d.origin.is_some()).count();
    assert!(
        stamped_structs > 0 && stamped_enums > 0,
        "the fixture stamps both"
    );
    let twice = merged(&stamped, &stamped, &MergePolicy::EXECUTION_IMAGE).expect("dedups");
    assert_eq!(twice.structs.len(), stamped.structs.len());
    assert_eq!(twice.enums.len(), stamped.enums.len());

    // Erase every origin: each STAMPED definition becomes a second type, each
    // unstamped one is literally equal and dedups.
    let mut erased = stamped.clone();
    erased.name = "erased".into();
    for def in &mut erased.structs {
        def.origin = None;
    }
    for def in &mut erased.enums {
        def.origin = None;
    }
    let image = merged(&stamped, &erased, &MergePolicy::EXECUTION_IMAGE).expect("merges");
    assert_eq!(image.structs.len(), stamped.structs.len() + stamped_structs);
    assert_eq!(image.enums.len(), stamped.enums.len() + stamped_enums);
    assert!(
        image.structs[stamped.structs.len()..]
            .iter()
            .all(|d| d.origin.is_none()),
        "the appended structs are the erased twins"
    );
}

// ── WS1.14: effect summaries (wire v59) ─────────────────────────────────────

/// A mutable, initialized, `Internal` `u64` global named `name`.
fn counter_global(name: &str) -> trust_ir::Global {
    trust_ir::Global {
        name: name.into(),
        ty: Ty::U64,
        mutable: true,
        initializer: Some(Constant::Int(0)),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    }
}

/// A module holding only the globals `names`, in order.
fn globals_only(module: &str, names: &[&str]) -> Module {
    let mut m = Module::new(module);
    m.globals = names.iter().map(|name| counter_global(name)).collect();
    m
}

/// The effect summary of function `name` in `module`.
fn effects_of(module: &Module, name: &str) -> Option<EffectSummary> {
    module
        .functions
        .iter()
        .find(|f| f.name == name)
        .unwrap_or_else(|| panic!("@{name} is in the image"))
        .summary
        .as_ref()
        .and_then(|s| s.effects.clone())
}

/// WS1.14's `build_effect_summaries` merged behind two globals: its global
/// `COUNTER` moves from id 0 to id 2, and `set`'s write set names the moved
/// global, so the merged image still validates clean (`set` honours its
/// summary). `add` (pure) and `caller` (top) carry verbatim. The execution
/// image strips every summary to `None` (UNRECORDED — a caller havocs), never
/// inventing an effect claim. Mutation control: copying the place verbatim
/// leaves `Global(0)` (the image's `EARLIER0`, which `set` never touches)
/// and fails the exact-set assertion and `EffectSummaryViolated` (the
/// written `COUNTER` is uncovered).
#[test]
fn ws1_14_effect_summaries_follow_the_global_remap() {
    use trust_ir::value::GlobalId;

    let fixture = generate::build_effect_summaries().expect("fixture");
    assert!(
        validate_module(&fixture).is_empty(),
        "control: the fixture validates clean: {:?}",
        validate_module(&fixture)
    );
    let dst = globals_only("dst", &["EARLIER0", "EARLIER1"]);

    let mut image = dst.clone();
    let remap = merge_into(&mut image, &fixture, &MergePolicy::VERIFICATION_IMAGE).expect("merges");
    let counter = remap.global(GlobalId::new(0)).expect("COUNTER is mapped");
    assert_eq!(
        counter,
        GlobalId::new(2),
        "COUNTER moved past dst's globals"
    );
    assert_eq!(image.globals[counter.as_usize()].name, "COUNTER");
    assert_eq!(
        effects_of(&image, "set"),
        Some(EffectSummary::pure().writing(EffectSet::of([
            EffectPlace::ParamPointee { index: 0 },
            EffectPlace::Global(counter),
        ]))),
        "set's write set names the moved global"
    );
    assert_eq!(effects_of(&image, "add"), Some(EffectSummary::pure()));
    assert_eq!(effects_of(&image, "caller"), Some(EffectSummary::top()));
    assert_eq!(
        effects_of(&image, "ext"),
        None,
        "an unsummarized declaration"
    );
    assert!(
        validate_module(&image).is_empty(),
        "the merged image validates clean: {:?}",
        validate_module(&image)
    );

    // The execution image carries no claims: every summary stripped, counted,
    // and no effect claim invented in its place.
    let mut image = dst.clone();
    let remap = merge_into(&mut image, &fixture, &MergePolicy::EXECUTION_IMAGE).expect("merges");
    let summarized = fixture
        .functions
        .iter()
        .filter(|f| f.summary.is_some())
        .count();
    assert_eq!(remap.stripped().summaries, summarized);
    for name in ["set", "add", "caller", "ext"] {
        assert_eq!(effects_of(&image, name), None, "@{name}");
    }
    assert!(
        validate_module(&image).is_empty(),
        "{:?}",
        validate_module(&image)
    );
}

/// The global remap is not monotone, so a mapped `Places` list is re-sorted
/// into its one canonical spelling. `src` holds globals `X` (0) and `Y` (1)
/// and a `touch(p)` writing `*p`, `X` and `Y`; `dst` already holds `D0` (0)
/// and the same `Y` (1). `Y` maps onto `dst`'s `Y` (1) and `X` lands after it
/// (2), so `[p0, X, Y]` maps to `[p0, 2, 1]` and must be spelled
/// `[p0, 1, 2]`. Mutation controls: a verbatim copy names `D0` (never
/// written) and misses `X`, failing the exact set and
/// `EffectSummaryViolated`; a mapped-but-unsorted list fails the
/// canonicality assertion and the validator's shape rule
/// (`InvalidFunctionSummary`).
#[test]
fn ws1_14_merged_effect_places_keep_the_one_spelling() {
    use trust_ir::value::GlobalId;

    let ptr = || Ty::PtrMut(Box::new(Ty::U64));
    let mut src = globals_only("src", &["X", "Y"]);
    let ft = src
        .add_func_type(FuncTy {
            abi: None,
            params: vec![ptr()],
            returns: vec![],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut touch = Function::new(FuncId::new(0), "touch", ft, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry.params.push((ValueId::new(0), ptr()));
    entry.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(7),
        })
        .with_result(ValueId::new(1)),
    );
    let store = |ptr: u32| {
        InstrNode::new(Inst::Store {
            ty: Ty::U64,
            ptr: ValueId::new(ptr),
            value: ValueId::new(1),
            volatile: false,
            align: None,
        })
    };
    entry.body.push(store(0));
    for (global, result) in [(0, 2), (1, 3)] {
        entry.body.push(
            InstrNode::new(Inst::GlobalAddr {
                global: GlobalId::new(global),
            })
            .with_result(ValueId::new(result)),
        );
        entry.body.push(store(result));
    }
    entry
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    touch.blocks.push(entry);
    touch.body_gate = Some(BodyGate::Ungated);
    let p0 = EffectPlace::ParamPointee { index: 0 };
    touch.summary = Some(
        FunctionSummary::new().with_effects(EffectSummary::pure().writing(EffectSet::of([
            p0,
            EffectPlace::Global(GlobalId::new(0)),
            EffectPlace::Global(GlobalId::new(1)),
        ]))),
    );
    src.try_add_function(touch)
        .expect("Module::try_add_function: test fixture");
    assert!(
        validate_module(&src).is_empty(),
        "control: src validates clean: {:?}",
        validate_module(&src)
    );

    let mut image = globals_only("dst", &["D0", "Y"]);
    let remap = merge_into(&mut image, &src, &MergePolicy::VERIFICATION_IMAGE).expect("merges");
    let (x, y) = (
        remap.global(GlobalId::new(0)).expect("X"),
        remap.global(GlobalId::new(1)).expect("Y"),
    );
    assert_eq!(
        (x, y),
        (GlobalId::new(2), GlobalId::new(1)),
        "control: the remap reverses X and Y"
    );
    let writes = effects_of(&image, "touch").expect("carried").writes;
    assert!(writes.is_canonical(), "{writes:?}");
    assert_eq!(
        writes,
        EffectSet::Places(vec![p0, EffectPlace::Global(y), EffectPlace::Global(x)])
    );
    assert!(
        validate_module(&image).is_empty(),
        "{:?}",
        validate_module(&image)
    );
}

/// Two DECLARATIONS that differ only in their effect summary. The
/// verification image refuses them naming `summary`, in both orders — an
/// effect summary is a claim, and input order must not pick one. Under
/// `FirstStands` with proof state carried, the EARLIER declaration's effects
/// stand in both orders: never the later one's, never their union, and an
/// earlier declaration with no effects keeps none (the later claim is not
/// adopted). The execution image is `FirstStands` and strips only `src`'s
/// claims, so `dst`'s earlier declaration keeps its effects there too, and
/// merged into an empty image both are stripped. Mutation controls: a merge
/// that kept the wider claim (or a union) fails the pure-first order; one
/// that kept the later declaration fails the top-first order; one that
/// filled a missing claim from the later declaration fails the
/// unrecorded-first order.
#[test]
fn ws1_14_two_declarations_differing_only_in_effects() {
    let declaration = |module: &str, effects: Option<EffectSummary>| {
        let mut m = one_function(module, "f", false, None);
        let mut summary = FunctionSummary::new();
        summary.effects = effects;
        m.functions[0].summary = Some(summary);
        m
    };
    let pure = declaration("pure", Some(EffectSummary::pure()));
    let top = declaration("top", Some(EffectSummary::top()));
    let unrecorded = declaration("unrecorded", None);
    let first_stands = MergePolicy {
        on_duplicate_declaration: DuplicateDecl::FirstStands,
        ..MergePolicy::VERIFICATION_IMAGE
    };
    for (a, b) in [(&pure, &top), (&pure, &unrecorded), (&top, &unrecorded)] {
        for (x, y) in [(a, b), (b, a)] {
            assert_eq!(
                merged(x, y, &MergePolicy::VERIFICATION_IMAGE),
                Err(MergeError::ConflictingDefinition {
                    symbol: "f".into(),
                    field: "summary",
                }),
                "{} <- {}",
                x.name,
                y.name
            );
            let image = merged(x, y, &first_stands)
                .unwrap_or_else(|e| panic!("{} <- {}: {e}", x.name, y.name));
            assert_eq!(image.functions.len(), 1);
            assert_eq!(
                effects_of(&image, "f"),
                effects_of(x, "f"),
                "{} <- {}: the earlier declaration's effects stand",
                x.name,
                y.name
            );
            assert_eq!(image.functions[0].summary, x.functions[0].summary);
            // The execution image is `FirstStands` too, and strips only
            // `src`'s claims: `dst`'s earlier declaration keeps its own
            // effects, the later one's are dropped (and counted).
            let mut image = x.clone();
            let remap = merge_into(&mut image, y, &MergePolicy::EXECUTION_IMAGE)
                .unwrap_or_else(|e| panic!("{} <- {}: {e}", x.name, y.name));
            assert_eq!(remap.stripped().summaries, 1);
            assert_eq!(
                effects_of(&image, "f"),
                effects_of(x, "f"),
                "{} <- {} (execution image)",
                x.name,
                y.name
            );
            // The linker's shape — both inputs merged into an empty image —
            // strips both claims: the image records no effects at all.
            let mut image = Module::new("image");
            for input in [x, y] {
                merge_into(&mut image, input, &MergePolicy::EXECUTION_IMAGE)
                    .unwrap_or_else(|e| panic!("{} <- {}: {e}", x.name, y.name));
            }
            assert_eq!(effects_of(&image, "f"), None, "{} <- {}", x.name, y.name);
        }
    }
    // Control: identical effects are one declaration under both policies.
    let twin = declaration("twin", Some(EffectSummary::pure()));
    let image = merged(&pure, &twin, &MergePolicy::VERIFICATION_IMAGE).expect("identical");
    assert_eq!(effects_of(&image, "f"), Some(EffectSummary::pure()));
}

/// A `src` effect set the merge cannot carry is refused and leaves `dst`
/// untouched: a place naming a global `src` does not have is `Dangling`
/// (like any other cited global), and a non-canonical `Places` list is
/// `Malformed` — the remap re-sorts, so carrying one would silently repair
/// it. The execution image strips both before they could be carried.
#[test]
fn ws1_14_a_dangling_or_non_canonical_effect_set_is_refused() {
    use trust_ir::value::GlobalId;

    let with_writes = |writes: EffectSet| {
        let mut m = returns_const("src", "f", 1);
        m.functions[0].summary =
            Some(FunctionSummary::new().with_effects(EffectSummary::pure().writing(writes)));
        m
    };
    let p = |index| EffectPlace::ParamPointee { index };
    let cases = [
        (
            "dangling global",
            with_writes(EffectSet::Places(vec![EffectPlace::Global(GlobalId::new(
                3,
            ))])),
            MergeError::Dangling {
                table: "globals",
                id: 3,
            },
        ),
        (
            "empty Places",
            with_writes(EffectSet::Places(vec![])),
            MergeError::Malformed {
                table: "functions",
                id: 0,
                detail: "an effect set of the summary is not canonical",
            },
        ),
        (
            "unsorted Places",
            with_writes(EffectSet::Places(vec![p(1), p(0)])),
            MergeError::Malformed {
                table: "functions",
                id: 0,
                detail: "an effect set of the summary is not canonical",
            },
        ),
        (
            "duplicate place",
            with_writes(EffectSet::Places(vec![p(0), p(0)])),
            MergeError::Malformed {
                table: "functions",
                id: 0,
                detail: "an effect set of the summary is not canonical",
            },
        ),
    ];
    for (what, src, error) in cases {
        let mut dst = globals_only("dst", &["G"]);
        let before = format!("{dst:?}");
        assert_eq!(
            merge_into(&mut dst, &src, &MergePolicy::VERIFICATION_IMAGE).map(|_| ()),
            Err(error),
            "{what}"
        );
        assert_eq!(format!("{dst:?}"), before, "{what}: dst unchanged");
        let mut dst = globals_only("dst", &["G"]);
        merge_into(&mut dst, &src, &MergePolicy::EXECUTION_IMAGE)
            .unwrap_or_else(|e| panic!("{what}: a stripped claim is never carried: {e}"));
        assert_eq!(effects_of(&dst, "f"), None, "{what}");
    }
}
