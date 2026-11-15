//! b4 — cross-crate linking: `Module.imports`, `ExternRef`, `backed_by`,
//! `InheritedFromCallee { external: Some }`, `Module::verify_import`,
//! `Module::resolve_extern_ref`, `trust_ir_build::validate_linked_module`.
//!
//! Ported (roadmap WS8.6) from the archived Part B battery
//! `reports/2026-09-17-two-language-proof-program/partb/tests/b4_cross_crate_linking.rs`, measured there
//! at trust-ir 4efb21bc and re-measured at the port. Every row is checked against
//! `RATCHETS.tsv` (see `harness.rs`). `file:line` citations are relative to
//! `crates/` and date from 4efb21bc: re-locate them by name.
//! The linked RUN rows execute the real `trust-ir` binary and live in
//! `crates/trust-ir-cli/tests/two_language_cli.rs`, over `b4_fixtures.rs`.
//!
//! The two-crate program (the design's END STATE shape — a MIXED dependency):
//!
//! ```text
//! crate b4_dep   [TRust] dep_scale(x: u64) -> u64        = x * 3
//!                        proved `ensures (>= result 0)`, kernel-CERTIFIED Postcondition #0
//!                [Clean] dep_addmul(a: u64, b: u64) -> u64 = a * b + a
//!                        proved `ensures (<= 1 2)`, kernel-CERTIFIED Postcondition #1
//! crate b4_root  imports: #0 = (b4_dep, digest, TRust), #1 = (b4_dep, digest, Clean)
//!                [TRust] decl dep_scale   proved, backed_by  (#0, "dep_scale",  far #0)
//!                [Clean] decl dep_addmul  local Discharged #0, InheritedFromCallee
//!                                         { external: (#1, "dep_addmul", far #1) }
//!                [TRust] program() -> u64 = dep_addmul(dep_scale(2), 7)  == 48
//! ```
//!
//! HONESTY NOTE on the clauses: the contract minter
//! (`trust_ir::clean_expr_lowering::contract`) certifies exactly two shapes:
//! CLOSED ground comparisons over Nat literals (`contract_clean_cic_certificate`,
//! module-free), and the single-free-name non-negativity tautology `(>= x 0)` /
//! `(<= 0 x)`, which since WS1.1 (0aeae341) only the module-bound
//! `contract_clean_cic_certificate_in` mints, after binding `x` to an unsigned
//! IR place read at sort Int. So
//! `dep_scale` carries the one certifiable clause that has a FREE NAME —
//! `(>= result 0)`, bound `result -> (Int, ResultSlot 0)` — and `dep_addmul` a
//! closed one (`(<= 1 2)`). What this file measures is the LINK machinery
//! (identity, resolution, re-earning, exact restatement INCLUDING bindings),
//! not the strength of the clauses.
//!
//! REVIEW NOTE (adversarial pass): the `dep_scale` clause was `(= 1 1)`; it was
//! upgraded so the backed_by restatement carries a v41 binding, and the rows
//! marked `[review]` below were added.

mod common;

use std::collections::BTreeSet;
use std::panic::{AssertUnwindSafe, catch_unwind};

use common::{Expect, Outcome, feature_check, feature_ratified, roundtrip_all};
use trust_ir::binary::{
    BinaryProjectionError, ModuleBinaryOptions, ModuleBinaryPlan, ProjectedModuleBinaryPlan,
    deserialize_module, serialize_module,
};
use trust_ir::proof::{
    ClausePlace, ModuleProofAuthority, ObligationKind, ProofCertificate, ProofDigest,
    ProofEvidence, ProofFormula, ProofObligation, ProofStatus, RejectingModuleProofAuthority,
};
use trust_ir::ty::Ty;
use trust_ir::value::{FuncId, ImportId, ProofId};
use trust_ir::{
    ExternRef, ExternRefSite, FunctionSummary, HashedModule, IdentityScheme,
    ImportVerificationError, Linkage, MODULE_IDENTITY_DOMAIN, Module, ModuleImport, Producer,
};
use trust_ir_build::{
    ModuleBuilder, ModuleSet, ValidationError, validate_linked_module, validate_module,
    validate_module_report, validate_module_report_with_authority, validate_module_with_authority,
};

// ---------------------------------------------------------------------------
// fixtures
// ---------------------------------------------------------------------------

#[path = "b4_fixtures.rs"]
mod b4_fixtures;
#[allow(unused_imports)]
use b4_fixtures::*;

fn backed_ref(ids: RootIds) -> ExternRef {
    ExternRef::new(ids.rust_row, SCALE).relying_on(ProofId::new(0))
}

fn inherited_ref(ids: RootIds) -> ExternRef {
    ExternRef::new(ids.clean_row, ADDMUL).relying_on(ProofId::new(1))
}

fn unauthenticated(errors: &[ValidationError], at: &str, needle: &str) -> bool {
    errors.iter().any(|e| {
        matches!(
            e,
            ValidationError::UnauthenticatedImport { site, detail, .. }
                if *site == at && detail.contains(needle)
        )
    })
}

// ---------------------------------------------------------------------------
// 1. the import row, the digest, the wire
// ---------------------------------------------------------------------------

fn b4_01_import_rows_digest_and_wire() {
    let dep = build_dep(3);
    let (root, ids) = build_root(&dep, true);

    // dep and root are each well-formed at the structural tier.
    // [review] strictest applicable entry points for a module with no
    // cross-crate claim of its own: structural AND authority tier (Rejecting
    // capability), and the kernel tier must really have replayed BOTH
    // certificates (not merely tolerated the `Certified` label).
    let dep_errors = validate_module(&dep);
    let dep_report = validate_module_report_with_authority(&dep, &RejectingModuleProofAuthority);
    let dep_replayed = dep_report
        .replayed_certificate_refs()
        .cloned()
        .unwrap_or_default();
    let both_replayed = dep_replayed
        == dep
            .proof_certificates
            .iter()
            .map(|c| c.lineage_ref())
            .collect::<BTreeSet<_>>()
        && dep_replayed.len() == 2;
    assert!(feature_check(
        "b4.dep.validates",
        dep_errors.is_empty() && dep_report.is_ok() && both_replayed,
        &format!(
            "mixed TRust+Clean dependency with 2 kernel-Certified Postconditions (one with a \
             bound free name); validate_module errors={dep_errors:?}; authority tier errors={:?}; \
             kernel-tier replayed certificate refs = {} of {}",
            dep_report.errors(),
            dep_replayed.len(),
            dep.proof_certificates.len()
        ),
    ));
    // [review] negative twin: the SAME certificate under a clause it was not
    // minted for. One mutation (obligation #0's formula text).
    let mut relabelled_dep = dep.clone();
    relabelled_dep.proof_obligations[0].formula = Some(ProofFormula::smtlib2("(= 1 2)", "Bool"));
    let relabelled_errors = validate_module(&relabelled_dep);
    assert!(feature_check(
        "b4.dep.validates.negative_twin.certificate_under_another_clause",
        relabelled_errors.iter().any(|e| matches!(
            e,
            ValidationError::CertifiedCleanCicLineageMismatch { obligation: 0 }
        )),
        &format!(
            "dep obligation #0 restated as (= 1 2), certificate untouched => {relabelled_errors:?}"
        ),
    ));

    // [review] the importer, structural tier. Baseline = the root WITHOUT its
    // inheritance row (obligation + certificate removed): validates clean, so
    // imports / ExternRef / backed_by are taken on faith here. With the
    // inheritance row the ONLY error is the general Discharged rule
    // (validate.rs:12343-12367: the structural tier supplies the Rejecting
    // capability, so NO Discharged row of any evidence ever validates there).
    let mut root_without_inheritance = root.clone();
    root_without_inheritance.proof_obligations.clear();
    root_without_inheritance.proof_certificates.clear();
    let baseline_errors = validate_module(&root_without_inheritance);
    let root_errors = validate_module(&root);
    assert!(feature_check(
        "b4.root.validates_structurally",
        baseline_errors.is_empty()
            && root_errors.len() == 1
            && matches!(
                root_errors[0],
                ValidationError::DischargedWithoutCertificate { obligation: 0 }
            ),
        &format!(
            "structural tier: root minus its inheritance row => {baseline_errors:?} (imports + \
             backed_by taken on faith); full root => {root_errors:?} (the inherited Discharged \
             row needs the linked authority; plain `validate_module` can never admit it)"
        ),
    ));

    // The import digest IS dep.stable_digest(), and that IS the canonical
    // binary image — with the debug file strings projected out (the V3
    // identity, WS4.10) — hashed under MODULE_IDENTITY_DOMAIN.
    let recorded = root.import(ids.rust_row).unwrap().digest;
    let mut blanked = dep.clone();
    blanked.files.iter_mut().for_each(String::clear);
    let recomputed = ModuleBinaryPlan::new(&blanked).sha256_domain(MODULE_IDENTITY_DOMAIN);
    let by_hand = ProofDigest::sha256_domain(
        MODULE_IDENTITY_DOMAIN,
        &serialize_module(&blanked).expect("serialize_module: test fixture"),
    );
    assert!(feature_check(
        "b4.import.digest_is_stable_digest",
        recorded == dep.stable_digest()
            && recorded == recomputed
            && root.import(ids.rust_row).unwrap().scheme == IdentityScheme::V3
            && MODULE_IDENTITY_DOMAIN == "trust_ir.module.v3",
        &format!(
            "ModuleImport.digest == dep.stable_digest() == ModuleBinaryPlan(files blanked)::sha256_domain({MODULE_IDENTITY_DOMAIN:?}), row scheme V3; \
             equals sha256_domain(domain, serialize_module(dep, files blanked)) = {} (informational)",
            by_hand == recorded
        ),
    ));
    // negative twin: the rebuilt dependency has a DIFFERENT digest.
    assert!(feature_check(
        "b4.import.digest_is_stable_digest.negative_twin",
        tampered_dep().stable_digest() != recorded,
        "dep rebuilt with dep_scale factor 3->2 (same name/symbols/contracts) hashes differently",
    ));

    // Content interning: same triple => same id.
    let mut probe = root.clone();
    let again = probe
        .intern_import(
            ModuleImport::new(dep.name.clone(), dep.stable_digest()).with_producer(Producer::TRust),
        )
        .expect("Module::intern_import: test fixture");
    assert!(feature_check(
        "b4.import.interned",
        again == ids.rust_row && probe.imports.len() == 2,
        &format!(
            "re-interning the (name,digest,TRust) triple returns {again:?}, table stays at 2 rows"
        ),
    ));

    // ExternRef must resolve to a DECLARED import.
    let mut dangling = root.clone();
    dangling.function_by_id_mut(ids.scale).unwrap().summary = Some(
        scale_contract()
            .proved()
            .backed_by(ExternRef::new(ImportId::new(9), SCALE).relying_on(ProofId::new(0))),
    );
    let errors = validate_module(&dangling);
    assert!(feature_check(
        "b4.extern_ref.negative_twin.dangling_import",
        errors.iter().any(|e| matches!(
            e,
            ValidationError::DanglingExternRef { detail } if detail.contains("import #9")
        )),
        &format!("backed_by into undeclared import #9 => {errors:?}"),
    ));
    let mut no_claim = root.clone();
    if let ProofEvidence::InheritedFromCallee { external, .. } =
        &mut no_claim.proof_certificates[0].evidence
    {
        *external = Some(ExternRef::new(ids.clean_row, ADDMUL));
    }
    let errors = validate_module(&no_claim);
    assert!(feature_check(
        "b4.inherited_external.negative_twin.no_obligation",
        errors.iter().any(|e| matches!(
            e,
            ValidationError::DanglingExternRef { detail } if detail.contains("names no obligation")
        )),
        &format!("inheritance through an ExternRef with obligation=None => {errors:?}"),
    ));

    // What a consumer must supply.
    let bearing = validate_module_report(&root).proof_bearing_imports();
    assert!(feature_check(
        "b4.proof_bearing_imports",
        bearing == BTreeSet::from([ids.rust_row, ids.clean_row]),
        &format!("ModuleValidationReport::proof_bearing_imports() = {bearing:?}"),
    ));

    // Wire: imports + backed_by + evidence tag 8 force v41, and the root's
    // rows — minted by `ModuleImport::new` under the portable V3 identity —
    // raise it to v44 (WS4.10); lossless on the three production transports.
    let rt = roundtrip_all(&root);
    // [review] the dependency crosses the wire too (it carries the CleanCic
    // certificates and the bound clause); its digest must survive every
    // lossless transport, or a reloaded dep would stop authenticating.
    let rt_dep = roundtrip_all(&dep);
    let dep_digest_survives = [&rt_dep.binary, &rt_dep.json, &rt_dep.msgpack]
        .iter()
        .all(|t| {
            t.decoded
                .as_ref()
                .is_some_and(|m| m.stable_digest() == dep.stable_digest())
        });
    assert!(feature_check(
        "b4.roundtrip.production",
        rt.lossless_production()
            && rt.binary_version == 44
            && rt_dep.lossless_production()
            && rt_dep.binary_version == 41
            && dep_digest_survives,
        &format!(
            "root: {} || dep: {} || dep.stable_digest identical after binary/json/msgpack = \
             {dep_digest_survives}",
            rt.summary(),
            rt_dep.summary()
        ),
    ));
    let decoded = rt.binary.decoded.as_ref().unwrap();
    assert!(feature_check(
        "b4.roundtrip.cross_crate_rows_survive",
        decoded.imports == root.imports
            && decoded
                .function_by_id(ids.scale)
                .unwrap()
                .summary
                .as_ref()
                .unwrap()
                .backed_by
                == Some(backed_ref(ids))
            && matches!(
                &decoded.proof_certificates[0].evidence,
                ProofEvidence::InheritedFromCallee { external: Some(r), .. } if *r == inherited_ref(ids)
            ),
        "binary decode: imports table, FunctionSummary.backed_by and InheritedFromCallee.external identical",
    ));
    // negative twin: an explicit v38 projection refuses the cross-crate surface...
    let projected = ProjectedModuleBinaryPlan::try_new(&root, ModuleBinaryOptions::default());
    // ...and a reader told the blob is v40 refuses rather than misreading it.
    let mut relabelled = rt.binary.encoded.clone();
    relabelled[8..12].copy_from_slice(&40u32.to_le_bytes());
    let old_reader = deserialize_module(&relabelled);
    // [review] the relabelled ROOT desyncs on an earlier v41-gated field, so its
    // refusal is real but incidental. The DESIGNED refusal is evidence tag 8:
    // a function-free module whose only v41 content is one external
    // inheritance certificate, relabelled v40, must die on exactly that tag.
    let mut tag8 = ModuleBuilder::new_with_target_info("b4_tag8", target())
        .build()
        .expect("ModuleBuilder::build: test fixture");
    tag8.proof_obligations.push(ProofObligation::new(
        ProofId::new(0),
        ObligationKind::Postcondition,
        ProofStatus::Discharged,
        "tag-8 carrier",
    ));
    tag8.proof_certificates.push(ProofCertificate {
        obligation: ProofId::new(0),
        prover: "b4".to_string(),
        evidence: ProofEvidence::InheritedFromCallee {
            callee: FuncId::new(0),
            obligation: ProofId::new(0),
            external: Some(ExternRef::new(ImportId::new(0), SCALE).relying_on(ProofId::new(0))),
        },
        assurance: None,
    });
    let tag8_bytes = serialize_module(&tag8).expect("serialize_module: test fixture");
    let tag8_version = common::binary_version(&tag8_bytes);
    let mut tag8_relabelled = tag8_bytes.clone();
    tag8_relabelled[8..12].copy_from_slice(&40u32.to_le_bytes());
    let tag8_old_reader = deserialize_module(&tag8_relabelled);
    assert!(feature_check(
        "b4.roundtrip.negative_twin.v38_projection_refused",
        // The root's V3 rows are its highest requirement since WS4.10, so the
        // refusal names v44 (highest wins); a V2-row root names v41.
        matches!(
            projected.as_ref().err(),
            Some(BinaryProjectionError::ImportSchemeRequiresV44)
        ) && old_reader.is_err()
            && tag8_version == 41
            && deserialize_module(&tag8_bytes).ok().as_ref() == Some(&tag8)
            && matches!(
                &tag8_old_reader,
                Err(trust_ir::binary::BinaryError::InvalidTag(8))
            ),
        &format!(
            "RawV38 projection => {:?}; root bytes with header relabelled v40 => {:?} (desync \
             refusal); function-free module whose only v41 content is external inheritance: \
             writer selects v{tag8_version}, relabelled v40 => {:?} (the designed evidence-tag \
             refusal)",
            projected.as_ref().err(),
            old_reader.as_ref().err(),
            tag8_old_reader.as_ref().err()
        ),
    ));

    // FLIPPED by WS4.4 (F-064), formerly a GAP: canonical TEXT carried HALF
    // of the cross-crate surface — the import table and the `external` clause
    // of an inheritance certificate re-parsed, but `FunctionSummary` had no
    // text syntax, so `backed_by` (the OTHER proof-bearing cross-crate row)
    // was dropped and a text-transported root silently stopped claiming (and
    // re-earning) its `proved` contract; WS4.2 then refused the text as
    // `#lossy: function-summary(..)`. Text now carries the summary and its
    // `; #backed-by:` citation, so the text image keeps BOTH proof-bearing
    // rows. Mutation control: deleting the `#backed-by` lines from the text
    // shrinks `proof_bearing_imports` to the inheritance row alone — exactly
    // the old drop.
    let decoded = rt.text.decoded.as_ref();
    let text_imports_kept = decoded.is_some_and(|text| text.imports == root.imports);
    let text_external_kept = decoded.is_some_and(|text| {
        text.proof_certificates.iter().any(|c| {
            matches!(
                &c.evidence,
                ProofEvidence::InheritedFromCallee { external: Some(r), .. }
                    if *r == inherited_ref(ids)
            )
        })
    });
    let text_summaries_kept = decoded.is_some_and(|text| {
        text.functions
            .iter()
            .zip(&root.functions)
            .all(|(t, r)| t.summary == r.summary)
    });
    let text_bearing = decoded
        .map(|text| validate_module_report(text).proof_bearing_imports())
        .unwrap_or_default();
    let printed = String::from_utf8_lossy(&rt.text.encoded).into_owned();
    let without_backing: String = printed
        .lines()
        .filter(|line| !line.contains("; #backed-by:"))
        .map(|line| format!("{line}\n"))
        .collect();
    let dropped_bearing = trust_ir::parser::parse_module(&without_backing)
        .map(|m| validate_module_report(&m).proof_bearing_imports())
        .unwrap_or_default();
    assert!(feature_check(
        "b4.gap.text_drops_backed_by",
        rt.text.lossless()
            && text_imports_kept
            && text_external_kept
            && text_summaries_kept
            && text_bearing == bearing
            && dropped_bearing == BTreeSet::from([ids.clean_row]),
        &format!(
            "{}; imports kept={text_imports_kept}, InheritedFromCallee.external kept=\
             {text_external_kept}, every summary (backed_by included) kept = \
             {text_summaries_kept} => proof_bearing_imports {bearing:?} -> {text_bearing:?}; \
             mutation control, `#backed-by` lines deleted => {dropped_bearing:?}",
            rt.text.summary()
        ),
    ));
}

// ---------------------------------------------------------------------------
// 2. Module::verify_import — one edge
// ---------------------------------------------------------------------------

fn b4_02_verify_import() {
    let dep = build_dep(3);
    let (root, ids) = build_root(&dep, true);

    let verified = root.verify_import(ids.rust_row, &dep);
    assert!(feature_check(
        "b4.verify_import",
        matches!(&verified, Ok(v) if v.digest() == dep.stable_digest()
            && v.id() == ids.rust_row
            && std::ptr::eq(v.module(), &dep))
            && root.verify_import(ids.clean_row, &dep).is_ok(),
        &format!(
            "both rows authenticate against the held dep: {:?}",
            verified.as_ref().map(|v| v.digest())
        ),
    ));

    // negative twin A: the semantically tampered rebuild.
    let tampered = tampered_dep();
    let refused = root.verify_import(ids.rust_row, &tampered);
    assert!(feature_check(
        "b4.verify_import.negative_twin.rebuilt_dep",
        matches!(
            &refused,
            Err(ImportVerificationError::DigestMismatch { import: 0, recorded, actual })
                if *recorded == dep.stable_digest() && *actual == tampered.stable_digest()
        ),
        &format!(
            "same-name dep with factor 3->2 => {:?}",
            refused.as_ref().err()
        ),
    ));

    // negative twin B: EVERY single flipped bit of the serialized dep. Each
    // flip either fails to decode (refused at load) or decodes to a module the
    // edge refuses with DigestMismatch. A flip that decodes AND authenticates
    // would be a hole (a non-canonical spelling the reader tolerates is
    // reported separately).
    let bytes = serialize_module(&dep).expect("serialize_module: test fixture");
    let (mut undecodable, mut mismatched, mut same_module, mut holes, mut panics) =
        (0usize, 0usize, 0usize, Vec::new(), 0usize);
    for index in 0..bytes.len() {
        let mut flipped = bytes.clone();
        flipped[index] ^= 0x01;
        let decoded = catch_unwind(AssertUnwindSafe(|| deserialize_module(&flipped)));
        match decoded {
            Err(_) => panics += 1,
            Ok(Err(_)) => undecodable += 1,
            Ok(Ok(candidate)) => match root.verify_import(ids.rust_row, &candidate) {
                Err(ImportVerificationError::DigestMismatch { .. }) => mismatched += 1,
                Ok(_) if candidate == dep => same_module += 1,
                other => holes.push((index, format!("{:?}", other.err()))),
            },
        }
    }
    assert!(feature_check(
        "b4.verify_import.negative_twin.one_flipped_byte",
        holes.is_empty() && mismatched > 0 && panics == 0,
        &format!(
            "{} byte positions, bit0 flipped in each: {undecodable} refused by the reader, \
             {mismatched} decoded and refused as DigestMismatch, {same_module} decoded to the \
             IDENTICAL module (non-canonical spelling tolerated by the reader), {panics} reader \
             panics, holes={holes:?}",
            bytes.len()
        ),
    ));

    // negative twins C: the C4-C6 agreement checks (digest matches, the record lies).
    let mut renamed = root.clone();
    renamed.imports[0].name = "b4_dep_v2".into();
    let name = renamed.verify_import(ids.rust_row, &dep).err();
    let mut unrecorded = root.clone();
    unrecorded.imports[0].producer = None;
    let producer = unrecorded.verify_import(ids.rust_row, &dep).err();
    let mut retargeted = root.clone();
    retargeted.target_info.as_mut().unwrap().pointer_size = 4;
    let target_skew = retargeted.verify_import(ids.rust_row, &dep).err();
    let mut untargeted = dep.clone();
    untargeted.target_info = None;
    let mut root_for_untargeted = root.clone();
    repin(&mut root_for_untargeted, &untargeted);
    let target_absent = root_for_untargeted
        .verify_import(ids.rust_row, &untargeted)
        .err();
    let mut checksum = root.clone();
    checksum.imports[0].digest = ProofDigest::trust_ir_stable(
        MODULE_IDENTITY_DOMAIN,
        &serialize_module(&dep).expect("serialize_module: test fixture"),
    );
    let algorithm = checksum.verify_import(ids.rust_row, &dep).err();
    let unresolved = root.verify_import(ImportId::new(7), &dep).err();
    assert!(feature_check(
        "b4.verify_import.negative_twin.record_disagrees",
        matches!(
            &name,
            Some(ImportVerificationError::NameMismatch { import: 0, .. })
        ) && matches!(
            &producer,
            Some(ImportVerificationError::ProducerUnrecorded {
                import: 0,
                side: "import"
            })
        ) && matches!(
            &target_skew,
            Some(ImportVerificationError::TargetMismatch { import: 0, .. })
        ) && matches!(&target_absent, Some(ImportVerificationError::TargetMismatch { import: 0, detail }) if detail.contains("pins no target"))
            && matches!(
                &algorithm,
                Some(ImportVerificationError::UnsupportedDigestAlgorithm { import: 0, .. })
            )
            && matches!(
                &unresolved,
                Some(ImportVerificationError::UnresolvedImport { import: 7 })
            ),
        &format!(
            "renamed record => {name:?}; producer None => {producer:?}; pointer_size 8 vs 4 => \
             {target_skew:?}; dep without target_info => {target_absent:?}; TrustIrStableV1 \
             checksum as identity => {algorithm:?}; undeclared id => {unresolved:?}"
        ),
    ));
}

// ---------------------------------------------------------------------------
// 3. Module::resolve_extern_ref — one reference across the edge
// ---------------------------------------------------------------------------

fn b4_03_resolve_extern_ref() {
    let dep = build_dep(3);
    let (root, ids) = build_root(&dep, false);
    let rust_edge = root.verify_import(ids.rust_row, &dep).unwrap();
    let clean_edge = root.verify_import(ids.clean_row, &dep).unwrap();

    let backed = root.resolve_extern_ref(
        &backed_ref(ids),
        ids.scale,
        ExternRefSite::SummaryBackedBy,
        &rust_edge,
    );
    let inherited = root.resolve_extern_ref(
        &inherited_ref(ids),
        ids.addmul,
        ExternRefSite::InheritedFromCallee,
        &clean_edge,
    );
    assert!(feature_check(
        "b4.resolve_extern_ref",
        matches!(&backed, Ok(r) if r.far.name == SCALE && !r.far.is_declaration()
            && r.local.is_declaration()
            && r.obligation.is_some_and(|o| o.id == ProofId::new(0) && o.status == ProofStatus::Certified))
            && matches!(&inherited, Ok(r) if r.far.name == ADDMUL
                && r.far.producer == Some(Producer::Clean)
                && r.obligation.is_some_and(|o| o.id == ProofId::new(1))),
        &format!(
            "backed_by -> far {:?}; inherited -> far {:?}",
            backed
                .as_ref()
                .map(|r| (&r.far.name, r.obligation.map(|o| o.id)))
                .map_err(|e| e.to_string()),
            inherited
                .as_ref()
                .map(|r| (&r.far.name, r.obligation.map(|o| o.id)))
                .map_err(|e| e.to_string()),
        ),
    ));

    // wrong producer: the Clean far function cited through the TRust row.
    let wrong_producer = root
        .resolve_extern_ref(
            &ExternRef::new(ids.rust_row, ADDMUL).relying_on(ProofId::new(1)),
            ids.addmul,
            ExternRefSite::InheritedFromCallee,
            &rust_edge,
        )
        .err();
    assert!(feature_check(
        "b4.resolve_extern_ref.negative_twin.wrong_producer",
        matches!(
            &wrong_producer,
            Some(ImportVerificationError::ProducerMismatch { symbol, recorded: Producer::TRust, actual: Producer::Clean })
                if symbol == ADDMUL
        ),
        &format!("{wrong_producer:?}"),
    ));

    // non-exported far symbol: dep rebuilt with dep_scale Internal; the root is
    // RE-PINNED to that build, so the digest matches and R4 does the refusing.
    let mut private_dep = dep.clone();
    private_dep.functions[0].linkage = Linkage::Internal;
    let mut private_root = root.clone();
    repin(&mut private_root, &private_dep);
    let edge = private_root
        .verify_import(ids.rust_row, &private_dep)
        .unwrap();
    let not_exported = private_root
        .resolve_extern_ref(
            &backed_ref(ids),
            ids.scale,
            ExternRefSite::SummaryBackedBy,
            &edge,
        )
        .err();
    assert!(feature_check(
        "b4.resolve_extern_ref.negative_twin.symbol_not_exported",
        matches!(
            &not_exported,
            Some(ImportVerificationError::SymbolNotExported { symbol, linkage: Linkage::Internal })
                if symbol == SCALE
        ),
        &format!("{not_exported:?}"),
    ));

    // signature skew: the importer declares dep_scale(u32) -> u64.
    let mut skewed = root.clone();
    let narrow = skewed
        .add_func_type(trust_ir::ty::FuncTy {
            params: vec![Ty::U32],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    skewed.function_by_id_mut(ids.scale).unwrap().ty = narrow;
    let edge = skewed.verify_import(ids.rust_row, &dep).unwrap();
    let skew = skewed
        .resolve_extern_ref(
            &backed_ref(ids),
            ids.scale,
            ExternRefSite::SummaryBackedBy,
            &edge,
        )
        .err();
    assert!(feature_check(
        "b4.resolve_extern_ref.negative_twin.signature_skew",
        matches!(
            &skew,
            Some(ImportVerificationError::SignatureMismatch { symbol, detail })
                if symbol == SCALE && detail.contains("parameter 0 type")
        ),
        &format!("{skew:?}"),
    ));

    // the rest of R1-R7, one mutation each.
    let foreign_edge = root
        .resolve_extern_ref(
            &backed_ref(ids),
            ids.scale,
            ExternRefSite::SummaryBackedBy,
            &clean_edge,
        )
        .err();
    let unknown_symbol = root
        .resolve_extern_ref(
            &ExternRef::new(ids.rust_row, "dep_scale_v2").relying_on(ProofId::new(0)),
            ids.scale,
            ExternRefSite::SummaryBackedBy,
            &rust_edge,
        )
        .err();
    let wrong_scope = root
        .resolve_extern_ref(
            &ExternRef::new(ids.rust_row, SCALE).relying_on(ProofId::new(1)),
            ids.scale,
            ExternRefSite::SummaryBackedBy,
            &rust_edge,
        )
        .err();
    let no_such_obligation = root
        .resolve_extern_ref(
            &ExternRef::new(ids.rust_row, SCALE).relying_on(ProofId::new(42)),
            ids.scale,
            ExternRefSite::SummaryBackedBy,
            &rust_edge,
        )
        .err();
    assert!(feature_check(
        "b4.resolve_extern_ref.negative_twin.reference_rules",
        matches!(
            &foreign_edge,
            Some(ImportVerificationError::ImportIdMismatch {
                expected: 1,
                actual: 0
            })
        ) && matches!(
            &unknown_symbol,
            Some(ImportVerificationError::LinkSymbolMismatch { function: 0, .. })
        ) && matches!(
            &wrong_scope,
            Some(ImportVerificationError::ObligationScopeMismatch {
                obligation: 1,
                expected: 0,
                actual: Some(1)
            })
        ) && matches!(
            &no_such_obligation,
            Some(ImportVerificationError::ObligationUnresolved { obligation: 42, .. })
        ),
        &format!(
            "edge of another row => {foreign_edge:?}; symbol the local decl does not carry => \
             {unknown_symbol:?}; far #1 is scoped to dep_addmul => {wrong_scope:?}; far #42 => \
             {no_such_obligation:?}"
        ),
    ));

    // a Pending far obligation, and a kind a summary may not rest on.
    let mut pending_dep = dep.clone();
    pending_dep.proof_obligations[0].status = ProofStatus::Pending;
    let mut pending_root = root.clone();
    repin(&mut pending_root, &pending_dep);
    let edge = pending_root
        .verify_import(ids.rust_row, &pending_dep)
        .unwrap();
    let pending = pending_root
        .resolve_extern_ref(
            &backed_ref(ids),
            ids.scale,
            ExternRefSite::SummaryBackedBy,
            &edge,
        )
        .err();
    let mut kind_dep = dep.clone();
    kind_dep.proof_obligations[0].kind = ObligationKind::MemorySafety;
    let mut kind_root = root.clone();
    repin(&mut kind_root, &kind_dep);
    let edge = kind_root.verify_import(ids.rust_row, &kind_dep).unwrap();
    let kind = kind_root
        .resolve_extern_ref(
            &backed_ref(ids),
            ids.scale,
            ExternRefSite::SummaryBackedBy,
            &edge,
        )
        .err();
    assert!(feature_check(
        "b4.resolve_extern_ref.negative_twin.obligation_rules",
        matches!(
            &pending,
            Some(ImportVerificationError::ObligationNotDischarged {
                obligation: 0,
                status: ProofStatus::Pending
            })
        ) && matches!(
            &kind,
            Some(ImportVerificationError::ObligationKindInadmissible {
                obligation: 0,
                site: ExternRefSite::SummaryBackedBy,
                ..
            })
        ),
        &format!("Pending far row => {pending:?}; MemorySafety behind a contract => {kind:?}"),
    ));
}

// ---------------------------------------------------------------------------
// 4. validate_linked_module — the closure walk
// ---------------------------------------------------------------------------

fn b4_04_validate_linked_module() {
    let dep = build_dep(3);
    let (root, ids) = build_root(&dep, true);
    let set = ModuleSet::new([&dep]);

    let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    let ok = report.is_ok();
    let imports = report.authenticated_imports().cloned().unwrap_or_default();
    let backed: Vec<FuncId> = report
        .authenticated()
        .map(|a| a.authenticated_backed_by().collect())
        .unwrap_or_default();
    let inherited = report
        .authenticated_certificate_refs()
        .cloned()
        .unwrap_or_default();
    let replayed = report
        .replayed_certificate_refs()
        .cloned()
        .unwrap_or_default();
    assert!(feature_check(
        "b4.validate_linked_module",
        ok && report
            .validated_root()
            .is_some_and(|m| std::ptr::eq(m, &root))
            && imports.get(&ids.rust_row) == Some(&dep.stable_digest())
            && imports.get(&ids.clean_row) == Some(&dep.stable_digest())
            && backed == vec![ids.scale]
            && inherited == BTreeSet::from([root.proof_certificates[0].lineage_ref()])
            && replayed.is_empty(),
        &format!(
            "errors={:?}; authenticated imports={} rows; backed_by re-earned for {backed:?}; \
             {} inheritance cert admitted to the Discharged tier; kernel-tier refs on the root = {} \
             (inherited authority is never kernel-tier)",
            report.errors(),
            imports.len(),
            inherited.len(),
            replayed.len()
        ),
    ));

    // The same verdict from the WIRE alone: both crates serialized, reloaded
    // through each lossless transport, and re-earned from the decoded modules.
    let mut store = Vec::new();
    let loaded_digest = ModuleSet::decode_into(
        &mut store,
        &serialize_module(&dep).expect("serialize_module: test fixture"),
    );
    let truncated = {
        let bytes = serialize_module(&dep).expect("serialize_module: test fixture");
        ModuleSet::decode_into(&mut Vec::new(), &bytes[..bytes.len() - 1]).is_err()
    };
    let wire_root =
        deserialize_module(&serialize_module(&root).expect("serialize_module: test fixture"))
            .expect("root decodes");
    let from_binary = {
        let wire_set = ModuleSet::new(store.iter());
        validate_linked_module(&wire_root, &wire_set, &RejectingModuleProofAuthority).is_ok()
    };
    let json_dep: Module =
        serde_json::from_str(&serde_json::to_string(&dep).unwrap()).expect("dep json");
    let json_root: Module =
        serde_json::from_str(&serde_json::to_string(&root).unwrap()).expect("root json");
    let from_json = validate_linked_module(
        &json_root,
        &ModuleSet::new([&json_dep]),
        &RejectingModuleProofAuthority,
    )
    .is_ok();
    let pack_dep: Module =
        rmp_serde::from_slice(&rmp_serde::to_vec(&dep).unwrap()).expect("dep msgpack");
    let pack_root: Module =
        rmp_serde::from_slice(&rmp_serde::to_vec(&root).unwrap()).expect("root msgpack");
    let from_msgpack = validate_linked_module(
        &pack_root,
        &ModuleSet::new([&pack_dep]),
        &RejectingModuleProofAuthority,
    )
    .is_ok();
    assert!(feature_check(
        "b4.validate_linked_module.from_the_wire",
        loaded_digest.as_ref().ok() == Some(&dep.stable_digest())
            && from_binary
            && from_json
            && from_msgpack
            && truncated,
        &format!(
            "dep+root reloaded and re-earned: binary={from_binary} (ModuleSet::decode_into digest              matches={}), json={from_json}, msgpack={from_msgpack}; negative twin: dep blob minus              its last byte is refused at load={truncated}",
            loaded_digest.as_ref().ok() == Some(&dep.stable_digest())
        ),
    ));

    // authority entry point WITHOUT a resolver.
    let refused = validate_module_with_authority(&root, &RejectingModuleProofAuthority);
    assert!(feature_check(
        "b4.validate_linked_module.negative_twin.authority_without_resolver",
        unauthenticated(&refused, "backed_by", "no import resolver")
            && unauthenticated(&refused, "inherited", "no import resolver"),
        &format!("validate_module_with_authority(root) => {refused:?}"),
    ));

    // no module supplied.
    let empty = ModuleSet::new([]);
    let errors =
        validate_linked_module(&root, &empty, &RejectingModuleProofAuthority).into_errors();
    assert!(feature_check(
        "b4.validate_linked_module.negative_twin.import_unavailable",
        errors.iter().any(|e| matches!(e, ValidationError::ImportUnavailable { import: 0, name } if name == "b4_dep"))
            && errors.iter().any(|e| matches!(e, ValidationError::ImportUnavailable { import: 1, .. })),
        &format!("{errors:?}"),
    ));

    // one flipped byte in dep (resolved by NAME so the EDGE does the refusing).
    let tampered = tampered_dep();
    let by_name = |import: &ModuleImport| (import.name == "b4_dep").then_some(&tampered);
    let report = validate_linked_module(&root, &by_name, &RejectingModuleProofAuthority);
    let errors = report.errors().to_vec();
    assert!(feature_check(
        "b4.validate_linked_module.negative_twin.flipped_byte_in_dep",
        unauthenticated(&errors, "import", "stable digest")
            && report.validated_root().is_none()
            && report.authenticated_imports().is_none(),
        &format!("dep rebuilt with factor 3->2 => {errors:?}"),
    ));

    // [review] the LITERAL "one flipped byte" through the closure walk: every
    // decodable single-bit flip of the serialized dep, offered (a) by NAME =>
    // the edge refuses with the digest error, (b) through the digest-keyed
    // ModuleSet => it is simply not the module asked for (ImportUnavailable).
    let dep_bytes = serialize_module(&dep).expect("serialize_module: test fixture");
    let (mut flips, mut by_name_refused, mut by_digest_unavailable, mut linked_holes) =
        (0usize, 0usize, 0usize, Vec::new());
    for index in 0..dep_bytes.len() {
        let mut flipped = dep_bytes.clone();
        flipped[index] ^= 0x01;
        let Ok(Ok(candidate)) = catch_unwind(AssertUnwindSafe(|| deserialize_module(&flipped)))
        else {
            continue;
        };
        if candidate == dep {
            continue; // a tolerated non-canonical spelling of the SAME module
        }
        flips += 1;
        let by_name = |import: &ModuleImport| (import.name == "b4_dep").then_some(&candidate);
        let named = validate_linked_module(&root, &by_name, &RejectingModuleProofAuthority);
        let flipped_set = ModuleSet::new([&candidate]);
        let keyed = validate_linked_module(&root, &flipped_set, &RejectingModuleProofAuthority);
        let named_ok = unauthenticated(named.errors(), "import", "stable digest")
            && named.validated_root().is_none();
        let keyed_ok = keyed
            .errors()
            .iter()
            .any(|e| matches!(e, ValidationError::ImportUnavailable { import: 0, .. }));
        by_name_refused += usize::from(named_ok);
        by_digest_unavailable += usize::from(keyed_ok);
        if !(named_ok && keyed_ok) {
            linked_holes.push(index);
        }
    }
    assert!(feature_check(
        "b4.validate_linked_module.negative_twin.every_flipped_byte_in_dep",
        flips > 0
            && linked_holes.is_empty()
            && by_name_refused == flips
            && by_digest_unavailable == flips,
        &format!(
            "{flips} decodable single-bit flips of the {}-byte dep blob: resolved by NAME => \
             {by_name_refused} refused as UnauthenticatedImport{{import, digest}}; resolved by \
             DIGEST (ModuleSet) => {by_digest_unavailable} ImportUnavailable; holes={linked_holes:?}",
            dep_bytes.len()
        ),
    ));

    // [review] a resolver that hands back the importer itself is a CYCLE, named
    // as such (the cycle guard runs before the digest comparison).
    let itself = |_: &ModuleImport| Some(&root);
    let errors =
        validate_linked_module(&root, &itself, &RejectingModuleProofAuthority).into_errors();
    assert!(feature_check(
        "b4.validate_linked_module.negative_twin.import_cycle",
        errors.iter().any(|e| matches!(
            e,
            ValidationError::ImportCycle { import: 0, path } if path == &["b4_root", "b4_root"]
        )),
        &format!("resolver returns the root for its own import => {errors:?}"),
    ));

    // wrong producer on the import row the backed_by site cites.
    let mut wrong = root.clone();
    wrong.imports[0].producer = Some(Producer::Other("b4-unknown-frontend".into()));
    let errors = validate_linked_module(&wrong, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(feature_check(
        "b4.validate_linked_module.negative_twin.wrong_producer",
        errors.len() == 1 && unauthenticated(&errors, "backed_by", "was produced by"),
        &format!("{errors:?}"),
    ));

    // non-exported far symbol (root re-pinned to that build of dep).
    let mut private_dep = dep.clone();
    private_dep.functions[0].linkage = Linkage::Internal;
    let mut private_root = root.clone();
    repin(&mut private_root, &private_dep);
    let private_set = ModuleSet::new([&private_dep]);
    let errors =
        validate_linked_module(&private_root, &private_set, &RejectingModuleProofAuthority)
            .into_errors();
    assert!(feature_check(
        "b4.validate_linked_module.negative_twin.symbol_not_exported",
        errors.len() == 1
            && unauthenticated(&errors, "backed_by", "is not exported")
            && !unauthenticated(&errors, "inherited", ""),
        &format!(
            "dep_scale Internal in dep => {errors:?} (the dep_addmul inheritance still re-earns)"
        ),
    ));

    // signature skew (declaration-only importer, so nothing local co-fires).
    let (mut skewed, _) = build_root(&dep, false);
    let narrow = skewed
        .add_func_type(trust_ir::ty::FuncTy {
            params: vec![Ty::U32],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    skewed.function_by_id_mut(ids.scale).unwrap().ty = narrow;
    let errors =
        validate_linked_module(&skewed, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(feature_check(
        "b4.validate_linked_module.negative_twin.signature_skew",
        errors.len() == 1 && unauthenticated(&errors, "backed_by", "signature mismatch"),
        &format!("local decl dep_scale(u32)->u64 vs far (u64)->u64 => {errors:?}"),
    ));

    // a local contract that says MORE than the far one proved.
    let mut louder = root.clone();
    let summary = louder
        .function_by_id_mut(ids.scale)
        .unwrap()
        .summary
        .take()
        .unwrap();
    louder.function_by_id_mut(ids.scale).unwrap().summary =
        Some(summary.ensuring(ProofFormula::smtlib2("(= 2 2)", "Bool")));
    let errors =
        validate_linked_module(&louder, &set, &RejectingModuleProofAuthority).into_errors();
    // an inherited restatement that states a DIFFERENT formula.
    let mut restated = root.clone();
    restated.proof_obligations[0].formula = Some(ProofFormula::smtlib2("(<= 1 3)", "Bool"));
    let errors2 =
        validate_linked_module(&restated, &set, &RejectingModuleProofAuthority).into_errors();
    // [review] exactness INCLUDES the v41 bindings: same clause text, the free
    // name re-bound to a different IR place (ResultSlot 0 -> Param 0).
    let mut rebound = root.clone();
    rebound
        .function_by_id_mut(ids.scale)
        .unwrap()
        .summary
        .as_mut()
        .unwrap()
        .ensures[0]
        .bindings[0]
        .1
        .place = ClausePlace::Param { index: 0 };
    let same_text = rebound
        .function_by_id(ids.scale)
        .unwrap()
        .summary
        .as_ref()
        .unwrap()
        .ensures[0]
        .payload
        == scale_clause().payload;
    let errors3 =
        validate_linked_module(&rebound, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(feature_check(
        "b4.validate_linked_module.negative_twin.restatement_must_be_exact",
        errors.len() == 1
            && unauthenticated(&errors, "backed_by", "`ensures` differ")
            && unauthenticated(&errors2, "inherited", "does not restate")
            && same_text
            && errors3.len() == 1
            && unauthenticated(&errors3, "backed_by", "`ensures` differ"),
        &format!(
            "extra local ensures => {errors:?}; different inherited formula => {errors2:?}; same \
             clause text with `result` re-bound ResultSlot0->Param0 => {errors3:?}"
        ),
    ));

    // the far proof must itself be EARNED: strip dep's certificates (re-pinned).
    let mut hollow_dep = dep.clone();
    hollow_dep.proof_certificates.clear();
    let mut hollow_root = root.clone();
    repin(&mut hollow_root, &hollow_dep);
    let hollow_set = ModuleSet::new([&hollow_dep]);
    let errors = validate_linked_module(&hollow_root, &hollow_set, &RejectingModuleProofAuthority)
        .into_errors();
    assert!(feature_check(
        "b4.validate_linked_module.negative_twin.far_label_without_certificate",
        errors.iter().any(|e| matches!(
            e,
            ValidationError::ImportedModuleInvalid { import: 0, errors, first }
                if *errors == 2 && first.contains("carries no CleanCic certificate")
        )),
        &format!("dep says Certified but carries no CleanCic certificate => {errors:?}"),
    ));

    // [review] a far row that a CAPABILITY admitted (Discharged + solver
    // evidence, consumer authority that replays everything) validates in the
    // dependency but is NOT inheritable: only kernel-tier / authenticated
    // inheritance grounds a cross-crate inheritance (linked.rs:706-715).
    struct AdmitEverything;
    impl ModuleProofAuthority for AdmitEverything {
        fn replays_authority(&self, _: &Module, _: &ProofObligation, _: &ProofCertificate) -> bool {
            true
        }
    }
    let mut solver_dep = dep.clone();
    solver_dep.proof_obligations[1].status = ProofStatus::Discharged;
    solver_dep.proof_certificates[1].evidence = ProofEvidence::SmtProof(vec![0xB4]);
    let solver_dep_alone = validate_module_with_authority(&solver_dep, &AdmitEverything);
    let mut solver_root = root.clone();
    repin(&mut solver_root, &solver_dep);
    let solver_set = ModuleSet::new([&solver_dep]);
    let errors = validate_linked_module(&solver_root, &solver_set, &AdmitEverything).into_errors();
    assert!(feature_check(
        "b4.validate_linked_module.negative_twin.far_discharged_not_grounded",
        solver_dep_alone.is_empty() && unauthenticated(&errors, "inherited", "not grounded"),
        &format!(
            "dep #1 := Discharged + SmtProof, consumer capability admits everything: dep alone \
             => {solver_dep_alone:?}; linked => {errors:?}"
        ),
    ));
}

// ---------------------------------------------------------------------------
// 5. link + interpret the two modules together
// ---------------------------------------------------------------------------

/// The in-process half of section 5. The linked run itself (`b4.link_and_interpret`)
/// and the two linker GAP rows (`b4.gap.linked_image_of_proved_modules_fails_validation`,
/// `b4.gap.cli_linker_ignores_import_digest`) execute the real `trust-ir` binary, so they
/// live in `crates/trust-ir-cli/tests/two_language_cli.rs` over the same fixtures
/// (`b4_fixtures.rs`).
fn b4_05_link_and_interpret() {
    let dep = build_dep(3);
    let (root, _) = build_root(&dep, true);

    // The in-process reference interpreter executes ONE module: the root alone
    // cannot run, because its callees are body-less. Since WS2.12 a call into a
    // bodyless declaration with no host model is the named, fail-closed
    // `UnsupportedCall` (it used to enter the declaration and trap the
    // structural `MissingBlock` on validated IR).
    let alone = common::run_nullary(&root, "program");
    assert!(feature_check(
        "b4.link_and_interpret.negative_twin.root_alone",
        matches!(&alone, Err(why) if why.starts_with("UnsupportedCall")
            && why.contains("call to bodyless declaration @dep_scale: no host model")),
        &format!(
            "unlinked root on the in-process interpreter (call into a body-less declaration) => {alone:?}"
        ),
    ));
}

// ---------------------------------------------------------------------------
// 5b. [review] the CLOSURE: a claim re-earned through an intermediate crate
// ---------------------------------------------------------------------------

/// A crate that only RE-EXPORTS the proof: body-less `symbol` declaration whose
/// `proved` summary is `backed_by` far #`far_obligation` of `far`, plus a local
/// Discharged restatement #0 inheriting the same far row (so an importer of
/// THIS crate has an obligation to cite — R7 needs one scoped to the far fn).
fn build_forwarder(name: &str, far: &Module, far_obligation: u32) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info(name, target());
    let unary = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    mb.set_default_producer(Producer::TRust);
    let scale = mb.declare_function(SCALE, unary);
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    let row = m
        .intern_import(
            ModuleImport::new(far.name.clone(), far.stable_digest()).with_producer(Producer::TRust),
        )
        .expect("Module::intern_import: test fixture");
    let reference = ExternRef::new(row, SCALE).relying_on(ProofId::new(far_obligation));
    m.function_by_id_mut(scale).unwrap().summary =
        Some(scale_contract().proved().backed_by(reference.clone()));
    m.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Discharged,
            "inherited: dep_scale ensures (>= result 0)",
        )
        .with_function(scale)
        .with_formula(scale_clause()),
    );
    m.proof_certificates.push(ProofCertificate {
        obligation: ProofId::new(0),
        prover: "b4-compose".to_string(),
        evidence: ProofEvidence::InheritedFromCallee {
            callee: scale,
            obligation: ProofId::new(0),
            external: Some(reference),
        },
        assurance: None,
    });
    m
}

fn b4_05b_transitive_closure() {
    let dep = build_dep(3);
    let mid = build_forwarder("b4_mid", &dep, 0);
    let top = build_forwarder("b4_top", &mid, 0);

    let set = ModuleSet::new([&dep, &mid]);
    let report = validate_linked_module(&top, &set, &RejectingModuleProofAuthority);
    let imports = report.authenticated_imports().cloned().unwrap_or_default();
    assert!(feature_check(
        "b4.validate_linked_module.transitive",
        report.is_ok()
            && imports.get(&ImportId::new(0)) == Some(&mid.stable_digest())
            && report.authenticated_certificate_refs().map(|r| r.len()) == Some(1)
            && report
                .authenticated()
                .map(|a| a.authenticated_backed_by().count())
                == Some(1),
        &format!(
            "b4_top -> b4_mid (body-less forwarder: backed_by + inheritance) -> b4_dep \
             (definition, kernel-Certified): errors={:?}; top's import authenticated at mid's \
             digest={}",
            report.errors(),
            imports.get(&ImportId::new(0)) == Some(&mid.stable_digest())
        ),
    ));

    // twin 1: the LEAF is withheld. The chain must not bottom out in mid's say-so.
    let only_mid = ModuleSet::new([&mid]);
    let errors =
        validate_linked_module(&top, &only_mid, &RejectingModuleProofAuthority).into_errors();
    let leaf_withheld = errors.iter().any(|e| matches!(
        e,
        ValidationError::ImportedModuleInvalid { import: 0, first, .. } if first.contains("b4_dep")
    ));
    // twin 2: the LEAF is the rebuilt dep (factor 3->2), offered by name.
    let tampered = tampered_dep();
    let by_name = |import: &ModuleImport| match import.name.as_str() {
        "b4_dep" => Some(&tampered),
        "b4_mid" => Some(&mid),
        _ => None,
    };
    let errors2 =
        validate_linked_module(&top, &by_name, &RejectingModuleProofAuthority).into_errors();
    let leaf_tampered = errors2.iter().any(|e| matches!(
        e,
        ValidationError::ImportedModuleInvalid { import: 0, first, .. } if first.contains("stable digest")
    ));
    // twin 3: the intermediate is a BARE re-declaration (no summary, no proof
    // rows): a well-formed module that proves nothing. top re-pinned to it.
    let bare = {
        let mut mb = ModuleBuilder::new_with_target_info("b4_mid", target());
        let unary = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
        mb.set_default_producer(Producer::TRust);
        mb.declare_function(SCALE, unary);
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let bare_valid = validate_module(&bare).is_empty();
    let mut top_on_bare = top.clone();
    repin(&mut top_on_bare, &bare);
    let bare_set = ModuleSet::new([&bare]);
    let errors3 = validate_linked_module(&top_on_bare, &bare_set, &RejectingModuleProofAuthority)
        .into_errors();
    let bare_refused = unauthenticated(&errors3, "backed_by", "bare re-declaration proves nothing")
        && unauthenticated(&errors3, "inherited", "bare re-declaration proves nothing");
    let direct = top_on_bare
        .verify_import(ImportId::new(0), &bare)
        .and_then(|edge| {
            top_on_bare
                .resolve_extern_ref(
                    &ExternRef::new(ImportId::new(0), SCALE).relying_on(ProofId::new(0)),
                    FuncId::new(0),
                    ExternRefSite::SummaryBackedBy,
                    &edge,
                )
                .map(|_| ())
        })
        .err();
    assert!(feature_check(
        "b4.validate_linked_module.transitive.negative_twins",
        leaf_withheld
            && leaf_tampered
            && bare_valid
            && bare_refused
            && matches!(
                &direct,
                Some(ImportVerificationError::FarSiteIsUnbackedDeclaration { symbol }) if symbol == SCALE
            ),
        &format!(
            "leaf withheld => {errors:?}; leaf rebuilt 3->2 => {errors2:?}; intermediate is a bare \
             re-declaration (itself valid={bare_valid}) => {errors3:?}; resolve_extern_ref => {direct:?}"
        ),
    ));
}

// ---------------------------------------------------------------------------
// 6. GAP ratchets
// ---------------------------------------------------------------------------

/// RATIFIED-OUT (WS4.7, 42d9db73, F-077; docs/SPEC_RATIFICATIONS.md §6 "One
/// row per `(artifact, producer)` edge"). The archived GAP: R5 compares the far
/// function's producer with `ModuleImport.producer`, a single
/// `Option<Producer>`, and C5 refuses `None`, so a MIXED Rust+Clean dependency
/// needs TWO rows carrying the SAME digest -- the "one artifact, two ids" shape
/// `intern_import`'s doc then warned against. WS4.7 adopted that shape as
/// normative and reconciled the rustdoc (consumers deduplicating artifacts key
/// on digest). The row holds the ratified shape exactly: the two-row baseline
/// links, ONE row citing the Clean function is refused by R5, and an
/// unrecorded producer is refused by C5.
fn b4_06_gap_one_import_row_per_producer() {
    let dep = build_dep(3);
    let set = ModuleSet::new([&dep]);

    // Baseline (well-formed today): two rows, same digest, one per producer.
    let (root, ids) = build_root(&dep, true);
    let baseline = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    let two_rows_same_digest = root.imports.len() == 2
        && root.imports[0].digest == root.imports[1].digest
        && root.imports[0].name == root.imports[1].name
        && ids.rust_row != ids.clean_row;
    assert!(
        baseline.is_ok(),
        "baseline must link: {:?}",
        baseline.errors()
    );

    // The single change: ONE row for the one artifact; the Clean site cites it.
    let mut single = root.clone();
    single.imports.truncate(1);
    if let ProofEvidence::InheritedFromCallee { external, .. } =
        &mut single.proof_certificates[0].evidence
    {
        *external = Some(ExternRef::new(ids.rust_row, ADDMUL).relying_on(ProofId::new(1)));
    }
    let errors =
        validate_linked_module(&single, &set, &RejectingModuleProofAuthority).into_errors();

    // ...and an UNRECORDED producer is no way out either.
    let mut neutral = single.clone();
    neutral.imports[0].producer = None;
    let errors_none =
        validate_linked_module(&neutral, &set, &RejectingModuleProofAuthority).into_errors();
    let refused_unrecorded = unauthenticated(&errors_none, "import", "producer is unrecorded");

    assert!(feature_ratified(
        "b4.gap.one_import_row_per_producer",
        // Follow-on: the inheritance row the refused import was to ground stays undischarged.
        Expect::refused_with("UnauthenticatedImport", &["was produced by clean"])
            .with_follow_ons(&["DischargedWithoutCertificate"]),
        Outcome::of(&errors).given(&[
            (
                "the baseline needs two rows with the same digest",
                two_rows_same_digest
            ),
            ("an unrecorded producer is refused too", refused_unrecorded),
        ]),
        &format!(
            "mixed TRust+Clean dep: baseline needs 2 import rows with the SAME digest \
             ({two_rows_same_digest}); ONE row (TRust) citing the Clean fn => {errors:?}; ONE row \
             with producer None => {errors_none:?}"
        ),
    ));
}

/// RATIFIED-OUT — a NAMED NON-TASK (WS1.16, F-027; docs/SPEC_RATIFICATIONS.md
/// §12 "Named non-tasks", row F-027). DECIDE adopted: compiler-side erasure —
/// a proof-only edge is erased before lowering, so the format carries no
/// proof-only marker and a single module needs none. TRIGGER: a cross-crate
/// WHITE-BOX proof entering the plan; then `Function.proof_only` and
/// `ExternRefSite::ProofOnly` are added (a wire change) and this row flips to
/// PASS with a negative twin. Held in its exact archived shape, which was:
///
/// GAP: no PROOF-only / proof-private marker. Two halves of one absence:
/// (a) a proof may only be cited about an EXPORTED far symbol (R4,
///     trust-ir/src/imports.rs:671-676 `SymbolNotExported`) — a cross-crate
///     white-box proof about a private item cannot be re-earned;
/// (b) nothing on `Function` / `ModuleImport` / `ExternRef` says "PROOF may
///     name this, CALL may not": once a spec-only symbol is exported so that
///     it CAN be cited, an importer may also CALL it and every validator tier
///     admits the call. Design requirement blocked: G5 PROOF/CALL visibility +
///     the proof-only firewall enforced across links (spec-surface row 18).
fn b4_07_gap_no_proof_only_marker() {
    let dep = build_dep(3);
    let set = ModuleSet::new([&dep]);

    // Baseline: a declaration-only importer CITES both far functions and calls
    // neither. Links.
    let (citing, ids) = build_root(&dep, false);
    let baseline = validate_linked_module(&citing, &set, &RejectingModuleProofAuthority);
    assert!(baseline.is_ok(), "{:?}", baseline.errors());

    // Single change: the importer also CALLS the cited symbols. Nothing refuses.
    let (calling, _) = build_root(&dep, true);
    let called = validate_linked_module(&calling, &set, &RejectingModuleProofAuthority);
    let call_admitted = called.is_ok();

    // (a) private far symbol cannot be cited at all.
    let mut private_dep = dep.clone();
    private_dep.functions[0].linkage = Linkage::Private;
    let mut private_root = citing.clone();
    repin(&mut private_root, &private_dep);
    let private_set = ModuleSet::new([&private_dep]);
    let errors =
        validate_linked_module(&private_root, &private_set, &RejectingModuleProofAuthority)
            .into_errors();
    let private_uncitable = unauthenticated(&errors, "backed_by", "is not exported");

    // The carriers, field by field (JSON = the self-describing transport).
    let function_keys = json_keys(&serde_json::to_value(&dep.functions[0]).unwrap());
    let import_keys = json_keys(&serde_json::to_value(&citing.imports[0]).unwrap());
    let extern_keys = json_keys(&serde_json::to_value(backed_ref(ids)).unwrap());
    let marker_words = [
        "proof_only",
        "ghost",
        "erased",
        "spec_only",
        "proof_visible",
        "call_visible",
        "observer",
    ];
    let no_marker = function_keys
        .iter()
        .chain(&import_keys)
        .chain(&extern_keys)
        .all(|k| marker_words.iter().all(|w| !k.contains(w)));

    assert!(feature_ratified(
        "b4.gap.no_proof_only_marker",
        Expect::Accepted,
        Outcome::of(called.errors()).given(&[
            ("a private far symbol is uncitable", private_uncitable),
            (
                "no proof-only / ghost field on Function / ModuleImport / ExternRef",
                no_marker
            ),
            (
                "ExternRef is {module, obligation, symbol}",
                extern_keys == ["module", "obligation", "symbol"]
            ),
        ]),
        &format!(
            "cited-only importer links; SAME importer + CALLS to the cited symbols also links \
             ({call_admitted}); Linkage::Private far symbol is uncitable ({errors:?}); ExternRef \
             fields={extern_keys:?}; ModuleImport fields={import_keys:?}; no proof-only/ghost field \
             among {} Function fields",
            function_keys.len()
        ),
    ));
}

/// FLIPPED (closed by WS4.10, F-084). The archived GAP: no
/// `ModuleImport.scheme` — the identity domain was ONE compile-time constant
/// and the row was exactly (name, digest, producer), so an import recorded
/// under `trust_ir.module.v2` could not stay authenticable once the digest
/// construction changed. v44 adds the `IdentityScheme` discriminator and
/// `Module::stable_digest_under(scheme)`; the verifier hashes the candidate
/// under the ROW's scheme. PASS = the discriminator rides every codec, a V3
/// row authenticates under v3 and a V2 row under v2; right-reason negative
/// twin = the SAME v3 digest recorded on a V2 row is `DigestMismatch` (a
/// scheme is never silently re-read as another).
fn b4_08_gap_no_import_scheme() {
    let dep = build_dep(3);
    let (root, ids) = build_root(&dep, false);
    let row = root.import(ids.rust_row).unwrap();

    // JSON: the V3 row spells its scheme; the same row as V2 omits the key
    // (the pre-v44 spelling) and a key-less row reads back as V2.
    let value = serde_json::to_value(row).unwrap();
    let keys = json_keys(&value);
    let reread: ModuleImport = serde_json::from_value(value.clone()).unwrap();
    let legacy_row = row.clone().with_scheme(IdentityScheme::V2);
    let legacy_value = serde_json::to_value(&legacy_row).unwrap();
    let legacy_keys = json_keys(&legacy_value);
    let mut keyless = value.clone();
    keyless.as_object_mut().unwrap().remove("scheme");
    let keyless_scheme = serde_json::from_value::<ModuleImport>(keyless)
        .unwrap()
        .scheme;

    // Positional MessagePack: V3 is a 4-array, V2 keeps the 3-array.
    let packed = rmp_serde::to_vec(row).unwrap();
    let packed_legacy = rmp_serde::to_vec(&legacy_row).unwrap();
    let arities = (packed.first().copied(), packed_legacy.first().copied());

    // Binary: the V3 row selects v44 and survives a round trip.
    let bytes = serialize_module(&root).expect("serialize_module: test fixture");
    let header = u32::from_le_bytes(bytes[8..12].try_into().unwrap());
    let decoded_scheme = trust_ir::binary::deserialize_module(&bytes)
        .ok()
        .and_then(|m| m.imports.get(ids.rust_row.as_usize()).map(|r| r.scheme));

    // Authentication follows the row's scheme.
    let v3_ok = root.verify_import(ids.rust_row, &dep).is_ok();
    let mut v2_root = root.clone();
    v2_root.imports[ids.rust_row.as_usize()] = ModuleImport {
        digest: dep.stable_digest_under(IdentityScheme::V2),
        ..legacy_row.clone()
    };
    let v2_ok = v2_root.verify_import(ids.rust_row, &dep).is_ok();
    // twin: the v3 digest on a V2 row (a scheme swap) is refused by name.
    let mut swapped = root.clone();
    swapped.imports[ids.rust_row.as_usize()].scheme = IdentityScheme::V2;
    let swap = swapped.verify_import(ids.rust_row, &dep).err();

    assert!(feature_check(
        "b4.gap.no_module_import_scheme",
        keys == ["digest", "name", "producer", "scheme"]
            && reread == *row
            && legacy_keys == ["digest", "name", "producer"]
            && keyless_scheme == IdentityScheme::V2
            && arities == (Some(0x94), Some(0x93))
            && header == 44
            && decoded_scheme == Some(IdentityScheme::V3)
            && v3_ok
            && v2_ok
            && matches!(
                swap,
                Some(ImportVerificationError::DigestMismatch { import: 0, .. })
            ),
        &format!(
            "closed by WS4.10: V3 row JSON keys={keys:?} (V2 row keys={legacy_keys:?}; a key-less \
             row reads as {keyless_scheme:?}); msgpack arrays V3/V2 = {arities:?}; binary header \
             v{header}, decoded scheme {decoded_scheme:?}; V3 row authenticates={v3_ok}, V2 row \
             under the v2 digest authenticates={v2_ok}; the v3 digest on a V2 row => {swap:?}; \
             current domain {MODULE_IDENTITY_DOMAIN:?}"
        ),
    ));
}

/// FLIPPED (closed upstream by da6ff616 + c3a1594e, roadmap WS1.7 = WS4.8,
/// F-068). The archived GAP: an import row that no PROOF-bearing row cited was
/// never authenticated — `validate_linked_module` walked `proof_bearing_sites`
/// only, so a plain cross-crate CALL edge was checked against nothing: the
/// digest could name no module anyone holds, and the importer's declaration
/// could disagree with the far definition's signature. WS1.7 runs L1-L4 for
/// EVERY `Module::imports` row (an unsupplied row is `ImportUnavailable`) and
/// resolves every call edge (L10, `UnauthenticatedImport { site: "call" }`).
/// Requirement: G5 "one shared ABI across the boundary" / I-IFACE
/// compat(I_1..I_n) checked at link.
///
/// The single-module authority tier (no resolver) is measured and reported in
/// the detail only: a call-only row is not proof-bearing, so that tier's
/// `UnauthenticatedImport` refusal does not reach it; authentication of such a
/// row is the linked walk's job.
fn b4_09_gap_call_only_import_is_never_authenticated() {
    let dep = build_dep(3);

    // Baseline: a call-only importer (no summary, no certificate), correct
    // digest, correct signature. Links, and its one row is authenticated
    // although nothing cites it (mutation control: no false refusal).
    let call_only = |digest: ProofDigest, scale_param: Ty| -> Module {
        let mut mb = ModuleBuilder::new_with_target_info("b4_call_only", target());
        let unary = mb.add_func_type(vec![scale_param.clone()], vec![Ty::U64]);
        let nullary = mb.add_func_type(vec![], vec![Ty::U64]);
        mb.set_default_producer(Producer::TRust);
        let scale = mb.declare_function(SCALE, unary);
        let mut fb = mb.function("program", nullary);
        fb.set_producer(Producer::TRust);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let two = fb.uconst(scale_param, 2);
        let out = fb.call(scale, vec![two]);
        fb.ret(vec![out]);
        fb.build();
        let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
        m.intern_import(ModuleImport::new("b4_dep", digest).with_producer(Producer::TRust))
            .expect("Module::intern_import: test fixture");
        m
    };
    let set = ModuleSet::new([&dep]);
    let good = call_only(dep.stable_digest(), Ty::U64);
    let baseline = validate_linked_module(&good, &set, &RejectingModuleProofAuthority);
    assert!(baseline.is_ok(), "{:?}", baseline.errors());
    let baseline_authenticated = baseline.authenticated_imports().map(|m| m.len());

    // Negative twin 1: the digest names nothing, and NO module is supplied.
    let empty = ModuleSet::new([]);
    let bogus = call_only(ProofDigest::sha256([0xEE; 32]), Ty::U64);
    let bogus_report = validate_linked_module(&bogus, &empty, &RejectingModuleProofAuthority);
    // Negative twin 2: the declaration's signature is skewed against the far
    // definition — the same skew the raw comparator sees.
    let skewed = call_only(dep.stable_digest(), Ty::U32);
    let skewed_report = validate_linked_module(&skewed, &set, &RejectingModuleProofAuthority);
    let comparator = trust_ir::signatures_compatible(
        &skewed,
        skewed.function_by_name(SCALE).unwrap(),
        &dep,
        dep.function_by_name(SCALE).unwrap(),
    );
    let authority_tier = validate_module_with_authority(&bogus, &RejectingModuleProofAuthority);

    let unavailable = matches!(
        bogus_report.errors(),
        [ValidationError::ImportUnavailable { import: 0, name }] if name == "b4_dep"
    );
    let call_refused = matches!(
        skewed_report.errors(),
        [ValidationError::UnauthenticatedImport { import: 0, site: "call", detail }]
            if detail.contains("signature mismatch")
    );
    assert!(feature_check(
        "b4.gap.call_only_import_never_authenticated",
        unavailable && call_refused && baseline_authenticated == Some(1) && comparator.is_err(),
        &format!(
            "closed upstream by da6ff616: call-only importer: authenticated import rows on \
             the honest baseline = {baseline_authenticated:?}; garbage digest + EMPTY resolver \
             => {:?}; decl dep_scale(u32) vs far (u64) => {:?} (signatures_compatible says \
             {comparator:?}); single-module authority tier (no resolver, row not \
             proof-bearing) => {authority_tier:?}",
            bogus_report.errors(),
            skewed_report.errors()
        ),
    ));
}

/// FLIPPED (closed upstream by 42d9db73, roadmap WS4.7, F-075 / F-076). The
/// archived GAPs: `Module.imports` was documented as content-interned ("never
/// `push`") but no validator tier rejected a duplicated row; and the hash-once
/// hook `verify_import_with_computed_digest` trusted a CALLER-ASSERTED `actual`
/// digest, so passing the record authenticated an arbitrary module. WS4.7
/// added `ValidationError::ImportTableNotInterned` in every tier and
/// `HashedModule` / `Module::verify_import_hashed` (the deprecated form now
/// always recomputes).
fn b4_10_gap_import_table_hygiene() {
    let dep = build_dep(3);
    let set = ModuleSet::new([&dep]);
    let (root, ids) = build_root(&dep, true);
    let baseline = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    let baseline_structural = validate_module(&root);
    assert!(baseline.is_ok(), "{:?}", baseline.errors());

    // PASS: a pushed clone of imports[0] is refused by name in the structural
    // tier (beside the one known structural row: the Discharged inheritance a
    // linked walk alone can admit) and in the linked tier. Negative twin: the
    // interned table (the baseline) links, and its structural report is that
    // known row alone.
    let mut duplicated = root.clone();
    duplicated.imports.push(root.imports[0].clone());
    let structural = validate_module(&duplicated);
    let linked = validate_linked_module(&duplicated, &set, &RejectingModuleProofAuthority);
    let not_interned = |e: &ValidationError| {
        matches!(
            e,
            ValidationError::ImportTableNotInterned { first: 0, duplicate: 2, name }
                if name == "b4_dep"
        )
    };
    let known_row = |e: &ValidationError| {
        matches!(
            e,
            ValidationError::DischargedWithoutCertificate { obligation: 0 }
        )
    };
    let structural_exact = structural.len() == 2
        && structural.iter().filter(|e| not_interned(e)).count() == 1
        && structural.iter().filter(|e| known_row(e)).count() == 1;
    let linked_refused =
        !linked.is_ok() && linked.errors().iter().filter(|e| not_interned(e)).count() == 1;
    assert!(feature_check(
        "b4.gap.duplicate_import_rows_admitted",
        structural_exact
            && linked_refused
            && duplicated.imports[0] == duplicated.imports[2]
            && matches!(baseline_structural.as_slice(), [e] if known_row(e)),
        &format!(
            "closed upstream by 42d9db73: imports[2] := clone of imports[0] (pushed, not \
             interned): validate_module => {structural:?}; validate_linked_module => {:?}; \
             interned baseline: structural {baseline_structural:?}, linked ok",
            linked.errors()
        ),
    ));

    // PASS: the hash-once form can no longer be handed the RECORDED digest.
    // Both the typed `verify_import_hashed(HashedModule::new(..))` and the
    // deprecated caller-digest form refuse the tampered module with
    // DigestMismatch, like `verify_import`. Negative twin: the honest dependency
    // authenticates through both forms.
    let tampered = tampered_dep();
    let recorded = root.import(ids.rust_row).unwrap().digest;
    #[allow(deprecated)]
    let asserted = root.verify_import_with_computed_digest(ids.rust_row, &tampered, recorded);
    let hashed = root.verify_import_hashed(ids.rust_row, &HashedModule::new(&tampered));
    let honest = root.verify_import(ids.rust_row, &tampered);
    #[allow(deprecated)]
    let honest_asserted = root.verify_import_with_computed_digest(ids.rust_row, &dep, recorded);
    let honest_hashed = root.verify_import_hashed(ids.rust_row, &HashedModule::new(&dep));
    let mismatch = |r: &Result<_, ImportVerificationError>| {
        matches!(r, Err(ImportVerificationError::DigestMismatch { .. }))
    };
    assert!(feature_check(
        "b4.gap.computed_digest_is_caller_asserted",
        mismatch(&asserted)
            && mismatch(&hashed)
            && mismatch(&honest)
            && honest_asserted.is_ok()
            && honest_hashed.is_ok(),
        &format!(
            "closed upstream by 42d9db73: tampered dep given the RECORDED digest => {:?}; \
             verify_import_hashed(tampered) => {:?}; verify_import(tampered) => {:?}; honest dep \
             through both hash-once forms: ok={} / ok={}",
            asserted.as_ref().err(),
            hashed.as_ref().err(),
            honest.as_ref().err(),
            honest_asserted.is_ok(),
            honest_hashed.is_ok()
        ),
    ));
}

/// FLIPPED (closed by WS1.3, F-003; the cross-crate face of b2's "no
/// per-clause -> obligation backref"). The archived GAP (discovered in
/// review): `backed_by` re-earned a COUNT, not a CLAUSE. `proved` was a
/// counting rule (N ensures needed N Discharged/Certified Postconditions
/// scoped to the function — formulas never compared), and `check_backed_by`
/// compared the importer's clauses with the far SUMMARY's clauses, never with
/// the cited obligation's formula. So a dependency could publish a FALSE
/// `ensures`, mark it `proved` beside a kernel-certified tautology, and an
/// importer re-earned the false clause under the strictest linked entry point.
/// Now the dependency's own pass refuses the unbacked clause by name, the
/// linked walk takes that verdict (`ImportedModuleInvalid`), and nothing is
/// re-earned. The inheritance site (which always compared formulas) is kept
/// as contrast.
fn b4_11_gap_backed_by_reearns_a_count_not_a_clause() {
    // Baseline: the honest pair (summary clause == certified obligation's formula).
    let dep = build_dep(3);
    let (root, ids) = build_root(&dep, true);
    let honest = validate_linked_module(
        &root,
        &ModuleSet::new([&dep]),
        &RejectingModuleProofAuthority,
    );
    assert!(honest.is_ok(), "baseline must link: {:?}", honest.errors());
    let honest_clause_is_the_certified_formula = dep.functions[0].summary.as_ref().unwrap().ensures
        [0]
        == *dep.proof_obligations[0].formula.as_ref().unwrap();

    // Single change (made on BOTH sides, because restatement must be exact):
    // the published clause becomes `result = 0` — FALSE for dep_scale(2) = 6.
    // Obligations and certificates are untouched.
    let mut false_clause = ProofFormula::smtlib2("(= result 0)", "Bool");
    false_clause.bindings = scale_clause().bindings;
    let false_contract = || {
        FunctionSummary::new()
            .with_params(vec!["x".to_string()])
            .ensuring(false_clause.clone())
    };
    let mut lying_dep = dep.clone();
    lying_dep.functions[0].summary = Some(false_contract().proved());
    let lying_dep_errors =
        validate_module_with_authority(&lying_dep, &RejectingModuleProofAuthority);
    let (mut lying_root, _) = build_root(&lying_dep, true);
    lying_root.function_by_id_mut(ids.scale).unwrap().summary =
        Some(false_contract().proved().backed_by(backed_ref(ids)));
    let report = validate_linked_module(
        &lying_root,
        &ModuleSet::new([&lying_dep]),
        &RejectingModuleProofAuthority,
    );
    let reearned: Vec<FuncId> = report
        .authenticated()
        .map(|a| a.authenticated_backed_by().collect())
        .unwrap_or_default();
    // The clause really is false of the body that was linked.
    let actual = common::run_with_args(
        &lying_dep,
        SCALE,
        vec![trust_ir::interpret::InterpretValue::int(Ty::U64, 2).unwrap()],
    )
    .ok()
    .and_then(|r| r.first().and_then(common::as_u128));

    // Contrast: the SAME lie told through the inheritance site is refused.
    let mut lying_inheritance = root.clone();
    lying_inheritance.proof_obligations[0].formula =
        Some(ProofFormula::smtlib2("(= result 0)", "Bool"));
    let inheritance_errors = validate_linked_module(
        &lying_inheritance,
        &ModuleSet::new([&dep]),
        &RejectingModuleProofAuthority,
    )
    .into_errors();

    let refusal = "ensures clause 0 `(= result 0)` has no Discharged/Certified Postcondition row \
                   scoped to this function stating exactly this clause (rows stating other \
                   clauses do not count)";
    let dep_refused = matches!(
        lying_dep_errors.as_slice(),
        [ValidationError::InvalidFunctionSummary { function: 0, detail }] if detail == refusal
    );
    // The walk takes the dependency's verdict; the root's own rows that
    // leaned on it lose their ground (`DischargedWithoutCertificate`), and
    // nothing else is reported.
    let walk_refused = report.errors().iter().any(|e| {
        matches!(e, ValidationError::ImportedModuleInvalid { import: 0, first, .. }
            if first.ends_with(refusal))
    }) && report.errors().iter().all(|e| {
        matches!(e, ValidationError::ImportedModuleInvalid { first, .. } if first.ends_with(refusal))
            || matches!(e, ValidationError::DischargedWithoutCertificate { .. })
    });
    assert!(feature_check(
        "b4.gap.backed_by_reearns_a_count_not_a_clause",
        dep_refused
            && walk_refused
            && reearned.is_empty()
            && honest_clause_is_the_certified_formula
            && actual == Some(6)
            && unauthenticated(&inheritance_errors, "inherited", "does not restate"),
        &format!(
            "closed by WS1.3: dep publishes `ensures (= result 0)` proved, backed only by the \
             kernel-Certified `(>= result 0)`: dep authority-tier errors={lying_dep_errors:?}; \
             importer restating the false clause => validate_linked_module errors={:?}, \
             backed_by re-earned for {reearned:?}; dep_scale(2) = {actual:?} on the reference \
             interpreter. Contrast: the same false formula through InheritedFromCallee => \
             {inheritance_errors:?}",
            report.errors()
        ),
    ));
}

// ---------------------------------------------------------------------------
// local helpers
// ---------------------------------------------------------------------------

fn json_keys(value: &serde_json::Value) -> Vec<String> {
    let mut keys: Vec<String> = value
        .as_object()
        .map(|o| o.keys().cloned().collect())
        .unwrap_or_default();
    keys.sort();
    keys
}

#[test]
fn two_language_b4() {
    common::run_target(
        "b4",
        &[
            (
                "b4_01_import_rows_digest_and_wire",
                b4_01_import_rows_digest_and_wire,
            ),
            ("b4_02_verify_import", b4_02_verify_import),
            ("b4_03_resolve_extern_ref", b4_03_resolve_extern_ref),
            ("b4_04_validate_linked_module", b4_04_validate_linked_module),
            ("b4_05_link_and_interpret", b4_05_link_and_interpret),
            ("b4_05b_transitive_closure", b4_05b_transitive_closure),
            (
                "b4_06_gap_one_import_row_per_producer",
                b4_06_gap_one_import_row_per_producer,
            ),
            (
                "b4_07_gap_no_proof_only_marker",
                b4_07_gap_no_proof_only_marker,
            ),
            ("b4_08_gap_no_import_scheme", b4_08_gap_no_import_scheme),
            (
                "b4_09_gap_call_only_import_is_never_authenticated",
                b4_09_gap_call_only_import_is_never_authenticated,
            ),
            (
                "b4_10_gap_import_table_hygiene",
                b4_10_gap_import_table_hygiene,
            ),
            (
                "b4_11_gap_backed_by_reearns_a_count_not_a_clause",
                b4_11_gap_backed_by_reearns_a_count_not_a_clause,
            ),
        ],
    );
}
