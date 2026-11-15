// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! IMPORT AUTHENTICATION, layer 2 (`trust_ir_build::validate_linked_module`).
//!
//! The structural validator takes `Module::imports` on faith; the authority
//! tier refuses proof-bearing imports outright; the linked validator RE-EARNS
//! them against the dependency module's stable digest. Every positive test has
//! its negatives beside it, because each forgery below is spellable on the
//! v41 wire and compiles cleanly.

use std::cell::Cell;
use std::collections::BTreeSet;

use trust_ir::clean_expr_lowering::contract::contract_clean_cic_certificate;
use trust_ir::proof::{
    CoverageAssurance, CoverageBound, ModuleProofAuthority, ObligationKind, ProofCertificate,
    ProofCertificateRef, ProofDigest, ProofDigestAlgorithm, ProofEvidence, ProofFormula,
    ProofObligation, ProofStatus, RejectingModuleProofAuthority,
};
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{FuncId, ImportId, ProofId};
use trust_ir::{
    Endianness, ExternRef, Function, FunctionSummary, Linkage, Module, ModuleImport, Producer,
    TargetInfo,
};
use trust_ir_build::{
    ModuleBuilder, ModuleSet, ValidationError, coverage_supports, validate_linked_module,
    validate_module, validate_module_report, validate_module_with_authority,
};

// ---------------------------------------------------------------------------
// fixtures
// ---------------------------------------------------------------------------

fn target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    }
}

fn clause() -> ProofFormula {
    ProofFormula::smtlib2("(= 1 1)", "Bool")
}

/// The contract both sides state: `fn f(x) ensures (= 1 1)`.
fn contract() -> FunctionSummary {
    FunctionSummary::new()
        .with_params(vec!["x".to_string()])
        .ensuring(clause())
}

/// A kernel-CERTIFIED Postcondition obligation `id`, scoped to `function`,
/// with its `CleanCic` certificate: the Clean kernel really discharges
/// `(= 1 1)`, and the in-process validator really re-checks it.
fn certified_postcondition(id: u32, function: FuncId) -> (ProofObligation, ProofCertificate) {
    let obligation = ProofObligation::new(
        ProofId::new(id),
        ObligationKind::Postcondition,
        ProofStatus::Certified,
        "ensures (= 1 1)",
    )
    .with_function(function)
    .with_formula(clause());
    let certificate = contract_clean_cic_certificate(&obligation, "contract-prover")
        .expect("(= 1 1) is genuinely kernel-provable");
    (obligation, certificate)
}

/// A dependency module `name` defining `fn f(x: i64) -> i64 { x + 1 }` with a
/// `proved` contract backed by a kernel-certified Postcondition (#0).
fn dependency(name: &str) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info(name, target());
    mb.set_default_producer(Producer::TRust);
    let ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::I64);
    fb.switch_to_block(entry);
    let one = fb.iconst(Ty::I64, 1);
    let r = fb.add(Ty::I64, x, one);
    fb.ret(vec![r]);
    fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    let f = module.functions[0].id;
    module.functions[0].summary = Some(contract().proved());
    let (obligation, certificate) = certified_postcondition(0, f);
    module.proof_obligations.push(obligation);
    module.proof_certificates.push(certificate);
    assert!(
        validate_module(&module).is_empty(),
        "the dependency fixture must validate on its own: {:?}",
        validate_module(&module)
    );
    module
}

/// An importer `name` that records `dep` and declares `f` (body-less, same
/// signature and producer), with `summary`.
fn importer(name: &str, dep: &Module, summary: FunctionSummary) -> (Module, ImportId) {
    let mut m = Module::new(name);
    m.target_info = Some(target());
    let id = m
        .intern_import(
            ModuleImport::new(dep.name.clone(), dep.stable_digest()).with_producer(Producer::TRust),
        )
        .expect("Module::intern_import: test fixture");
    let ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::declaration(FuncId::new(0), "f", ft, summary);
    f.producer = Some(Producer::TRust);
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    (m, id)
}

fn far(id: ImportId, obligation: u32) -> ExternRef {
    ExternRef::new(id, "f").relying_on(ProofId::new(obligation))
}

/// An importer whose `proved` contract is backed by the dependency's #0.
fn backed_importer(name: &str, dep: &Module) -> Module {
    let (mut m, id) = importer(name, dep, contract());
    m.functions[0].summary = Some(contract().proved().backed_by(far(id, 0)));
    m
}

/// An importer whose local obligation #0 (Discharged) restates the
/// dependency's #0 through a cross-crate inheritance certificate.
fn inheriting_importer(name: &str, dep: &Module) -> Module {
    let (mut m, id) = importer(name, dep, contract());
    let f = m.functions[0].id;
    m.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Discharged,
            "inherited ensures (= 1 1)",
        )
        .with_function(f)
        .with_formula(clause()),
    );
    m.proof_certificates
        .push(inheritance_certificate(0, f, far(id, 0)));
    m
}

fn inheritance_certificate(
    discharges: u32,
    callee: FuncId,
    external: ExternRef,
) -> ProofCertificate {
    ProofCertificate {
        obligation: ProofId::new(discharges),
        prover: "compose".to_string(),
        evidence: ProofEvidence::InheritedFromCallee {
            callee,
            obligation: ProofId::new(discharges),
            external: Some(external),
        },
        assurance: None,
    }
}

/// Admits exactly one certificate by lineage reference — the shape of a
/// consumer that re-established one solver verdict in-process.
struct AdmitExact(ProofCertificateRef);

impl ModuleProofAuthority for AdmitExact {
    fn replays_authority(
        &self,
        _module: &Module,
        obligation: &ProofObligation,
        certificate: &ProofCertificate,
    ) -> bool {
        certificate.obligation == obligation.id && certificate.lineage_ref() == self.0
    }
}

fn has(errors: &[ValidationError], predicate: impl Fn(&ValidationError) -> bool) -> bool {
    errors.iter().any(predicate)
}

fn unauthenticated_at(errors: &[ValidationError], at: &str) -> bool {
    has(
        errors,
        |e| matches!(e, ValidationError::UnauthenticatedImport { site, .. } if *site == at),
    )
}

fn detail_contains(errors: &[ValidationError], at: &str, needle: &str) -> bool {
    has(errors, |e| {
        matches!(
            e,
            ValidationError::UnauthenticatedImport { site, detail, .. }
                if *site == at && detail.contains(needle)
        )
    })
}

// ---------------------------------------------------------------------------
// the three tiers on the g5 module
// ---------------------------------------------------------------------------

/// The g5 `backed` module: a contract-only declaration whose `proved` bit is
/// backed ONLY by a citation into an import whose digest names no module
/// anyone holds.
fn g5_backed_module() -> Module {
    let mut module = Module::new("g5_decl");
    module.target_info = Some(target());
    let ft = module
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    module.imports.push(
        ModuleImport::new("upstream", ProofDigest::sha256([0xA1; 32]))
            .with_producer(Producer::TRust),
    );
    module
        .try_add_function(Function::declaration(
            FuncId::new(0),
            "opaque",
            ft,
            contract()
                .proved()
                .backed_by(ExternRef::new(ImportId::new(0), "opaque").relying_on(ProofId::new(3))),
        ))
        .expect("Module::try_add_function: test fixture");
    module
}

#[test]
fn the_structural_tier_keeps_its_faith_floor_and_the_authority_tier_refuses() {
    let module = g5_backed_module();
    assert!(
        validate_module(&module).is_empty(),
        "structural validation is unchanged: {:?}",
        validate_module(&module)
    );
    let report = validate_module_report(&module);
    assert_eq!(
        report.proof_bearing_imports(),
        BTreeSet::from([ImportId::new(0)])
    );

    let errors = validate_module_with_authority(&module, &RejectingModuleProofAuthority);
    assert!(
        unauthenticated_at(&errors, "backed_by"),
        "the authority tier has no resolver and must refuse: {errors:?}"
    );

    let empty = ModuleSet::new([]);
    let report = validate_linked_module(&module, &empty, &RejectingModuleProofAuthority);
    assert!(
        has(report.errors(), |e| matches!(
            e,
            ValidationError::ImportUnavailable { import: 0, name } if name == "upstream"
        )),
        "no module supplied for the import: {:?}",
        report.errors()
    );
    assert!(report.validated_root().is_none());
    assert!(report.authenticated_imports().is_none());
}

#[test]
fn an_unproved_or_obligation_free_citation_is_not_proof_bearing() {
    let dep = dependency("dep");
    let (mut m, id) = importer("root", &dep, contract());
    // Names the entity only: no claim, nothing to authenticate, nothing refused.
    m.functions[0].summary = Some(contract().backed_by(ExternRef::new(id, "f")));
    assert!(
        validate_module_report(&m)
            .proof_bearing_imports()
            .is_empty()
    );
    assert!(validate_module_with_authority(&m, &RejectingModuleProofAuthority).is_empty());
}

// ---------------------------------------------------------------------------
// backed_by
// ---------------------------------------------------------------------------

#[test]
fn a_backed_by_contract_is_re_earned_against_the_dependency() {
    let dep = dependency("dep");
    let root = backed_importer("root", &dep);
    let set = ModuleSet::new([&dep]);
    let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    assert!(report.is_ok(), "{:?}", report.errors());
    assert!(std::ptr::eq(report.validated_root().unwrap(), &root));
    let digests = report.authenticated_imports().unwrap();
    assert_eq!(digests.len(), 1);
    assert_eq!(digests.get(&ImportId::new(0)), Some(&dep.stable_digest()));
    assert_eq!(
        report
            .authenticated()
            .unwrap()
            .authenticated_backed_by()
            .collect::<Vec<_>>(),
        vec![FuncId::new(0)]
    );
    // The same module is still refused without a resolver.
    assert!(unauthenticated_at(
        &validate_module_with_authority(&root, &RejectingModuleProofAuthority),
        "backed_by"
    ));
}

#[test]
fn a_local_contract_that_says_more_than_the_far_one_is_refused() {
    let dep = dependency("dep");
    let mut root = backed_importer("root", &dep);
    let summary = root.functions[0].summary.take().unwrap();
    root.functions[0].summary = Some(summary.ensuring(ProofFormula::smtlib2("(= 2 2)", "Bool")));
    let set = ModuleSet::new([&dep]);
    let errors = validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(
        detail_contains(&errors, "backed_by", "`ensures` differ"),
        "{errors:?}"
    );
}

#[test]
fn a_far_summary_that_is_not_proved_backs_nothing() {
    let mut dep = dependency("dep");
    dep.functions[0].summary = Some(contract());
    let root = backed_importer("root", &dep);
    let set = ModuleSet::new([&dep]);
    let errors = validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(
        detail_contains(&errors, "backed_by", "not `proved`"),
        "{errors:?}"
    );
}

/// A dependency whose Postcondition is `Discharged` on the strength of an
/// opaque SMT certificate: valid only under an authority that replays it.
fn capability_discharged_dependency() -> (Module, ProofCertificateRef) {
    let mut dep = dependency("dep");
    dep.proof_obligations[0].status = ProofStatus::Discharged;
    dep.proof_certificates[0] = ProofCertificate {
        obligation: ProofId::new(0),
        prover: "ay-bvblast".to_string(),
        evidence: ProofEvidence::SmtProof(b"(unsat)".to_vec()),
        assurance: None,
    };
    let reference = dep.proof_certificates[0].lineage_ref();
    (dep, reference)
}

#[test]
fn the_dependency_is_validated_under_the_supplied_authority() {
    let (dep, reference) = capability_discharged_dependency();
    let root = backed_importer("root", &dep);
    let set = ModuleSet::new([&dep]);

    let errors = validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(
        has(&errors, |e| matches!(
            e,
            ValidationError::ImportedModuleInvalid { import: 0, first, .. }
                if first.contains("Discharged but no exact certificate")
        )),
        "a rejecting authority cannot ground the far Discharged row: {errors:?}"
    );

    // An authority that replays the far certificate makes the DEPENDENCY
    // valid — but a capability-replayed `Discharged` row is not GROUNDED
    // there, so it cannot back a cross-crate `proved` (WS1.3): across an edge
    // only kernel-tier replays and authenticated inheritances count.
    let report = validate_linked_module(&root, &set, &AdmitExact(reference));
    let errors = report.errors();
    assert!(
        !has(errors, |e| matches!(
            e,
            ValidationError::ImportedModuleInvalid { .. }
        )),
        "the replaying authority validates the dependency: {errors:?}"
    );
    assert!(
        detail_contains(
            errors,
            "backed_by",
            "far obligation #0 backs `proved` but is not grounded in the dependency \
             (kernel-tier replay or authenticated inheritance)"
        ),
        "a capability-Discharged far row backs nothing across the edge: {errors:?}"
    );
}

#[test]
fn a_tampered_candidate_is_a_digest_mismatch_at_the_edge() {
    let dep = dependency("dep");
    let root = backed_importer("root", &dep);
    let mut tampered = dep.clone();
    tampered.functions[0].summary = Some(contract().proved().ensuring(clause()));
    // Resolved by NAME so the edge check, not the lookup, does the refusing.
    let resolver = |import: &ModuleImport| (import.name == "dep").then_some(&tampered);
    let errors =
        validate_linked_module(&root, &resolver, &RejectingModuleProofAuthority).into_errors();
    assert!(
        detail_contains(&errors, "import", "stable digest"),
        "a rebuilt dependency with the same name is a different module: {errors:?}"
    );
}

#[test]
fn renamed_symbol_renumbered_obligation_and_wrong_scope_are_refused_at_the_reference() {
    let dep = dependency("dep");

    let (mut root, id) = importer("root", &dep, contract());
    root.functions[0].name = "f_v2".into();
    root.functions[0].summary = Some(
        contract()
            .proved()
            .backed_by(ExternRef::new(id, "f_v2").relying_on(ProofId::new(0))),
    );
    let set = ModuleSet::new([&dep]);
    let errors = validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(
        detail_contains(&errors, "backed_by", "symbol \"f_v2\""),
        "{errors:?}"
    );

    let (mut root, id) = importer("root", &dep, contract());
    root.functions[0].summary = Some(contract().proved().backed_by(far(id, 7)));
    let errors = validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(
        detail_contains(&errors, "backed_by", "obligation #7"),
        "{errors:?}"
    );

    // An obligation scoped to ANOTHER far function: add `g` to the dependency
    // with its own certified Postcondition, and cite it from `f`.
    let mut dep2 = dependency("dep2");
    let ft = dep2.functions[0].ty;
    let mut g = Function::declaration(FuncId::new(1), "g", ft, contract());
    g.producer = Some(Producer::TRust);
    dep2.try_add_function(g)
        .expect("Module::try_add_function: test fixture");
    let (obligation, certificate) = certified_postcondition(1, FuncId::new(1));
    dep2.proof_obligations.push(obligation);
    dep2.proof_certificates.push(certificate);
    assert!(
        validate_module(&dep2).is_empty(),
        "{:?}",
        validate_module(&dep2)
    );
    let (mut root, id) = importer("root", &dep2, contract());
    root.functions[0].summary = Some(contract().proved().backed_by(far(id, 1)));
    let set2 = ModuleSet::new([&dep2]);
    let errors = validate_linked_module(&root, &set2, &RejectingModuleProofAuthority).into_errors();
    assert!(
        detail_contains(&errors, "backed_by", "scoped to function #1"),
        "{errors:?}"
    );
}

#[test]
fn a_certified_far_obligation_without_a_certificate_invalidates_the_dependency() {
    let mut dep = dependency("dep");
    dep.proof_certificates.clear();
    let root = backed_importer("root", &dep);
    let set = ModuleSet::new([&dep]);
    let errors = validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(
        has(&errors, |e| matches!(
            e,
            ValidationError::ImportedModuleInvalid { import: 0, errors, .. } if *errors >= 1
        )),
        "Certified without a certificate is not a proof: {errors:?}"
    );
}

#[test]
fn an_inadmissible_kind_is_refused_for_the_citing_site() {
    let mut dep = dependency("dep");
    // A MemorySafety row cannot back a contract, even when discharged.
    dep.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(1),
            ObligationKind::MemorySafety,
            ProofStatus::Discharged,
            "ms",
        )
        .with_function(dep.functions[0].id),
    );
    dep.proof_certificates.push(ProofCertificate {
        obligation: ProofId::new(1),
        prover: "ay".into(),
        evidence: ProofEvidence::SmtProof(b"(unsat)".to_vec()),
        assurance: None,
    });
    let admit = AdmitExact(dep.proof_certificates[1].lineage_ref());
    let (mut root, id) = importer("root", &dep, contract());
    root.functions[0].summary = Some(contract().proved().backed_by(far(id, 1)));
    let set = ModuleSet::new([&dep]);
    let errors = validate_linked_module(&root, &set, &admit).into_errors();
    assert!(
        detail_contains(&errors, "backed_by", "memory_safety"),
        "{errors:?}"
    );
}

// ---------------------------------------------------------------------------
// InheritedFromCallee { external: Some }
// ---------------------------------------------------------------------------

#[test]
fn a_cross_crate_inheritance_grounds_its_restatement_only_when_linked() {
    let dep = dependency("dep");
    let root = inheriting_importer("root", &dep);
    let set = ModuleSet::new([&dep]);
    let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    assert!(report.is_ok(), "{:?}", report.errors());
    assert_eq!(
        report.authenticated_certificate_refs().unwrap(),
        &BTreeSet::from([root.proof_certificates[0].lineage_ref()])
    );
    // Inherited authority is `Discharged`-tier, never kernel-tier.
    assert!(report.replayed_certificate_refs().unwrap().is_empty());

    // Alone, the root's Discharged row has nothing behind it.
    let errors = validate_module(&root);
    assert!(
        has(&errors, |e| matches!(
            e,
            ValidationError::DischargedWithoutCertificate { obligation: 0 }
        )),
        "{errors:?}"
    );
    assert!(unauthenticated_at(
        &validate_module_with_authority(&root, &RejectingModuleProofAuthority),
        "inherited"
    ));
}

#[test]
fn a_certificate_must_discharge_the_obligation_its_evidence_restates() {
    let dep = dependency("dep");
    let mut root = inheriting_importer("root", &dep);
    let f = root.functions[0].id;
    root.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(1),
            ObligationKind::Postcondition,
            ProofStatus::Discharged,
            "a different claim",
        )
        .with_function(f)
        .with_formula(ProofFormula::smtlib2("(= 2 2)", "Bool")),
    );
    // Discharges #1 while the evidence restates #0.
    root.proof_certificates[0].obligation = ProofId::new(1);
    let set = ModuleSet::new([&dep]);
    let errors = validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(
        has(&errors, |e| matches!(
            e,
            ValidationError::ExternInheritanceRestatementMismatch {
                certificate_obligation: 1,
                evidence_obligation: 0
            }
        )),
        "{errors:?}"
    );
}

#[test]
fn a_restatement_with_a_different_kind_or_no_formula_is_refused() {
    let dep = dependency("dep");
    let set = ModuleSet::new([&dep]);

    let mut root = inheriting_importer("root", &dep);
    root.proof_obligations[0].kind = ObligationKind::Precondition;
    let errors = validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(
        detail_contains(&errors, "inherited", "has kind precondition"),
        "{errors:?}"
    );

    let mut root = inheriting_importer("root", &dep);
    root.proof_obligations[0].formula = None;
    let errors = validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(
        detail_contains(&errors, "inherited", "carries no formula"),
        "{errors:?}"
    );

    let mut root = inheriting_importer("root", &dep);
    root.proof_obligations[0].function = None;
    let errors = validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(
        detail_contains(&errors, "inherited", "scoped to None"),
        "{errors:?}"
    );
}

#[test]
fn a_far_row_that_is_only_capability_discharged_cannot_be_inherited() {
    let (dep, reference) = capability_discharged_dependency();
    let root = inheriting_importer("root", &dep);
    let set = ModuleSet::new([&dep]);
    let errors = validate_linked_module(&root, &set, &AdmitExact(reference)).into_errors();
    assert!(
        detail_contains(&errors, "inherited", "not grounded"),
        "a capability-replayed Discharged row is not kernel-tier ground: {errors:?}"
    );
}

#[test]
fn a_far_row_grounded_only_by_an_unauthenticated_inheritance_cannot_be_inherited() {
    let leaf = dependency("leaf");
    // `mid` inherits from `leaf`; nobody supplies `leaf`.
    let mid = inheriting_importer("mid", &leaf);
    let root = inheriting_importer("root", &mid);
    let set = ModuleSet::new([&mid]);
    let errors = validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(
        has(&errors, |e| matches!(
            e,
            ValidationError::ImportedModuleInvalid { import: 0, first, .. }
                if first.contains("no module was supplied")
        )),
        "{errors:?}"
    );
}

// ---------------------------------------------------------------------------
// closure walk: chains, cycles, diamonds, depth
// ---------------------------------------------------------------------------

#[test]
fn a_chain_re_earns_through_authenticated_inheritances_and_a_tampered_leaf_breaks_it() {
    let c = dependency("C");
    let b = inheriting_importer("B", &c);
    let a = inheriting_importer("A", &b);
    let set = ModuleSet::new([&b, &c]);
    let report = validate_linked_module(&a, &set, &RejectingModuleProofAuthority);
    assert!(report.is_ok(), "{:?}", report.errors());

    let mut c_tampered = c.clone();
    c_tampered.proof_obligations[0].description = "rebuilt".into();
    let resolver = |import: &ModuleImport| match import.name.as_str() {
        "B" => Some(&b),
        "C" => Some(&c_tampered),
        _ => None,
    };
    let errors =
        validate_linked_module(&a, &resolver, &RejectingModuleProofAuthority).into_errors();
    assert!(
        has(&errors, |e| matches!(
            e,
            ValidationError::ImportedModuleInvalid { import: 0, first, .. }
                if first.contains("stable digest")
        )),
        "C tampered surfaces on A's import of B: {errors:?}"
    );
}

#[test]
fn a_resolver_that_returns_the_importer_is_a_cycle_not_a_mismatch() {
    let c = dependency("C");
    let b = inheriting_importer("B", &c);
    let a = inheriting_importer("A", &b);

    // Direct: A's own import resolves to A.
    let resolver = |_: &ModuleImport| Some(&a);
    let errors =
        validate_linked_module(&a, &resolver, &RejectingModuleProofAuthority).into_errors();
    assert!(
        has(&errors, |e| matches!(
            e,
            ValidationError::ImportCycle { import: 0, path } if *path == vec!["A".to_string(), "A".to_string()]
        )),
        "{errors:?}"
    );

    // Nested: B's import of C resolves to A, which is on the walk.
    let resolver = |import: &ModuleImport| match import.name.as_str() {
        "B" => Some(&b),
        "C" => Some(&a),
        _ => None,
    };
    let errors =
        validate_linked_module(&a, &resolver, &RejectingModuleProofAuthority).into_errors();
    assert!(
        has(&errors, |e| matches!(
            e,
            ValidationError::ImportedModuleInvalid { import: 0, first, .. }
                if first.contains("cyclic import closure A -> B -> A")
        )),
        "{errors:?}"
    );
}

#[test]
fn a_diamond_resolves_and_validates_its_shared_leaf_once() {
    let d = dependency("D");
    let b = inheriting_importer("B", &d);
    let c = inheriting_importer("C", &d);
    // A restates B's #0 as its #0 and C's #0 as its #1.
    let mut a = Module::new("A");
    a.target_info = Some(target());
    let b_id = a
        .intern_import(ModuleImport::new("B", b.stable_digest()).with_producer(Producer::TRust))
        .expect("Module::intern_import: test fixture");
    let c_id = a
        .intern_import(ModuleImport::new("C", c.stable_digest()).with_producer(Producer::TRust))
        .expect("Module::intern_import: test fixture");
    let ft = a
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::declaration(FuncId::new(0), "f", ft, contract());
    f.producer = Some(Producer::TRust);
    a.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    for (local, id) in [(0, b_id), (1, c_id)] {
        a.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(local),
                ObligationKind::Postcondition,
                ProofStatus::Discharged,
                "inherited",
            )
            .with_function(FuncId::new(0))
            .with_formula(clause()),
        );
        a.proof_certificates
            .push(inheritance_certificate(local, FuncId::new(0), far(id, 0)));
    }

    let set = ModuleSet::new([&b, &c, &d]);
    let d_resolutions = Cell::new(0usize);
    let resolver = |import: &ModuleImport| {
        if import.name == "D" {
            d_resolutions.set(d_resolutions.get() + 1);
        }
        trust_ir_build::ImportResolver::resolve(&set, import)
    };
    let report = validate_linked_module(&a, &resolver, &RejectingModuleProofAuthority);
    assert!(report.is_ok(), "{:?}", report.errors());
    assert_eq!(
        d_resolutions.get(),
        1,
        "the shared leaf is resolved (and validated) once, memoized by digest"
    );
    assert_eq!(report.authenticated_imports().unwrap().len(), 2);
}

#[test]
fn an_import_chain_deeper_than_the_cap_is_refused() {
    // MAX_IMPORT_DEPTH + 2 modules: the root at depth 0, the leaf at depth
    // MAX_IMPORT_DEPTH + 1, one past the cap. Every link is a genuine
    // authenticated inheritance, so the ONLY refusal is the depth.
    let mut chain: Vec<Module> = vec![dependency("m0")];
    for index in 1..=(trust_ir_build::MAX_IMPORT_DEPTH + 1) {
        let previous = chain.last().unwrap();
        let next = inheriting_importer(&format!("m{index}"), previous);
        chain.push(next);
    }
    let root = chain.last().unwrap();
    let set = ModuleSet::new(chain.iter());
    let errors = validate_linked_module(root, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(
        has(&errors, |e| matches!(
            e,
            ValidationError::ImportedModuleInvalid { import: 0, first, .. }
                if first.contains("import closure depth")
        )),
        "{errors:?}"
    );

    // One module shorter, the whole chain re-earns.
    let root = &chain[chain.len() - 2];
    let report = validate_linked_module(root, &set, &RejectingModuleProofAuthority);
    assert!(report.is_ok(), "{:?}", report.errors());
}

#[test]
fn the_linked_authority_admits_only_the_exact_authenticated_certificate() {
    let dep = dependency("dep");
    let mut root = inheriting_importer("root", &dep);
    // Same obligation, same prover, different evidence bytes: a different
    // lineage reference, and NOT admitted.
    root.proof_certificates.push(ProofCertificate {
        obligation: ProofId::new(0),
        prover: "compose".to_string(),
        evidence: ProofEvidence::Trusted("faith".to_string()),
        assurance: None,
    });
    let set = ModuleSet::new([&dep]);
    let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    assert!(report.is_ok(), "{:?}", report.errors());
    let admitted = report.authenticated_certificate_refs().unwrap();
    assert!(admitted.contains(&root.proof_certificates[0].lineage_ref()));
    assert!(!admitted.contains(&root.proof_certificates[1].lineage_ref()));
    assert_eq!(admitted.len(), 1);
}

#[test]
fn module_set_is_keyed_by_digest_never_by_name() {
    let dep = dependency("dep");
    let mut same_name = dep.clone();
    same_name.proof_obligations[0].description = "rebuilt".into();
    let mut set = ModuleSet::new([&same_name]);
    assert_eq!(set.len(), 1);
    assert!(set.get(&dep.stable_digest()).is_none());
    assert_eq!(set.insert(&dep), dep.stable_digest());
    assert_eq!(set.len(), 2);
    assert!(std::ptr::eq(set.get(&dep.stable_digest()).unwrap(), &dep));
}

// ---------------------------------------------------------------------------
// wire
// ---------------------------------------------------------------------------

#[test]
fn the_identity_domains_are_pinned_current_v3_and_legacy_v2() {
    // Every fact the linked validator reads is on the v41 wire except the
    // row's identity scheme (v44, WS4.10). New rows are compared under the
    // portable v3 domain; a pre-v44 row decodes as V2 and is compared under
    // the legacy domain the goldens' recorded imports were minted under.
    assert_eq!(trust_ir::MODULE_IDENTITY_DOMAIN, "trust_ir.module.v3");
    assert_eq!(trust_ir::MODULE_IDENTITY_DOMAIN_V2, "trust_ir.module.v2");
    assert_eq!(
        trust_ir::IdentityScheme::default(),
        trust_ir::IdentityScheme::V2
    );
}

/// `ModuleSet::decode_into` loads through the canonical reader, so a
/// truncated or tampered artifact refuses at load rather than producing a
/// module whose digest can never match. Gated on this crate's `binary`
/// feature exactly as the function is.
#[cfg(feature = "binary")]
#[test]
fn decode_into_loads_through_the_canonical_reader() {
    let dep = dependency("dep");
    let bytes = trust_ir::binary::serialize_module(&dep).expect("serialize_module: test fixture");
    let mut store = Vec::new();
    let digest = ModuleSet::decode_into(&mut store, &bytes).expect("canonical bytes decode");
    assert_eq!(digest, dep.stable_digest());
    assert!(ModuleSet::decode_into(&mut store, &bytes[..bytes.len() - 1]).is_err());
    let set = ModuleSet::new(store.iter());
    let root = backed_importer("root", &dep);
    assert!(validate_linked_module(&root, &set, &RejectingModuleProofAuthority).is_ok());
}

// ---------------------------------------------------------------------------
// a body-less declaration proves nothing locally
// ---------------------------------------------------------------------------

fn decl_summary_refused(errors: &[ValidationError], function: u32) -> bool {
    has(errors, |e| {
        matches!(
            e,
            ValidationError::InvalidFunctionSummary { function: f, detail }
                if *f == function && detail.contains("body-less declaration")
        )
    })
}

#[test]
fn an_inherited_obligation_cannot_earn_proved_for_a_locally_stated_contract() {
    // The declaration states a clause the dependency never proved, marks the
    // summary `proved` with its backing NOT RECORDED, and lets the inherited
    // `(= 1 1)` restatement — the only Postcondition scoped to it — satisfy
    // the counting rule. Measured before the fix: `report.is_ok()`, while the
    // same `(= (result 0) 42)` through `backed_by` was refused ("local
    // `ensures` differ from the far summary's").
    let dep = dependency("dep");
    let mut root = inheriting_importer("root", &dep);
    root.functions[0].summary = Some(
        FunctionSummary::new()
            .with_params(vec!["x".to_string()])
            .ensuring(ProofFormula::smtlib2("(= (result 0) 42)", "Bool"))
            .proved(),
    );
    // Refused at the structural tier already: a declaration has no local
    // obligations to count.
    assert!(
        decl_summary_refused(&validate_module(&root), 0),
        "{:?}",
        validate_module(&root)
    );
    let set = ModuleSet::new([&dep]);
    let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    assert!(
        decl_summary_refused(report.errors(), 0),
        "{:?}",
        report.errors()
    );
    assert!(report.validated_root().is_none());
    // The exact restatement is still fine and still authenticates.
    root.functions[0].summary = Some(contract());
    let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    assert!(report.is_ok(), "{:?}", report.errors());
}

#[test]
fn a_dependency_that_only_declares_the_symbol_backs_nothing() {
    // `resolve_extern_ref` binds the local site to a body (R2) but not the far
    // one, so a dependency that merely DECLARES `f` — body-less, External —
    // with a `proved` contract and a kernel-certified `(= 1 1)` scoped to it
    // authenticated an importer's `backed_by`; the symbol's definition lived
    // in an unverified object outside both modules. Measured before the fix:
    // `validate_module(&dep_decl) == []` and the linked report was ok.
    let mut dep = Module::new("dep_decl");
    dep.target_info = Some(target());
    let ft = dep
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::declaration(FuncId::new(0), "f", ft, contract().proved());
    f.producer = Some(Producer::TRust);
    dep.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    let (obligation, certificate) = certified_postcondition(0, FuncId::new(0));
    dep.proof_obligations.push(obligation);
    dep.proof_certificates.push(certificate);
    // The declaration-only module is refused on its own ...
    assert!(
        decl_summary_refused(&validate_module(&dep), 0),
        "{:?}",
        validate_module(&dep)
    );
    // ... and therefore as a dependency.
    let root = backed_importer("root", &dep);
    let set = ModuleSet::new([&dep]);
    let errors = validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(
        has(&errors, |e| matches!(
            e,
            ValidationError::ImportedModuleInvalid { import: 0, first, .. }
                if first.contains("body-less declaration")
        )),
        "{errors:?}"
    );
    // A far declaration whose own `proved` is cross-crate backed, and whose
    // obligation is an authenticated inheritance, is the legitimate chain
    // shape, and it still re-earns.
    let leaf = dependency("leaf");
    let mut mid = inheriting_importer("mid", &leaf);
    mid.functions[0].summary = Some(contract().proved().backed_by(far(ImportId::new(0), 0)));
    let root = backed_importer("root", &mid);
    let set = ModuleSet::new([&mid, &leaf]);
    let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    assert!(report.is_ok(), "{:?}", report.errors());
}

// ---------------------------------------------------------------------------
// the INHERITED path cannot launder a `proved` summary's clauses
// ---------------------------------------------------------------------------

/// The exact laundering shape the `backed_by` path is closed against, tried on
/// the INHERITED path instead: a body-less declaration `f` whose `proved`
/// summary states a clause the dependency never proved, whose only backing is
/// an AUTHENTICATED cross-crate inheritance restating the dependency's real
/// obligation, and with NO `backed_by` at all.
///
/// The inheritance itself is legitimate — it restates `(= 1 1)` with the same
/// kind, cites a grounded far row, and is admitted into the `Discharged` tier.
/// What must still be refused is the `proved` bit: the local summary says
/// `ensures (= 2 2)`, which nothing anywhere established, and the `Discharged`
/// restatement scoped to a DECLARATION must not be counted as its backing.
///
/// Pre-8121569 this was admitted: the counting rule counted Discharged /
/// Certified contract rows scoped to a declaration, so the inherited row
/// earned `proved` for whatever clause text the declaration cared to spell —
/// and `backed_by`'s exact-restatement rule never ran, because there was no
/// `backed_by`. Flipping `counts_locally` back to `true` in
/// `validate.rs` makes this test's first assertion fail with `Ok`.
fn laundering_inheriting_importer(name: &str, dep: &Module) -> Module {
    let mut root = inheriting_importer(name, dep);
    // The lie: `proved` with a clause the dependency never stated, and NO
    // `backed_by` to be measured against the far contract.
    root.functions[0].summary = Some(
        FunctionSummary::new()
            .with_params(vec!["x".to_string()])
            .ensuring(ProofFormula::smtlib2("(= 2 2)", "Bool"))
            .proved(),
    );
    assert!(root.functions[0].is_declaration());
    assert!(
        root.functions[0]
            .summary
            .as_ref()
            .unwrap()
            .backed_by
            .is_none()
    );
    root
}

#[test]
fn an_authenticated_inheritance_does_not_back_a_declarations_proved_clauses() {
    let dep = dependency("dep");
    let root = laundering_inheriting_importer("root", &dep);
    let set = ModuleSet::new([&dep]);
    let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    let errors = report.errors().to_vec();
    assert!(
        !errors.is_empty(),
        "a `proved` declaration whose only backing is an inherited row must be refused"
    );
    assert!(
        has(&errors, |e| matches!(
            e,
            ValidationError::InvalidFunctionSummary { detail, .. }
                if detail.contains("claims `proved`")
                    && detail.contains("body-less declaration has no body")
        )),
        "the refusal must name the declaration rule, not something incidental: {errors:?}"
    );

    // The inheritance itself is sound and stays authenticated — the refusal is
    // about the summary's `proved` bit, not about the cross-crate edge.
    let plain = inheriting_importer("root", &dep);
    let ok = validate_linked_module(&plain, &set, &RejectingModuleProofAuthority);
    assert!(ok.is_ok(), "{:?}", ok.errors());
    assert_eq!(
        ok.authenticated_certificate_refs().unwrap(),
        &BTreeSet::from([plain.proof_certificates[0].lineage_ref()])
    );

    // And the same lie is refused by the single-module validator too, so the
    // rule is not something only the closure walk knows.
    assert!(has(&validate_module(&root), |e| matches!(
        e,
        ValidationError::InvalidFunctionSummary { detail, .. }
            if detail.contains("claims `proved`")
                && detail.contains("body-less declaration has no body")
    )));
}

#[test]
fn an_inherited_restatement_cannot_stand_in_for_an_exact_backed_by() {
    // The other half: WITH a `backed_by`, the inherited row does not excuse
    // the exact-restatement rule either. The local summary keeps the far
    // clause count but states a different clause, and cites the far #0.
    let dep = dependency("dep");
    let set = ModuleSet::new([&dep]);
    let mut root = inheriting_importer("root", &dep);
    let id = ImportId::new(0);
    root.functions[0].summary = Some(
        FunctionSummary::new()
            .with_params(vec!["x".to_string()])
            .ensuring(ProofFormula::smtlib2("(= 2 2)", "Bool"))
            .proved()
            .backed_by(far(id, 0)),
    );
    let errors = validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(
        detail_contains(
            &errors,
            "backed_by",
            "local `ensures` differ from the far summary's"
        ),
        "{errors:?}"
    );
}

// ---------------------------------------------------------------------------
// L9 — CROSS-CRATE COVERAGE MONOTONICITY
// ---------------------------------------------------------------------------
//
// The half the residual ledger named as deliberately left open beside the
// bundle re-derivation rule: "the `validate_linked_module` rule refusing an
// IMPORT whose cited discharge is Unrecorded/bounded where the importer's
// claim needs unbounded is a different table and a separate rule."
//
// Demand per site kind:
//   * `backed_by` — `CoverageBound::Unbounded`. `FunctionSummary::proved` is a
//     bare bool whose own rustdoc says a caller may ASSUME the `ensures`, with
//     no restriction on inputs, so a re-stated `proved` claims all of them.
//   * `inherited` — exactly the certificate's own `assurance`, or `Unrecorded`
//     when it records none (a row that claims no grade demands none).
//
// Supply: every bound the DEPENDENCY's certificates record for the cited far
// obligation, and EVERY one of them must supply the demand (weakest link) —
// otherwise a producer licenses a stronger claim by ADDING a decorative
// certificate nothing replays. Two states are counted rather than refused,
// both by `coverage_unrecorded()`: no far record at all (the pre-v41
// grandfather state) and a local row that records no grade, so nothing was
// compared. Neither is read as agreement, and the counter spans the whole
// CLOSURE — a dependency's unrecorded site is not an error and so has no
// other route to the root's report.
//
// `CoverageAssurance::request_digest` is deliberately arbitrary in these
// fixtures: re-deriving it against a `NativeVerificationBundle` is
// `coverage_assurance_report`'s rule over a different table
// (`tests/coverage_assurance.rs`). L9 is about the BOUND.

fn assurance(bound: CoverageBound) -> CoverageAssurance {
    CoverageAssurance {
        bound,
        request_digest: ProofDigest {
            algorithm: ProofDigestAlgorithm::Sha256,
            bytes: [7u8; 32],
        },
    }
}

/// `dependency(name)` with `bound` recorded on the certificate discharging its
/// obligation #0 — the far supply L9 reads.
fn dependency_recording(name: &str, bound: CoverageBound) -> Module {
    let mut dep = dependency(name);
    dep.proof_certificates[0].assurance = Some(assurance(bound));
    // Still a valid module on its own: `validate_module` re-derives nothing
    // without a bundle, so recording a bound is never a local error.
    assert!(
        validate_module(&dep).is_empty(),
        "{:?}",
        validate_module(&dep)
    );
    dep
}

/// `dependency_recording` plus a SECOND certificate for the SAME obligation
/// #0 from a different prover, recording `sibling`.
///
/// Legal, and the point: certificate uniqueness is only over
/// `(obligation, prover)`, and `Certified` is satisfied by the ONE matching
/// `CleanCic` row, so this extra row is never consulted as proof authority —
/// it is not replayed, it never enters `ground`, and `check_inherited` would
/// refuse it outright. Its coverage claim must not be currency either.
fn dependency_with_sibling_grade(
    name: &str,
    grounding: CoverageBound,
    sibling: CoverageBound,
) -> Module {
    let mut dep = dependency_recording(name, grounding);
    dep.proof_certificates.push(ProofCertificate {
        obligation: ProofId::new(0),
        prover: "ay".to_string(),
        evidence: ProofEvidence::SmtProof(vec![0xB1, 0xA5]),
        assurance: Some(assurance(sibling)),
    });
    assert!(
        validate_module(&dep).is_empty(),
        "a sibling certificate is still a valid module: {:?}",
        validate_module(&dep)
    );
    dep
}

/// A MIDDLE module for a two-edge closure: an importer of `leaf` (so it has a
/// cross-crate site of its OWN) that also carries a kernel-certified #0 for a
/// root to cite, with `grade` recorded on it.
///
/// Body-LESS, like every importer here: a cross-crate claim must be cited from
/// a declaration of the callee, and a declaration whose summary is `backed_by`
/// is the backed far site a transitive chain is allowed to pass through.
fn middle_recording(name: &str, leaf: &Module, grade: CoverageBound) -> Module {
    let mut mid = backed_importer(name, leaf);
    let f = mid.functions[0].id;
    let (obligation, mut certificate) = certified_postcondition(0, f);
    certificate.assurance = Some(assurance(grade));
    mid.proof_obligations.push(obligation);
    mid.proof_certificates.push(certificate);
    assert!(
        validate_module(&mid).is_empty(),
        "the middle fixture must validate on its own: {:?}",
        validate_module(&mid)
    );
    mid
}

fn below_claim(errors: &[ValidationError], at: &str) -> bool {
    has(errors, |e| {
        matches!(
            e,
            ValidationError::ImportCoverageBelowClaim { site, .. } if *site == at
        )
    })
}

fn backed_by_errors(dep: &Module) -> Vec<ValidationError> {
    let set = ModuleSet::new([dep]);
    let root = backed_importer("root", dep);
    validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors()
}

/// An inheriting importer whose certificate CLAIMS `bound`.
fn inheriting_claiming(name: &str, dep: &Module, bound: CoverageBound) -> Module {
    let mut root = inheriting_importer(name, dep);
    root.proof_certificates[0].assurance = Some(assurance(bound));
    root
}

fn inherited_errors(dep: &Module, claim: CoverageBound) -> Vec<ValidationError> {
    let set = ModuleSet::new([dep]);
    let root = inheriting_claiming("root", dep, claim);
    let admitted = root.proof_certificates[0].lineage_ref();
    validate_linked_module(&root, &set, &AdmitExact(admitted)).into_errors()
}

#[test]
fn coverage_supports_is_the_ratified_partial_order_over_every_pair() {
    use CoverageBound::{ModelBounded, Unbounded, Unrecorded, UnwindBounded};
    let unwind = UnwindBounded { depth: 7 };
    let model = ModelBounded { size: 7 };

    // `Unbounded` supplies every demand: it is the top of the order.
    for needs in [Unbounded, unwind, model, Unrecorded] {
        assert!(
            coverage_supports(Unbounded, needs),
            "Unbounded -> {needs:?}"
        );
    }

    // A demand of `Unrecorded` states no grade, so nothing under-supports it.
    for far in [Unbounded, unwind, model, Unrecorded] {
        assert!(coverage_supports(far, Unrecorded), "{far:?} -> Unrecorded");
    }

    // Neither bounded rung supplies an unqualified claim — the ledger's case.
    assert!(!coverage_supports(unwind, Unbounded));
    assert!(!coverage_supports(model, Unbounded));

    // Same axis compares by magnitude, and 0 is still an affirmative grade.
    assert!(coverage_supports(
        UnwindBounded { depth: 9 },
        UnwindBounded { depth: 7 }
    ));
    assert!(coverage_supports(unwind, UnwindBounded { depth: 7 }));
    assert!(!coverage_supports(
        UnwindBounded { depth: 7 },
        UnwindBounded { depth: 9 }
    ));
    assert!(coverage_supports(
        ModelBounded { size: 9 },
        ModelBounded { size: 7 }
    ));
    assert!(!coverage_supports(
        ModelBounded { size: 7 },
        ModelBounded { size: 9 }
    ));
    assert!(coverage_supports(
        UnwindBounded { depth: 0 },
        UnwindBounded { depth: 0 }
    ));

    // The two bounded rungs are INCOMPARABLE at every magnitude: a loop
    // unwinding depth is not evidence about a finite model size, or back.
    assert!(!coverage_supports(
        UnwindBounded { depth: u64::MAX },
        ModelBounded { size: 1 }
    ));
    assert!(!coverage_supports(
        ModelBounded { size: u64::MAX },
        UnwindBounded { depth: 1 }
    ));

    // `Unrecorded` IS NOT A WILDCARD as a supply — not for `Unbounded`, and
    // not for the weakest positive grade either.
    assert!(!coverage_supports(Unrecorded, Unbounded));
    assert!(!coverage_supports(Unrecorded, UnwindBounded { depth: 0 }));
    assert!(!coverage_supports(Unrecorded, ModelBounded { size: 0 }));
    assert!(coverage_supports(Unrecorded, Unrecorded));
}

#[test]
fn an_unqualified_backed_by_needs_an_unbounded_far_discharge() {
    // POSITIVE: the far module says it proved the contract for all inputs.
    let dep = dependency_recording("dep", CoverageBound::Unbounded);
    let set = ModuleSet::new([&dep]);
    let root = backed_importer("root", &dep);
    let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    assert!(report.is_ok(), "{:?}", report.errors());
    assert_eq!(report.coverage_supported(), 1);
    assert_eq!(report.coverage_unrecorded(), 0);

    // NEGATIVES, one per far bound that cannot support an unqualified claim.
    for bound in [
        CoverageBound::UnwindBounded { depth: 1 },
        CoverageBound::UnwindBounded { depth: u64::MAX },
        CoverageBound::ModelBounded { size: 8 },
        CoverageBound::Unrecorded,
    ] {
        let dep = dependency_recording("dep", bound);
        let errors = backed_by_errors(&dep);
        assert!(
            below_claim(&errors, "backed_by"),
            "{bound:?} must not support an unqualified `proved`: {errors:?}"
        );
    }
}

#[test]
fn an_inheritance_may_not_claim_more_coverage_than_the_far_discharge_recorded() {
    // Same axis, far too shallow.
    let dep = dependency_recording("dep", CoverageBound::UnwindBounded { depth: 2 });
    let errors = inherited_errors(&dep, CoverageBound::UnwindBounded { depth: 7 });
    assert!(below_claim(&errors, "inherited"), "{errors:?}");

    // Same axis, far deep enough — the positive control for the pair above.
    let dep = dependency_recording("dep", CoverageBound::UnwindBounded { depth: 7 });
    let set = ModuleSet::new([&dep]);
    let root = inheriting_claiming("root", &dep, CoverageBound::UnwindBounded { depth: 7 });
    let admitted = root.proof_certificates[0].lineage_ref();
    let report = validate_linked_module(&root, &set, &AdmitExact(admitted));
    assert!(report.is_ok(), "{:?}", report.errors());
    assert_eq!(report.coverage_supported(), 1);

    // Same axis, model size too small.
    let dep = dependency_recording("dep", CoverageBound::ModelBounded { size: 4 });
    let errors = inherited_errors(&dep, CoverageBound::ModelBounded { size: 9 });
    assert!(below_claim(&errors, "inherited"), "{errors:?}");

    // CROSS-AXIS, both directions: a deep unwinding is not a large model and
    // a large model is not a deep unwinding.
    let dep = dependency_recording("dep", CoverageBound::UnwindBounded { depth: 9 });
    let errors = inherited_errors(&dep, CoverageBound::ModelBounded { size: 2 });
    assert!(below_claim(&errors, "inherited"), "{errors:?}");
    let dep = dependency_recording("dep", CoverageBound::ModelBounded { size: 9 });
    let errors = inherited_errors(&dep, CoverageBound::UnwindBounded { depth: 2 });
    assert!(below_claim(&errors, "inherited"), "{errors:?}");

    // A bounded far discharge cannot support an UNBOUNDED inheritance claim.
    let dep = dependency_recording("dep", CoverageBound::UnwindBounded { depth: 1 });
    let errors = inherited_errors(&dep, CoverageBound::Unbounded);
    assert!(below_claim(&errors, "inherited"), "{errors:?}");

    // `Unrecorded` recorded EXPLICITLY on the far side is not a wildcard.
    let dep = dependency_recording("dep", CoverageBound::Unrecorded);
    let errors = inherited_errors(&dep, CoverageBound::UnwindBounded { depth: 1 });
    assert!(below_claim(&errors, "inherited"), "{errors:?}");
}

#[test]
fn a_coverage_refusal_denies_the_site_it_names_rather_than_only_reporting_it() {
    // The refusal must also stop the inheritance from GROUNDING its
    // restatement: an error that leaves the claim admitted would be a report,
    // not a rule.
    let dep = dependency_recording("dep", CoverageBound::UnwindBounded { depth: 1 });
    let set = ModuleSet::new([&dep]);
    let root = inheriting_claiming("root", &dep, CoverageBound::Unbounded);
    let admitted = root.proof_certificates[0].lineage_ref();
    let report = validate_linked_module(&root, &set, &AdmitExact(admitted));
    assert!(below_claim(report.errors(), "inherited"));
    assert!(!report.is_ok());
    assert!(report.authenticated_certificate_refs().is_none());
    assert!(report.validated_root().is_none());
}

#[test]
fn an_unrecorded_far_discharge_is_counted_not_refused_and_never_read_as_agreement() {
    // The grandfather state: nothing in the fleet stamps `assurance` yet, so
    // the far certificate records no bound at all. Distinguished from an
    // explicit `CoverageBound::Unrecorded`, which IS refused above — the v41
    // `body_gate` precedent, where "no claim" and "affirmatively none" are
    // different wire states.
    let dep = dependency("dep");
    assert!(dep.proof_certificates[0].assurance.is_none());
    let set = ModuleSet::new([&dep]);
    let root = backed_importer("root", &dep);
    let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    assert!(report.is_ok(), "{:?}", report.errors());
    assert_eq!(report.coverage_supported(), 0);
    assert_eq!(report.coverage_unrecorded(), 1);
    // Absence is never rendered as agreement.
    assert!(report.coverage_summary().contains("UNRECORDED"));
    assert!(report.coverage_summary().contains("0 of 1"));
    // And the admission rule a fail-closed caller uses does NOT hold here.
    assert!(!(report.is_ok() && report.coverage_unrecorded() == 0));
}

#[test]
fn an_inheritance_that_claims_no_grade_is_counted_unrecorded_never_supported() {
    // `assurance: None` on the local certificate is NOT RECORDED, so the row
    // claims no coverage and demands none — which is why the site is not
    // REFUSED, and that half is sound: a fail-closed consumer already reads
    // that row as UNKNOWN, never as `Unbounded`.
    //
    // It is not SUPPORTED either. Nothing was compared, so nothing was
    // established, and `coverage_supports(_, Unrecorded)` is true for EVERY
    // far bound — so tallying this site as supported would relocate the forge
    // this rule closes, absence read as agreement, from the far row onto the
    // near one and into the tally. Measured before the fix: the documented
    // admission gate `is_ok() && coverage_unrecorded() == 0` PASSED for this
    // closure, whose one inherited claim rests on a depth-1 bounded far
    // discharge, and `coverage_summary()` printed it as "1 of 1 ... supported
    // by a recorded far bound".
    let dep = dependency_recording("dep", CoverageBound::UnwindBounded { depth: 1 });
    let set = ModuleSet::new([&dep]);
    let root = inheriting_importer("root", &dep);
    assert!(root.proof_certificates[0].assurance.is_none());
    let admitted = root.proof_certificates[0].lineage_ref();
    let report = validate_linked_module(&root, &set, &AdmitExact(admitted));
    assert!(report.is_ok(), "{:?}", report.errors());
    assert_eq!(report.coverage_supported(), 0);
    assert_eq!(report.coverage_unrecorded(), 1);
    assert_eq!(report.coverage_refused(), 0);
    assert!(!(report.is_ok() && report.coverage_unrecorded() == 0));

    // So omission buys SILENCE, never standing — and the honest spelling the
    // `inherited_needs` rustdoc recommends really is admitted: the same
    // closure with the field stamped at the bound the far side recorded is
    // supported, with nothing left unrecorded.
    let root = inheriting_claiming("root", &dep, CoverageBound::UnwindBounded { depth: 1 });
    let admitted = root.proof_certificates[0].lineage_ref();
    let report = validate_linked_module(&root, &set, &AdmitExact(admitted));
    assert!(report.is_ok(), "{:?}", report.errors());
    assert_eq!(report.coverage_supported(), 1);
    assert_eq!(report.coverage_unrecorded(), 0);
}

#[test]
fn an_inflated_sibling_certificate_cannot_license_what_the_grounding_discharge_never_covered() {
    // The laundering edge L9 exists to refuse, in its cheapest form. The
    // dependency's #0 is GROUNDED by a depth-1 kernel discharge; beside it
    // sits a second certificate, from a prover this walk replays nothing for,
    // stamped `Unbounded`. Under a supply quantifier of `any` the root's
    // unqualified `proved` re-earned unbounded standing from a depth-1 check
    // — the exact sentence the module docs say L9 prevents — and the root
    // passed even the strict gate (`is_ok() && coverage_unrecorded() == 0`).
    //
    // Note the asymmetry that made it a defect rather than a scoping choice:
    // the same walk refuses this row as PROOF authority (not replayed, so not
    // in `ground`; `check_inherited` rejects it by name), and then accepted
    // its coverage claim as the licence.
    let dep = dependency_with_sibling_grade(
        "dep",
        CoverageBound::UnwindBounded { depth: 1 },
        CoverageBound::Unbounded,
    );
    let set = ModuleSet::new([&dep]);
    let root = backed_importer("root", &dep);
    let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    assert!(
        below_claim(report.errors(), "backed_by"),
        "{:?}",
        report.errors()
    );
    assert!(!report.is_ok());
    assert_eq!(report.coverage_supported(), 0);
    assert_eq!(report.coverage_refused(), 1);
    // The refusal must also DENY the site, not merely report it.
    assert!(report.validated_root().is_none());

    // The diagnostic names BOTH recorded bounds, so a reader can see which
    // row is the weak link rather than only that something was short.
    let far_bounds = report
        .errors()
        .iter()
        .find_map(|e| match e {
            ValidationError::ImportCoverageBelowClaim { far, .. } => Some(far.clone()),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{:?}", report.errors()));
    assert!(
        far_bounds.iter().any(|b| b.contains("UnwindBounded")),
        "{far_bounds:?}"
    );
    assert!(
        far_bounds.iter().any(|b| b == "Unbounded"),
        "{far_bounds:?}"
    );

    // POSITIVE control: the rule is weakest-link, not one-certificate-only.
    // Two recorded rows that BOTH supply the demand still support it.
    let dep =
        dependency_with_sibling_grade("dep", CoverageBound::Unbounded, CoverageBound::Unbounded);
    let set = ModuleSet::new([&dep]);
    let root = backed_importer("root", &dep);
    let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    assert!(report.is_ok(), "{:?}", report.errors());
    assert_eq!(report.coverage_supported(), 1);
}

#[test]
fn the_coverage_tally_spans_the_whole_import_closure_not_only_the_root() {
    // R -> MID -> LEAF. The ROOT's own site is supported (MID records
    // `Unbounded` on the obligation R cites); MID's site is UNRECORDED (LEAF
    // records nothing at all).
    //
    // A dependency's unrecorded site is NOT an error, so unlike an
    // insufficiency it can never arrive folded into
    // `ImportedModuleInvalid` — which is the whole justification a root-only
    // counter rested on. Measured before the fix: `coverage_unrecorded()`
    // was 0 here, so a caller applying the documented admission rule admitted
    // R while R's unbounded standing chained through MID's unqualified
    // `proved`, whose own far coverage MID's dependency never recorded.
    let leaf = dependency("leaf");
    assert!(leaf.proof_certificates[0].assurance.is_none());
    let mid = middle_recording("mid", &leaf, CoverageBound::Unbounded);
    let root = backed_importer("root", &mid);
    let set = ModuleSet::new([&mid, &leaf]);
    let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    assert!(report.is_ok(), "{:?}", report.errors());
    assert_eq!(report.coverage_supported(), 1, "the root's own site");
    assert_eq!(
        report.coverage_unrecorded(),
        1,
        "MID's site, which only a closure-wide tally can see"
    );
    assert!(!(report.is_ok() && report.coverage_unrecorded() == 0));
    assert!(
        report.coverage_summary().contains("1 of 2"),
        "{}",
        report.coverage_summary()
    );
}

#[test]
fn the_coverage_summary_counts_a_refused_site_in_its_denominator() {
    // The rustdoc bills this as the one line a report or CLI can print.
    // Printed alone — the stated use — a total that omits refusals reads as
    // complete coverage for a module that carries one: before the fix a
    // single refused site rendered as "0 of 0 authenticated sites ... 0 left
    // UNRECORDED", with only `is_ok()` recording the refusal.
    let dep = dependency_recording("dep", CoverageBound::UnwindBounded { depth: 1 });
    let set = ModuleSet::new([&dep]);
    let root = backed_importer("root", &dep);
    let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    assert!(below_claim(report.errors(), "backed_by"));
    assert_eq!(report.coverage_refused(), 1);
    let line = report.coverage_summary();
    assert!(line.contains("0 of 1"), "{line}");
    assert!(line.contains("1 REFUSED"), "{line}");
}

#[test]
fn a_coverage_refusal_names_the_obligation_the_demand_and_the_far_bounds() {
    // A diagnostic that says only "coverage insufficient" cannot be acted on:
    // the reader needs which far obligation, what the local claim needed, and
    // what the dependency actually recorded.
    let dep = dependency_recording("dep", CoverageBound::UnwindBounded { depth: 3 });
    let errors = backed_by_errors(&dep);
    let named = errors
        .iter()
        .find_map(|e| match e {
            ValidationError::ImportCoverageBelowClaim {
                import,
                site,
                obligation,
                needs,
                far,
            } => Some((*import, *site, *obligation, needs.clone(), far.clone())),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{errors:?}"));
    assert_eq!(named.0, 0);
    assert_eq!(named.1, "backed_by");
    assert_eq!(named.2, 0);
    assert!(named.3.contains("Unbounded"), "{}", named.3);
    assert!(named.3.contains("ALL inputs"), "{}", named.3);
    assert_eq!(named.4, vec!["UnwindBounded { depth: 3 }".to_string()]);
    // The far list is never empty: an empty far record is the UNRECORDED
    // outcome, which is not a refusal.
    assert!(!named.4.is_empty());
    assert!(
        errors[0]
            .to_string()
            .contains("may not exceed the coverage")
    );
}

// ---------------------------------------------------------------------------
// WS8.14 (F-126): an interposable site cannot carry a cross-crate proof
// ---------------------------------------------------------------------------

#[test]
fn validate_linked_module_refuses_an_interposable_far_or_local_site() {
    // The far definition flipped to an interposable linkage: both proof-
    // bearing sites surface `InterposableFarSite { side: "far" }` through
    // `resolve_extern_ref`.
    for linkage in [Linkage::ExternalWeak, Linkage::Weak, Linkage::LinkOnce] {
        let mut dep = dependency("dep");
        dep.functions[0].linkage = linkage;
        let set = ModuleSet::new([&dep]);
        let needle = format!("far symbol `f` has interposable linkage {linkage:?}");

        let root = backed_importer("root", &dep);
        let errors =
            validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors();
        assert!(detail_contains(&errors, "backed_by", &needle), "{errors:?}");

        let root = inheriting_importer("root", &dep);
        let errors =
            validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors();
        assert!(detail_contains(&errors, "inherited", &needle), "{errors:?}");
    }

    // The far definition stays `External`; the importer's local declaration
    // is `ExternalWeak` and may bind to null: `side: "local"`.
    let dep = dependency("dep");
    let set = ModuleSet::new([&dep]);
    let needle = "local symbol `f` has interposable linkage ExternalWeak";
    let mut root = backed_importer("root", &dep);
    root.functions[0].linkage = Linkage::ExternalWeak;
    let errors = validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(detail_contains(&errors, "backed_by", needle), "{errors:?}");
    let mut root = inheriting_importer("root", &dep);
    root.functions[0].linkage = Linkage::ExternalWeak;
    let errors = validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(detail_contains(&errors, "inherited", needle), "{errors:?}");

    // Mutation control: the ODR spelling of the far definition still re-earns.
    let mut dep = dependency("dep");
    dep.functions[0].linkage = Linkage::WeakOdr;
    let set = ModuleSet::new([&dep]);
    let root = backed_importer("root", &dep);
    let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    assert!(report.is_ok(), "{:?}", report.errors());
}

fn imported_invalid_with(errors: &[ValidationError], needle: &str) -> bool {
    has(errors, |e| {
        matches!(
            e,
            ValidationError::ImportedModuleInvalid { import: 0, first, .. } if first.contains(needle)
        )
    })
}

#[test]
fn an_interposable_leaf_breaks_a_transitive_chain_at_the_edge_that_names_it() {
    // Review (adversarial): the root's own edge is clean — the MIDDLE's far
    // site is an `External` declaration that records a backing — and the
    // interposable definition sits one edge further down. The walk must not
    // stop at the root's edge: the middle's citation of the leaf is refused,
    // and that refusal surfaces on the root's import of the middle.
    for linkage in [Linkage::Weak, Linkage::LinkOnce, Linkage::ExternalWeak] {
        let needle = format!("far symbol `f` has interposable linkage {linkage:?}");

        // backed_by chain: root -> mid (backed declaration) -> leaf.
        let mut leaf = dependency("leaf");
        leaf.functions[0].linkage = linkage;
        let mid = middle_recording("mid", &leaf, CoverageBound::Unbounded);
        let root = backed_importer("root", &mid);
        let set = ModuleSet::new([&mid, &leaf]);
        let errors =
            validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors();
        assert!(imported_invalid_with(&errors, &needle), "{errors:?}");

        // Inheritance chain: A inherits from B, which inherits from C.
        let mut c = dependency("C");
        c.functions[0].linkage = linkage;
        let b = inheriting_importer("B", &c);
        let a = inheriting_importer("A", &b);
        let set = ModuleSet::new([&b, &c]);
        let errors = validate_linked_module(&a, &set, &RejectingModuleProofAuthority).into_errors();
        assert!(imported_invalid_with(&errors, &needle), "{errors:?}");
    }

    // Mutation control: the same chains with an `External` (and an ODR)
    // leaf re-earn, so the refusal above is the linkage and nothing else.
    for linkage in [Linkage::External, Linkage::LinkOnceOdr] {
        let mut leaf = dependency("leaf");
        leaf.functions[0].linkage = linkage;
        let mid = middle_recording("mid", &leaf, CoverageBound::Unbounded);
        let root = backed_importer("root", &mid);
        let set = ModuleSet::new([&mid, &leaf]);
        let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
        assert!(report.is_ok(), "{linkage:?}: {:?}", report.errors());

        let mut c = dependency("C");
        c.functions[0].linkage = linkage;
        let b = inheriting_importer("B", &c);
        let a = inheriting_importer("A", &b);
        let set = ModuleSet::new([&b, &c]);
        let report = validate_linked_module(&a, &set, &RejectingModuleProofAuthority);
        assert!(report.is_ok(), "{linkage:?}: {:?}", report.errors());
    }
}

#[test]
fn a_weak_middle_declaration_is_refused_on_both_of_its_edges() {
    // Review (adversarial): the MIDDLE's declaration of `f` is both the far
    // site of the root's edge and the local site of its own edge to the leaf.
    // Spelled `ExternalWeak` it may bind to null, so neither edge may carry
    // the proof.
    let leaf = dependency("leaf");
    let mut mid = middle_recording("mid", &leaf, CoverageBound::Unbounded);
    mid.functions[0].linkage = Linkage::ExternalWeak;

    // The middle's own edge: refused `local`.
    let set = ModuleSet::new([&leaf]);
    let errors = validate_linked_module(&mid, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(
        detail_contains(
            &errors,
            "backed_by",
            "local symbol `f` has interposable linkage ExternalWeak"
        ),
        "{errors:?}"
    );

    // The root's edge: the walk validates the middle first and fails closed
    // on it, so the root is refused with the middle's `local` refusal as the
    // named first cause.
    let root = backed_importer("root", &mid);
    let set = ModuleSet::new([&mid, &leaf]);
    let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    assert!(!report.is_ok());
    let errors = report.into_errors();
    assert!(
        imported_invalid_with(
            &errors,
            "local symbol `f` has interposable linkage ExternalWeak"
        ),
        "{errors:?}"
    );
}

// ---------------------------------------------------------------------------
// WS4.7 — import-table hygiene: the interning rule, type-enforced hash-once,
// and the ratified one-row-per-(artifact, producer) shape
// ---------------------------------------------------------------------------

const SCALE: &str = "dep_scale";
const ADDMUL: &str = "dep_addmul";

fn unary_contract() -> FunctionSummary {
    contract()
}

fn binary_contract() -> FunctionSummary {
    FunctionSummary::new()
        .with_params(vec!["a".to_string(), "b".to_string()])
        .ensuring(clause())
}

/// The MIXED dependency — the two-language design's normal crate: one module,
/// a TRust `dep_scale(x) = x * factor` and a Clean `dep_addmul(a, b) = a*b + a`,
/// each `proved` beside a kernel-CERTIFIED Postcondition (#0 and #1).
fn mixed_dependency(factor: u128) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("mixed_dep", target());
    let unary = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let binary = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let scale = {
        let mut fb = mb.function(SCALE, unary);
        fb.set_producer(Producer::TRust);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        let k = fb.uconst(Ty::U64, factor);
        let out = fb.mul(Ty::U64, x, k);
        fb.ret(vec![out]);
        fb.build()
    };
    let addmul = {
        let mut fb = mb.function(ADDMUL, binary);
        fb.set_producer(Producer::Clean);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::U64);
        let b = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        let ab = fb.mul(Ty::U64, a, b);
        let out = fb.add(Ty::U64, ab, a);
        fb.ret(vec![out]);
        fb.build()
    };
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    module.function_by_id_mut(scale).unwrap().summary = Some(unary_contract().proved());
    module.function_by_id_mut(addmul).unwrap().summary = Some(binary_contract().proved());
    for (id, function) in [(0, scale), (1, addmul)] {
        let (obligation, certificate) = certified_postcondition(id, function);
        module.proof_obligations.push(obligation);
        module.proof_certificates.push(certificate);
    }
    assert!(
        validate_module(&module).is_empty(),
        "the mixed dependency must validate on its own: {:?}",
        validate_module(&module)
    );
    module
}

#[derive(Debug, Clone, Copy)]
struct MixedIds {
    rust_row: ImportId,
    clean_row: ImportId,
    addmul: FuncId,
}

/// The importer of the mixed dependency: TWO interned rows — one per producer,
/// the SAME digest — a TRust declaration of `dep_scale` whose `proved` rests
/// on the far #0 through the Rust row, and a Clean declaration of `dep_addmul`
/// whose local Discharged #0 inherits the far #1 through the Clean row.
fn mixed_importer(dep: &Module) -> (Module, MixedIds) {
    let mut mb = ModuleBuilder::new_with_target_info("mixed_root", target());
    let unary = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let binary = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    mb.set_default_producer(Producer::TRust);
    let scale = mb.declare_function(SCALE, unary);
    mb.set_default_producer(Producer::Clean);
    let addmul = mb.declare_function(ADDMUL, binary);
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");

    let digest = dep.stable_digest();
    let rust_row = m
        .intern_import(ModuleImport::new(dep.name.clone(), digest).with_producer(Producer::TRust))
        .expect("Module::intern_import: test fixture");
    let clean_row = m
        .intern_import(ModuleImport::new(dep.name.clone(), digest).with_producer(Producer::Clean))
        .expect("Module::intern_import: test fixture");

    m.function_by_id_mut(scale).unwrap().summary = Some(
        unary_contract()
            .proved()
            .backed_by(ExternRef::new(rust_row, SCALE).relying_on(ProofId::new(0))),
    );
    m.function_by_id_mut(addmul).unwrap().summary = Some(binary_contract());
    m.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Discharged,
            "inherited: dep_addmul ensures (= 1 1)",
        )
        .with_function(addmul)
        .with_formula(clause()),
    );
    m.proof_certificates.push(inheritance_certificate(
        0,
        addmul,
        ExternRef::new(clean_row, ADDMUL).relying_on(ProofId::new(1)),
    ));
    (
        m,
        MixedIds {
            rust_row,
            clean_row,
            addmul,
        },
    )
}

fn not_interned(errors: &[ValidationError], first: u32, duplicate: u32) -> bool {
    has(errors, |e| {
        matches!(
            e,
            ValidationError::ImportTableNotInterned { first: f, duplicate: d, name }
                if *f == first && *d == duplicate && name == "mixed_dep"
        )
    })
}

/// Ratchet row `b4.gap.one_import_row_per_producer` — PASS, ratified §6.
///
/// A mixed Rust+Clean dependency is imported through TWO rows, one per
/// producer, sharing one digest (`docs/SPEC_RATIFICATIONS.md` §6). The pinned
/// shape: the two rows are distinct interned rows (not an interning
/// violation), both authenticate against the one module, and the alternatives
/// the ratification rejects stay refused — one row cannot serve both producers
/// (R5), and an unrecorded producer is no way out (C5).
#[test]
fn b4_gap_one_import_row_per_producer() {
    let dep = mixed_dependency(3);
    let set = ModuleSet::new([&dep]);
    let (root, ids) = mixed_importer(&dep);

    // The ratified shape: two rows, one digest, one producer each.
    assert_eq!(root.imports.len(), 2);
    assert_ne!(ids.rust_row, ids.clean_row);
    assert_eq!(root.imports[0].digest, root.imports[1].digest);
    assert_eq!(root.imports[0].name, root.imports[1].name);
    assert_ne!(root.imports[0].producer, root.imports[1].producer);
    assert!(
        !has(&validate_module(&root), |e| matches!(
            e,
            ValidationError::ImportTableNotInterned { .. }
        )),
        "rows differing in producer are distinct edges, not duplicates"
    );
    let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    assert!(
        report.is_ok(),
        "the ratified shape links: {:?}",
        report.errors()
    );

    // Rejected alternative 1: ONE row for the artifact, the Clean site cites it.
    let mut single = root.clone();
    single.imports.truncate(1);
    if let ProofEvidence::InheritedFromCallee { external, .. } =
        &mut single.proof_certificates[0].evidence
    {
        *external = Some(ExternRef::new(ids.rust_row, ADDMUL).relying_on(ProofId::new(1)));
    }
    let errors =
        validate_linked_module(&single, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(
        detail_contains(&errors, "inherited", "was produced by clean"),
        "one row cannot pair with two producers: {errors:?}"
    );

    // Rejected alternative 2: an UNRECORDED producer on the single row.
    let mut neutral = single.clone();
    neutral.imports[0].producer = None;
    let errors =
        validate_linked_module(&neutral, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(
        detail_contains(&errors, "import", "producer is unrecorded"),
        "`None` is never a wildcard producer: {errors:?}"
    );
}

/// WS1.16 (F-077): the linked walk inherits the structural rule that rows
/// sharing a digest share a name. The ratified two-row shape links (above);
/// renaming ONE of its rows is `ImportIdentityConflict` — and, being a name
/// no module under that digest carries, also `NameMismatch` at L3.
#[test]
fn ws1_16_linked_walk_refuses_a_digest_under_two_names() {
    let dep = mixed_dependency(3);
    let set = ModuleSet::new([&dep]);
    let (mut root, ids) = mixed_importer(&dep);
    root.imports[ids.clean_row.as_usize()].name = "renamed_dep".into();
    let errors = validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(
        has(&errors, |e| matches!(
            e,
            ValidationError::ImportIdentityConflict { conflicting_name, .. }
                if conflicting_name == "renamed_dep"
        )),
        "{errors:?}"
    );
    // The name the renamed row records is a name no module under that digest
    // carries, so the edge check refuses it too and the inheritance cited
    // through it is not admitted.
    assert!(
        has(&errors, |e| matches!(
            e,
            ValidationError::UnauthenticatedImport { detail, .. }
                if detail.contains("renamed_dep")
        )),
        "the mislabelled row must also fail C4 at the edge: {errors:?}"
    );
}

/// WS1.16 review (F-077), adversarial: the conflict is in the DEPENDENCY's own
/// table, one edge down. The walk validates every module it authenticates, so
/// a mislabelled row there is refused exactly as in the root — an importer
/// cannot launder one by pushing it into a crate it depends on.
#[test]
fn ws1_16_a_conflicting_import_table_one_edge_down_is_refused_by_the_walk() {
    let leaf = dependency("leaf");
    let leaf_digest = leaf.stable_digest();
    let mut dep = dependency("dep");
    dep.imports
        .push(ModuleImport::new(leaf.name.clone(), leaf_digest).with_producer(Producer::TRust));
    dep.imports
        .push(ModuleImport::new("not_the_leafs_name", leaf_digest).with_producer(Producer::Clean));
    assert!(
        has(&validate_module(&dep), |e| matches!(
            e,
            ValidationError::ImportIdentityConflict { conflicting_name, .. }
                if conflicting_name == "not_the_leafs_name"
        )),
        "{:?}",
        validate_module(&dep)
    );
    let root = backed_importer("root", &dep);
    let set = ModuleSet::new([&dep, &leaf]);
    let errors = validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors();
    // The walk reports a refused dependency as ONE row naming its edge, so
    // what the root sees is `ImportedModuleInvalid` over the dependency the
    // rule refused — not the variant itself.
    assert!(
        has(&errors, |e| matches!(
            e,
            ValidationError::ImportedModuleInvalid { import: 0, .. }
        )),
        "the dependency's own mislabelled row must refuse the walk: {errors:?}"
    );

    // Mutation control: name the leaf correctly on both rows and the same
    // two-producer shape one edge down validates, root and dependency alike.
    let mut fixed = dep.clone();
    fixed.imports[1].name = leaf.name.clone();
    assert!(
        validate_module(&fixed).is_empty(),
        "{:?}",
        validate_module(&fixed)
    );
    let root = backed_importer("root", &fixed);
    let set = ModuleSet::new([&fixed, &leaf]);
    let errors = validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(errors.is_empty(), "{errors:?}");
}

/// WS1.16 review (F-077 × F-084), adversarial: the identity SCHEME is not an
/// escape hatch. One artifact recorded under two schemes has two digests, so
/// the structural rule — which keys on the digest value — cannot see a rename
/// across them. That is its stated limit, and it is closed one tier up: the
/// row authenticates under the scheme it RECORDS, so C4 compares the name
/// against the one candidate and refuses.
#[test]
fn ws1_16_a_cross_scheme_rename_is_invisible_structurally_and_refused_at_the_edge() {
    use trust_ir::IdentityScheme;

    let dep = mixed_dependency(3);
    let (mut root, ids) = mixed_importer(&dep);
    // The same artifact, re-minted under the LEGACY domain and renamed.
    root.imports[ids.clean_row.as_usize()] =
        ModuleImport::new("renamed_dep", dep.stable_digest_under(IdentityScheme::V2))
            .with_scheme(IdentityScheme::V2)
            .with_producer(Producer::Clean);
    assert_ne!(root.imports[0].digest, root.imports[1].digest);
    assert!(
        !has(&validate_module(&root), |e| matches!(
            e,
            ValidationError::ImportIdentityConflict { .. }
        )),
        "two schemes are two digests: the structural rule cannot see this one"
    );

    let set = ModuleSet::new([&dep]);
    let errors = validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(
        has(&errors, |e| matches!(
            e,
            ValidationError::UnauthenticatedImport { detail, .. }
                if detail.contains("renamed_dep")
        )),
        "the legacy-scheme row still authenticates against the one artifact, \
         whose name it misstates: {errors:?}"
    );

    // Mutation control: the SAME cross-scheme row under the artifact's real
    // name authenticates, so it is the name — not the older scheme — that was
    // refused.
    let mut honest = root.clone();
    honest.imports[ids.clean_row.as_usize()].name = dep.name.clone();
    let errors =
        validate_linked_module(&honest, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(
        !has(&errors, |e| matches!(
            e,
            ValidationError::UnauthenticatedImport { .. }
                | ValidationError::ImportIdentityConflict { .. }
        )),
        "a legacy-scheme row is legal: {errors:?}"
    );
}

/// Ratchet row `small-designs/LCR-08-import-producer-is-module-level` — PASS,
/// ratified §6: a cross-crate citation into a mixed crate may target a
/// Clean-produced OR a Rust-produced function of the same dependency, each
/// through its own producer's row, and BOTH rows authenticate against the ONE
/// artifact. A consumer deduplicating artifacts keys on `digest` and sees one.
#[test]
fn small_designs_lcr_08_import_producer_is_module_level() {
    let dep = mixed_dependency(3);
    let set = ModuleSet::new([&dep]);
    let (root, ids) = mixed_importer(&dep);
    let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    assert!(report.is_ok(), "{:?}", report.errors());

    let digests = report.authenticated_imports().unwrap();
    assert_eq!(digests.get(&ids.rust_row), Some(&dep.stable_digest()));
    assert_eq!(digests.get(&ids.clean_row), Some(&dep.stable_digest()));
    let artifacts: BTreeSet<ProofDigest> = root.imports.iter().map(|row| row.digest).collect();
    assert_eq!(artifacts.len(), 1, "two edges, one artifact");

    let authenticated = report.authenticated().unwrap();
    // The Rust citation (backed_by through the TRust row) ...
    assert_eq!(
        authenticated.authenticated_backed_by().count(),
        1,
        "the TRust declaration's backed_by re-earned"
    );
    // ... and the Clean citation (inheritance through the Clean row).
    assert_eq!(
        authenticated.authenticated_inheritances().len(),
        1,
        "the Clean declaration's inheritance re-earned"
    );
    assert!(
        root.proof_certificates
            .iter()
            .any(|c| matches!(c.evidence, ProofEvidence::InheritedFromCallee { callee, .. } if callee == ids.addmul))
    );
}

/// Ratchet row `b4.gap.duplicate_import_rows_admitted` — CLOSED (F-075).
///
/// A pushed clone of `imports[0]` (not interned) is refused as
/// `ImportTableNotInterned { first: 0, duplicate: 2 }` by the structural tier,
/// the authority tier and the linked walk alike. Mutation control: the
/// untouched two-producer table (rows equal in digest, different in producer)
/// raises nothing and links.
#[test]
fn b4_gap_duplicate_import_rows_admitted() {
    let dep = mixed_dependency(3);
    let set = ModuleSet::new([&dep]);
    let (root, _) = mixed_importer(&dep);
    assert!(validate_linked_module(&root, &set, &RejectingModuleProofAuthority).is_ok());

    let mut duplicated = root.clone();
    duplicated.imports.push(root.imports[0].clone());
    assert_eq!(duplicated.imports[0], duplicated.imports[2]);

    let structural = validate_module(&duplicated);
    assert!(
        not_interned(&structural, 0, 2),
        "structural: {structural:?}"
    );
    assert!(
        !not_interned(&structural, 1, 2) && !not_interned(&structural, 0, 1),
        "reported once, against the first EQUAL row only: {structural:?}"
    );
    let codegen = trust_ir_build::validate_module_for_codegen(&duplicated);
    assert!(not_interned(&codegen, 0, 2), "codegen: {codegen:?}");
    let authority = validate_module_with_authority(&duplicated, &RejectingModuleProofAuthority);
    assert!(not_interned(&authority, 0, 2), "authority: {authority:?}");
    let linked = validate_linked_module(&duplicated, &set, &RejectingModuleProofAuthority);
    assert!(!linked.is_ok());
    assert!(
        not_interned(linked.errors(), 0, 2),
        "linked: {:?}",
        linked.errors()
    );
}

/// Ratchet row `b4.gap.computed_digest_is_caller_asserted` — CLOSED (F-076).
///
/// The hash-once form takes a [`trust_ir::HashedModule`], whose digest is
/// computed over its own module by its sole constructor (a struct literal does
/// not compile — see the `compile_fail` doctest on `HashedModule`), so the
/// tampered dependency is a `DigestMismatch`. The deprecated caller-asserted
/// spelling now recomputes the digest and refuses the same forgery.
#[test]
fn b4_gap_computed_digest_is_caller_asserted() {
    use trust_ir::{HashedModule, ImportVerificationError};

    let dep = mixed_dependency(3);
    let (root, ids) = mixed_importer(&dep);
    let tampered = mixed_dependency(2);
    assert_eq!(tampered.name, dep.name);
    let recorded = root.import(ids.rust_row).unwrap().digest;

    let hashed = HashedModule::new(&tampered);
    assert_eq!(hashed.digest(), tampered.stable_digest());
    assert!(std::ptr::eq(hashed.module(), &tampered));
    assert!(matches!(
        root.verify_import_hashed(ids.rust_row, &hashed),
        Err(ImportVerificationError::DigestMismatch { import: 0, recorded: r, actual })
            if r == recorded && actual == tampered.stable_digest()
    ));
    assert!(matches!(
        root.verify_import(ids.rust_row, &tampered),
        Err(ImportVerificationError::DigestMismatch { .. })
    ));

    // The old footgun: hand the RECORDED digest in as the "computed" one.
    #[allow(deprecated)]
    let asserted = root.verify_import_with_computed_digest(ids.rust_row, &tampered, recorded);
    assert!(
        matches!(
            asserted,
            Err(ImportVerificationError::DigestMismatch { import: 0, recorded: r, actual })
                if r == recorded && actual == tampered.stable_digest()
        ),
        "a caller-asserted digest is recomputed and refused: {asserted:?}"
    );

    // Mutation control: the honest dependency authenticates on BOTH rows
    // through the one hash, and the deprecated spelling given the digest it
    // really has still verifies.
    let honest = HashedModule::new(&dep);
    for row in [ids.rust_row, ids.clean_row] {
        let verified = root
            .verify_import_hashed(row, &honest)
            .expect("honest edge");
        assert_eq!(verified.digest(), dep.stable_digest());
        assert!(std::ptr::eq(verified.module(), &dep));
    }
    #[allow(deprecated)]
    let honest_legacy =
        root.verify_import_with_computed_digest(ids.rust_row, &dep, dep.stable_digest());
    assert!(honest_legacy.is_ok());
}

// ---------------------------------------------------------------------------
// WS4.7 review — adversarial modules the increment's own rows do not spell
// ---------------------------------------------------------------------------

/// A DEPENDENCY (not the root) whose import table carries a pushed duplicate
/// row is invalid under the same interning rule, so it backs nothing: the
/// importer's citations fail as `ImportedModuleInvalid`, naming the rule.
/// Mutation control: the same dependency with the row INTERNED once links.
#[test]
fn ws4_7_review_a_dependency_with_a_pushed_duplicate_row_backs_nothing() {
    // The dependency's own row names a real, supplied module: since WS1.7 the
    // walk authenticates EVERY row, cited or not, so an unsupplied one would
    // be refused for a reason other than the one this test pins.
    let mut unrelated_module = Module::new("unrelated");
    unrelated_module.target_info = Some(target());
    let unrelated = ModuleImport::new("unrelated", unrelated_module.stable_digest())
        .with_producer(Producer::TRust);

    let mut interned = mixed_dependency(3);
    interned
        .intern_import(unrelated.clone())
        .expect("Module::intern_import: test fixture");
    interned
        .intern_import(unrelated.clone())
        .expect("Module::intern_import: test fixture");
    assert_eq!(interned.imports.len(), 1, "intern_import is idempotent");
    assert!(
        validate_module(&interned).is_empty(),
        "{:?}",
        validate_module(&interned)
    );
    let set = ModuleSet::new([&interned, &unrelated_module]);
    let (root, _) = mixed_importer(&interned);
    let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    assert!(report.is_ok(), "control links: {:?}", report.errors());

    let mut duplicated = mixed_dependency(3);
    duplicated.imports.push(unrelated.clone());
    duplicated.imports.push(unrelated);
    assert!(has(&validate_module(&duplicated), |e| matches!(
        e,
        ValidationError::ImportTableNotInterned { first: 0, duplicate: 1, name } if name == "unrelated"
    )));
    let set = ModuleSet::new([&duplicated, &unrelated_module]);
    let (root, _) = mixed_importer(&duplicated);
    let errors = validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors();
    let poisoned = |e: &ValidationError| {
        matches!(
            e,
            ValidationError::ImportedModuleInvalid { first, .. }
                if first.contains("not content-interned")
        )
    };
    assert_eq!(
        errors.iter().filter(|e| poisoned(e)).count(),
        2,
        "both edges into the invalid dependency are refused: {errors:?}"
    );
}

/// A citation REROUTED through the pushed duplicate row. Each edge on its own
/// authenticates (the duplicate is byte-for-byte the honest row), so the ONLY
/// thing that can refuse this module is the interning rule — and it does, in
/// the linked tier, against the first equal row.
#[test]
fn ws4_7_review_a_citation_through_the_duplicate_row_is_still_refused() {
    let dep = mixed_dependency(3);
    let set = ModuleSet::new([&dep]);
    let (root, ids) = mixed_importer(&dep);

    let mut rerouted = root.clone();
    let duplicate = ImportId::new(u32::try_from(rerouted.imports.len()).unwrap());
    rerouted
        .imports
        .push(root.import(ids.rust_row).unwrap().clone());
    let scale = rerouted.function_by_name(SCALE).unwrap().id;
    rerouted.function_by_id_mut(scale).unwrap().summary = Some(
        unary_contract()
            .proved()
            .backed_by(ExternRef::new(duplicate, SCALE).relying_on(ProofId::new(0))),
    );
    // The edge itself is indistinguishable from the honest one.
    assert!(rerouted.verify_import(duplicate, &dep).is_ok());

    let linked = validate_linked_module(&rerouted, &set, &RejectingModuleProofAuthority);
    assert!(!linked.is_ok());
    assert!(
        not_interned(linked.errors(), ids.rust_row.index(), duplicate.index()),
        "{:?}",
        linked.errors()
    );
}

/// The deprecated caller-asserted spelling keeps the check ORDER for an honest
/// caller and refuses the honest-hash-of-a-tampered-module case at C3 with the
/// row's own recorded digest: self-checking must not turn into a way around
/// the edge checks, in either direction.
#[test]
#[allow(deprecated)]
fn ws4_7_review_the_deprecated_spelling_is_exactly_the_hashed_form_for_an_honest_digest() {
    use trust_ir::ImportVerificationError;

    let dep = mixed_dependency(3);
    let tampered = mixed_dependency(2);
    let (root, ids) = mixed_importer(&dep);
    let recorded = root.import(ids.rust_row).unwrap().digest;

    // C1 still names itself for an out-of-range id with an honest digest.
    assert!(matches!(
        root.verify_import_with_computed_digest(ImportId::new(9), &dep, dep.stable_digest()),
        Err(ImportVerificationError::UnresolvedImport { import: 9 })
    ));
    // An HONEST hash of the tampered module: refused at C3 against the row.
    assert!(matches!(
        root.verify_import_with_computed_digest(ids.rust_row, &tampered, tampered.stable_digest()),
        Err(ImportVerificationError::DigestMismatch { recorded: r, actual, .. })
            if r == recorded && actual == tampered.stable_digest()
    ));
    // C4 is still reached: an honest digest of a same-digest-but-renamed row.
    let mut renamed = root.clone();
    renamed.imports[ids.rust_row.index() as usize].name = "someone_else".into();
    assert!(matches!(
        renamed.verify_import_with_computed_digest(ids.rust_row, &dep, dep.stable_digest()),
        Err(ImportVerificationError::NameMismatch { .. })
    ));
}

// ---------------------------------------------------------------------------
// WS1.7 = WS4.8 (DG-78): every import row is authenticated, unconditionally,
// and every call edge into an authenticated dependency is resolved across it
// ---------------------------------------------------------------------------

/// A call-only dependency: `g(x: u64) -> u64 { x + k }`, producer TRust. No
/// summary, no obligation — the far side of a plain call.
fn callee_dependency(name: &str, k: u128) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info(name, target());
    mb.set_default_producer(Producer::TRust);
    let ft = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function("g", ft);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::U64);
    fb.switch_to_block(entry);
    let kk = fb.uconst(Ty::U64, k);
    let r = fb.add(Ty::U64, x, kk);
    fb.ret(vec![r]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert!(
        validate_module(&module).is_empty(),
        "{:?}",
        validate_module(&module)
    );
    module
}

/// A CALL-ONLY importer: one import row recording `digest`, a body-less
/// declaration `g(param) -> u64`, and `program() -> u64 { g(1) }`. No
/// summary, no certificate, no `ExternRef` — the shape verify/c12 rows 1a/1b
/// measured as authenticated by nothing.
fn call_only_importer(digest: ProofDigest, param: Ty) -> (Module, ImportId) {
    let mut mb = ModuleBuilder::new_with_target_info("root", target());
    mb.set_default_producer(Producer::TRust);
    let gt = mb.add_func_type(vec![param.clone()], vec![Ty::U64]);
    let pt = mb.add_func_type(vec![], vec![Ty::U64]);
    let g = mb.declare_function("g", gt);
    let mut fb = mb.function("program", pt);
    fb.set_body_gate(trust_ir::BodyGate::Gated {
        authority: "import-authentication-test".to_string(),
        evidence: None,
    });
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let one = fb.uconst(param, 1);
    let r = fb.call(g, vec![one]);
    fb.ret(vec![r]);
    fb.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    let id = m
        .intern_import(ModuleImport::new("dep", digest).with_producer(Producer::TRust))
        .expect("Module::intern_import: test fixture");
    (m, id)
}

fn call_refused(errors: &[ValidationError], needle: &str) -> bool {
    detail_contains(errors, "call", needle)
}

fn ambiguous(errors: &[ValidationError], symbol: &str, rows: &[u32]) -> bool {
    has(errors, |e| {
        matches!(
            e,
            ValidationError::AmbiguousImportedSymbol { symbol: s, imports } if s == symbol && imports == rows
        )
    })
}

fn assert_call_only_faith_floor(module: &Module) {
    assert!(validate_module(module).is_empty());
    let errors = trust_ir_build::validate_module_for_codegen(module);
    assert!(errors.is_empty(), "codegen faith floor: {errors:?}");
    assert!(validate_module_with_authority(module, &RejectingModuleProofAuthority).is_empty());
    assert!(
        validate_module_report(module)
            .proof_bearing_imports()
            .is_empty()
    );
}

/// Positive: a call-only importer whose row records the correct digest and
/// whose declaration `g(u64)` matches the far `g(u64)` links, the row is
/// authenticated although nothing cites it, and the call edge is counted.
#[test]
fn ws1_7_a_call_only_importer_with_the_correct_digest_links() {
    let dep = callee_dependency("dep", 1);
    let set = ModuleSet::new([&dep]);
    let (root, id) = call_only_importer(dep.stable_digest(), Ty::U64);
    assert_call_only_faith_floor(&root);
    assert!(
        validate_module_report(&root)
            .proof_bearing_imports()
            .is_empty()
    );
    let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    assert!(report.is_ok(), "{:?}", report.errors());
    assert_eq!(
        report.authenticated_imports().unwrap().get(&id),
        Some(&dep.stable_digest()),
        "an uncited row is authenticated like a cited one"
    );
    assert_eq!(report.authenticated_call_edges(), 1);
    assert!(report.unbound_declarations().is_empty());
    assert!(
        report
            .call_edge_summary()
            .contains("1 authenticated against a supplied dependency, 0 body-less"),
        "{}",
        report.call_edge_summary()
    );
}

/// Ratchet row `verify.c12.L1` / c12 repro 1a — CLOSED (F-068).
///
/// A call-only importer whose row records a garbage digest was measured
/// passing `validate_linked_module` with an EMPTY resolver. Every row is now
/// authenticated: with no module supplied (or the real dependency supplied
/// under a digest-keyed set) the row is `ImportUnavailable`; with a resolver
/// that finds the dependency by NAME, the edge is `DigestMismatch`.
/// Mutation control: the honest digest links (the positive above), and the
/// structural faith floor is unchanged — it never authenticated imports.
#[test]
fn verify_c12_l1_call_only_garbage_digest_is_refused() {
    let dep = callee_dependency("dep", 1);
    let (garbage, _) = call_only_importer(ProofDigest::sha256([0xEE; 32]), Ty::U64);
    assert_call_only_faith_floor(&garbage);
    assert!(
        validate_module(&garbage).is_empty(),
        "the structural floor takes rows on faith, by design"
    );

    for set in [ModuleSet::new([]), ModuleSet::new([&dep])] {
        let report = validate_linked_module(&garbage, &set, &RejectingModuleProofAuthority);
        assert!(!report.is_ok());
        assert!(report.authenticated_imports().is_none());
        assert!(
            has(report.errors(), |e| matches!(
                e,
                ValidationError::ImportUnavailable { import: 0, name } if name == "dep"
            )),
            "{:?}",
            report.errors()
        );
    }

    // A resolver keyed by NAME hands over the real dependency: the digest is
    // compared and the edge refused as the mismatch it is.
    let by_name = |import: &ModuleImport| (import.name == "dep").then_some(&dep);
    let errors =
        validate_linked_module(&garbage, &by_name, &RejectingModuleProofAuthority).into_errors();
    assert!(
        detail_contains(&errors, "import", "is not the recorded"),
        "DigestMismatch on an uncited row: {errors:?}"
    );
}

/// Ratchet row `verify.c12.L2` / c12 repro 1b — CLOSED (F-068).
///
/// Declaration `g(u32)` against the far definition `g(u64)`: refused as a
/// `SignatureMismatch` on the call edge, both when the edge is implicit (the
/// symbol the authenticated dependency exports) and when the declaration
/// names the far entity with an obligation-free `backed_by`.
#[test]
fn verify_c12_l2_signature_drift_is_refused() {
    let dep = callee_dependency("dep", 1);
    let set = ModuleSet::new([&dep]);

    let (drift, id) = call_only_importer(dep.stable_digest(), Ty::U32);
    assert_call_only_faith_floor(&drift);
    let errors = validate_linked_module(&drift, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(
        call_refused(&errors, "signature mismatch — parameter 0 type u32 vs u64"),
        "{errors:?}"
    );

    let mut named = drift.clone();
    let g = named.function_by_name("g").unwrap().id;
    named.function_by_id_mut(g).unwrap().summary = Some(
        FunctionSummary::new()
            .with_params(vec!["x".to_string()])
            .backed_by(ExternRef::new(id, "g")),
    );
    assert!(
        validate_module_report(&named)
            .proof_bearing_imports()
            .is_empty()
    );
    assert_call_only_faith_floor(&named);
    let errors = validate_linked_module(&named, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(
        call_refused(&errors, "signature mismatch — parameter 0 type u32 vs u64"),
        "{errors:?}"
    );

    // Mutation control: the same named edge with the matching signature links.
    let (honest, id) = call_only_importer(dep.stable_digest(), Ty::U64);
    let mut named = honest.clone();
    let g = named.function_by_name("g").unwrap().id;
    named.function_by_id_mut(g).unwrap().summary = Some(
        FunctionSummary::new()
            .with_params(vec!["x".to_string()])
            .backed_by(ExternRef::new(id, "g")),
    );
    let report = validate_linked_module(&named, &set, &RejectingModuleProofAuthority);
    assert!(report.is_ok(), "{:?}", report.errors());
    assert_eq!(report.authenticated_call_edges(), 1);
}

/// Ratchet row `b4.gap.call_only_import_never_authenticated` — CLOSED
/// (F-068). The partb measurement, inverted: the garbage-digest importer and
/// the `u32`/`u64` skew are both refused, and the honest baseline reports its
/// row authenticated (it reported zero).
#[test]
fn b4_gap_call_only_import_never_authenticated() {
    let dep = callee_dependency("b4_dep", 3);
    let set = ModuleSet::new([&dep]);
    let rename = |mut m: Module| {
        m.imports[0].name = "b4_dep".to_string();
        m
    };
    let good = rename(call_only_importer(dep.stable_digest(), Ty::U64).0);
    let baseline = validate_linked_module(&good, &set, &RejectingModuleProofAuthority);
    assert!(baseline.is_ok(), "{:?}", baseline.errors());
    assert_eq!(baseline.authenticated_imports().map(|m| m.len()), Some(1));

    let empty = ModuleSet::new([]);
    let bogus = rename(call_only_importer(ProofDigest::sha256([0xEE; 32]), Ty::U64).0);
    let bogus_report = validate_linked_module(&bogus, &empty, &RejectingModuleProofAuthority);
    assert!(!bogus_report.is_ok(), "garbage digest + empty resolver");

    let skewed = rename(call_only_importer(dep.stable_digest(), Ty::U32).0);
    let skewed_report = validate_linked_module(&skewed, &set, &RejectingModuleProofAuthority);
    assert!(
        call_refused(skewed_report.errors(), "signature mismatch"),
        "{:?}",
        skewed_report.errors()
    );
    // The raw comparator agrees with the walk.
    assert!(
        trust_ir::signatures_compatible(
            &skewed,
            skewed.function_by_name("g").unwrap(),
            &dep,
            dep.function_by_name("g").unwrap(),
        )
        .is_err()
    );
}

/// Negative twin: an obligation-free `backed_by` naming a symbol the
/// dependency does not carry is refused (`SymbolUnresolved`), not skipped.
#[test]
fn ws1_7_an_obligation_free_backed_by_to_a_missing_symbol_is_refused() {
    let dep = callee_dependency("dep", 1);
    let set = ModuleSet::new([&dep]);
    let (mut root, id) = call_only_importer(dep.stable_digest(), Ty::U64);
    let g = root.function_by_name("g").unwrap().id;
    let decl = root.function_by_id_mut(g).unwrap();
    decl.name = "h".to_string();
    decl.summary = Some(
        FunctionSummary::new()
            .with_params(vec!["x".to_string()])
            .backed_by(ExternRef::new(id, "h")),
    );
    let errors = validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(
        call_refused(
            &errors,
            "no function in the dependency carries symbol \"h\""
        ),
        "{errors:?}"
    );
    // Mutation control: without the `backed_by`, `h` is exported by nobody,
    // so it is an FFI extern — counted, not refused.
    root.function_by_id_mut(g).unwrap().summary = None;
    let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    assert!(report.is_ok(), "{:?}", report.errors());
    assert_eq!(report.unbound_declarations().len(), 1);
}

/// Mutation control: an import row nothing cites, whose dependency IS
/// supplied, authenticates — no false refusal. Its twin, the same row with
/// the dependency NOT supplied, is refused although nothing cites it.
#[test]
fn ws1_7_an_uncited_resolvable_row_authenticates_and_an_unsupplied_one_is_refused() {
    let dep = dependency("dep");
    let other = callee_dependency("other", 5);
    let mut root = backed_importer("root", &dep);
    let uncited = root
        .intern_import(
            ModuleImport::new("other", other.stable_digest()).with_producer(Producer::TRust),
        )
        .expect("Module::intern_import: test fixture");
    assert_eq!(
        validate_module_report(&root).proof_bearing_imports(),
        BTreeSet::from([ImportId::new(0)]),
        "the new row is cited by nothing"
    );

    let set = ModuleSet::new([&dep, &other]);
    let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    assert!(report.is_ok(), "{:?}", report.errors());
    assert_eq!(
        report.authenticated_imports().unwrap().get(&uncited),
        Some(&other.stable_digest())
    );

    let set = ModuleSet::new([&dep]);
    let errors = validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(
        has(&errors, |e| matches!(
            e,
            ValidationError::ImportUnavailable { import, name } if *import == uncited.index() && name == "other"
        )),
        "{errors:?}"
    );
}

/// Mutation control: a libc declaration no dependency exports is untouched —
/// not refused, not resolved — and reported as UNBOUND by name.
#[test]
fn ws1_7_a_libc_declaration_is_untouched_and_reported_unbound() {
    let dep = callee_dependency("dep", 1);
    let set = ModuleSet::new([&dep]);
    let (mut root, _) = call_only_importer(dep.stable_digest(), Ty::U64);
    let abs_ty = root
        .add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let next = FuncId::new(u32::try_from(root.functions.len()).unwrap());
    root.try_add_function(Function::new(
        next,
        "abs",
        abs_ty,
        trust_ir::value::BlockId::new(0),
    ))
    .expect("Module::try_add_function: test fixture");
    let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    assert!(report.is_ok(), "{:?}", report.errors());
    assert_eq!(report.authenticated_call_edges(), 1, "`g` only");
    assert_eq!(
        report.unbound_declarations(),
        &[trust_ir_build::UnboundDeclaration {
            module: "root".to_string(),
            symbol: "abs".to_string(),
        }]
    );
    assert!(
        report.call_edge_summary().contains("root::abs"),
        "{}",
        report.call_edge_summary()
    );
}

/// Negative twin + mutation control: a symbol DEFINED and exported by two
/// authenticated dependency artifacts is `AmbiguousImportedSymbol`, naming one
/// row per artifact; the same modules with one of the two definitions made
/// `Internal` link.
#[test]
fn ws1_7_a_symbol_two_dependencies_export_is_ambiguous() {
    let first = callee_dependency("dep_a", 1);
    let second = callee_dependency("dep_b", 2);
    let (mut root, _) = call_only_importer(first.stable_digest(), Ty::U64);
    root.intern_import(
        ModuleImport::new("dep_b", second.stable_digest()).with_producer(Producer::TRust),
    )
    .expect("Module::intern_import: test fixture");
    root.imports[0].name = "dep_a".to_string();
    let set = ModuleSet::new([&first, &second]);
    let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    assert!(
        ambiguous(report.errors(), "g", &[0, 1]),
        "{:?}",
        report.errors()
    );
    assert!(
        report.errors().iter().any(|e| e.to_string().contains(
            "ambiguous call edge: @g is defined and exported by import #0 and import #1"
        )),
        "{:?}",
        report.errors()
    );

    // An explicit `backed_by` does not disambiguate: the linker reads none.
    let mut cited = root.clone();
    let g = cited.function_by_name("g").unwrap().id;
    cited.function_by_id_mut(g).unwrap().summary = Some(
        FunctionSummary::new()
            .with_params(vec!["x".to_string()])
            .backed_by(ExternRef::new(ImportId::new(0), "g")),
    );
    let errors = validate_linked_module(&cited, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(ambiguous(&errors, "g", &[0, 1]), "{errors:?}");

    // Mutation control: `dep_b`'s `g` made Internal is no longer an export.
    let mut private = second.clone();
    private.functions[0].linkage = Linkage::Internal;
    assert!(
        validate_module(&private).is_empty(),
        "{:?}",
        validate_module(&private)
    );
    let mut root = root.clone();
    root.imports[1].digest = private.stable_digest();
    let set = ModuleSet::new([&first, &private]);
    let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    assert!(report.is_ok(), "{:?}", report.errors());
    assert_eq!(report.authenticated_call_edges(), 1);
}

/// Mutation control (see WS1.16): two rows sharing a digest but differing in
/// producer are one ARTIFACT, never an ambiguity, and each implicit call
/// edge resolves through the row of its far definition's producer. Negative
/// twin: with only the TRust row, the Clean-produced edge is refused by R5.
#[test]
fn ws1_7_two_producer_rows_of_one_artifact_bind_each_call_edge_to_its_producer() {
    let dep = mixed_dependency(3);
    let set = ModuleSet::new([&dep]);
    let mut mb = ModuleBuilder::new_with_target_info("mixed_calls", target());
    let unary = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let binary = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    mb.set_default_producer(Producer::TRust);
    mb.declare_function(SCALE, unary);
    mb.set_default_producer(Producer::Clean);
    mb.declare_function(ADDMUL, binary);
    let mut root = mb.build().expect("ModuleBuilder::build: test fixture");
    let digest = dep.stable_digest();
    root.intern_import(ModuleImport::new(dep.name.clone(), digest).with_producer(Producer::TRust))
        .expect("Module::intern_import: test fixture");
    root.intern_import(ModuleImport::new(dep.name.clone(), digest).with_producer(Producer::Clean))
        .expect("Module::intern_import: test fixture");

    let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    assert!(report.is_ok(), "{:?}", report.errors());
    assert_eq!(report.authenticated_call_edges(), 2);
    assert!(!has(report.errors(), |e| matches!(
        e,
        ValidationError::AmbiguousImportedSymbol { .. }
    )));

    let mut single = root.clone();
    single.imports.truncate(1);
    let errors =
        validate_linked_module(&single, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(call_refused(&errors, "was produced by clean"), "{errors:?}");
}

/// The walk is unconditional: an interposable (`Weak`) far definition on a
/// PLAIN call edge is named, not read as an FFI extern.
#[test]
fn ws1_7_a_call_edge_into_an_interposable_definition_is_refused_by_name() {
    let mut dep = callee_dependency("dep", 1);
    dep.functions[0].linkage = Linkage::Weak;
    let set = ModuleSet::new([&dep]);
    let (root, _) = call_only_importer(dep.stable_digest(), Ty::U64);
    let errors = validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(
        call_refused(&errors, "far symbol `g` has interposable linkage Weak"),
        "{errors:?}"
    );
}

// ---------------------------------------------------------------------------
// WS1.7 review: adversarial call-edge shapes the first cut did not cover
// ---------------------------------------------------------------------------

/// A root that reaches the dependency's `g` through a body-less
/// `ExternalWeak` declaration `g(param) -> u64` with the WS3.15 idiom:
/// `SymbolAddr : Ptr`, null check, `CallIndirect`.
fn weak_call_importer(digest: ProofDigest, param: Ty) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("root", target());
    mb.set_default_producer(Producer::TRust);
    let gt = mb.add_func_type(vec![param.clone()], vec![Ty::U64]);
    let g = mb.declare_function("g", gt);
    let mut fb = mb.function("use_g", gt);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, param);
    fb.switch_to_block(entry);
    let present = fb.create_block();
    let absent = fb.create_block();
    let address = fb.const_value(Ty::Ptr, trust_ir::Constant::symbol_addr("g"));
    let null = fb.null_ptr();
    let is_null = fb.icmp(trust_ir::inst::ICmpOp::Eq, Ty::Ptr, address, null);
    fb.condbr(is_null, absent, vec![], present, vec![]);
    fb.switch_to_block(present);
    let r = fb.call_indirect(address, gt, vec![x]);
    fb.ret(vec![r]);
    fb.switch_to_block(absent);
    let zero = fb.uconst(Ty::U64, 0);
    fb.ret(vec![zero]);
    fb.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    m.function_by_id_mut(g).unwrap().linkage = Linkage::ExternalWeak;
    m.intern_import(ModuleImport::new("dep", digest).with_producer(Producer::TRust))
        .expect("Module::intern_import: test fixture");
    m
}

/// WS1.7 review (legitimate module wrongly refused): a WS3.15 weak import of
/// a symbol an authenticated dependency exports is a claim-free call edge.
/// Its nullable binding is the in-module validator's business (the
/// null-checked address idiom); L10 must still check the SIGNATURE, not
/// refuse the edge for being weak — `InterposableFarSite { side: "local" }`
/// exists because a PROOF about the far body need not be about the body a
/// weak reference reaches, and a call edge carries no proof.
#[test]
fn ws1_7_review_a_weak_import_of_a_dependency_symbol_is_signature_checked_not_refused() {
    let dep = callee_dependency("dep", 1);
    let set = ModuleSet::new([&dep]);
    let root = weak_call_importer(dep.stable_digest(), Ty::U64);
    assert!(
        validate_module(&root).is_empty(),
        "{:?}",
        validate_module(&root)
    );
    let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    assert!(report.is_ok(), "{:?}", report.errors());
    assert_eq!(report.authenticated_call_edges(), 1);
    assert!(report.unbound_declarations().is_empty());

    // Negative twin: the weak edge is still signature-checked.
    let skewed = weak_call_importer(dep.stable_digest(), Ty::U32);
    assert!(validate_module(&skewed).is_empty());
    let errors =
        validate_linked_module(&skewed, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(
        call_refused(&errors, "signature mismatch — parameter 0 type u32 vs u64"),
        "{errors:?}"
    );

    // Mutation control: a weak declaration is still refused as the LOCAL side
    // of a PROOF-bearing citation.
    let mut cited = callee_dependency("dep", 1);
    let far_g = cited.functions[0].id;
    cited.functions[0].summary = Some(
        FunctionSummary::new()
            .with_params(vec!["x".to_string()])
            .ensuring(clause())
            .proved(),
    );
    let (obligation, certificate) = certified_postcondition(0, far_g);
    cited.proof_obligations.push(obligation);
    cited.proof_certificates.push(certificate);
    assert!(
        validate_module(&cited).is_empty(),
        "{:?}",
        validate_module(&cited)
    );
    let mut root = weak_call_importer(cited.stable_digest(), Ty::U64);
    let g = root.function_by_name("g").unwrap().id;
    root.function_by_id_mut(g).unwrap().summary = Some(
        FunctionSummary::new()
            .with_params(vec!["x".to_string()])
            .ensuring(clause())
            .proved()
            .backed_by(ExternRef::new(ImportId::new(0), "g").relying_on(ProofId::new(0))),
    );
    let set = ModuleSet::new([&cited]);
    let errors = validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(
        detail_contains(&errors, "backed_by", "interposable linkage ExternalWeak"),
        "{errors:?}"
    );
}

/// A root with NO declaration of `g` that takes `SymbolAddr("g") : Ptr` and
/// calls through it at `sig (param) -> u64`.
fn symbol_addr_importer(digest: ProofDigest, param: Ty, symbol: &str) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("root", target());
    mb.set_default_producer(Producer::TRust);
    let gt = mb.add_func_type(vec![param.clone()], vec![Ty::U64]);
    let pt = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("program", pt);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let address = fb.const_value(Ty::Ptr, trust_ir::Constant::symbol_addr(symbol));
    let one = fb.uconst(param, 1);
    let r = fb.call_indirect(address, gt, vec![one]);
    fb.ret(vec![r]);
    fb.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    m.intern_import(ModuleImport::new("dep", digest).with_producer(Producer::TRust))
        .expect("Module::intern_import: test fixture");
    m
}

/// WS1.7 review (false claim accepted): a call edge spelled with NO
/// declaration — a relocatable `SymbolAddr` naming a function an
/// authenticated dependency exports, called through `CallIndirect` at a
/// signature nothing compared with the far one — bypassed L10 entirely, and
/// was not even reported unbound. The linker binds it to the dependency's
/// body all the same. Refused: a call into a dependency must be spelled
/// through a declaration, which L10 signature-checks.
#[test]
fn ws1_7_review_a_symbol_address_into_a_dependency_without_a_declaration_is_refused() {
    let dep = callee_dependency("dep", 1);
    let set = ModuleSet::new([&dep]);
    let root = symbol_addr_importer(dep.stable_digest(), Ty::U32, "g");
    assert!(
        validate_module(&root).is_empty(),
        "{:?}",
        validate_module(&root)
    );
    let errors = validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(call_refused(&errors, "no local declaration"), "{errors:?}");

    // Mutation control: a symbol no dependency exports is an FFI address,
    // untouched.
    let ffi = symbol_addr_importer(dep.stable_digest(), Ty::U32, "abs");
    let report = validate_linked_module(&ffi, &set, &RejectingModuleProofAuthority);
    assert!(report.is_ok(), "{:?}", report.errors());

    // Mutation control: the same address taken of a LOCAL declaration is the
    // declaration's call edge, which L10 resolves (and would signature-check).
    let mut declared = symbol_addr_importer(dep.stable_digest(), Ty::U64, "g");
    let gt = declared
        .add_func_type(FuncTy {
            params: vec![Ty::U64],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let next = FuncId::new(u32::try_from(declared.functions.len()).unwrap());
    let mut decl = Function::new(next, "g", gt, trust_ir::value::BlockId::new(0));
    decl.producer = Some(Producer::TRust);
    declared
        .try_add_function(decl)
        .expect("Module::try_add_function: test fixture");
    let report = validate_linked_module(&declared, &set, &RejectingModuleProofAuthority);
    assert!(report.is_ok(), "{:?}", report.errors());
    assert_eq!(report.authenticated_call_edges(), 1);
}

/// A dependency that EXPORTS `g` as DATA: an initialized `External` global,
/// and no function of that name.
fn data_dependency(linkage: Linkage) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("dep", target());
    mb.set_default_producer(Producer::TRust);
    mb.add_global(trust_ir::Global {
        name: "g".into(),
        ty: Ty::U64,
        mutable: false,
        initializer: Some(trust_ir::Constant::Int(7)),
        linkage,
        tls: None,
        align: None,
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: true,
    });
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert!(
        validate_module(&module).is_empty(),
        "{:?}",
        validate_module(&module)
    );
    module
}

/// WS1.7 review (false claim accepted): a function declaration whose symbol
/// an authenticated dependency exports as DATA read as "exported by no
/// dependency" — an FFI extern, counted unbound — while the linker binds the
/// call to the dependency's static. Refused as a call edge into a data symbol.
#[test]
fn ws1_7_review_a_call_edge_that_binds_to_a_dependency_data_symbol_is_refused() {
    let dep = data_dependency(Linkage::External);
    let set = ModuleSet::new([&dep]);
    let (root, _) = call_only_importer(dep.stable_digest(), Ty::U64);
    let errors = validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(
        call_refused(&errors, "as DATA (an initialized global)"),
        "{errors:?}"
    );

    // Mutation control: the same static made `Internal` exports nothing, so
    // the declaration is an FFI extern — counted, not refused.
    let private = data_dependency(Linkage::Internal);
    let set = ModuleSet::new([&private]);
    let (root, _) = call_only_importer(private.stable_digest(), Ty::U64);
    let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    assert!(report.is_ok(), "{:?}", report.errors());
    assert_eq!(report.unbound_declarations().len(), 1);
}

/// WS1.7 review: a symbol one dependency exports as a FUNCTION and another as
/// DATA is ambiguous exactly like two function exports — the linker sees two
/// definitions of one symbol. And the call-edge site admits no obligation
/// kind: a claim-free edge relies on nothing.
#[test]
fn ws1_7_review_a_function_and_a_data_export_of_one_symbol_are_ambiguous() {
    let code = callee_dependency("dep", 1);
    let mut data = data_dependency(Linkage::External);
    data.name = "dep_data".to_string();
    let (mut root, _) = call_only_importer(code.stable_digest(), Ty::U64);
    root.intern_import(
        ModuleImport::new("dep_data", data.stable_digest()).with_producer(Producer::TRust),
    )
    .expect("Module::intern_import: test fixture");
    let set = ModuleSet::new([&code, &data]);
    let errors = validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(ambiguous(&errors, "g", &[0, 1]), "{errors:?}");

    assert_eq!(trust_ir::ExternRefSite::CallEdge.label(), "call");
    for kind in [
        ObligationKind::Precondition,
        ObligationKind::Postcondition,
        ObligationKind::Termination,
        ObligationKind::MemorySafety,
    ] {
        assert!(!trust_ir::ExternRefSite::CallEdge.admits(&kind), "{kind}");
    }
}

/// WS1.7 review: L10 runs on every module of the closure, not only the root.
/// A dependency whose OWN call edge into its dependency is skewed invalidates
/// the root that records it, although the root's own edge is honest.
#[test]
fn ws1_7_review_a_skewed_call_edge_inside_a_dependency_invalidates_the_importer() {
    let leaf = callee_dependency("dep", 1);
    for (param, skewed) in [(Ty::U64, false), (Ty::U32, true)] {
        let (mut mid, _) = call_only_importer(leaf.stable_digest(), param);
        mid.name = "mid".to_string();
        let mut root = Module::new("top");
        root.target_info = Some(target());
        root.intern_import(
            ModuleImport::new("mid", mid.stable_digest()).with_producer(Producer::TRust),
        )
        .expect("Module::intern_import: test fixture");
        let set = ModuleSet::new([&leaf, &mid]);
        let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
        if skewed {
            assert!(
                imported_invalid_with(report.errors(), "signature mismatch"),
                "{:?}",
                report.errors()
            );
        } else {
            assert!(report.is_ok(), "{:?}", report.errors());
            assert_eq!(
                report.authenticated_call_edges(),
                1,
                "mid's edge, closure-wide"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// WS1.3 — `backed_by` re-earns a CLAUSE, not a count (F-003)
// ---------------------------------------------------------------------------

/// Ratchet row `b4.gap.backed_by_reearns_a_count_not_a_clause` — FLIPPED
/// (also the cross-crate face of the critic's `crit.misw08` weighting).
///
/// The dependency publishes a FALSE `proved ensures (= result 0)` for
/// `dep_scale` (dep_scale(2) = 6) beside its kernel-Certified `(= 1 1)` row,
/// and an importer restates the false clause exactly, citing that row. Before
/// WS1.3 the dependency's COUNT held and the linked validator re-earned the
/// false clause. Now the dependency's own pass refuses the clause (no row
/// states it), so the edge is `ImportedModuleInvalid`; and even a dependency
/// that were valid could not lend a row about another claim — the cited
/// formula must be one of the restated clauses.
#[test]
fn b4_gap_backed_by_reearns_a_count_not_a_clause() {
    // Baseline: the honest pair links.
    let dep = mixed_dependency(3);
    let (root, _) = mixed_importer(&dep);
    let honest = validate_linked_module(
        &root,
        &ModuleSet::new([&dep]),
        &RejectingModuleProofAuthority,
    );
    assert!(honest.is_ok(), "{:?}", honest.errors());

    // The single change, on BOTH sides (restatement must be exact).
    let false_clause = ProofFormula::smtlib2("(= result 0)", "Bool");
    let false_contract = || {
        FunctionSummary::new()
            .with_params(vec!["x".to_string()])
            .ensuring(false_clause.clone())
    };
    let mut lying_dep = dep.clone();
    let scale = lying_dep
        .functions
        .iter()
        .find(|f| f.name == SCALE)
        .unwrap()
        .id;
    lying_dep.function_by_id_mut(scale).unwrap().summary = Some(false_contract().proved());
    let refusal = "ensures clause 0 `(= result 0)` has no Discharged/Certified Postcondition row \
                   scoped to this function stating exactly this clause (rows stating other \
                   clauses do not count)";
    assert!(
        has(&validate_module(&lying_dep), |e| matches!(
            e,
            ValidationError::InvalidFunctionSummary { detail, .. } if detail == refusal
        )),
        "the dependency's own pass refuses the false clause"
    );

    let (mut lying_root, ids) = mixed_importer(&lying_dep);
    let local_scale = lying_root
        .functions
        .iter()
        .find(|f| f.name == SCALE)
        .unwrap()
        .id;
    lying_root.function_by_id_mut(local_scale).unwrap().summary = Some(
        false_contract()
            .proved()
            .backed_by(ExternRef::new(ids.rust_row, SCALE).relying_on(ProofId::new(0))),
    );
    let errors = validate_linked_module(
        &lying_root,
        &ModuleSet::new([&lying_dep]),
        &RejectingModuleProofAuthority,
    )
    .into_errors();
    assert!(
        has(&errors, |e| matches!(
            e,
            ValidationError::ImportedModuleInvalid { first, .. } if first.ends_with(refusal)
        )),
        "{errors:?}"
    );
}

/// A far `proved` summary whose cited row is kernel-grounded but states a
/// DIFFERENT formula than any restated clause is refused at the site, by
/// name — even when every other check (restatement, far `proved`, grounding)
/// holds. Built on a dependency whose summary lists two clauses, each backed.
#[test]
fn a_cited_far_row_about_an_unrestated_claim_backs_nothing() {
    let mut dep = dependency("dep");
    let f = dep.functions[0].id;
    // A second kernel-certified row about `(= 2 2)`, which no summary states.
    let obligation = ProofObligation::new(
        ProofId::new(1),
        ObligationKind::Postcondition,
        ProofStatus::Certified,
        "ensures (= 2 2)",
    )
    .with_function(f)
    .with_formula(ProofFormula::smtlib2("(= 2 2)", "Bool"));
    let certificate = contract_clean_cic_certificate(&obligation, "contract-prover")
        .expect("(= 2 2) is genuinely kernel-provable");
    dep.proof_obligations.push(obligation);
    dep.proof_certificates.push(certificate);
    assert!(validate_module(&dep).is_empty());

    let (mut root, id) = importer("root", &dep, contract());
    root.functions[0].summary = Some(contract().proved().backed_by(far(id, 1)));
    let errors = validate_linked_module(
        &root,
        &ModuleSet::new([&dep]),
        &RejectingModuleProofAuthority,
    )
    .into_errors();
    assert!(
        detail_contains(
            &errors,
            "backed_by",
            "cited far obligation #1 states `(= 2 2)`, which is none of the restated ensures \
             clauses"
        ),
        "{errors:?}"
    );
    // The honest citation of the same dependency links.
    let honest = backed_importer("root", &dep);
    assert!(
        validate_linked_module(
            &honest,
            &ModuleSet::new([&dep]),
            &RejectingModuleProofAuthority
        )
        .is_ok()
    );
}

// Retain the distinct obligation-free identity cases from the archived C12
// review. A renamed declaration and a mismatched reference are separate edges.
#[test]
fn c12_obligation_free_identity_claim_authenticates_digest_and_symbol() {
    let named = |digest| {
        let (mut root, id) = call_only_importer(digest, Ty::U64);
        let g = root.function_by_name("g").unwrap().id;
        root.function_by_id_mut(g).unwrap().summary = Some(
            FunctionSummary::new()
                .with_params(vec!["x".to_string()])
                .backed_by(ExternRef::new(id, "no_such_symbol")),
        );
        root
    };
    let garbage = named(ProofDigest::sha256([0xEE; 32]));
    assert_call_only_faith_floor(&garbage);
    let empty = ModuleSet::new([]);
    let report = validate_linked_module(&garbage, &empty, &RejectingModuleProofAuthority);
    assert!(report.authenticated_imports().is_none());
    assert!(has(report.errors(), |e| matches!(
        e, ValidationError::ImportUnavailable { import: 0, name } if name == "dep"
    )));

    let dep = callee_dependency("dep", 1);
    let set = ModuleSet::new([&dep]);
    let honest = named(dep.stable_digest());
    assert_call_only_faith_floor(&honest);
    let errors =
        validate_linked_module(&honest, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(
        call_refused(
            &errors,
            "carries link symbol \"g\", reference names \"no_such_symbol\""
        ),
        "{errors:?}"
    );

    let mut renamed = honest.clone();
    let g = renamed.function_by_name("g").unwrap().id;
    renamed.function_by_id_mut(g).unwrap().name = "no_such_symbol".to_string();
    assert_call_only_faith_floor(&renamed);
    let errors =
        validate_linked_module(&renamed, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(
        call_refused(
            &errors,
            "no function in the dependency carries symbol \"no_such_symbol\""
        ),
        "{errors:?}"
    );
}

#[test]
fn c12_backed_by_only_producer_rows_are_authenticated_separately() {
    let dep = mixed_dependency(3);
    let set = ModuleSet::new([&dep]);
    let (mut root, ids) = mixed_importer(&dep);
    root.proof_obligations.clear();
    root.proof_certificates.clear();
    root.function_by_id_mut(ids.addmul).unwrap().summary = Some(
        binary_contract()
            .proved()
            .backed_by(ExternRef::new(ids.clean_row, ADDMUL).relying_on(ProofId::new(1))),
    );
    assert_eq!(root.imports.len(), 2);
    assert_eq!(root.imports[0].digest, root.imports[1].digest);
    let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    assert!(report.is_ok(), "{:?}", report.errors());
    assert_eq!(report.authenticated_imports().unwrap().len(), 2);
    assert_eq!(
        report
            .authenticated()
            .unwrap()
            .authenticated_backed_by()
            .count(),
        2
    );

    let mut single = root.clone();
    single.imports.truncate(1);
    single.function_by_id_mut(ids.addmul).unwrap().summary = Some(
        binary_contract()
            .proved()
            .backed_by(ExternRef::new(ids.rust_row, ADDMUL).relying_on(ProofId::new(1))),
    );
    let errors =
        validate_linked_module(&single, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(
        detail_contains(&errors, "backed_by", "produced by clean"),
        "{errors:?}"
    );
}
