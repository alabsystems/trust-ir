// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! WS1.6 (finding F-010): same-module inheritance is admitted with the
//! cross-crate restatement check.
//!
//! THE HOLE. A Rust caller restating a same-module Clean callee's
//! kernel-certified contract through `InheritedFromCallee { external: None }`
//! was `DischargedWithoutCertificate` under every entry point — only
//! `external: Some` rows were ever admitted — and when a capability DID admit
//! it, the local rule related the two rows by nothing but the callee's
//! `FuncId`: a restatement claiming `(= result 12345)`, no formula, another
//! kind, or a row owned by some other function all left `validate_module`'s
//! error list byte-identical. The cross-crate rule refuses exactly these.
//!
//! THE RULE. `validated_authority_refs` admits such a certificate into the
//! `Discharged` tier (never the kernel tier) iff the callee exists, the
//! inherited row is kernel-grounded and scoped to the callee, and the
//! discharged row passes `inheritance_restatement` — the same function the
//! cross-crate `check_inherited` now calls. Any other restatement failure is
//! `LocalInheritanceRestatementMismatch`, whoever else admits the certificate.
//!
//! Tests whose name starts `b2_gap_` are the in-repo ports of the two-language
//! proof program's ratchet rows of the same id (dots spelled `_`); WS8.6 folds
//! them into the conformance ratchet table.

use std::collections::BTreeSet;

use trust_ir::clean_expr_lowering::contract::contract_clean_cic_certificate_in;
use trust_ir::proof::{
    ClauseBinding, ClausePlace, ClauseSort, CoverageAssurance, CoverageBound, ModuleProofAuthority,
    ObligationKind, ObligationSite, ProofAnnotation, ProofCertificate, ProofCertificateRef,
    ProofContext, ProofDigest, ProofEvidence, ProofFormula, ProofObligation, ProofStatus,
    RejectingModuleProofAuthority,
};
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{FuncId, ProofId};
use trust_ir::{
    Endianness, ExternRef, Function, FunctionSummary, Module, ModuleImport, Producer, TargetInfo,
};
use trust_ir_build::{
    ModuleBuilder, ModuleSet, ValidationError, validate_linked_module, validate_module,
    validate_module_report, validate_module_with_authority,
};

const PROVER: &str = "trust_vc-clean-kernel";
const G: usize = 0;
const F: usize = 1;

// ===========================================================================
// fixtures
// ===========================================================================

/// A pinned target: a bodyless cross-crate declaration needs one (the twin
/// below), and the local fixture carries the same one so the two stay twins.
fn target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    }
}

/// `(<text>)` over `result`, bound to the first result slot at sort `Int`.
fn result_int(text: &str) -> ProofFormula {
    let mut formula = ProofFormula::smtlib2(text, "Bool");
    formula.bindings = vec![(
        "result".to_string(),
        ClauseBinding {
            sort: ClauseSort::Int,
            place: ClausePlace::ResultSlot { index: 0 },
        },
    )];
    formula
}

fn ensures() -> ProofFormula {
    result_int("(>= result 0)")
}

fn inherit(discharges: u32, callee: FuncId, inherited: u32) -> ProofCertificate {
    ProofCertificate {
        obligation: ProofId::new(discharges),
        prover: "compose".to_string(),
        evidence: ProofEvidence::InheritedFromCallee {
            callee,
            obligation: ProofId::new(inherited),
            external: None,
        },
        assurance: None,
    }
}

/// The positive fixture:
///
/// ```text
/// fn#0 g() -> u64 { 42 }      Clean   #0 Certified  ensures (>= result 0)  (kernel)
/// fn#1 f() -> u64 { g() }     Rust    #1 Discharged ensures (>= result 0)  scoped to g,
///                                        InheritedFromCallee { g, #0, external: None }
/// ```
///
/// #1 is the Rust caller's restatement of the callee contract it relies on.
fn fixture() -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("ws1_6_local_inheritance", target());
    let ft = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("g", ft);
    fb.set_producer(Producer::Clean);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let v = fb.uconst(Ty::U64, 42);
    fb.ret(vec![v]);
    let g = fb.build();
    let mut fb = mb.function("f", ft);
    fb.set_producer(Producer::TRust);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let r = fb.call(g, vec![]);
    fb.ret(vec![r]);
    fb.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    m.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Certified,
            "ensures clause 0 of 'g'",
        )
        .with_function(g)
        .with_formula(ensures()),
    );
    let kernel = contract_clean_cic_certificate_in(&m, &m.proof_obligations[0], PROVER)
        .expect("a bound nonneg clause over a u64 result is mintable");
    m.proof_certificates.push(kernel);
    m.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(1),
            ObligationKind::Postcondition,
            ProofStatus::Discharged,
            "f relies on ensures clause 0 of 'g'",
        )
        .with_function(g)
        .with_formula(ensures()),
    );
    m.proof_certificates.push(inherit(1, g, 0));
    m
}

fn g(m: &Module) -> FuncId {
    m.functions[G].id
}

/// A consumer capability that replays exactly the listed certificates — the
/// shape of the archive's `ReplayStandIn`. Proves nothing.
struct AdmitExact(BTreeSet<ProofCertificateRef>);

impl ModuleProofAuthority for AdmitExact {
    fn replays_authority(
        &self,
        _module: &Module,
        obligation: &ProofObligation,
        certificate: &ProofCertificate,
    ) -> bool {
        certificate.obligation == obligation.id && self.0.contains(&certificate.lineage_ref())
    }
}

/// A capability admitting every inheritance certificate of `m`.
fn admitting_inheritance(m: &Module) -> AdmitExact {
    AdmitExact(
        m.proof_certificates
            .iter()
            .filter(|c| matches!(c.evidence, ProofEvidence::InheritedFromCallee { .. }))
            .map(ProofCertificate::lineage_ref)
            .collect(),
    )
}

fn linked_alone(m: &Module) -> Vec<ValidationError> {
    let none = ModuleSet::new(std::iter::empty::<&Module>());
    validate_linked_module(m, &none, &RejectingModuleProofAuthority).into_errors()
}

fn mismatch_on(errors: &[ValidationError], obligation: u32, needle: &str) -> bool {
    errors.iter().any(|e| {
        matches!(
            e,
            ValidationError::LocalInheritanceRestatementMismatch { certificate_obligation, detail }
                if *certificate_obligation == obligation && detail.contains(needle)
        )
    })
}

fn any_mismatch(errors: &[ValidationError]) -> bool {
    errors.iter().any(|e| {
        matches!(
            e,
            ValidationError::LocalInheritanceRestatementMismatch { .. }
        )
    })
}

/// Exactly the two errors a refused restatement of #1 produces: the named
/// mismatch carrying `needle`, and #1 left without authority.
fn assert_refused_restatement(errors: &[ValidationError], needle: &str) {
    assert_eq!(errors.len(), 2, "{errors:?}");
    assert!(mismatch_on(errors, 1, needle), "{errors:?}");
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::DischargedWithoutCertificate { obligation: 1 }
        )),
        "{errors:?}"
    );
}

/// The four single-field mutations of the restatement #1, each with the
/// detail that names it.
fn restatement_twins(base: &Module) -> Vec<(&'static str, Module, &'static str)> {
    let mut formula = base.clone();
    formula.proof_obligations[1].formula = Some(result_int("(= result 12345)"));
    let mut no_formula = base.clone();
    no_formula.proof_obligations[1].formula = None;
    let mut kind = base.clone();
    kind.proof_obligations[1].kind = ObligationKind::MemorySafety;
    let mut owner = base.clone();
    owner.proof_obligations[1].function = Some(base.functions[F].id);
    vec![
        (
            "formula := (= result 12345)",
            formula,
            "local restatement obligation #1 does not restate far obligation #0's formula",
        ),
        (
            "formula := None",
            no_formula,
            "local restatement obligation #1 carries no formula",
        ),
        (
            "kind := MemorySafety",
            kind,
            "local restatement obligation #1 has kind memory_safety, far obligation #0 has \
             kind postcondition",
        ),
        (
            "owner := f (the caller)",
            owner,
            "local restatement obligation #1 is scoped to Some(1), not the callee declaration #0",
        ),
    ]
}

// ===========================================================================
// positive
// ===========================================================================

#[test]
fn a_restatement_of_a_kernel_certified_callee_row_validates_everywhere() {
    let m = fixture();
    assert_eq!(validate_module(&m), vec![]);
    assert_eq!(
        validate_module_with_authority(&m, &RejectingModuleProofAuthority),
        vec![]
    );
    assert_eq!(linked_alone(&m), vec![]);
    // Only the Clean callee's row is kernel-tier; the admitted restatement is
    // Discharged-tier and is not reported as replayed kernel authority.
    assert_eq!(
        validate_module_report(&m).replayed_certificate_refs(),
        Some(&BTreeSet::from([m.proof_certificates[0].lineage_ref()]))
    );
}

/// GAP flip `b2.gap.local_inheritance_not_admitted_without_capability`: the
/// same-module restatement was `DischargedWithoutCertificate` under
/// `validate_module` AND `validate_linked_module(no imports, Rejecting)`.
#[test]
fn b2_gap_local_inheritance_not_admitted_without_capability() {
    let m = fixture();
    for (layer, errors) in [
        ("validate_module", validate_module(&m)),
        ("validate_linked_module", linked_alone(&m)),
    ] {
        assert!(
            !errors
                .iter()
                .any(|e| matches!(e, ValidationError::DischargedWithoutCertificate { .. })),
            "{layer} must admit the local inheritance with no capability: {errors:?}"
        );
        assert_eq!(errors, vec![], "{layer}");
    }
}

// ===========================================================================
// negative twins
// ===========================================================================

#[test]
fn a_restatement_that_changes_the_formula_is_refused() {
    let twins = restatement_twins(&fixture());
    let (_, m, needle) = &twins[0];
    assert_refused_restatement(&validate_module(m), needle);
}

#[test]
fn a_restatement_with_no_formula_is_refused() {
    let twins = restatement_twins(&fixture());
    let (_, m, needle) = &twins[1];
    assert_refused_restatement(&validate_module(m), needle);
}

#[test]
fn a_restatement_of_another_kind_is_refused() {
    let twins = restatement_twins(&fixture());
    let (_, m, needle) = &twins[2];
    assert_refused_restatement(&validate_module(m), needle);
}

#[test]
fn a_restatement_re_owned_to_the_caller_is_refused() {
    let twins = restatement_twins(&fixture());
    let (_, m, needle) = &twins[3];
    assert_refused_restatement(&validate_module(m), needle);
}

/// No chain: #2 inherits #1, which is itself Discharged by an (admitted)
/// inheritance. #1 is not kernel-tier, so #2 is refused under the existing
/// named reason, and #1 stays admitted.
#[test]
fn an_inheritance_of_an_inherited_row_is_refused_as_not_kernel_grounded() {
    let mut m = fixture();
    let g = g(&m);
    m.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(2),
            ObligationKind::Postcondition,
            ProofStatus::Discharged,
            "second-hand restatement",
        )
        .with_function(g)
        .with_formula(ensures()),
    );
    m.proof_certificates.push(inherit(2, g, 1));
    let errors = validate_module(&m);
    assert_eq!(errors.len(), 2, "{errors:?}");
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::InheritedProofNotDischarged {
                obligation: 2,
                callee: 0,
                inherited_obligation: 1
            }
        )),
        "{errors:?}"
    );
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::DischargedWithoutCertificate { obligation: 2 }
        )),
        "{errors:?}"
    );
    assert!(
        !any_mismatch(&errors),
        "the chain has its own name: {errors:?}"
    );
}

/// A capability that replays the inheritance certificate does not make a
/// mismatched restatement true: the named refusal stands under the authority
/// tier too.
#[test]
fn a_capability_does_not_rescue_a_mismatched_restatement() {
    for (label, m, needle) in restatement_twins(&fixture()) {
        let errors = validate_module_with_authority(&m, &admitting_inheritance(&m));
        assert_eq!(errors.len(), 1, "{label}: {errors:?}");
        assert!(mismatch_on(&errors, 1, needle), "{label}: {errors:?}");
    }
}

/// GAP flip `b2.gap.local_inheritance_restatement_unchecked`: each single
/// change to the restatement left `validate_module`'s error list identical to
/// the unmutated baseline's, and a capability admitting the row got `[]`.
#[test]
fn b2_gap_local_inheritance_restatement_unchecked() {
    let base = fixture();
    let baseline = validate_module(&base);
    for (label, m, needle) in restatement_twins(&base) {
        let structural = validate_module(&m);
        assert_ne!(structural, baseline, "{label}");
        assert!(
            mismatch_on(&structural, 1, needle),
            "{label}: {structural:?}"
        );
        let with_capability = validate_module_with_authority(&m, &admitting_inheritance(&m));
        assert!(
            mismatch_on(&with_capability, 1, needle),
            "{label}: {with_capability:?}"
        );
    }
}

// ===========================================================================
// mutation controls
// ===========================================================================

/// The admitted row is `Discharged`-tier authority, which is not `ProofRef`
/// currency: a `ProofRef` to it is still unresolved, while the same
/// annotation citing the kernel row resolves.
#[test]
fn a_proof_ref_to_the_admitted_row_is_still_unresolved() {
    let cite = |id: u32| {
        let mut m = fixture();
        m.functions[G].proofs = vec![
            ProofAnnotation::Pure,
            ProofAnnotation::ProofRef(ProofId::new(id)),
        ];
        validate_module(&m)
    };
    assert_eq!(cite(0), vec![], "the kernel row backs the ProofRef");
    let errors = cite(1);
    assert_eq!(
        errors,
        vec![ValidationError::ProofRefUnresolved {
            function: 0,
            obligation: 1,
            missing: false,
        }]
    );
}

/// The certified callee row cannot be unscoped: a same-module inheritance must
/// cite a row its callee owns, so an unscoped far row is named.
#[test]
fn an_unscoped_far_row_is_refused() {
    let mut m = fixture();
    // `(= 1 1)` re-checks without a binding, so the far row stays kernel-tier
    // while scoped to nothing.
    let clause = ProofFormula::smtlib2("(= 1 1)", "Bool");
    m.proof_certificates.clear();
    m.proof_obligations[0].function = None;
    m.proof_obligations[0].formula = Some(clause.clone());
    m.proof_obligations[1].formula = Some(clause);
    let kernel = contract_clean_cic_certificate_in(&m, &m.proof_obligations[0], PROVER)
        .expect("(= 1 1) is kernel-provable");
    m.proof_certificates.push(kernel);
    let g = g(&m);
    m.proof_certificates.push(inherit(1, g, 0));
    assert_refused_restatement(&validate_module(&m), "is scoped to no function");
}

// ---------------------------------------------------------------------------
// the cross-crate twin keeps `check_inherited`
// ---------------------------------------------------------------------------

/// The fixture split across a crate edge: the dependency defines `g` with its
/// kernel row #0; the root declares `g` and restates #0 as its #0 through
/// `external: Some`.
fn cross_crate() -> (Module, Module) {
    let full = fixture();
    let mut dep = full.clone();
    dep.name = "ws1_6_dep".to_string();
    dep.functions.truncate(1);
    dep.proof_obligations.truncate(1);
    dep.proof_certificates.truncate(1);
    assert_eq!(validate_module(&dep), vec![]);

    let mut root = Module::new("ws1_6_root");
    root.target_info = dep.target_info.clone();
    let import = root
        .intern_import(
            ModuleImport::new(dep.name.clone(), dep.stable_digest()).with_producer(Producer::Clean),
        )
        .expect("Module::intern_import: test fixture");
    let ft = root
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut decl = Function::declaration(FuncId::new(0), "g", ft, FunctionSummary::new());
    decl.producer = Some(Producer::Clean);
    root.try_add_function(decl)
        .expect("Module::try_add_function: test fixture");
    let mut restatement = full.proof_obligations[1].clone();
    restatement.id = ProofId::new(0);
    restatement.function = Some(FuncId::new(0));
    root.proof_obligations.push(restatement);
    root.proof_certificates.push(ProofCertificate {
        obligation: ProofId::new(0),
        prover: "compose".to_string(),
        evidence: ProofEvidence::InheritedFromCallee {
            callee: FuncId::new(0),
            obligation: ProofId::new(0),
            external: Some(ExternRef::new(import, "g").relying_on(ProofId::new(0))),
        },
        assurance: None,
    });
    (dep, root)
}

/// Mutation control: the cross-crate edge still takes `check_inherited`, and
/// its refusal details are byte-identical to the pre-WS1.6 strings (the
/// restatement core moved, its words did not). The local rule never routes an
/// `external: Some` certificate.
#[test]
fn the_cross_crate_twin_still_takes_check_inherited_byte_identically() {
    let (dep, root) = cross_crate();
    let set = ModuleSet::new([&dep]);
    let linked =
        |m: &Module| validate_linked_module(m, &set, &RejectingModuleProofAuthority).into_errors();
    assert_eq!(linked(&root), vec![]);

    let refused = |m: &Module| -> Vec<String> {
        let errors = linked(m);
        assert!(!any_mismatch(&errors), "{errors:?}");
        errors
            .iter()
            .filter_map(|e| match e {
                ValidationError::UnauthenticatedImport {
                    site: "inherited",
                    detail,
                    ..
                } => Some(detail.clone()),
                _ => None,
            })
            .collect()
    };
    let mut m = root.clone();
    m.proof_obligations[0].formula = Some(result_int("(= result 12345)"));
    assert_eq!(
        refused(&m),
        ["local restatement obligation #0 does not restate far obligation #0's formula"]
    );
    let mut m = root.clone();
    m.proof_obligations[0].formula = None;
    assert_eq!(
        refused(&m),
        [
            "local restatement obligation #0 carries no formula; an inherited claim must be \
             stated, not implied"
        ]
    );
    let mut m = root.clone();
    m.proof_obligations[0].kind = ObligationKind::MemorySafety;
    assert_eq!(
        refused(&m),
        [
            "local restatement obligation #0 has kind memory_safety, far obligation #0 has kind \
             postcondition"
        ]
    );
    let mut m = root.clone();
    m.proof_obligations[0].function = None;
    assert_eq!(
        refused(&m),
        ["local restatement obligation #0 is scoped to None, not the callee declaration #0"]
    );
}

// ---------------------------------------------------------------------------
// review: adversarial inputs the first cut did not pin
// ---------------------------------------------------------------------------

/// Review (WS1.6): a restatement cannot MOVE the inherited claim onto another
/// check. Cross-crate the restatement sits on a body-less declaration and can
/// carry no site; here the callee has a body, so a `site` names one of its
/// checks, and a verifier backs a sited row only with the condition generated
/// there. The first cut admitted a restatement of an UNSITED row sited on
/// `g`'s first instruction.
#[test]
fn a_restatement_sited_on_another_check_is_refused() {
    let mut m = fixture();
    let g = g(&m);
    let block = m.functions[G].blocks[0].id;
    m.proof_obligations[1].site = Some(ObligationSite::new(g, block, 0));
    assert_refused_restatement(
        &validate_module(&m),
        "local restatement obligation #1 is sited at fn#0/bb0#0, but far obligation #0 is \
         unsited; an inheritance restates a claim, it cannot move it onto another check",
    );
    // A capability does not rescue it either.
    let errors = validate_module_with_authority(&m, &admitting_inheritance(&m));
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(mismatch_on(&errors, 1, "cannot move it"), "{errors:?}");
}

/// Mutation control for the site rule: an unsited restatement of a sited row
/// is admitted (it claims less, never more), and so is one sited exactly
/// where the inherited row is.
#[test]
fn a_restatement_unsited_or_sited_like_the_inherited_row_validates() {
    let sited = |restatement_sited: bool| {
        let mut m = fixture();
        let g = g(&m);
        let site = ObligationSite::new(g, m.functions[G].blocks[0].id, 0);
        m.proof_certificates.clear();
        m.proof_obligations[0].site = Some(site);
        let kernel = contract_clean_cic_certificate_in(&m, &m.proof_obligations[0], PROVER)
            .expect("the sited clause is still mintable");
        m.proof_certificates.push(kernel);
        m.proof_certificates.push(inherit(1, g, 0));
        if restatement_sited {
            m.proof_obligations[1].site = Some(site);
        }
        validate_module(&m)
    };
    assert_eq!(sited(false), vec![], "unsited restatement of a sited row");
    assert_eq!(
        sited(true),
        vec![],
        "restatement sited like the inherited row"
    );
}

fn assurance(bound: CoverageBound) -> Option<CoverageAssurance> {
    Some(CoverageAssurance {
        bound,
        request_digest: ProofDigest::sha256_domain("ws1_6.review.request", b"r"),
    })
}

/// Review (WS1.6): linked rule L9 holds on the same-module edge too — an
/// inheritance certificate claiming `Unbounded` coverage over a row whose
/// only certificate records a depth-1 bounded discharge was admitted by the
/// first cut, so coverage GREW across the edge (cross-crate this is
/// `ImportCoverageBelowClaim`).
#[test]
fn an_inheritance_claiming_more_coverage_than_it_inherits_is_refused() {
    let mut m = fixture();
    m.proof_certificates[0].assurance = assurance(CoverageBound::UnwindBounded { depth: 1 });
    m.proof_certificates[1].assurance = assurance(CoverageBound::Unbounded);
    assert_refused_restatement(
        &validate_module(&m),
        "the inheritance certificate claims coverage Unbounded, but far obligation #0 records \
         [UnwindBounded { depth: 1 }]; coverage does not grow across an inheritance edge",
    );
}

/// Mutation control for the coverage rule: claiming exactly what is recorded,
/// less than it, or no grade at all is admitted; so is any claim over a far
/// row that records no bound (the grandfather state L9 admits too).
#[test]
fn an_inheritance_claiming_no_more_coverage_than_it_inherits_validates() {
    let with = |far: Option<CoverageBound>, local: Option<CoverageBound>| {
        let mut m = fixture();
        m.proof_certificates[0].assurance = far.and_then(assurance);
        m.proof_certificates[1].assurance = local.and_then(assurance);
        validate_module(&m)
    };
    let depth = |depth| CoverageBound::UnwindBounded { depth };
    for (far, local) in [
        (Some(depth(4)), Some(depth(4))),
        (Some(depth(4)), Some(depth(2))),
        (Some(CoverageBound::Unbounded), Some(depth(2))),
        (Some(depth(1)), None),
        (None, Some(CoverageBound::Unbounded)),
    ] {
        assert_eq!(with(far, local), vec![], "far {far:?}, local {local:?}");
    }
}

/// The admitted row is not proof-context currency either: a caller cannot
/// ASSUME it at the call, while the kernel row it restates can be assumed.
#[test]
fn a_proof_context_cannot_assume_the_admitted_row() {
    let assume = |id: u32| {
        let mut m = fixture();
        m.functions[F].blocks[0].body[0].proof_context = Some(ProofContext {
            assumes: vec![ProofId::new(id)],
            establishes: vec![],
        });
        validate_module(&m)
    };
    assert_eq!(assume(0), vec![], "the kernel row may be assumed");
    assert_eq!(
        assume(1),
        vec![ValidationError::ProofContextAssumeNotAuthoritative {
            block: 0,
            obligation: 1,
        }]
    );
}

/// No chain across a crate edge either: an importer inheriting a dependency's
/// locally ADMITTED restatement is refused, because the dependency's exported
/// ground is its kernel tier plus its AUTHENTICATED cross-crate inheritances —
/// never the Discharged tier a same-module inheritance feeds. Citing the
/// kernel row the restatement restates is admitted.
#[test]
fn an_importer_cannot_inherit_a_locally_admitted_restatement() {
    let mut dep = fixture();
    dep.name = "ws1_6_dep_with_restatement".to_string();
    assert_eq!(validate_module(&dep), vec![]);
    let (_, template) = cross_crate();
    let citing = |far: u32| {
        let mut root = template.clone();
        root.imports.clear();
        let import = root
            .intern_import(
                ModuleImport::new(dep.name.clone(), dep.stable_digest())
                    .with_producer(Producer::Clean),
            )
            .expect("Module::intern_import: test fixture");
        root.proof_certificates[0].evidence = ProofEvidence::InheritedFromCallee {
            callee: FuncId::new(0),
            obligation: ProofId::new(0),
            external: Some(ExternRef::new(import, "g").relying_on(ProofId::new(far))),
        };
        let set = ModuleSet::new([&dep]);
        validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors()
    };
    assert_eq!(citing(0), vec![], "the dependency's kernel row");
    let errors = citing(1);
    assert_eq!(errors.len(), 2, "{errors:?}");
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::UnauthenticatedImport { site: "inherited", detail, .. }
                if detail.starts_with("far obligation #1 is discharged in the dependency but \
                                       not grounded there")
        )),
        "{errors:?}"
    );
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::DischargedWithoutCertificate { obligation: 0 }
        )),
        "{errors:?}"
    );
}
