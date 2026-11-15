// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// WS5.3b / F-090 (gate 9): the validator's rules over a module completeness
// claim (`Module.completeness`), and the linked walk's `ImportIncomplete`.
//
//   * `UnloweredRowNamesDefinition` — a `Partial` row may not name a bodied
//     function of the module (negative twin of the positive fixture in
//     `trust-ir-conformance/tests/module_completeness.rs`); a bodyless
//     declaration or an unknown symbol is legal;
//   * `DuplicateUnloweredRow` — rows are keyed by link symbol;
//   * `EmptyPartialClaim` — `Partial([])` is `Complete` spelled a second way;
//   * `ImportIncomplete` — a proof-bearing site (`backed_by`, inheritance)
//     may not cite a dependency that claims to be partial; a CALL-only edge
//     into one is not this error.
//
// Each refusal has its repaired control.

use trust_ir::clean_expr_lowering::contract::contract_clean_cic_certificate;
use trust_ir::proof::{
    ObligationKind, ProofCertificate, ProofEvidence, ProofFormula, ProofObligation, ProofStatus,
    RejectingModuleProofAuthority,
};
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{FuncId, ImportId, ProofId};
use trust_ir::{
    Endianness, ExternRef, Function, FunctionSummary, Module, ModuleCompleteness, ModuleImport,
    Producer, TargetInfo, UnloweredRow,
};
use trust_ir_build::{ModuleBuilder, ValidationError, validate_linked_module, validate_module};

fn target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    }
}

fn row(symbol: &str) -> UnloweredRow {
    UnloweredRow {
        symbol: symbol.into(),
        display_path: None,
        reason: "unsupported shape".into(),
    }
}

/// `fn f(x: i64) -> i64 { x + 1 }` (bodied) beside the bodyless declaration
/// `g`, with `claim`.
fn module_with(claim: Option<ModuleCompleteness>) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("m", target());
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
    mb.declare_function("g", ft);
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    m.completeness = claim;
    m
}

// ---------------------------------------------------------------------------
// validate_module rules
// ---------------------------------------------------------------------------

#[test]
fn a_partial_row_may_name_a_declaration_or_nothing_but_never_a_definition() {
    // Control: a row for the bodyless `g` and a row for a symbol the module
    // has nothing of.
    let ok = module_with(Some(ModuleCompleteness::Partial(vec![row("g"), row("h")])));
    assert!(
        validate_module(&ok).is_empty(),
        "{:?}",
        validate_module(&ok)
    );

    // Negative twin: the same claim also naming the bodied `f`.
    let twin = module_with(Some(ModuleCompleteness::Partial(vec![
        row("g"),
        row("f"),
        row("h"),
    ])));
    let errors = validate_module(&twin);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::UnloweredRowNamesDefinition { symbol, function: 0 } if symbol == "f"
        )),
        "{errors:?}"
    );
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(errors[0].to_string().contains("function #0 defines it"));

    // `None` and `Complete` have no rows to check.
    assert!(validate_module(&module_with(None)).is_empty());
    assert!(validate_module(&module_with(Some(ModuleCompleteness::Complete))).is_empty());
}

#[test]
fn duplicate_unlowered_rows_are_refused() {
    let twin = module_with(Some(ModuleCompleteness::Partial(vec![
        row("g"),
        UnloweredRow {
            display_path: Some("m::g".into()),
            ..row("g")
        },
    ])));
    let errors = validate_module(&twin);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::DuplicateUnloweredRow { symbol } if symbol == "g"
        )),
        "{errors:?}"
    );
    assert_eq!(
        errors.len(),
        1,
        "reported once, for the later row: {errors:?}"
    );
    // Control: one row per symbol.
    let ok = module_with(Some(ModuleCompleteness::Partial(vec![row("g")])));
    assert!(validate_module(&ok).is_empty());
}

#[test]
fn an_empty_partial_claim_is_refused() {
    let twin = module_with(Some(ModuleCompleteness::Partial(vec![])));
    let errors = validate_module(&twin);
    assert_eq!(errors, vec![ValidationError::EmptyPartialClaim]);
    assert!(errors[0].to_string().contains("must claim `Complete`"));
    // Control: the one spelling of "nothing unlowered".
    assert!(validate_module(&module_with(Some(ModuleCompleteness::Complete))).is_empty());
}

// ---------------------------------------------------------------------------
// linked: ImportIncomplete
// ---------------------------------------------------------------------------

fn clause() -> ProofFormula {
    ProofFormula::smtlib2("(= 1 1)", "Bool")
}

fn contract() -> FunctionSummary {
    FunctionSummary::new()
        .with_params(vec!["x".to_string()])
        .ensuring(clause())
}

/// A dependency defining `f` with a `proved` contract backed by a
/// kernel-certified Postcondition #0, plus the bodyless `g`. The claim is
/// stamped AFTER the importer has recorded the digest: a claimed module has
/// no wire identity until the wire batch, so the row records the digest of
/// the unclaimed content, and the walk must refuse the claim BEFORE it tries
/// to hash the candidate.
fn dependency(claim: Option<ModuleCompleteness>) -> (Module, Module) {
    let mut dep = module_with(None);
    let f = dep.functions[0].id;
    dep.functions[0].summary = Some(contract().proved());
    let obligation = ProofObligation::new(
        ProofId::new(0),
        ObligationKind::Postcondition,
        ProofStatus::Certified,
        "ensures (= 1 1)",
    )
    .with_function(f)
    .with_formula(clause());
    let certificate = contract_clean_cic_certificate(&obligation, "contract-prover")
        .expect("(= 1 1) is genuinely kernel-provable");
    dep.proof_obligations.push(obligation);
    dep.proof_certificates.push(certificate);
    assert!(
        validate_module(&dep).is_empty(),
        "{:?}",
        validate_module(&dep)
    );

    // The importer records the dependency's digest and declares `f`.
    let mut root = Module::new("root");
    root.target_info = Some(target());
    let id = root
        .intern_import(
            ModuleImport::new(dep.name.clone(), dep.stable_digest()).with_producer(Producer::TRust),
        )
        .expect("Module::intern_import: test fixture");
    let ft = root
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut decl = Function::declaration(FuncId::new(0), "f", ft, contract());
    decl.producer = Some(Producer::TRust);
    root.try_add_function(decl)
        .expect("Module::try_add_function: test fixture");
    assert_eq!(id, ImportId::new(0));

    dep.completeness = claim;
    (dep, root)
}

/// A resolver that hands the walk `dep` for every row. `ModuleSet` cannot
/// serve here: it hashes at insertion, and a claimed module has no wire
/// identity yet (`CompletenessClaimUnencodable`).
fn resolver<'a>(dep: &'a Module) -> impl Fn(&ModuleImport) -> Option<&'a Module> + 'a {
    move |_| Some(dep)
}

fn far() -> ExternRef {
    ExternRef::new(ImportId::new(0), "f").relying_on(ProofId::new(0))
}

fn backed(root: &mut Module) {
    root.functions[0].summary = Some(contract().proved().backed_by(far()));
}

fn inheriting(root: &mut Module) {
    let f = root.functions[0].id;
    root.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Discharged,
            "inherited ensures (= 1 1)",
        )
        .with_function(f)
        .with_formula(clause()),
    );
    root.proof_certificates.push(ProofCertificate {
        obligation: ProofId::new(0),
        prover: "compose".to_string(),
        evidence: ProofEvidence::InheritedFromCallee {
            callee: f,
            obligation: ProofId::new(0),
            external: Some(far()),
        },
        assurance: None,
    });
}

fn import_incomplete_at(errors: &[ValidationError], at: &str) -> bool {
    errors.iter().any(|e| {
        matches!(
            e,
            ValidationError::ImportIncomplete { import: 0, site, unlowered }
                if *site == at && unlowered == &["g".to_string()]
        )
    })
}

#[test]
fn a_proof_bearing_site_may_not_cite_a_partial_dependency() {
    let partial = Some(ModuleCompleteness::Partial(vec![row("g")]));
    for (site, wire) in [
        ("backed_by", backed as fn(&mut Module)),
        ("inherited", inheriting),
    ] {
        let (dep, mut root) = dependency(partial.clone());
        wire(&mut root);
        let report = validate_linked_module(&root, &resolver(&dep), &RejectingModuleProofAuthority);
        assert!(
            import_incomplete_at(report.errors(), site),
            "{site}: {:?}",
            report.errors()
        );
        // Refused by the claim's own name, not by the missing binary carrier.
        assert!(
            !report.errors().iter().any(|e| matches!(
                e,
                ValidationError::UnauthenticatedImport { site: "import", .. }
            )),
            "{site}: {:?}",
            report.errors()
        );
        assert!(
            report.errors()[0]
                .to_string()
                .contains("claims to be PARTIAL")
        );

        // Control: the same pair with no claim on the dependency links.
        let (dep, mut root) = dependency(None);
        wire(&mut root);
        let report = validate_linked_module(&root, &resolver(&dep), &RejectingModuleProofAuthority);
        assert!(report.is_ok(), "{site} control: {:?}", report.errors());
    }
}

/// A call-only edge into a partial dependency is not `ImportIncomplete`. It
/// is still refused today — the claimed candidate has no wire identity to
/// authenticate against until the wire batch lands — but by THAT name.
#[test]
fn a_call_only_edge_into_a_partial_dependency_is_not_import_incomplete() {
    let (dep, root) = dependency(Some(ModuleCompleteness::Partial(vec![row("g")])));
    let report = validate_linked_module(&root, &resolver(&dep), &RejectingModuleProofAuthority);
    assert!(
        !report
            .errors()
            .iter()
            .any(|e| matches!(e, ValidationError::ImportIncomplete { .. })),
        "{:?}",
        report.errors()
    );
    assert!(
        report.errors().iter().any(|e| matches!(
            e,
            ValidationError::UnauthenticatedImport { site: "import", detail, .. }
                if detail.contains("Module.completeness")
        )),
        "{:?}",
        report.errors()
    );
    // Control: no claim, the call-only edge links.
    let (dep, root) = dependency(None);
    let report = validate_linked_module(&root, &resolver(&dep), &RejectingModuleProofAuthority);
    assert!(report.is_ok(), "{:?}", report.errors());
}
