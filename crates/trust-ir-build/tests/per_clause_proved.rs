// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// WS1.3 — `proved` is PER-CLAUSE (finding F-002; the cross-crate face, F-003,
// is in `linked_import_authentication.rs` and at the end of this file).
//
// THE HOLE. For a definition, `validate_function_summary` COUNTED
// Discharged/Certified Precondition/Postcondition/Termination rows scoped to
// the function and compared the counts with the clause lists; no row's
// `formula` was ever read. So `fn f() -> u64 { 7 }` with `proved ensures
// (= result 42)` validated under every entry point when its only backing row
// was a genuinely kernel-rechecked `(>= result 0)` (audit c02 R1).
//
// THE RULE. For a `proved` definition every clause of every role must be
// matched by a Discharged/Certified row of the role's kind
// (Precondition↔requires, Postcondition↔ensures, Termination↔decreases),
// scoped to the function, whose `formula` EQUALS the clause — schema,
// payload, smtlib, sort and bindings alike. A formula-less row matches
// nothing. A role's clauses are a set: a duplicate is refused by name.
//
// Every negative twin below is ONE mutation of a validating fixture and
// asserts its SPECIFIC refusal.

use trust_ir::clean_expr_lowering::contract::contract_clean_cic_certificate_in;
use trust_ir::proof::{
    ClauseBinding, ClausePlace, ClauseSort, CoverageAssurance, CoverageBound, ModuleProofAuthority,
    ObligationKind, ProofCertificate, ProofCertificateRef, ProofDigest, ProofEvidence,
    ProofFormula, ProofObligation, ProofStatus, RejectingModuleProofAuthority,
};
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{FuncId, ProofId};
use trust_ir::{
    Endianness, ExternRef, Function, FunctionSummary, Module, ModuleImport, Producer, TargetInfo,
};
use trust_ir_build::{
    ModuleBuilder, ModuleSet, ValidationError, validate_linked_module, validate_module,
    validate_module_for_codegen, validate_module_report, validate_module_with_authority,
};

const PROVER: &str = "ws1_3-clean-kernel";
const NONNEG: &str = "(>= result 0)";
const FALSE_CLAIM: &str = "(= result 42)";
/// The tail every per-clause refusal carries.
const NO_ROW_TAIL: &str = "row scoped to this function stating exactly this clause (rows \
                           stating other clauses do not count)";

// ===========================================================================
// fixtures
// ===========================================================================

fn target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    }
}

/// A clause over `result`, bound to result slot 0 at `sort`.
fn result_clause(text: &str, sort: ClauseSort) -> ProofFormula {
    let mut formula = ProofFormula::smtlib2(text, "Bool");
    formula.bindings = vec![(
        "result".to_string(),
        ClauseBinding {
            sort,
            place: ClausePlace::ResultSlot { index: 0 },
        },
    )];
    formula
}

fn nonneg() -> ProofFormula {
    result_clause(NONNEG, ClauseSort::Int)
}

fn false_claim() -> ProofFormula {
    result_clause(FALSE_CLAIM, ClauseSort::Int)
}

/// A closed literal clause the kernel discharges on its own.
fn literal() -> ProofFormula {
    ProofFormula::smtlib2("(= 1 1)", "Bool")
}

/// `fn f() -> u64 { 7 }` (producer TRust) with a `proved` summary ensuring
/// `ensures`, and one kernel-CERTIFIED Postcondition per entry of `rows`
/// (ids 0, 1, …), scoped to `f`, stating that formula — each with a
/// `CleanCic` certificate minted through the module-bound entry point.
fn seven(name: &str, ensures: Vec<ProofFormula>, rows: Vec<ProofFormula>) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info(name, target());
    mb.set_default_producer(Producer::TRust);
    let ft = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let v = fb.uconst(Ty::U64, 7);
    fb.ret(vec![v]);
    let f = fb.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    let mut summary = FunctionSummary::new();
    summary.ensures = ensures;
    m.functions[0].summary = Some(summary.proved());
    for (index, formula) in rows.into_iter().enumerate() {
        let obligation = ProofObligation::new(
            ProofId::new(index as u32),
            ObligationKind::Postcondition,
            ProofStatus::Certified,
            format!("ensures row {index}"),
        )
        .with_function(f)
        .with_formula(formula);
        m.proof_obligations.push(obligation);
        let certificate =
            contract_clean_cic_certificate_in(&m, &m.proof_obligations[index], PROVER)
                .expect("the kernel genuinely discharges every backing formula used here");
        m.proof_certificates.push(certificate);
    }
    m
}

fn summary_details(errors: &[ValidationError]) -> Vec<String> {
    errors
        .iter()
        .filter_map(|error| match error {
            ValidationError::InvalidFunctionSummary { detail, .. } => Some(detail.clone()),
            _ => None,
        })
        .collect()
}

/// `role clause index `text`` has no backing row of `kind` — the exact
/// per-clause refusal.
fn no_row(role: &str, index: usize, text: &str, kind: &str) -> String {
    format!("{role} clause {index} `{text}` has no Discharged/Certified {kind} {NO_ROW_TAIL}")
}

fn assert_refused_exactly(errors: &[ValidationError], expected: &[String]) {
    let details = summary_details(errors);
    assert_eq!(
        details, expected,
        "the summary refusals must be exactly these: {errors:?}"
    );
}

/// Admits exactly one certificate by lineage reference — a consumer that
/// re-established one solver verdict in-process (capability tier).
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

// ===========================================================================
// positive fixtures
// ===========================================================================

#[test]
fn a_certified_row_stating_the_clause_backs_it() {
    let m = seven("ws1_3_pos", vec![nonneg()], vec![nonneg()]);
    assert!(validate_module(&m).is_empty(), "{:?}", validate_module(&m));
    assert!(validate_module_with_authority(&m, &RejectingModuleProofAuthority).is_empty());
    assert_eq!(
        validate_module_report(&m)
            .replayed_certificate_refs()
            .map(|refs| refs.len()),
        Some(1),
        "the backing row really is kernel-replayed"
    );
}

#[test]
fn two_distinct_clauses_each_backed_by_its_own_row() {
    let m = seven(
        "ws1_3_two",
        vec![nonneg(), literal()],
        vec![nonneg(), literal()],
    );
    assert!(validate_module(&m).is_empty(), "{:?}", validate_module(&m));
    // Row order is irrelevant: matching is by formula, not position.
    let swapped = seven(
        "ws1_3_two",
        vec![nonneg(), literal()],
        vec![literal(), nonneg()],
    );
    assert!(validate_module(&swapped).is_empty());
}

// ===========================================================================
// negative twins
// ===========================================================================

/// Audit c02 R1 (and the b2 kernel-tier row): the ONE change is the summary's
/// ensures text. The backing row and its kernel certificate are untouched.
#[test]
fn verify_c02_r1_a_false_clause_beside_a_certified_row_is_refused() {
    let base = seven("ws1_3_c02", vec![nonneg()], vec![nonneg()]);
    assert!(validate_module(&base).is_empty());
    let mutant = seven("ws1_3_c02", vec![false_claim()], vec![nonneg()]);
    assert_eq!(base.proof_obligations, mutant.proof_obligations);
    assert_eq!(base.proof_certificates, mutant.proof_certificates);

    let expected = [no_row("ensures", 0, FALSE_CLAIM, "Postcondition")];
    assert_refused_exactly(&validate_module(&mutant), &expected);
    assert_refused_exactly(
        &validate_module_with_authority(&mutant, &RejectingModuleProofAuthority),
        &expected,
    );
    assert_refused_exactly(&validate_module_for_codegen(&mutant), &expected);
    let report = validate_module_report(&mutant);
    assert!(!report.is_ok());
    assert_refused_exactly(report.errors(), &expected);
    let empty = ModuleSet::new([]);
    assert_refused_exactly(
        validate_linked_module(&mutant, &empty, &RejectingModuleProofAuthority).errors(),
        &expected,
    );
}

#[test]
fn duplicate_clauses_in_one_role_are_refused() {
    let m = seven("ws1_3_dup", vec![nonneg(), nonneg()], vec![nonneg()]);
    // Refused as a duplicate — not as an unbacked clause: a restated clause
    // says nothing new, so it needs no second row, and it is never accepted.
    assert_refused_exactly(
        &validate_module(&m),
        &["ensures clause 1 duplicates clause 0".to_string()],
    );
}

#[test]
fn one_row_cannot_back_two_distinct_clauses() {
    let m = seven("ws1_3_one_row", vec![nonneg(), literal()], vec![nonneg()]);
    assert_refused_exactly(
        &validate_module(&m),
        &[no_row("ensures", 1, "(= 1 1)", "Postcondition")],
    );
}

/// A Discharged row the supplied capability genuinely replays, but which
/// states no formula, backs nothing. Its formula-carrying twin, under the
/// same capability, backs the clause — the rule reads the statement, and the
/// row's authority stays the separate rule it always was.
#[test]
fn a_formula_less_capability_admitted_row_backs_nothing() {
    let build = |formula: Option<ProofFormula>| {
        let mut m = seven("ws1_3_capability", vec![nonneg()], vec![]);
        let f = m.functions[0].id;
        let mut row = ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Discharged,
            "ensures clause 0 of 'f': (>= result 0)",
        )
        .with_function(f);
        row.formula = formula;
        m.proof_obligations.push(row);
        m.proof_certificates.push(ProofCertificate {
            obligation: ProofId::new(0),
            prover: "ay-bvblast".to_string(),
            evidence: ProofEvidence::SmtProof(b"(unsat)".to_vec()),
            assurance: None,
        });
        let reference = m.proof_certificates[0].lineage_ref();
        (m, reference)
    };

    let (formula_less, reference) = build(None);
    let errors = validate_module_with_authority(&formula_less, &AdmitExact(reference));
    assert_refused_exactly(&errors, &[no_row("ensures", 0, NONNEG, "Postcondition")]);
    assert_eq!(
        errors.len(),
        1,
        "the row's authority is replayed; only the summary is refused: {errors:?}"
    );

    let (stated, reference) = build(Some(nonneg()));
    let errors = validate_module_with_authority(&stated, &AdmitExact(reference));
    assert!(errors.is_empty(), "{errors:?}");
}

#[test]
fn a_row_of_another_kind_status_or_function_backs_nothing() {
    let refusal = [no_row("ensures", 0, NONNEG, "Postcondition")];
    let honest = || {
        let mut m = seven("ws1_3_shape", vec![nonneg()], vec![]);
        let f = m.functions[0].id;
        m.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(0),
                ObligationKind::Postcondition,
                ProofStatus::Discharged,
                "stated",
            )
            .with_function(f)
            .with_formula(nonneg()),
        );
        m
    };
    assert!(summary_details(&validate_module(&honest())).is_empty());

    // A Precondition stating the ensures clause is about the wrong role.
    let mut wrong_kind = honest();
    wrong_kind.proof_obligations[0].kind = ObligationKind::Precondition;
    assert_refused_exactly(&validate_module(&wrong_kind), &refusal);

    for status in [ProofStatus::Pending, ProofStatus::Trusted] {
        let mut twin = honest();
        twin.proof_obligations[0].status = status;
        assert_refused_exactly(&validate_module(&twin), &refusal);
    }

    let mut unscoped = honest();
    unscoped.proof_obligations[0].function = None;
    assert_refused_exactly(&validate_module(&unscoped), &refusal);

    // A Failed row stating the clause still refutes `proved` outright.
    let mut failed = honest();
    failed.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(1),
            ObligationKind::Postcondition,
            ProofStatus::Failed,
            "refuted",
        )
        .with_function(failed.functions[0].id)
        .with_formula(nonneg()),
    );
    assert!(
        summary_details(&validate_module(&failed))
            .iter()
            .any(|d| d.contains("contract obligation #1, scoped to this function, is Failed"))
    );
}

#[test]
fn requires_and_decreases_are_matched_per_role() {
    let mut mb = ModuleBuilder::new_with_target_info("ws1_3_roles", target());
    let ft = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function("g", ft);
    fb.set_producer(Producer::TRust);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::U64);
    fb.switch_to_block(entry);
    fb.ret(vec![x]);
    let g = fb.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    let pre = ProofFormula::smtlib2("(bvuge x #x0000000000000000)", "Bool");
    let measure = ProofFormula::smtlib2("x", "Int");
    let mut summary = FunctionSummary::new()
        .with_params(vec!["x".to_string()])
        .requiring(pre.clone());
    summary.decreases.push(measure.clone());
    m.functions[0].summary = Some(summary.proved());
    for (id, kind, formula) in [
        (0, ObligationKind::Precondition, pre.clone()),
        (1, ObligationKind::Termination, measure.clone()),
    ] {
        m.proof_obligations.push(
            ProofObligation::new(ProofId::new(id), kind, ProofStatus::Discharged, "stated")
                .with_function(g)
                .with_formula(formula),
        );
    }
    assert!(summary_details(&validate_module(&m)).is_empty());

    // Swap the two rows' kinds: each now states a clause of the OTHER role.
    let mut swapped = m.clone();
    swapped.proof_obligations[0].kind = ObligationKind::Termination;
    swapped.proof_obligations[1].kind = ObligationKind::Precondition;
    assert_refused_exactly(
        &validate_module(&swapped),
        &[
            no_row(
                "requires",
                0,
                "(bvuge x #x0000000000000000)",
                "Precondition",
            ),
            no_row("decreases", 0, "x", "Termination"),
        ],
    );
}

// ===========================================================================
// mutation control
// ===========================================================================

/// Same clause TEXT, different bindings (`Int` vs `BitVec(64)`): the kernel-
/// certified row states the clause at `Int`, the summary at `BitVec(64)` (a
/// faithful reading of a `u64` result, so WS1.2 accepts the summary). The
/// bindings take part in the equality, so the row backs nothing.
#[test]
fn a_row_with_the_same_text_but_other_bindings_backs_nothing() {
    let bitvec = result_clause(NONNEG, ClauseSort::BitVec(64));
    assert_eq!(bitvec.smtlib, nonneg().smtlib);
    assert_ne!(bitvec, nonneg());
    let m = seven("ws1_3_bindings", vec![bitvec], vec![nonneg()]);
    assert_refused_exactly(
        &validate_module(&m),
        &[no_row("ensures", 0, NONNEG, "Postcondition")],
    );
}

// ===========================================================================
// ported GAP ratchet rows (proof program 2026-09-17, part B / verify)
// ===========================================================================

/// Row `b2.gap.no_per_clause_obligation_backref` — FLIPPED. A Discharged
/// Postcondition about an unrelated, trivially true claim no longer backs
/// ensures clause 0; the backref IS the formula.
#[test]
fn b2_gap_no_per_clause_obligation_backref() {
    let mut m = seven("ws1_3_b2", vec![nonneg()], vec![]);
    let f = m.functions[0].id;
    m.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Discharged,
            "ensures clause 0 of 'some other contract entirely'",
        )
        .with_function(f)
        .with_formula(literal()),
    );
    assert_eq!(
        summary_details(&validate_module(&m)),
        vec![no_row("ensures", 0, NONNEG, "Postcondition")]
    );
}

/// Row `b2.gap.kernel_certified_row_backs_an_unrelated_false_clause` —
/// FLIPPED (also the local face of the critic's `crit.misw08` weighting).
/// The only backing row is kernel-Certified and genuinely replayed; the
/// published clause is false of the body; the validator now says so.
#[test]
fn b2_gap_kernel_certified_row_backs_an_unrelated_false_clause() {
    let honest = seven("ws1_3_b2_kernel", vec![nonneg()], vec![nonneg()]);
    assert_eq!(
        validate_module_report(&honest)
            .replayed_certificate_refs()
            .map(|refs| refs.len()),
        Some(1),
        "the row is genuinely kernel-replayed"
    );
    let forged = seven("ws1_3_b2_kernel", vec![false_claim()], vec![nonneg()]);
    // The ONLY error is the summary refusal: the row and its certificate are
    // as valid as before, they just back nothing.
    let errors = validate_module(&forged);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_refused_exactly(
        &errors,
        &[no_row("ensures", 0, FALSE_CLAIM, "Postcondition")],
    );
}

// ===========================================================================
// the cross-crate face (F-003), audit c02 R2
// ===========================================================================

/// An importer declaring `f` and backing its `proved` `summary` by the
/// dependency's obligation `cited`.
fn importer(dep: &Module, summary: FunctionSummary, cited: u32) -> Module {
    let mut m = Module::new("ws1_3_importer");
    m.target_info = Some(target());
    let id = m
        .intern_import(
            ModuleImport::new(dep.name.clone(), dep.stable_digest()).with_producer(Producer::TRust),
        )
        .expect("Module::intern_import: test fixture");
    let ft = m
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let summary = summary
        .proved()
        .backed_by(ExternRef::new(id, "f").relying_on(ProofId::new(cited)));
    let mut f = Function::declaration(FuncId::new(0), "f", ft, summary);
    f.producer = Some(Producer::TRust);
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    m
}

fn ensuring(clauses: Vec<ProofFormula>) -> FunctionSummary {
    let mut summary = FunctionSummary::new();
    summary.ensures = clauses;
    summary
}

#[test]
fn verify_c02_r2_a_dependency_publishing_a_false_proved_clause_backs_nothing() {
    let rejecting = RejectingModuleProofAuthority;

    // Baseline: the honest pair links.
    let dep = seven("ws1_3_dep", vec![nonneg()], vec![nonneg()]);
    let root = importer(&dep, ensuring(vec![nonneg()]), 0);
    let report = validate_linked_module(&root, &ModuleSet::new([&dep]), &rejecting);
    assert!(report.is_ok(), "{:?}", report.errors());

    // The single change, on both sides (restatement must be exact): the
    // dependency publishes `proved ensures (= result 42)` beside the
    // kernel-Certified `(>= result 0)`. The dependency's OWN pass refuses it.
    let lying_dep = seven("ws1_3_dep", vec![false_claim()], vec![nonneg()]);
    let lying_root = importer(&lying_dep, ensuring(vec![false_claim()]), 0);
    let report = validate_linked_module(&lying_root, &ModuleSet::new([&lying_dep]), &rejecting);
    assert!(report.authenticated().is_none());
    let errors = report.into_errors();
    let refusal = no_row("ensures", 0, FALSE_CLAIM, "Postcondition");
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::ImportedModuleInvalid { import: 0, first, .. }
                if first.ends_with(&refusal)
        )),
        "{errors:?}"
    );
}

/// A multi-clause far summary: the importer restates both clauses honestly
/// and cites the row for the SECOND clause — accepted. Citing a far row whose
/// formula states no restated clause is refused by name.
#[test]
fn an_importer_may_cite_any_restated_clause_but_no_other_row() {
    let rejecting = RejectingModuleProofAuthority;
    let mut dep = seven(
        "ws1_3_multi",
        vec![nonneg(), literal()],
        vec![nonneg(), literal()],
    );
    assert!(validate_module(&dep).is_empty());
    let set = ModuleSet::new([&dep]);
    let root = importer(&dep, ensuring(vec![nonneg(), literal()]), 1);
    let report = validate_linked_module(&root, &set, &rejecting);
    assert!(report.is_ok(), "{:?}", report.errors());

    // A third, kernel-certified row about a clause nobody publishes.
    let f = dep.functions[0].id;
    let extra = ProofObligation::new(
        ProofId::new(2),
        ObligationKind::Postcondition,
        ProofStatus::Certified,
        "unpublished",
    )
    .with_function(f)
    .with_formula(ProofFormula::smtlib2("(= 2 2)", "Bool"));
    dep.proof_obligations.push(extra);
    let certificate = contract_clean_cic_certificate_in(&dep, &dep.proof_obligations[2], PROVER)
        .expect("(= 2 2) is kernel-provable");
    dep.proof_certificates.push(certificate);
    assert!(validate_module(&dep).is_empty());
    let set = ModuleSet::new([&dep]);
    let root = importer(&dep, ensuring(vec![nonneg(), literal()]), 2);
    let errors = validate_linked_module(&root, &set, &rejecting).into_errors();
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::UnauthenticatedImport { site: "backed_by", detail, .. }
                if detail == "cited far obligation #2 states `(= 2 2)`, which is none of the \
                              restated ensures clauses"
        )),
        "{errors:?}"
    );
}

// ===========================================================================
// review (adversarial): shapes the implementation pass did not write
// ===========================================================================

/// The importer [`importer`] builds, under a caller-chosen module name (a
/// chain needs two of them).
fn importer_named(name: &str, dep: &Module, summary: FunctionSummary, cited: u32) -> Module {
    let mut m = importer(dep, summary, cited);
    m.name = name.to_string();
    m
}

/// A DEFINITION cannot skip the per-clause rule by also carrying a
/// proof-bearing `backed_by`. A cross-crate citation can only ever be
/// authenticated from a body-less declaration (`LocalSiteHasBody`), so on a
/// definition it backs nothing — and before this review the local match was
/// skipped for ANY resolvable citation, so the structural tier accepted c02 R1
/// again the moment an import row was added beside it.
#[test]
fn review_a_definition_cannot_skip_the_clause_rule_with_a_backed_by() {
    let cite = |mut m: Module, clause: ProofFormula| {
        let id = m
            .intern_import(
                ModuleImport::new("upstream", trust_ir::proof::ProofDigest::sha256([0xA1; 32]))
                    .with_producer(Producer::TRust),
            )
            .expect("Module::intern_import: test fixture");
        m.functions[0].summary = Some(
            ensuring(vec![clause])
                .proved()
                .backed_by(ExternRef::new(id, "f").relying_on(ProofId::new(0))),
        );
        m
    };
    // Honest twin: the definition's own row states the clause, so the
    // structural tier (which takes the citation itself on faith) accepts.
    let honest = cite(seven("ws1_3_def_backed", vec![], vec![nonneg()]), nonneg());
    assert!(
        validate_module(&honest).is_empty(),
        "{:?}",
        validate_module(&honest)
    );

    let forged = cite(
        seven("ws1_3_def_backed", vec![], vec![nonneg()]),
        false_claim(),
    );
    let expected = [no_row("ensures", 0, FALSE_CLAIM, "Postcondition")];
    assert_refused_exactly(&validate_module(&forged), &expected);
    // The authority tier names the unauthenticated citation AND the clause.
    let errors = validate_module_with_authority(&forged, &RejectingModuleProofAuthority);
    assert_refused_exactly(&errors, &expected);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::UnauthenticatedImport {
                site: "backed_by",
                ..
            }
        )),
        "{errors:?}"
    );
}

/// A dependency `fn f() -> u64 { 7 }` whose `proved` summary requires `(= 1 1)`
/// and ensures `(= 2 2)`, with kernel-Certified rows #0 Precondition `(= 1 1)`,
/// #1 Postcondition `(= 2 2)`, and an extra #2 PRECONDITION stating the
/// ENSURES clause `(= 2 2)`.
fn two_role_dependency() -> Module {
    let requires = ProofFormula::smtlib2("(= 1 1)", "Bool");
    let ensures = ProofFormula::smtlib2("(= 2 2)", "Bool");
    let mut m = seven("ws1_3_two_role", vec![ensures.clone()], vec![]);
    let f = m.functions[0].id;
    let summary = m.functions[0].summary.take().unwrap();
    m.functions[0].summary = Some(summary.requiring(requires.clone()));
    for (id, kind, formula) in [
        (0, ObligationKind::Precondition, requires),
        (1, ObligationKind::Postcondition, ensures.clone()),
        (2, ObligationKind::Precondition, ensures),
    ] {
        let row = ProofObligation::new(ProofId::new(id), kind, ProofStatus::Certified, "stated")
            .with_function(f)
            .with_formula(formula);
        let certificate = contract_clean_cic_certificate_in(&m, &row, PROVER)
            .expect("a closed literal is kernel-provable at every contract kind");
        m.proof_obligations.push(row);
        m.proof_certificates.push(certificate);
    }
    assert!(validate_module(&m).is_empty(), "{:?}", validate_module(&m));
    m
}

/// The cited far row's ROLE is part of what it states: a far Precondition
/// whose formula equals a restated ENSURES clause is not one of the restated
/// REQUIRES clauses, and backs nothing, even though it is kernel-grounded and
/// its text appears in the summary.
#[test]
fn review_a_cited_far_row_of_the_wrong_role_backs_nothing() {
    let rejecting = RejectingModuleProofAuthority;
    let dep = two_role_dependency();
    let set = ModuleSet::new([&dep]);
    let restated = dep.functions[0].summary.clone().unwrap();
    let restated = FunctionSummary {
        proved: false,
        ..restated
    };
    for honest in [0, 1] {
        let root = importer(&dep, restated.clone(), honest);
        let report = validate_linked_module(&root, &set, &rejecting);
        assert!(report.is_ok(), "cite #{honest}: {:?}", report.errors());
    }
    let root = importer(&dep, restated, 2);
    let errors = validate_linked_module(&root, &set, &rejecting).into_errors();
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::UnauthenticatedImport { site: "backed_by", detail, .. }
                if detail == "cited far obligation #2 states `(= 2 2)`, which is none of the \
                              restated requires clauses"
        )),
        "{errors:?}"
    );
}

/// A multi-clause far summary where ONE clause is kernel-grounded and the
/// other rests only on a capability-replayed `Discharged` row. The dependency
/// is valid under the replaying authority, and the importer cites the
/// grounded row — but its `proved` restates BOTH clauses, so admitting it
/// would let the capability-tier row back a cross-crate `proved` (the WS1.3
/// DECIDE says it may not). Every restated clause of a far DEFINITION must be
/// stated by a grounded far row.
#[test]
fn review_a_capability_only_far_clause_is_not_laundered_by_citing_a_grounded_sibling() {
    let mut dep = seven("ws1_3_launder", vec![nonneg(), literal()], vec![nonneg()]);
    let f = dep.functions[0].id;
    dep.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(1),
            ObligationKind::Postcondition,
            ProofStatus::Discharged,
            "ensures (= 1 1), replayed by a capability",
        )
        .with_function(f)
        .with_formula(literal()),
    );
    dep.proof_certificates.push(ProofCertificate {
        obligation: ProofId::new(1),
        prover: "ay-bvblast".to_string(),
        evidence: ProofEvidence::SmtProof(b"(unsat)".to_vec()),
        assurance: None,
    });
    let capability = AdmitExact(dep.proof_certificates[1].lineage_ref());
    assert!(validate_module_with_authority(&dep, &capability).is_empty());

    let set = ModuleSet::new([&dep]);
    let root = importer(&dep, ensuring(vec![nonneg(), literal()]), 0);
    let errors = validate_linked_module(&root, &set, &capability).into_errors();
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::UnauthenticatedImport { site: "backed_by", detail, .. }
                if detail == "far ensures clause 1 `(= 1 1)` is stated by no Postcondition row \
                              grounded in the dependency (kernel-tier replay or authenticated \
                              inheritance); a capability-replayed row cannot back a cross-crate \
                              `proved`"
        )),
        "{errors:?}"
    );

    // Control: the same clause kernel-Certified instead, and the edge links.
    let honest = seven(
        "ws1_3_launder",
        vec![nonneg(), literal()],
        vec![nonneg(), literal()],
    );
    let set = ModuleSet::new([&honest]);
    let root = importer(&honest, ensuring(vec![nonneg(), literal()]), 0);
    let report = validate_linked_module(&root, &set, &capability);
    assert!(report.is_ok(), "{:?}", report.errors());
}

/// Positive chain: A's `proved` is backed by B's DECLARATION, whose own
/// `proved` is backed by C's definition and whose cited row is an
/// authenticated inheritance of C's kernel-Certified row. The far-clause
/// grounding rule applies at the definition (C, via B's own citation), so the
/// declaration in the middle needs only the cited, grounded, stated row.
#[test]
fn review_a_backed_by_chain_through_a_declaration_still_links() {
    let rejecting = RejectingModuleProofAuthority;
    let c = seven("ws1_3_C", vec![nonneg()], vec![nonneg()]);
    let mut b = importer_named("ws1_3_B", &c, ensuring(vec![nonneg()]), 0);
    let b_f = b.functions[0].id;
    b.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Discharged,
            "inherited ensures (>= result 0)",
        )
        .with_function(b_f)
        .with_formula(nonneg()),
    );
    b.proof_certificates.push(ProofCertificate {
        obligation: ProofId::new(0),
        prover: "compose".to_string(),
        evidence: ProofEvidence::InheritedFromCallee {
            callee: b_f,
            obligation: ProofId::new(0),
            external: Some(
                ExternRef::new(trust_ir::value::ImportId::new(0), "f").relying_on(ProofId::new(0)),
            ),
        },
        assurance: None,
    });
    let set = ModuleSet::new([&b, &c]);
    let report = validate_linked_module(&b, &set, &rejecting);
    assert!(report.is_ok(), "B links against C: {:?}", report.errors());

    let a = importer_named("ws1_3_A", &b, ensuring(vec![nonneg()]), 0);
    let report = validate_linked_module(&a, &set, &rejecting);
    assert!(
        report.is_ok(),
        "A links through B to C: {:?}",
        report.errors()
    );

    // Tamper: B cites a far row about another claim; B's own pass refuses
    // it, and A sees B invalid.
    let mut lying = c.clone();
    lying.functions[0].summary = Some(ensuring(vec![nonneg(), literal()]).proved());
    let lying_row = ProofObligation::new(
        ProofId::new(1),
        ObligationKind::Postcondition,
        ProofStatus::Discharged,
        "capability only",
    )
    .with_function(lying.functions[0].id)
    .with_formula(literal());
    lying.proof_obligations.push(lying_row);
    lying.proof_certificates.push(ProofCertificate {
        obligation: ProofId::new(1),
        prover: "ay-bvblast".to_string(),
        evidence: ProofEvidence::SmtProof(b"(unsat)".to_vec()),
        assurance: None,
    });
    let capability = AdmitExact(lying.proof_certificates[1].lineage_ref());
    assert!(validate_module_with_authority(&lying, &capability).is_empty());
    let mut b2 = b.clone();
    b2.imports.clear();
    let id = b2
        .intern_import(
            ModuleImport::new(lying.name.clone(), lying.stable_digest())
                .with_producer(Producer::TRust),
        )
        .expect("Module::intern_import: test fixture");
    assert_eq!(id.index(), 0);
    b2.functions[0].summary = Some(
        ensuring(vec![nonneg(), literal()])
            .proved()
            .backed_by(ExternRef::new(id, "f").relying_on(ProofId::new(0))),
    );
    let set = ModuleSet::new([&b2, &lying]);
    let a2 = importer_named("ws1_3_A", &b2, ensuring(vec![nonneg(), literal()]), 0);
    let errors = validate_linked_module(&a2, &set, &capability).into_errors();
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::ImportedModuleInvalid { import: 0, first, .. }
                if first.contains("far ensures clause 1 `(= 1 1)` is stated by no Postcondition row")
        )),
        "{errors:?}"
    );
}

// ===========================================================================
// adversarial review, second pass: coverage and scope of the SIBLING clauses
// ===========================================================================

/// A coverage row a producer projected from some evidence bundle.
fn assurance(bound: CoverageBound) -> Option<CoverageAssurance> {
    Some(CoverageAssurance {
        bound,
        request_digest: ProofDigest::sha256([0x5A; 32]),
    })
}

/// The far definition `f` of [`seven`] with ensures `[(>= result 0), (= 1 1)]`,
/// each kernel-Certified, recording `bounds[i]` on row `i`'s certificate (and
/// any extra rows `bounds[2..]` restating `(= 1 1)`).
fn covered_dependency(bounds: &[Option<CoverageBound>]) -> Module {
    let mut rows = vec![nonneg(), literal()];
    rows.extend(std::iter::repeat_n(
        literal(),
        bounds.len().saturating_sub(2),
    ));
    let mut dep = seven("ws1_3_cov", vec![nonneg(), literal()], rows);
    for (certificate, bound) in dep.proof_certificates.iter_mut().zip(bounds) {
        certificate.assurance = bound.and_then(assurance);
    }
    assert!(
        validate_module(&dep).is_empty(),
        "{:?}",
        validate_module(&dep)
    );
    dep
}

/// L9 compared the recorded coverage of the CITED far row only. A far
/// definition whose SIBLING clause is kernel-grounded only by a row recording
/// a depth-1 bounded discharge therefore lent that clause to the importer's
/// unqualified `proved` — `is_ok()` with `coverage_unrecorded() == 0`, so even
/// the documented admission gate passed. Every restated clause's coverage now
/// takes part: the site is judged on its least-covered clause, and the refusal
/// names the sibling row.
#[test]
fn review_a_bounded_sibling_clause_cannot_ride_on_the_cited_rows_coverage() {
    let rejecting = RejectingModuleProofAuthority;
    let citing_row_0 = |dep: &Module| importer(dep, ensuring(vec![nonneg(), literal()]), 0);

    // Control: both clauses recorded Unbounded — supported, and established.
    let honest = covered_dependency(&[Some(CoverageBound::Unbounded); 2]);
    let set = ModuleSet::new([&honest]);
    let root = citing_row_0(&honest);
    let report = validate_linked_module(&root, &set, &rejecting);
    assert!(report.is_ok(), "{:?}", report.errors());
    assert_eq!(
        (report.coverage_supported(), report.coverage_unrecorded()),
        (1, 0)
    );

    // The forge: clause 1 was only explored to depth 1.
    let bounded = covered_dependency(&[
        Some(CoverageBound::Unbounded),
        Some(CoverageBound::UnwindBounded { depth: 1 }),
    ]);
    let set = ModuleSet::new([&bounded]);
    let root = citing_row_0(&bounded);
    let report = validate_linked_module(&root, &set, &rejecting);
    let named: Vec<(&str, u32)> = report
        .errors()
        .iter()
        .filter_map(|e| match e {
            ValidationError::ImportCoverageBelowClaim {
                site, obligation, ..
            } => Some((*site, *obligation)),
            _ => None,
        })
        .collect();
    assert_eq!(
        named,
        vec![("backed_by", 1)],
        "the bounded SIBLING row is named: {:?}",
        report.errors()
    );

    // Silence on the sibling is not agreement either: admitted, but counted
    // UNRECORDED, so the admission gate `coverage_unrecorded() == 0` refuses.
    let silent = covered_dependency(&[Some(CoverageBound::Unbounded), None]);
    let set = ModuleSet::new([&silent]);
    let root = citing_row_0(&silent);
    let report = validate_linked_module(&root, &set, &rejecting);
    assert!(report.is_ok(), "{:?}", report.errors());
    assert_eq!(
        (report.coverage_supported(), report.coverage_unrecorded()),
        (0, 1)
    );
}

/// The per-clause coverage takes each clause's BEST-covered grounded row: a
/// clause stated by one Unbounded and one bounded kernel-Certified row is
/// covered, so the legitimate edge is not refused because a weaker duplicate
/// discharge also exists.
#[test]
fn review_a_clause_is_covered_by_its_best_grounded_row() {
    let dep = covered_dependency(&[
        Some(CoverageBound::Unbounded),
        Some(CoverageBound::UnwindBounded { depth: 1 }),
        Some(CoverageBound::Unbounded),
    ]);
    let root = importer(&dep, ensuring(vec![nonneg(), literal()]), 0);
    let set = ModuleSet::new([&dep]);
    let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    assert!(report.is_ok(), "{:?}", report.errors());
    assert_eq!(
        (report.coverage_supported(), report.coverage_unrecorded()),
        (1, 0)
    );
}

/// A far module with TWO definitions `f` and `g` that publish the same
/// `proved` contract. `g`'s `(= 1 1)` row is kernel-Certified; `f`'s is only
/// capability-replayed. Citing `f`'s grounded `(>= result 0)` row must not let
/// `g`'s grounded row stand in for `f`'s sibling clause: the grounding rule is
/// scoped to the far function the importer's symbol resolves to.
#[test]
fn review_a_grounded_row_of_another_far_function_grounds_no_sibling_clause() {
    let mut mb = ModuleBuilder::new_with_target_info("ws1_3_two_fns", target());
    mb.set_default_producer(Producer::TRust);
    let ft = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut ids = Vec::new();
    for name in ["f", "g"] {
        let mut fb = mb.function(name, ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let v = fb.uconst(Ty::U64, 7);
        fb.ret(vec![v]);
        ids.push(fb.build());
    }
    let (f, g) = (ids[0], ids[1]);
    let mut dep = mb.build().expect("ModuleBuilder::build: test fixture");
    for function in &mut dep.functions {
        function.summary = Some(ensuring(vec![nonneg(), literal()]).proved());
    }
    // #0 f nonneg (kernel), #1 g literal (kernel), #2 g nonneg (kernel),
    // #3 f literal (capability only).
    for (id, function, formula) in [(0, f, nonneg()), (1, g, literal()), (2, g, nonneg())] {
        let row = ProofObligation::new(
            ProofId::new(id),
            ObligationKind::Postcondition,
            ProofStatus::Certified,
            "stated",
        )
        .with_function(function)
        .with_formula(formula);
        let certificate = contract_clean_cic_certificate_in(&dep, &row, PROVER)
            .expect("kernel-provable backing formula");
        dep.proof_obligations.push(row);
        dep.proof_certificates.push(certificate);
    }
    dep.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(3),
            ObligationKind::Postcondition,
            ProofStatus::Discharged,
            "ensures (= 1 1), replayed by a capability",
        )
        .with_function(f)
        .with_formula(literal()),
    );
    dep.proof_certificates.push(ProofCertificate {
        obligation: ProofId::new(3),
        prover: "ay-bvblast".to_string(),
        evidence: ProofEvidence::SmtProof(b"(unsat)".to_vec()),
        assurance: None,
    });
    let capability = AdmitExact(dep.proof_certificates[3].lineage_ref());
    assert!(
        validate_module_with_authority(&dep, &capability).is_empty(),
        "{:?}",
        validate_module_with_authority(&dep, &capability)
    );

    let root = importer(&dep, ensuring(vec![nonneg(), literal()]), 0);
    let errors = validate_linked_module(&root, &ModuleSet::new([&dep]), &capability).into_errors();
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::UnauthenticatedImport { site: "backed_by", detail, .. }
                if detail.starts_with("far ensures clause 1 `(= 1 1)` is stated by no \
                                       Postcondition row grounded in the dependency")
        )),
        "{errors:?}"
    );
}

// ===========================================================================
// WS1.9 review — adversarial inputs against the minted Termination rows
// ===========================================================================

/// `fn g(x: u64) -> u64 { x }` (producer TRust) with a `proved` summary whose
/// `decreases` list is `measures`, and NO obligation rows: the caller mints
/// them (`mint_summary_obligations`) or hand-builds them.
fn g_with_measures(name: &str, measures: Vec<ProofFormula>) -> (Module, FuncId) {
    let mut mb = ModuleBuilder::new_with_target_info(name, target());
    let ft = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function("g", ft);
    fb.set_producer(Producer::TRust);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::U64);
    fb.switch_to_block(entry);
    fb.ret(vec![x]);
    let g = fb.build();
    // A second definition the scope twin can re-home a row onto.
    let mut hb = mb.function("h", ft);
    hb.set_producer(Producer::TRust);
    let hentry = hb.create_block();
    let y = hb.add_block_param(hentry, Ty::U64);
    hb.switch_to_block(hentry);
    hb.ret(vec![y]);
    hb.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    let mut summary = FunctionSummary::new().with_params(vec!["x".to_string()]);
    summary.decreases = measures;
    m.functions[0].summary = Some(summary.proved());
    (m, g)
}

/// The kernel contract grounder certifies a closed literal Bool clause for a
/// `Postcondition` row. A producer that controls the summary can therefore
/// write a `decreases` "measure" the kernel WOULD prove — `(= 1 1)` — mint a
/// genuine certificate for a `Postcondition` twin of the row (same id,
/// description, formula, scope), recompute the public lineage digest for the
/// `Termination` kind and attach it. WS1.9 DECIDE A says a `Termination` row
/// is NEVER `Certified` here, so `validate_module` must refuse the row on its
/// KIND — not on the certificate mechanics, which the control shows are sound.
#[test]
fn ws1_9_review_a_forged_kernel_certificate_never_certifies_a_termination_row() {
    use trust_ir::proof::clean_cic_lineage_digest;
    let (mut m, g) = g_with_measures("ws1_9_forged", vec![literal()]);
    let minted = trust_ir_build::mint_summary_obligations(&mut m, g).expect("fresh obligation ids");
    assert_eq!(minted.len(), 1);
    let id = minted[0];
    let index = id.index() as usize;
    assert_eq!(m.proof_obligations[index].kind, ObligationKind::Termination);
    // The genuine certificate: minted for a Postcondition twin of the row.
    let mut twin_module = m.clone();
    twin_module.proof_obligations[index].kind = ObligationKind::Postcondition;
    let genuine = contract_clean_cic_certificate_in(
        &twin_module,
        &twin_module.proof_obligations[index],
        PROVER,
    )
    .expect("the kernel proves (= 1 1) for a Postcondition row");
    // The forgery: the same term, re-bound by lineage to the Termination row.
    m.proof_obligations[index].status = ProofStatus::Certified;
    let ProofEvidence::CleanCic {
        term,
        context,
        kernel_recheck,
        ..
    } = genuine.evidence.clone()
    else {
        panic!("a contract certificate is CleanCic")
    };
    m.proof_certificates.push(ProofCertificate {
        obligation: id,
        prover: PROVER.to_string(),
        evidence: ProofEvidence::CleanCic {
            term,
            context,
            lineage: clean_cic_lineage_digest(&m.proof_obligations[index]),
            kernel_recheck,
        },
        assurance: None,
    });
    let errors = validate_module(&m);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::CertifiedCleanCicKernelRecheckFailed { obligation, .. }
                if *obligation == id.index()
        )),
        "a Termination row cannot be kernel-certified (DECIDE A): {errors:?}"
    );
    assert!(
        !validate_module_with_authority(&m, &RejectingModuleProofAuthority).is_empty(),
        "no authority tier re-admits it"
    );
    assert_eq!(
        validate_module_report(&m).replayed_certificate_refs(),
        None,
        "nothing about this module is replayed"
    );
    // The lineage-only forgery (the genuine certificate attached unchanged,
    // its lineage still naming the Postcondition twin) is refused too, by the
    // lineage floor.
    let mut lineage_only = m.clone();
    lineage_only.proof_certificates.clear();
    lineage_only.proof_certificates.push(genuine.clone());
    assert!(
        validate_module(&lineage_only).iter().any(|e| matches!(
            e,
            ValidationError::CertifiedCleanCicLineageMismatch { obligation }
                if *obligation == id.index()
        )),
        "{:?}",
        validate_module(&lineage_only)
    );
    // CONTROL: the identical certificate on the Postcondition twin, whose
    // summary states the clause as `ensures`, is genuinely re-checked and the
    // module validates — so the refusal above is the KIND, nothing else.
    let mut control = twin_module;
    control.proof_obligations[index].status = ProofStatus::Certified;
    control.proof_certificates.push(genuine);
    let summary = control.functions[0].summary.as_mut().unwrap();
    summary.ensures = std::mem::take(&mut summary.decreases);
    assert!(
        validate_module(&control).is_empty(),
        "{:?}",
        validate_module(&control)
    );
    assert_eq!(
        validate_module_report(&control)
            .replayed_certificate_refs()
            .map(|refs| refs.len()),
        Some(1)
    );
}

/// Two `decreases` measures (a lexicographic pair) mint TWO Termination rows,
/// and `proved` needs BOTH: each twin is one mutation of the validating
/// fixture, refused with the per-clause reason naming the clause it unbacks.
#[test]
fn ws1_9_review_every_decreases_measure_needs_its_own_termination_row() {
    let first = ProofFormula::smtlib2("x", "Int");
    let second = ProofFormula::smtlib2("(+ x 1)", "Int");
    let (mut m, g) = g_with_measures("ws1_9_lex", vec![first.clone(), second.clone()]);
    let minted = trust_ir_build::mint_summary_obligations(&mut m, g).expect("fresh obligation ids");
    assert_eq!(minted.len(), 2, "one Termination row per measure");
    for id in &minted {
        let row = &mut m.proof_obligations[id.index() as usize];
        assert_eq!(row.kind, ObligationKind::Termination);
        row.status = ProofStatus::Discharged;
    }
    assert_eq!(
        m.proof_obligations[minted[0].index() as usize].formula,
        Some(first.clone())
    );
    assert_eq!(
        m.proof_obligations[minted[1].index() as usize].formula,
        Some(second.clone())
    );
    assert!(summary_details(&validate_module(&m)).is_empty());
    let second_index = minted[1].index() as usize;

    // Twin 1: the second row deleted — the first row states measure 0, not
    // measure 1 ("rows stating other clauses do not count").
    let mut deleted = m.clone();
    deleted.proof_obligations.remove(second_index);
    assert_refused_exactly(
        &validate_module(&deleted),
        &[no_row("decreases", 1, "(+ x 1)", "Termination")],
    );

    // Twin 2: the second row re-scoped to the OTHER definition `h`: a row
    // about `h`'s descent says nothing about `g`'s.
    let mut foreign = m.clone();
    let h = foreign.functions[1].id;
    assert_ne!(h, g);
    foreign.proof_obligations[second_index].function = Some(h);
    assert_refused_exactly(
        &validate_module(&foreign),
        &[no_row("decreases", 1, "(+ x 1)", "Termination")],
    );

    // Twin 3: the second row's formula keeps its TEXT but gains a binding the
    // clause does not carry — bindings take part in the equality, so the row
    // states a different clause.
    let mut rebound = m.clone();
    let row = &mut rebound.proof_obligations[second_index];
    let formula = row.formula.as_mut().unwrap();
    formula.bindings.push((
        "x".to_string(),
        ClauseBinding {
            sort: ClauseSort::Int,
            place: ClausePlace::Param { index: 0 },
        },
    ));
    assert_eq!(
        rebound.proof_obligations[second_index]
            .formula
            .as_ref()
            .unwrap()
            .smtlib,
        second.smtlib
    );
    assert_refused_exactly(
        &validate_module(&rebound),
        &[no_row("decreases", 1, "(+ x 1)", "Termination")],
    );

    // Twin 4: a summary that restates the measure is refused as a duplicate,
    // never credited twice by the one row.
    let mut duplicated = m.clone();
    duplicated.functions[0]
        .summary
        .as_mut()
        .unwrap()
        .decreases
        .push(first);
    assert!(
        summary_details(&validate_module(&duplicated))
            .iter()
            .any(|d| d == "decreases clause 2 duplicates clause 0"),
        "{:?}",
        summary_details(&validate_module(&duplicated))
    );
}
