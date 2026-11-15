// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// GAP G5 regression tests — the UNCHECKED CONTRACT.
//
// v41 added `ProofFormula.bindings`: every clause free name bound to a
// `ClauseSort` and a `ClausePlace`. The CARRIER shipped; the RULES did not.
// Before these tests `validate_function_summary` performed exactly two checks
// (clause schema non-blank, `params` arity), so a contract could bind `result`
// to return slot 7 of a one-result function, bind an SSA value that does not
// exist, put the give-back place on a precondition, or assert `proved` with
// nothing in the module backing it — and validate clean.
//
// Every test here was observed FAILING against the pre-fix validator.

use trust_ir::proof::{
    ClauseBinding, ClausePlace, ClauseSort, ObligationKind, ProofDigest, ProofFormula,
    ProofObligation, ProofStatus,
};
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{FuncId, ImportId, ProofId, ValueId};
use trust_ir::{
    Endianness, ExternRef, Function, FunctionSummary, Module, ModuleImport, TargetInfo,
};
use trust_ir_build::validate::ValidationError;
use trust_ir_build::{ModuleBuilder, validate_module};

// ---------------------------------------------------------------------------
// helpers
// ---------------------------------------------------------------------------

/// `fn bump(x: i64) -> i64 { x + 1 }` — a body-bearing function whose SSA
/// values are real, so a `ClausePlace::Value` binding has something to resolve
/// against. Returns the module plus (param `x`, result `r`).
fn bump_module() -> (Module, ValueId, ValueId) {
    let mut mb = ModuleBuilder::new("g5");
    let ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function("bump", ft);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::I64);
    fb.switch_to_block(entry);
    let one = fb.iconst(Ty::I64, 1);
    let r = fb.add(Ty::I64, x, one);
    fb.ret(vec![r]);
    fb.build();
    (
        mb.build().expect("ModuleBuilder::build: test fixture"),
        x,
        r,
    )
}

/// A body-LESS contract-only declaration `fn opaque(x: i64) -> i64`.
fn declaration_module() -> Module {
    let mut module = Module::new("g5_decl");
    // A body-less External declaration is an FFI boundary, which is only
    // well-defined against a pinned target (`TargetInfoRequired`).
    module.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    let ft = module
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    module
        .try_add_function(Function::declaration(
            FuncId::new(0),
            "opaque",
            ft,
            FunctionSummary::new().with_params(vec!["x".to_string()]),
        ))
        .expect("Module::try_add_function: test fixture");
    module
}

/// An SMT-LIB clause carrying `bindings`.
fn clause(text: &str, bindings: &[(&str, ClausePlace)]) -> ProofFormula {
    let mut formula = ProofFormula::smtlib2(text, "Bool");
    formula.bindings = bindings
        .iter()
        .map(|(name, place)| {
            (
                (*name).to_string(),
                ClauseBinding {
                    sort: ClauseSort::BitVec(64),
                    place: *place,
                },
            )
        })
        .collect();
    formula
}

/// `fn bump_in_place(p: &mut i64)` — the shape `MutParamExit` exists for.
fn mut_ref_module() -> Module {
    let mut mb = ModuleBuilder::new("g5_mut");
    let param = Ty::RefMut(Box::new(Ty::I64));
    let ft = mb.add_func_type(vec![param.clone()], vec![]);
    let mut fb = mb.function("bump_in_place", ft);
    let entry = fb.create_block();
    let _p = fb.add_block_param(entry, param);
    fb.switch_to_block(entry);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn summary_errors(module: &Module) -> Vec<String> {
    validate_module(module)
        .into_iter()
        .filter_map(|error| match error {
            ValidationError::InvalidFunctionSummary { detail, .. } => Some(detail),
            _ => None,
        })
        .collect()
}

fn assert_rejected(module: &Module, needle: &str) {
    let details = summary_errors(module);
    assert!(
        details.iter().any(|detail| detail.contains(needle)),
        "expected an InvalidFunctionSummary mentioning {needle:?}; got {details:?} \
         (all errors: {:?})",
        validate_module(module)
    );
}

fn assert_clean(module: &Module) {
    let errors = validate_module(module);
    assert!(errors.is_empty(), "expected a clean module, got {errors:?}");
}

/// The summary rules raised nothing.
///
/// Used where the fixture must carry a `Discharged`/`Certified` obligation:
/// `validate_module` supplies `RejectingModuleProofAuthority`, so a strong
/// status is ALWAYS reported as `DischargedWithoutCertificate` /
/// `CertifiedWithoutCleanCic` by the structural entry point (a format build
/// cannot replay a solver or a kernel). That is a different, orthogonal rule;
/// this assertion isolates the one under test.
fn assert_no_summary_error(module: &Module) {
    let errors: Vec<_> = validate_module(module)
        .into_iter()
        .filter(|error| {
            matches!(
                error,
                ValidationError::InvalidFunctionSummary { .. }
                    | ValidationError::DanglingExternRef { .. }
            )
        })
        .collect();
    assert!(
        errors.is_empty(),
        "expected no contract-summary error, got {errors:?}"
    );
}

/// Attach `summary` to the only function of `module`.
fn with_summary(mut module: Module, summary: FunctionSummary) -> Module {
    module.functions[0].summary = Some(summary);
    module
}

// ---------------------------------------------------------------------------
// (1) resolution
// ---------------------------------------------------------------------------

#[test]
fn fully_resolvable_bindings_validate() {
    let (module, x, r) = bump_module();
    let module = with_summary(
        module,
        FunctionSummary::new()
            .with_params(vec!["x".to_string()])
            .requiring(clause(
                "(bvsge x #x0000000000000000)",
                &[("x", ClausePlace::Param { index: 0 })],
            ))
            .ensuring(clause(
                "(= result (bvadd x #x0000000000000001))",
                &[
                    ("x", ClausePlace::Param { index: 0 }),
                    ("result", ClausePlace::ResultSlot { index: 0 }),
                    ("heap", ClausePlace::World),
                    ("sum", ClausePlace::Value(r)),
                ],
            )),
    );
    assert!(x.index() != r.index());
    assert_clean(&module);
}

#[test]
fn a_param_binding_past_the_signature_arity_is_rejected() {
    let (module, ..) = bump_module();
    let module = with_summary(
        module,
        FunctionSummary::new()
            .with_params(vec!["x".to_string()])
            .requiring(clause(
                "(bvsge y #x00)",
                &[("y", ClausePlace::Param { index: 1 })],
            )),
    );
    assert_rejected(&module, "names parameter 1 but the signature declares 1");
}

#[test]
fn a_result_slot_binding_past_the_return_arity_is_rejected() {
    let (module, ..) = bump_module();
    let module = with_summary(
        module,
        FunctionSummary::new()
            .with_params(vec!["x".to_string()])
            .ensuring(clause(
                "(= snd #x00)",
                &[("snd", ClausePlace::ResultSlot { index: 1 })],
            )),
    );
    assert_rejected(&module, "names result slot 1 but the signature declares 1");
}

#[test]
fn a_value_binding_must_name_a_value_the_body_defines() {
    let (module, _, r) = bump_module();

    // A value the body really defines resolves.
    let good = with_summary(
        module.clone(),
        FunctionSummary::new()
            .with_params(vec!["x".to_string()])
            .ensuring(clause("(= sum result)", &[("sum", ClausePlace::Value(r))])),
    );
    assert_clean(&good);

    // A value it does not define is unresolvable.
    let bad = with_summary(
        module,
        FunctionSummary::new()
            .with_params(vec!["x".to_string()])
            .ensuring(clause(
                "(= ghost result)",
                &[("ghost", ClausePlace::Value(ValueId::new(99)))],
            )),
    );
    assert_rejected(
        &bad,
        "names SSA value v99, which this function's body never defines",
    );
}

#[test]
fn a_value_binding_is_never_resolvable_on_a_bodyless_declaration() {
    // `ClausePlace::Value`'s own doc: "Never resolvable on a body-less
    // contract-only declaration." There is no body to resolve INTO, so this is
    // rejected on the id itself, not on whether the id happens to look small.
    let module = declaration_module();
    let module = with_summary(
        module,
        FunctionSummary::new()
            .with_params(vec!["x".to_string()])
            .ensuring(clause(
                "(= tmp result)",
                &[("tmp", ClausePlace::Value(ValueId::new(0)))],
            )),
    );
    assert_rejected(
        &module,
        "on a body-less declaration, which has no body to resolve it in",
    );
}

// ---------------------------------------------------------------------------
// (2) place legality — `ClausePlace`'s doc comments are normative
// ---------------------------------------------------------------------------

#[test]
fn mut_param_exit_is_legal_only_on_an_ensures_clause() {
    let module = mut_ref_module();
    let exit = ("p_prime", ClausePlace::MutParamExit { index: 0 });

    // ensures: the give-back / primed-output place, legal.
    let ensures = with_summary(
        module.clone(),
        FunctionSummary::new()
            .with_params(vec!["p".to_string()])
            .ensuring(clause("(= p_prime #x0000000000000000)", &[exit])),
    );
    assert_clean(&ensures);

    // requires: illegal — a precondition cannot speak about the exit value.
    let requires = with_summary(
        module.clone(),
        FunctionSummary::new()
            .with_params(vec!["p".to_string()])
            .requiring(clause("(= p_prime #x0000000000000000)", &[exit])),
    );
    assert_rejected(&requires, "on a requires clause");

    // decreases: also illegal. The doc says ENSURES ONLY, and a measure that
    // reads a post-state cannot be evaluated at a back edge.
    let mut decreasing = FunctionSummary::new().with_params(vec!["p".to_string()]);
    decreasing.decreases.push(clause("p_prime", &[exit]));
    let decreases = with_summary(module, decreasing);
    assert_rejected(&decreases, "on a decreases clause");

    // WS1.2: and only on a `&mut` / `*mut` parameter — the by-value `x: i64`
    // of `bump` has no exit value distinct from its entry value.
    let (by_value, ..) = bump_module();
    let by_value = with_summary(
        by_value,
        FunctionSummary::new()
            .with_params(vec!["x".to_string()])
            .ensuring(clause(
                "(= x_prime #x0000000000000000)",
                &[("x_prime", ClausePlace::MutParamExit { index: 0 })],
            )),
    );
    assert_rejected(&by_value, "uses MutParamExit on parameter 0 of type i64");
}

#[test]
fn unwind_is_illegal_on_a_requires_clause() {
    let (module, ..) = bump_module();
    let unwind = ("unwinding", ClausePlace::Unwind);

    let requires = with_summary(
        module.clone(),
        FunctionSummary::new()
            .with_params(vec!["x".to_string()])
            .requiring(clause("(not unwinding)", &[unwind])),
    );
    assert_rejected(
        &requires,
        "names the in-flight unwind state on a requires clause",
    );

    // On an `ensures` it is exactly the right place: "did this call unwind?"
    let ensures = with_summary(
        module,
        FunctionSummary::new()
            .with_params(vec!["x".to_string()])
            .ensuring(clause("(not unwinding)", &[unwind])),
    );
    assert_clean(&ensures);
}

// ---------------------------------------------------------------------------
// (3) the binding map must be a map
// ---------------------------------------------------------------------------

#[test]
fn a_repeated_binding_name_leaves_the_free_variable_ambiguous() {
    let (module, ..) = bump_module();
    let module = with_summary(
        module,
        FunctionSummary::new()
            .with_params(vec!["x".to_string()])
            .ensuring(clause(
                "(= x result)",
                &[
                    ("x", ClausePlace::Param { index: 0 }),
                    ("x", ClausePlace::ResultSlot { index: 0 }),
                ],
            )),
    );
    assert_rejected(&module, "is bound more than once");
}

#[test]
fn a_blank_binding_name_is_rejected() {
    let (module, ..) = bump_module();
    let module = with_summary(
        module,
        FunctionSummary::new()
            .with_params(vec!["x".to_string()])
            .ensuring(clause(
                "(= x result)",
                &[("   ", ClausePlace::Param { index: 0 })],
            )),
    );
    assert_rejected(&module, "binds a blank free name");
}

#[test]
fn a_decreases_clause_is_a_clause_and_is_checked_like_one() {
    // Pre-fix, `decreases` (v41) was not even reached by the blank-schema
    // check: the loop ran over `requires` and `ensures` only.
    let (module, ..) = bump_module();
    let mut summary = FunctionSummary::new().with_params(vec!["x".to_string()]);
    let mut measure = ProofFormula::new("", "x");
    measure.bindings.push((
        "x".to_string(),
        ClauseBinding {
            sort: ClauseSort::BitVec(64),
            place: ClausePlace::Param { index: 4 },
        },
    ));
    summary.decreases.push(measure);
    let module = with_summary(module, summary);
    let details = summary_errors(&module);
    assert!(
        details
            .iter()
            .any(|d| d.contains("decreases clause 0 has an empty schema")),
        "a decreases measure must route like any other clause: {details:?}"
    );
    assert!(
        details
            .iter()
            .any(|d| d.contains("names parameter 4 but the signature declares 1")),
        "a decreases measure's bindings must resolve: {details:?}"
    );

    // And a decreases-ONLY summary is still a clause-bearing summary, so it
    // needs the param names that make its measure instantiable — even though
    // `FunctionSummary::is_empty` (a serialization predicate) says otherwise.
    let (module, ..) = bump_module();
    let mut paramless = FunctionSummary::new();
    paramless.decreases.push(ProofFormula::smtlib2("x", "Int"));
    let module = with_summary(module, paramless);
    assert_rejected(
        &module,
        "summary lists 0 parameter name(s) but the signature has 1",
    );
}

// ---------------------------------------------------------------------------
// (4) `proved` must be backed
// ---------------------------------------------------------------------------

/// Give `module`'s function `count` FORMULA-LESS obligations of `kind` with
/// `status`, scoped (B4) to `function`. Since WS1.3 a formula-less row backs no
/// clause of a `proved` summary (it does not say which clause it established);
/// it still REFUTES `proved` when `Failed`.
fn push_obligations(
    module: &mut Module,
    function: FuncId,
    kind: ObligationKind,
    status: ProofStatus,
    count: usize,
) {
    let first = module
        .proof_obligations
        .iter()
        .map(|o| o.id.index() + 1)
        .max()
        .unwrap_or(0);
    for id in first..first + count as u32 {
        module.proof_obligations.push(
            ProofObligation::new(ProofId::new(id), kind.clone(), status, "clause")
                .with_function(function),
        );
    }
}

/// Give `module`'s function one obligation of `kind` with `status`, scoped
/// (B4) to `function`, STATING `formula` — the only shape that backs a clause
/// of a `proved` summary (WS1.3).
fn push_stating(
    module: &mut Module,
    function: FuncId,
    kind: ObligationKind,
    status: ProofStatus,
    formula: ProofFormula,
) {
    let id = module
        .proof_obligations
        .iter()
        .map(|o| o.id.index() + 1)
        .max()
        .unwrap_or(0);
    module.proof_obligations.push(
        ProofObligation::new(ProofId::new(id), kind, status, "clause")
            .with_function(function)
            .with_formula(formula),
    );
}

const BUMP_REQUIRES: &str = "(bvsge x #x00)";
const BUMP_ENSURES: &str = "(= result (bvadd x #x01))";

fn bump_requires() -> ProofFormula {
    ProofFormula::smtlib2(BUMP_REQUIRES, "Bool")
}

fn bump_ensures() -> ProofFormula {
    ProofFormula::smtlib2(BUMP_ENSURES, "Bool")
}

/// The per-clause refusal (WS1.3) for `role` clause 0 stating `text`.
fn unbacked(role: &str, text: &str, kind: &str) -> String {
    format!(
        "{role} clause 0 `{text}` has no Discharged/Certified {kind} row scoped to this function"
    )
}

/// A `proved` summary on `bump`: one requires, one ensures.
fn proved_bump() -> (Module, FuncId) {
    let (module, ..) = bump_module();
    let function = module.functions[0].id;
    let module = with_summary(
        module,
        FunctionSummary::new()
            .with_params(vec!["x".to_string()])
            .requiring(bump_requires())
            .ensuring(bump_ensures())
            .proved(),
    );
    (module, function)
}

/// `proved_bump` with a Discharged Precondition and a Certified
/// Postcondition, each stating its clause.
fn backed_bump() -> (Module, FuncId) {
    let (mut module, function) = proved_bump();
    push_stating(
        &mut module,
        function,
        ObligationKind::Precondition,
        ProofStatus::Discharged,
        bump_requires(),
    );
    push_stating(
        &mut module,
        function,
        ObligationKind::Postcondition,
        ProofStatus::Certified,
        bump_ensures(),
    );
    (module, function)
}

#[test]
fn proved_with_nothing_backing_it_is_rejected() {
    let (module, _) = proved_bump();
    assert_rejected(
        &module,
        &unbacked("requires", BUMP_REQUIRES, "Precondition"),
    );
    assert_rejected(&module, &unbacked("ensures", BUMP_ENSURES, "Postcondition"));
}

#[test]
fn proved_backed_by_function_scoped_discharged_obligations_is_accepted() {
    let (module, _) = backed_bump();
    assert_no_summary_error(&module);
}

#[test]
fn formula_less_rows_do_not_back_proved() {
    // WS1.3: the right kind, status and scope, but no statement of WHICH
    // clause was established — so no clause is backed.
    let (mut module, function) = proved_bump();
    push_obligations(
        &mut module,
        function,
        ObligationKind::Precondition,
        ProofStatus::Discharged,
        1,
    );
    push_obligations(
        &mut module,
        function,
        ObligationKind::Postcondition,
        ProofStatus::Certified,
        1,
    );
    assert_rejected(
        &module,
        &unbacked("requires", BUMP_REQUIRES, "Precondition"),
    );
    assert_rejected(&module, &unbacked("ensures", BUMP_ENSURES, "Postcondition"));
}

#[test]
fn pending_and_trusted_obligations_do_not_back_proved() {
    // `proved`'s own doc says DISCHARGED. `Trusted` is a manual audit taken on
    // faith — strictly weaker — and `Pending` is not a verdict at all.
    for status in [ProofStatus::Pending, ProofStatus::Trusted] {
        let (mut module, _) = backed_bump();
        for obligation in &mut module.proof_obligations {
            obligation.status = status;
        }
        assert_rejected(
            &module,
            &unbacked("requires", BUMP_REQUIRES, "Precondition"),
        );
        assert_rejected(&module, &unbacked("ensures", BUMP_ENSURES, "Postcondition"));
    }
}

#[test]
fn obligations_scoped_to_another_function_do_not_back_proved() {
    let (mut module, _) = backed_bump();
    // Discharged, right kinds, stating the very clauses — but about someone
    // else. B4 scope binds a row to the function whose contract it states.
    for obligation in &mut module.proof_obligations {
        obligation.function = Some(FuncId::new(77));
    }
    assert_rejected(
        &module,
        &unbacked("requires", BUMP_REQUIRES, "Precondition"),
    );
}

#[test]
fn a_discharged_obligation_of_the_wrong_kind_does_not_back_a_clause() {
    let (mut module, function) = proved_bump();
    for formula in [bump_requires(), bump_ensures()] {
        push_stating(
            &mut module,
            function,
            ObligationKind::MemorySafety,
            ProofStatus::Discharged,
            formula,
        );
    }
    assert_rejected(
        &module,
        &unbacked("requires", BUMP_REQUIRES, "Precondition"),
    );
}

#[test]
fn a_failed_contract_obligation_refutes_proved() {
    let (mut module, function) = backed_bump();
    assert_no_summary_error(&module);
    // Every clause backed — and one of this function's contract obligations
    // was REFUTED. Backing must not launder that.
    push_obligations(
        &mut module,
        function,
        ObligationKind::Postcondition,
        ProofStatus::Failed,
        1,
    );
    assert_rejected(&module, "is Failed");
}

#[test]
fn decreases_clauses_need_discharged_termination_obligations() {
    let (module, ..) = bump_module();
    let function = module.functions[0].id;
    let measure = ProofFormula::smtlib2("x", "Int");
    let mut summary = FunctionSummary::new()
        .with_params(vec!["x".to_string()])
        .proved();
    summary.decreases.push(measure.clone());
    let mut module = with_summary(module, summary);
    let refusal = unbacked("decreases", "x", "Termination");
    assert_rejected(&module, &refusal);

    // v41 gave termination its own kind precisely so it stops being filed
    // under the category-ambiguous `Liveness`; a Liveness row must not back it.
    push_stating(
        &mut module,
        function,
        ObligationKind::Liveness,
        ProofStatus::Discharged,
        measure.clone(),
    );
    assert_rejected(&module, &refusal);

    push_stating(
        &mut module,
        function,
        ObligationKind::Termination,
        ProofStatus::Discharged,
        measure,
    );
    assert_no_summary_error(&module);
}

#[test]
fn a_cross_crate_backed_by_authenticates_proved_only_when_it_names_an_obligation() {
    // A contract-only declaration has no local body and therefore no local
    // obligations: `backed_by` is the ONLY thing that can authenticate its
    // `proved` bit, exactly as the v41 field doc says.
    let base = with_summary(
        declaration_module(),
        FunctionSummary::new()
            .with_params(vec!["x".to_string()])
            .ensuring(ProofFormula::smtlib2("(bvsgt result #x00)", "Bool"))
            .proved(),
    );
    assert_rejected(&base, "summary claims `proved` with 1 ensures clause(s)");

    // Naming the entity but NO obligation carries no proof claim, so it
    // authenticates nothing.
    let mut named_only = base.clone();
    named_only
        .imports
        .push(ModuleImport::new("upstream", ProofDigest::zero()));
    named_only.functions[0].summary = Some(
        named_only.functions[0]
            .summary
            .clone()
            .unwrap()
            .backed_by(ExternRef::new(ImportId::new(0), "opaque")),
    );
    assert_rejected(
        &named_only,
        "summary claims `proved` with 1 ensures clause(s)",
    );

    // Naming the obligation it relies on authenticates the bit.
    let mut backed = named_only.clone();
    backed.functions[0].summary = Some(
        backed.functions[0]
            .summary
            .clone()
            .unwrap()
            .backed_by(ExternRef::new(ImportId::new(0), "opaque").relying_on(ProofId::new(3))),
    );
    assert_clean(&backed);

    // A citation into an import that was never declared is dangling: the
    // import's digest is the only thing that makes it checkable at all.
    let mut dangling = base;
    dangling.functions[0].summary = Some(
        dangling.functions[0]
            .summary
            .clone()
            .unwrap()
            .backed_by(ExternRef::new(ImportId::new(9), "opaque").relying_on(ProofId::new(3))),
    );
    let errors = validate_module(&dangling);
    assert!(
        errors
            .iter()
            .any(|e| matches!(e, ValidationError::DanglingExternRef { .. })),
        "an unresolvable backed_by import must be reported: {errors:?}"
    );
}

// ---------------------------------------------------------------------------
// (5) the two documented non-rules
// ---------------------------------------------------------------------------

#[test]
fn empty_bindings_stay_unbindable_and_are_never_a_wildcard() {
    // A clause with NO bindings has nothing for this pass to resolve, so it
    // raises no binding error. That silence is NOT a blessing: `bindings`'
    // own doc makes empty read as UNBINDABLE (the v34 `site = None`
    // precedent), and the validator must never contain a rule that turns "no
    // bindings" into "all names fine". The observable half of that promise is
    // that an unbound clause buys nothing ELSEWHERE either — `proved` on a
    // module with no backing is still refused.
    let (module, ..) = bump_module();
    let module = with_summary(
        module,
        FunctionSummary::new()
            .with_params(vec!["x".to_string()])
            .ensuring(ProofFormula::smtlib2("(= result whatever)", "Bool"))
            .proved(),
    );
    let details = summary_errors(&module);
    assert!(
        !details.iter().any(|d| d.contains("binding")),
        "an empty bindings list raises no binding error: {details:?}"
    );
    assert!(
        details
            .iter()
            .any(|d| d.contains("has no Discharged/Certified Postcondition row")),
        "and it is still not backed: {details:?}"
    );
}

#[test]
fn a_row_about_another_clause_does_not_back_proved() {
    // FLIPPED by WS1.3 (formerly
    // `the_counting_rule_cannot_bind_a_clause_to_its_own_obligation`, which
    // pinned the counting rule's blind spot as ledgered residue). The row is
    // Discharged, of the right kind, scoped to `bump` — and states a different
    // clause, so it backs nothing. A formula-less row (the old minted shape)
    // backs nothing either.
    let (module, ..) = bump_module();
    let function = module.functions[0].id;
    let mut module = with_summary(
        module,
        FunctionSummary::new()
            .with_params(vec!["x".to_string()])
            .ensuring(bump_ensures())
            .proved(),
    );
    push_stating(
        &mut module,
        function,
        ObligationKind::Postcondition,
        ProofStatus::Discharged,
        ProofFormula::smtlib2("(= 1 1)", "Bool"),
    );
    assert_rejected(&module, &unbacked("ensures", BUMP_ENSURES, "Postcondition"));
    push_obligations(
        &mut module,
        function,
        ObligationKind::Postcondition,
        ProofStatus::Discharged,
        1,
    );
    assert_rejected(&module, &unbacked("ensures", BUMP_ENSURES, "Postcondition"));
    // The row that states the clause backs it.
    push_stating(
        &mut module,
        function,
        ObligationKind::Postcondition,
        ProofStatus::Discharged,
        bump_ensures(),
    );
    assert_no_summary_error(&module);
}

#[test]
fn a_declaration_cannot_count_local_obligations_toward_proved() {
    // The doc on `a_cross_crate_backed_by_authenticates_proved_only_when_it_names_an_obligation`
    // already said it: a contract-only declaration has no local body and
    // therefore no local obligations, so `backed_by` is the ONLY thing that
    // can authenticate its `proved` bit. The counting rule nevertheless
    // counted Discharged/Certified rows scoped to the declaration, so a
    // certified tautology beside a body-less `f` earned `proved` for any
    // clause text at all.
    let mut module = with_summary(
        declaration_module(),
        FunctionSummary::new()
            .with_params(vec!["x".to_string()])
            .ensuring(ProofFormula::smtlib2("(bvsgt result #x00)", "Bool"))
            .proved(),
    );
    // Even a Certified row STATING the clause backs nothing on a declaration.
    push_stating(
        &mut module,
        FuncId::new(0),
        ObligationKind::Postcondition,
        ProofStatus::Certified,
        ProofFormula::smtlib2("(bvsgt result #x00)", "Bool"),
    );
    assert_rejected(&module, "summary claims `proved` with 1 ensures clause(s)");
    assert_rejected(&module, "body-less declaration");
    // A Failed row scoped to the declaration still refutes `proved`.
    push_obligations(
        &mut module,
        FuncId::new(0),
        ObligationKind::Postcondition,
        ProofStatus::Failed,
        1,
    );
    assert_rejected(&module, "is Failed");
    // A definition with a row stating its clause is backed by it.
    let (defined, ..) = bump_module();
    let function = defined.functions[0].id;
    let mut defined = with_summary(
        defined,
        FunctionSummary::new()
            .with_params(vec!["x".to_string()])
            .ensuring(bump_ensures())
            .proved(),
    );
    push_stating(
        &mut defined,
        function,
        ObligationKind::Postcondition,
        ProofStatus::Discharged,
        bump_ensures(),
    );
    assert_no_summary_error(&defined);
}
