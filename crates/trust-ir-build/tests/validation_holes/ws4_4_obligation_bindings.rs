// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Roadmap WS4.4, NEW-1 (both halves).
//
// 1. `format::canonicalize` renumbered a function's SSA values and NOT the
//    `ClausePlace::Value` bindings that name them, so after canonicalization a
//    binding dangled or — worse — named whichever value took its old number.
//    `into_canonical` now remaps the bindings of the function's own summary
//    clauses and of every module obligation scoped to it.
// 2. A module obligation's `formula.bindings` were validated by NO rule other
//    than the v46 spec-variable one: a dangling `Value`, an out-of-range
//    `Param`, a `MutParamExit` on a non-`ensures` kind, or any non-`World`
//    place on an unscoped obligation all passed. They are now resolved against
//    the owning function (`function`, else `site.function`) exactly as a
//    summary clause is, and refused as `InvalidObligationBinding`.
//
// The fixture is `fn f(%5: u64) -> u64 { %9 = const u64 1; ret %9 }` —
// values `%5, %9`, which canonicalization renumbers to `%0, %1`.

use trust_ir::inst::Inst;
use trust_ir::node::InstrNode;
use trust_ir::proof::{
    ClauseBinding, ClausePlace, ClauseSort, ObligationKind, ObligationSite, ProofCertificate,
    ProofEvidence, ProofFormula, ProofObligation, ProofStatus, clean_cic_lineage_digest,
};
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{BlockId, FuncId, ProofId, ValueId};
use trust_ir::{Block, Function, FunctionSummary, Module};
use trust_ir_build::validate::ValidationError;
use trust_ir_build::validate_module;

fn v(i: u32) -> ValueId {
    ValueId::new(i)
}

fn bound(bindings: Vec<(&str, ClauseSort, ClausePlace)>) -> ProofFormula {
    let mut formula = ProofFormula::smtlib2("(= r r)", "Bool");
    formula.bindings = bindings
        .into_iter()
        .map(|(name, sort, place)| (name.to_string(), ClauseBinding { sort, place }))
        .collect();
    formula
}

/// `fn f(%5: <param>) -> u64 { %9 = const u64 1; ret %9 }`.
fn sparse_module(param: Ty) -> Module {
    let mut module = Module::new("ws4_4");
    let ft = module
        .add_func_type(FuncTy {
            abi: None,
            params: vec![param.clone()],
            returns: vec![Ty::U64],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), "f", ft, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.params.push((v(5), param));
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: trust_ir::Constant::Int(1),
        })
        .with_result(v(9)),
    );
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![v(9)] }));
    f.blocks.push(block);
    module
        .try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    module
}

fn obligation(id: u32, kind: ObligationKind, formula: ProofFormula) -> ProofObligation {
    ProofObligation::new(ProofId::new(id), kind, ProofStatus::Pending, "o").with_formula(formula)
}

fn scoped(id: u32, kind: ObligationKind, formula: ProofFormula) -> ProofObligation {
    obligation(id, kind, formula).with_function(FuncId::new(0))
}

/// The `InvalidObligationBinding` refusals of `m`, each as `(id, detail)`.
fn binding_refusals(m: &Module) -> Vec<(u32, String)> {
    validate_module(m)
        .into_iter()
        .filter_map(|e| match e {
            ValidationError::InvalidObligationBinding { obligation, detail } => {
                Some((obligation, detail))
            }
            _ => None,
        })
        .collect()
}

/// Exactly one `InvalidObligationBinding` on obligation 0, naming `needle`,
/// and nothing else.
fn refused_once(m: &Module, needle: &str) {
    let errors = validate_module(m);
    assert!(
        matches!(
            errors.as_slice(),
            [ValidationError::InvalidObligationBinding { obligation: 0, detail }]
                if detail.contains(needle)
        ),
        "expected one InvalidObligationBinding naming {needle:?}: {errors:?}"
    );
}

fn with(mut m: Module, o: ProofObligation) -> Module {
    m.proof_obligations.push(o);
    m
}

// ---------------------------------------------------------------------------
// positive controls: well-bound obligations are accepted
// ---------------------------------------------------------------------------

#[test]
fn ws4_4_well_bound_obligations_are_accepted() {
    let m = with(
        with(
            with(
                with(
                    sparse_module(Ty::U64),
                    scoped(
                        0,
                        ObligationKind::Postcondition,
                        bound(vec![
                            ("x", ClauseSort::BitVec(64), ClausePlace::Param { index: 0 }),
                            (
                                "r",
                                ClauseSort::BitVec(64),
                                ClausePlace::ResultSlot { index: 0 },
                            ),
                            ("v", ClauseSort::BitVec(64), ClausePlace::Value(v(9))),
                            ("h", ClauseSort::Int, ClausePlace::World),
                            ("u", ClauseSort::Bool, ClausePlace::Unwind),
                        ]),
                    ),
                ),
                // Scoped by its SITE alone: a panic-freedom row about the
                // `ret` (WS1.8 rule (c) admits that kind at a return).
                obligation(
                    1,
                    ObligationKind::PanicFreedom,
                    bound(vec![(
                        "p",
                        ClauseSort::BitVec(64),
                        ClausePlace::Value(v(5)),
                    )]),
                )
                .with_site(ObligationSite::new(FuncId::new(0), BlockId::new(0), 1)),
            ),
            // Unscoped, binding only World.
            obligation(
                2,
                ObligationKind::MemorySafety,
                bound(vec![("h", ClauseSort::Int, ClausePlace::World)]),
            ),
        ),
        // Empty bindings: UNBINDABLE, never refused here.
        obligation(
            3,
            ObligationKind::Liveness,
            ProofFormula::smtlib2("true", "Bool"),
        ),
    );
    assert_eq!(validate_module(&m), vec![]);
}

#[test]
fn ws4_4_mut_exit_is_accepted_on_a_postcondition_and_a_give_back() {
    for kind in [
        ObligationKind::Postcondition,
        ObligationKind::GiveBackRefinement,
    ] {
        let m = with(
            sparse_module(Ty::RefMut(Box::new(Ty::U64))),
            scoped(
                0,
                kind.clone(),
                bound(vec![(
                    "x'",
                    ClauseSort::BitVec(64),
                    ClausePlace::MutParamExit { index: 0 },
                )]),
            ),
        );
        assert_eq!(binding_refusals(&m), vec![], "{kind}");
    }
}

// ---------------------------------------------------------------------------
// negative twins (roadmap WS4.4 mutation control 4): each ONE mutation of
// the accepted control, refused by name
// ---------------------------------------------------------------------------

#[test]
fn ws4_4_dangling_value_binding_is_refused() {
    refused_once(
        &with(
            sparse_module(Ty::U64),
            scoped(
                0,
                ObligationKind::Postcondition,
                bound(vec![(
                    "v",
                    ClauseSort::BitVec(64),
                    ClausePlace::Value(v(7)),
                )]),
            ),
        ),
        "SSA value v7, which function #0's body never defines",
    );
}

#[test]
fn ws4_4_param_index_equal_to_arity_is_refused() {
    refused_once(
        &with(
            sparse_module(Ty::U64),
            scoped(
                0,
                ObligationKind::Postcondition,
                bound(vec![(
                    "x",
                    ClauseSort::BitVec(64),
                    ClausePlace::Param { index: 1 },
                )]),
            ),
        ),
        "Param 1 but function #0's signature declares 1 parameter(s)",
    );
    refused_once(
        &with(
            sparse_module(Ty::U64),
            scoped(
                0,
                ObligationKind::Postcondition,
                bound(vec![(
                    "r",
                    ClauseSort::BitVec(64),
                    ClausePlace::ResultSlot { index: 1 },
                )]),
            ),
        ),
        "ResultSlot 1 but function #0's signature declares 1 return value(s)",
    );
}

#[test]
fn ws4_4_value_on_an_unscoped_obligation_is_refused() {
    refused_once(
        &with(
            sparse_module(Ty::U64),
            obligation(
                0,
                ObligationKind::MemorySafety,
                bound(vec![(
                    "v",
                    ClauseSort::BitVec(64),
                    ClausePlace::Value(v(9)),
                )]),
            ),
        ),
        "an unscoped obligation may bind only World",
    );
    refused_once(
        &with(
            sparse_module(Ty::U64),
            obligation(
                0,
                ObligationKind::MemorySafety,
                bound(vec![(
                    "x",
                    ClauseSort::BitVec(64),
                    ClausePlace::Param { index: 0 },
                )]),
            ),
        ),
        "an unscoped obligation may bind only World",
    );
}

#[test]
fn ws4_4_role_illegal_places_are_refused() {
    // MutParamExit on a non-ensures kind.
    for kind in [ObligationKind::Precondition, ObligationKind::MemorySafety] {
        refused_once(
            &with(
                sparse_module(Ty::RefMut(Box::new(Ty::U64))),
                scoped(
                    0,
                    kind,
                    bound(vec![(
                        "x'",
                        ClauseSort::BitVec(64),
                        ClausePlace::MutParamExit { index: 0 },
                    )]),
                ),
            ),
            "legal only on a Postcondition or a GiveBackRefinement",
        );
    }
    // Unwind on a precondition.
    refused_once(
        &with(
            sparse_module(Ty::U64),
            scoped(
                0,
                ObligationKind::Precondition,
                bound(vec![("u", ClauseSort::Bool, ClausePlace::Unwind)]),
            ),
        ),
        "the in-flight unwind state on a Precondition",
    );
}

#[test]
fn ws4_4_sort_contradicting_the_ir_type_is_refused() {
    refused_once(
        &with(
            sparse_module(Ty::U64),
            scoped(
                0,
                ObligationKind::Postcondition,
                bound(vec![(
                    "x",
                    ClauseSort::Bool,
                    ClausePlace::Param { index: 0 },
                )]),
            ),
        ),
        "has sort Bool but Param 0 is u64",
    );
}

#[test]
fn ws4_4_blank_and_repeated_names_are_refused() {
    refused_once(
        &with(
            sparse_module(Ty::U64),
            scoped(
                0,
                ObligationKind::Postcondition,
                bound(vec![
                    ("x", ClauseSort::BitVec(64), ClausePlace::Param { index: 0 }),
                    ("x", ClauseSort::Int, ClausePlace::World),
                ]),
            ),
        ),
        "binds \"x\" more than once",
    );
    refused_once(
        &with(
            sparse_module(Ty::U64),
            scoped(
                0,
                ObligationKind::Postcondition,
                bound(vec![(" ", ClauseSort::Int, ClausePlace::World)]),
            ),
        ),
        "binds a blank free name",
    );
}

#[test]
fn ws4_4_value_on_a_declaration_is_refused() {
    let mut m = sparse_module(Ty::U64);
    let ft = m.functions[0].ty;
    m.try_add_function(Function::declaration(
        FuncId::new(1),
        "decl",
        ft,
        FunctionSummary::new(),
    ))
    .expect("Module::try_add_function: test fixture");
    m.proof_obligations.push(
        obligation(
            0,
            ObligationKind::Postcondition,
            bound(vec![(
                "v",
                ClauseSort::BitVec(64),
                ClausePlace::Value(v(0)),
            )]),
        )
        .with_function(FuncId::new(1)),
    );
    let refusals = binding_refusals(&m);
    assert!(
        matches!(refusals.as_slice(), [(0, detail)] if detail.contains("a body-less declaration")),
        "{refusals:?}"
    );
}

// ---------------------------------------------------------------------------
// NEW-1: canonicalization carries the bindings with the renumbering
// ---------------------------------------------------------------------------

/// The canonicalized body with the ORIGINAL (un-remapped) bindings: exactly
/// what `format::canonicalize` produced before WS4.4 — the mutant that skips
/// the remap.
fn skip_remap_mutant(original: &Module) -> Module {
    let mut mutant = trust_ir::format::canonicalize(original);
    mutant.functions[0].summary = original.functions[0].summary.clone();
    for (row, before) in mutant
        .proof_obligations
        .iter_mut()
        .zip(&original.proof_obligations)
    {
        row.formula = before.formula.clone();
    }
    mutant
}

fn summary_bound_to_9() -> Module {
    let mut m = sparse_module(Ty::U64);
    m.functions[0].summary = Some(
        FunctionSummary::new()
            .with_params(vec!["x".into()])
            .ensuring(bound(vec![(
                "r",
                ClauseSort::BitVec(64),
                ClausePlace::Value(v(9)),
            )])),
    );
    m
}

/// Roadmap mutation control 3 (summary half): `ensures` bound to `value(%9)`
/// becomes `value(%1)` under canonicalization; the skip-remap mutant is caught
/// by `validate_module` AND by the direct assertion.
#[test]
fn ws4_new1_summary_value_binding_follows_canonicalization() {
    let m = summary_bound_to_9();
    assert_eq!(validate_module(&m), vec![]);
    let canon = trust_ir::format::canonicalize(&m);
    assert_eq!(validate_module(&canon), vec![]);
    assert_eq!(
        canon.functions[0].summary.as_ref().unwrap().ensures[0].bindings[0]
            .1
            .place,
        ClausePlace::Value(v(1)),
        "direct assertion: %9 is renumbered to %1"
    );
    let mutant = skip_remap_mutant(&m);
    let errors = validate_module(&mutant);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::InvalidFunctionSummary { function: 0, detail }
                if detail.contains("names SSA value v9, which this function's body never defines")
        )),
        "the skip-remap mutant must be refused: {errors:?}"
    );
}

/// Roadmap mutation control 3 (obligation half), the row the roadmap names
/// `ws4.new1.obligation_binding_unvalidated`: before WS4.4's validator
/// sub-item the skip-remap mutant with the binding on a MODULE obligation
/// (`function: Some(f)`) PASSED `validate_module` (no rule read obligation
/// bindings). Both halves land in this increment, so the row is born flipped:
/// the mutant is now `InvalidObligationBinding`, and the correctly
/// canonicalized module validates.
#[test]
fn ws4_new1_obligation_binding_unvalidated() {
    let m = with(
        sparse_module(Ty::U64),
        scoped(
            0,
            ObligationKind::Postcondition,
            bound(vec![(
                "r",
                ClauseSort::BitVec(64),
                ClausePlace::Value(v(9)),
            )]),
        ),
    );
    assert_eq!(validate_module(&m), vec![]);
    let canon = trust_ir::format::canonicalize(&m);
    assert_eq!(validate_module(&canon), vec![]);
    assert_eq!(
        canon.proof_obligations[0]
            .formula
            .as_ref()
            .unwrap()
            .bindings[0]
            .1
            .place,
        ClausePlace::Value(v(1))
    );
    refused_once(
        &skip_remap_mutant(&m),
        "SSA value v9, which function #0's body never defines",
    );
}

/// A binding that names a value the function does NOT define is refused
/// before canonicalization AND after it: the rewrite moves it out of the
/// renumbered range instead of letting it name the value that took its number
/// (`%1` would otherwise name the `const` result after canonicalization).
#[test]
fn ws4_new1_dangling_binding_stays_refused_through_canonicalization() {
    let m = with(
        sparse_module(Ty::U64),
        scoped(
            0,
            ObligationKind::Postcondition,
            bound(vec![(
                "r",
                ClauseSort::BitVec(64),
                ClausePlace::Value(v(1)),
            )]),
        ),
    );
    refused_once(&m, "SSA value v1, which function #0's body never defines");
    let canon = trust_ir::format::canonicalize(&m);
    refused_once(&canon, "which function #0's body never defines");
}

/// The REVIEW note "remap vs. certificates": bindings are part of the v6
/// CleanCic lineage, so a certificate bound BEFORE canonicalization no longer
/// matches the remapped row and is refused by name — fail-closed. (No
/// `Value`-bound contract row can be kernel-Certified at all: the contract
/// grounder refuses an SSA-value place. The measurement here is only that the
/// lineage COVERS the binding: the mismatch refusal appears exactly when the
/// rewrite moves the binding, and never on the control whose binding the
/// rewrite does not touch.)
#[test]
fn ws4_new1_a_lineage_bound_before_canonicalization_is_refused_after_it() {
    let lineage_mismatch = |m: &Module| {
        validate_module(m).into_iter().any(|e| {
            matches!(
                e,
                ValidationError::CertifiedCleanCicLineageMismatch { obligation: 0 }
            )
        })
    };
    let certified = |place: ClausePlace| {
        let mut m = sparse_module(Ty::U64);
        let mut row = scoped(
            0,
            ObligationKind::Postcondition,
            bound(vec![("r", ClauseSort::BitVec(64), place)]),
        );
        row.status = ProofStatus::Certified;
        m.proof_certificates.push(ProofCertificate {
            obligation: row.id,
            prover: "trust_vc-clean-kernel".into(),
            evidence: ProofEvidence::CleanCic {
                term: vec![1],
                context: Vec::new(),
                lineage: clean_cic_lineage_digest(&row),
                kernel_recheck: None,
            },
            assurance: None,
        });
        m.proof_obligations.push(row);
        m
    };
    let value_bound = certified(ClausePlace::Value(v(9)));
    assert!(
        !lineage_mismatch(&value_bound),
        "the lineage matches before"
    );
    assert!(
        lineage_mismatch(&trust_ir::format::canonicalize(&value_bound)),
        "the remapped binding no longer matches the pre-canonical lineage"
    );
    // Control: a binding the rewrite does not move keeps its lineage.
    let param_bound = certified(ClausePlace::ResultSlot { index: 0 });
    assert!(!lineage_mismatch(&param_bound));
    assert!(!lineage_mismatch(&trust_ir::format::canonicalize(
        &param_bound
    )));
}

// ---------------------------------------------------------------------------
// Review twins (WS4.4): the remaining places and kinds of rule 2, each ONE
// mutation of an accepted control, refused by name.
// ---------------------------------------------------------------------------

/// Every non-`World` function place on an UNSCOPED obligation — not only
/// `Value` and `Param` — has no function to resolve against and is refused.
#[test]
fn ws4_4_review_every_function_place_on_an_unscoped_obligation_is_refused() {
    let exit = || Ty::RefMut(Box::new(Ty::U64));
    for (sort, place) in [
        (ClauseSort::BitVec(64), ClausePlace::ResultSlot { index: 0 }),
        (
            ClauseSort::BitVec(64),
            ClausePlace::MutParamExit { index: 0 },
        ),
        (ClauseSort::Bool, ClausePlace::Unwind),
    ] {
        // Control: the same binding on the SCOPED twin is accepted.
        let scoped_ok = with(
            sparse_module(exit()),
            scoped(
                0,
                ObligationKind::Postcondition,
                bound(vec![("x", sort.clone(), place)]),
            ),
        );
        assert_eq!(binding_refusals(&scoped_ok), vec![], "{place:?}");
        refused_once(
            &with(
                sparse_module(exit()),
                obligation(
                    0,
                    ObligationKind::Postcondition,
                    bound(vec![("x", sort, place)]),
                ),
            ),
            "an unscoped obligation may bind only World",
        );
    }
}

/// `MutParamExit` on a BY-VALUE parameter has no exit value distinct from its
/// entry value: refused by the typing rule, even on a `Postcondition`.
#[test]
fn ws4_4_review_mut_exit_on_a_by_value_parameter_is_refused() {
    refused_once(
        &with(
            sparse_module(Ty::U64),
            scoped(
                0,
                ObligationKind::Postcondition,
                bound(vec![(
                    "x_exit",
                    ClauseSort::BitVec(64),
                    ClausePlace::MutParamExit { index: 0 },
                )]),
            ),
        ),
        "uses MutParamExit on parameter 0 of type u64, which is not a &mut",
    );
}

/// The kind -> role map is closed: a v41 kind is not a post-state kind, so
/// `MutParamExit` on a `Termination` / `Ownership` / `Custom` row is refused
/// exactly like on a `MemorySafety` one.
#[test]
fn ws4_4_review_mut_exit_on_a_v41_kind_is_refused() {
    for kind in [
        ObligationKind::Termination,
        ObligationKind::Ownership,
        ObligationKind::Custom {
            namespace: "trust.contract".into(),
            name: "frame".into(),
        },
    ] {
        refused_once(
            &with(
                sparse_module(Ty::RefMut(Box::new(Ty::U64))),
                scoped(
                    0,
                    kind.clone(),
                    bound(vec![(
                        "x_exit",
                        ClauseSort::BitVec(64),
                        ClausePlace::MutParamExit { index: 0 },
                    )]),
                ),
            ),
            "legal only on a Postcondition or a GiveBackRefinement",
        );
    }
}

/// A `Value` binding resolves in the obligation's OWN function: a value
/// another function defines (here `g`'s `%3`) is dangling in `f`, even though
/// the module defines it somewhere.
#[test]
fn ws4_4_review_value_of_another_function_is_dangling() {
    let mut m = sparse_module(Ty::U64);
    let ft = m.functions[0].ty;
    let mut g = Function::new(FuncId::new(1), "g", ft, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.params.push((v(3), Ty::U64));
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![v(3)] }));
    g.blocks.push(block);
    m.try_add_function(g)
        .expect("Module::try_add_function: test fixture");
    let control = with(
        m.clone(),
        obligation(
            0,
            ObligationKind::Postcondition,
            bound(vec![(
                "r",
                ClauseSort::BitVec(64),
                ClausePlace::Value(v(3)),
            )]),
        )
        .with_function(FuncId::new(1)),
    );
    assert_eq!(validate_module(&control), vec![]);
    refused_once(
        &with(
            m,
            scoped(
                0,
                ObligationKind::Postcondition,
                bound(vec![(
                    "r",
                    ClauseSort::BitVec(64),
                    ClausePlace::Value(v(3)),
                )]),
            ),
        ),
        "SSA value v3, which function #0's body never defines",
    );
}
