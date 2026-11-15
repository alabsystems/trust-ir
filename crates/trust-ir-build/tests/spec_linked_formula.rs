// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! WS1.10 (F-014): under `SpecEnforcementMode::Linked` the spec surface fails
//! closed. A `Linked` module is a certification claim; its variable types and
//! invariant formulas are read (`trust_ir::spec_surface`) and anything outside
//! the SMT-LIB2 surface is a NAMED refusal — `SpecLinkedFormulaUnparsed` or
//! `SpecLinkedVariableUnparsed` — from both `validate_module` and the
//! certifying `link_spec_modules` pass. `DesignOnly` strings stay opaque.
//!
//! Tests are named after the proof-program rows they port
//! (`b7.spec.unparsed.*`, `crit.unex07`).

use trust_ir::{
    FuncId, HarnessManifest, Module, ProofKind, SpecAnchor, SpecEnforcementMode, SpecInvariant,
    SpecLinkOptions, SpecLinkViolation, SpecModule, SpecProjectionTarget, SpecProof, SpecVar, Ty,
    link_spec_modules,
};
use trust_ir_build::{ModuleBuilder, ValidationError, validate_module};

const MACHINE: &str = "ring";
const HARNESS: &str = "ring_push_refines";

/// The positive fixture: an embedded `Linked` machine whose one action is
/// anchored to an exact body with a typed `(&T) -> R` projection, whose one
/// proof binding resolves through a manifest, and whose invariants are
/// well-sorted SMT-LIB2 terms over declared variables of every surface type.
fn linked_module(invariants: &[(&str, &str)], vars: &[(&str, &str)]) -> Module {
    let mut mb = ModuleBuilder::new("ring_impl");
    let action_ty = mb.add_func_type(vec![], vec![]);
    let mut action = mb.function("ring::push", action_ty);
    let entry = action.create_block();
    action.switch_to_block(entry);
    action.ret(vec![]);
    action.build();

    let projection_ty = mb.add_func_type(vec![Ty::Ref(Box::new(Ty::I64))], vec![Ty::I64]);
    let mut projection = mb.function("ring::project", projection_ty);
    let entry = projection.create_block();
    projection.add_block_param(entry, Ty::Ref(Box::new(Ty::I64)));
    projection.switch_to_block(entry);
    let zero = projection.iconst(Ty::I64, 0);
    projection.ret(vec![zero]);
    projection.build();

    let mut spec = SpecModule::linked(MACHINE);
    spec.vars = vars
        .iter()
        .map(|(name, ty)| SpecVar::new(*name, *ty))
        .collect();
    spec.actions.push("Push".to_string());
    spec.invariants = invariants
        .iter()
        .map(|(name, formula)| SpecInvariant::new(*name, *formula))
        .collect();
    spec.anchors.push(SpecAnchor {
        machine: MACHINE.to_string(),
        action: "Push".to_string(),
        rust_symbol: "ring::push".to_string(),
        span: "src/ring.rs:10:4".to_string(),
        project: Some("ring::project".to_string()),
        function: Some(FuncId::new(0)),
        projection_target: Some(SpecProjectionTarget::Function(FuncId::new(1))),
    });
    spec.proofs.push(SpecProof {
        machine: MACHINE.to_string(),
        action: "Push".to_string(),
        proof_name: HARNESS.to_string(),
        kind: ProofKind::Kani,
    });
    mb.add_spec_module(spec);
    mb.build().expect("ModuleBuilder::build: test fixture")
}

const VARS: &[(&str, &str)] = &[
    ("seq", "0..7"),
    ("full", "Bool"),
    ("count", "Int"),
    ("mask", "BitVec(8)"),
];

fn good() -> Module {
    linked_module(
        &[
            ("BoundedSeq", "(and (<= 0 seq) (<= seq 7))"),
            ("FullImpliesSeven", "(=> full (= seq 7))"),
            ("CountTracksSeq", "(>= count (- seq 7))"),
            ("MaskLow", "(bvule mask #x7f)"),
        ],
        VARS,
    )
}

fn with_invariant(formula: &str) -> Module {
    linked_module(&[("Bounded", formula)], VARS)
}

fn manifest() -> HarnessManifest {
    HarnessManifest::from_names([HARNESS])
}

fn spec_link(module: &Module) -> trust_ir::SpecLinkReport {
    link_spec_modules(module, Some(&manifest()), SpecLinkOptions::default())
        .expect("well-formed manifest")
}

fn design_only(mut module: Module) -> Module {
    module.spec_modules[0].enforcement = SpecEnforcementMode::DesignOnly;
    module
}

/// Assert `module` is refused by EXACTLY one `SpecLinkedFormulaUnparsed` on
/// invariant `Bounded` whose detail contains `needle`, by the validator AND by
/// the certifying linker (the same S3 violation, non-certifying).
fn assert_formula_refused(module: &Module, needle: &str) {
    let errors = validate_module(module);
    match errors.as_slice() {
        [
            ValidationError::SpecLinkedFormulaUnparsed {
                module: machine,
                invariant,
                detail,
            },
        ] => {
            assert_eq!(machine, MACHINE);
            assert_eq!(invariant, "Bounded");
            assert!(detail.contains(needle), "{needle:?} not in {detail:?}");
        }
        other => panic!("expected exactly one SpecLinkedFormulaUnparsed, got {other:?}"),
    }
    let report = spec_link(module);
    assert!(!report.is_certifying());
    match report.violations.as_slice() {
        [SpecLinkViolation::LinkedFormulaUnparsed { detail, .. }] => {
            assert!(detail.contains(needle), "{detail}")
        }
        other => panic!("spec-link: expected exactly one S3 violation, got {other:?}"),
    }
}

/// crit.unex07 — the positive certifying `Linked` path is exercised: the
/// fixture validates with no error and the linker reports it certifying.
#[test]
fn crit_unex07_positive_linked_fixture_validates_and_certifies() {
    let module = good();
    assert_eq!(validate_module(&module), Vec::<ValidationError>::new());
    let report = spec_link(&module);
    assert!(report.is_certifying(), "{report:?}");
    assert_eq!(report.coverage.len(), 1);
    assert_eq!(report.coverage[0].enforcement, SpecEnforcementMode::Linked);
    // Without the manifest the same module is refused (L1), so the positive
    // verdict above is earned by the manifest, not by default.
    let bare = link_spec_modules(&module, None, SpecLinkOptions::default()).unwrap();
    assert!(!bare.is_certifying());
}

/// b7.spec.unparsed.garbage_syntax (Linked half).
#[test]
fn b7_spec_unparsed_garbage_syntax_linked_is_refused() {
    assert_formula_refused(
        &with_invariant(")))( @@ [] <> not a formula"),
        "not one quantifier-free SMT-LIB2 term",
    );
    // TLA+ surface syntax is refused the same way (the roadmap's named risk).
    assert_formula_refused(
        &with_invariant("[](seq >= 0)"),
        "not one quantifier-free SMT-LIB2 term",
    );
    assert_formula_refused(
        &with_invariant("seq <= 7"),
        "not one quantifier-free SMT-LIB2 term",
    );
}

/// b7.spec.unparsed.undeclared_variable (Linked half).
#[test]
fn b7_spec_unparsed_undeclared_variable_linked_is_refused() {
    assert_formula_refused(
        &with_invariant("(>= zzz_undeclared 0)"),
        "undeclared variable `zzz_undeclared`",
    );
    // A primed variable is a successor-state reference, spelled through a
    // `SpecVarNext` binding in an action relation; `seq'` is no SMT-LIB2 token
    // at all, so the one reader refuses it before any name is resolved.
    assert_formula_refused(
        &with_invariant("(<= seq' 7)"),
        "`seq'` at byte 4, which is no SMT-LIB2 token",
    );
}

/// b7.spec.unparsed.ill_typed (Linked half): an ill-sorted comparison, and a
/// variable whose declared type is not a type.
#[test]
fn b7_spec_unparsed_ill_typed_linked_is_refused() {
    assert_formula_refused(&with_invariant("(>= full 3)"), "ill-sorted");
    assert_formula_refused(&with_invariant("(= seq full)"), "ill-sorted");
    assert_formula_refused(&with_invariant("(bvult mask #x0000)"), "ill-sorted");
    assert_formula_refused(&with_invariant("(+ seq 1)"), "has sort Int");

    let module = linked_module(
        &[("Bounded", "(<= 0 seq)")],
        &[("seq", "this is not a type")],
    );
    let errors = validate_module(&module);
    // The variable is refused by name, and the invariant that uses it cannot
    // resolve it: both are named, neither is guessed.
    assert!(
        matches!(
            errors.as_slice(),
            [
                ValidationError::SpecLinkedVariableUnparsed { variable, detail, .. },
                ValidationError::SpecLinkedFormulaUnparsed { detail: formula, .. },
            ] if variable == "seq"
                && detail.contains("is not one of `Bool`, `Int`")
                && formula.contains("undeclared variable `seq`")
        ),
        "{errors:?}"
    );
    assert!(!spec_link(&module).is_certifying());
}

/// b7.spec.unparsed.linked_mode — the row as archived: under `Linked` the
/// good spec validates, garbage is refused with the NAMED reason (not the
/// blank-formula S0 refusal), and a blank formula is still S0.
#[test]
fn b7_spec_unparsed_linked_mode() {
    assert_eq!(
        validate_module(&with_invariant("(>= seq 0)")),
        Vec::<ValidationError>::new()
    );
    assert_formula_refused(
        &with_invariant(")))( @@ [] <> not a formula"),
        "not one quantifier-free",
    );
    let blank = validate_module(&with_invariant("  "));
    assert!(
        matches!(
            blank.as_slice(),
            [ValidationError::InvalidSpecStructure {
                violation: SpecLinkViolation::BlankSemanticValue {
                    field: "formula",
                    ..
                }
            }]
        ),
        "{blank:?}"
    );
}

/// Mutation control: every refused shape above validates unchanged under
/// `DesignOnly` (its strings stay opaque), so the refusals are caused by the
/// `Linked` claim and nothing else.
#[test]
fn design_only_twins_still_validate() {
    for formula in [
        ")))( @@ [] <> not a formula",
        "[](seq >= 0)",
        "(>= zzz_undeclared 0)",
        "(<= seq' 7)",
        "(>= full 3)",
    ] {
        let module = design_only(with_invariant(formula));
        assert_eq!(
            validate_module(&module),
            Vec::<ValidationError>::new(),
            "{formula}"
        );
        let report = spec_link(&module);
        assert!(report.is_ok() && !report.is_certifying(), "{report:?}");
    }
    let bad_ty = design_only(linked_module(
        &[("Bounded", "anything")],
        &[("seq", "this is not a type"), ("x y", "Int")],
    ));
    assert_eq!(validate_module(&bad_ty), Vec::<ValidationError>::new());
}

/// Variable names a `Linked` invariant could never denote (not a simple
/// symbol, primed) or that would shadow a surface operator are refused.
#[test]
fn linked_variable_names_must_be_unprimed_simple_symbols() {
    let module = linked_module(
        &[("Bounded", "(<= 0 seq)")],
        &[
            ("seq", "0..7"),
            ("seq'", "Int"),
            ("x y", "Bool"),
            ("and", "Bool"),
        ],
    );
    let errors = validate_module(&module);
    let refused: Vec<&str> = errors
        .iter()
        .filter_map(|error| match error {
            ValidationError::SpecLinkedVariableUnparsed { variable, .. } => Some(variable.as_str()),
            _ => None,
        })
        .collect();
    assert_eq!(refused, vec!["and", "seq'", "x y"], "{errors:?}");
    assert_eq!(errors.len(), 3, "{errors:?}");
}

/// [review] adversarial: a hostile nesting depth used to abort the validating
/// process (stack overflow in the sort checker) instead of refusing; a
/// no-break space was admitted as whitespace although an SMT-LIB2 reader does
/// not split on it. Both are now the named S3 refusal from validator and
/// linker, and both twins validate under `DesignOnly`.
#[test]
fn review_hostile_depth_and_non_smt_whitespace_are_named_refusals() {
    let deep = format!("{}full{}", "(not ".repeat(100_000), ")".repeat(100_000));
    assert_formula_refused(&with_invariant(&deep), "deeper than 256");
    assert_formula_refused(
        &with_invariant("(and\u{a0}full full)"),
        "neither printable ASCII",
    );
    for formula in [deep.as_str(), "(and\u{a0}full full)"] {
        assert_eq!(
            validate_module(&design_only(with_invariant(formula))),
            Vec::<ValidationError>::new()
        );
    }
}

/// [review] adversarial: a variable named after a theory function the
/// surface does not admit as an operator (`concat`, `bvcomp`) validated and
/// certified, but no SMT-LIB2 consumer can declare it. A range beyond `i128`
/// is a legitimate mathematical domain and must validate and certify.
#[test]
fn review_theory_symbol_names_refused_and_wide_ranges_admitted() {
    let module = linked_module(
        &[("Bounded", "(<= 0 seq)")],
        &[("seq", "0..7"), ("concat", "Int"), ("bvcomp", "BitVec(1)")],
    );
    let errors = validate_module(&module);
    assert!(
        matches!(
            errors.as_slice(),
            [
                ValidationError::SpecLinkedVariableUnparsed { variable: a, .. },
                ValidationError::SpecLinkedVariableUnparsed { variable: b, .. },
            ] if a == "bvcomp" && b == "concat"
        ),
        "{errors:?}"
    );
    assert!(!spec_link(&module).is_certifying());

    let wide = linked_module(
        &[(
            "Bounded",
            "(<= seq 999999999999999999999999999999999999999999)",
        )],
        &[(
            "seq",
            "-999999999999999999999999999999999999999999..999999999999999999999999999999999999999999",
        )],
    );
    assert_eq!(validate_module(&wide), Vec::<ValidationError>::new());
    assert!(spec_link(&wide).is_certifying());
}
