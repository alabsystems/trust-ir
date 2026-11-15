// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Roadmap DG-63, the trust-ir prerequisite of WS5.5: the entry-state pointee
// clause place `ClausePlace::ParamPointeeEntry { index }` (wire v62). The
// format half (codec, read gate, version selection, digests, the v38
// projection refusal) is `trust-ir/src/binary/param_pointee_place_tests.rs`;
// the text / JSON / MessagePack spellings are the `param_pointee_place`
// conformance golden.
//
// What is pinned here, against the real validator:
//
// * the place reads the value behind a `&T` / `&mut T` at ENTRY, typed
//   against `T`, and is legal on every clause role and every obligation kind
//   that may bind a parameter;
// * every parameter that is not a reference is refused BY NAME (a by-value
//   parameter, a raw pointer — even the `*mut T` `MutParamExit` admits — an
//   untyped `Ptr`, a fat pointer, an `Rc`), on a summary clause
//   (`InvalidFunctionSummary`) and on a module obligation
//   (`InvalidObligationBinding`);
// * the sort is checked against the POINTEE, so a width strip is refused;
// * the WS5.5 mutation: `requires *x > 0` on `fn f(x: &mut u64)` bound as
//   `Param { 0 }: BitVec(64)` is the width/type lie the binding check refuses,
//   and the honest spelling at this place validates;
// * a spec carrier, which has no signature, refuses the place by name.

use trust_ir::proof::{
    ClauseBinding, ClausePlace, ClauseSort, ObligationKind, ProofFormula, ProofObligation,
    ProofStatus,
};
use trust_ir::ty::{FatPtrKind, Ty};
use trust_ir::value::{FuncId, ProofId};
use trust_ir::{
    Endianness, Function, FunctionSummary, Module, Producer, SpecInvariant, SpecLinkViolation,
    SpecModule, SpecVar, TargetInfo,
};
use trust_ir_build::{ModuleBuilder, ValidationError, validate_module};

const BV64: ClauseSort = ClauseSort::BitVec(64);

fn pointee(index: u32) -> ClausePlace {
    ClausePlace::ParamPointeeEntry { index }
}

fn formula(text: &str, bindings: Vec<(&str, ClauseSort, ClausePlace)>) -> ProofFormula {
    let mut formula = ProofFormula::smtlib2(text, "Bool");
    formula.bindings = bindings
        .into_iter()
        .map(|(name, sort, place)| (name.to_string(), ClauseBinding { sort, place }))
        .collect();
    formula
}

/// `(= q q)` with the one binding `q: sort` at `place`.
fn one(sort: ClauseSort, place: ClausePlace) -> ProofFormula {
    formula("(= q q)", vec![("q", sort, place)])
}

fn aarch64() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    }
}

/// `fn probe(p0: params[0], ..)` — a body that only returns — under an
/// UNPROVED summary with the given clauses, so the always-on binding rules are
/// the only thing that can speak.
fn probe(
    params: Vec<Ty>,
    target: Option<TargetInfo>,
    requires: Vec<ProofFormula>,
    ensures: Vec<ProofFormula>,
    decreases: Vec<ProofFormula>,
) -> Module {
    let mut mb = match target {
        Some(target) => ModuleBuilder::new_with_target_info("pointee_probe", target),
        None => ModuleBuilder::new("pointee_probe"),
    };
    let ft = mb.add_func_type(params.clone(), vec![]);
    let mut fb = mb.function("probe", ft);
    fb.set_producer(Producer::TRust);
    let entry = fb.create_block();
    for ty in &params {
        let _ = fb.add_block_param(entry, ty.clone());
    }
    fb.switch_to_block(entry);
    fb.ret(vec![]);
    fb.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    let mut summary =
        FunctionSummary::new().with_params((0..params.len()).map(|i| format!("p{i}")).collect());
    summary.requires = requires;
    summary.ensures = ensures;
    summary.decreases = decreases;
    m.functions[0].summary = Some(summary);
    m
}

fn requires(params: Vec<Ty>, clause: ProofFormula) -> Vec<ValidationError> {
    validate_module(&probe(params, None, vec![clause], vec![], vec![]))
}

fn assert_only_summary_refusal(errors: &[ValidationError], needle: &str) {
    assert!(
        matches!(
            errors,
            [ValidationError::InvalidFunctionSummary { function: 0, detail }]
                if detail.contains(needle)
        ),
        "expected exactly one InvalidFunctionSummary on f0 mentioning {needle:?}; got {errors:?}"
    );
}

fn reference(ty: Ty) -> Ty {
    Ty::Ref(Box::new(ty))
}

fn reference_mut(ty: Ty) -> Ty {
    Ty::RefMut(Box::new(ty))
}

/// The place binds on EVERY role: a `requires` reads `*x`, an `ensures`
/// relates the `&mut`'s exit value to its entry value (`old(*p)`), and a
/// `decreases` measure reads the entry pointee. Each pointee is typed against
/// its own `T`.
#[test]
fn the_entry_pointee_binds_on_every_role() {
    let params = vec![reference(Ty::U64), reference_mut(Ty::U32)];
    let m = probe(
        params,
        None,
        vec![formula(
            "(bvult x_entry #x0000000000000010)",
            vec![("x_entry", BV64, pointee(0))],
        )],
        vec![formula(
            "(= p_exit (bvadd p_entry #x00000001))",
            vec![
                (
                    "p_exit",
                    ClauseSort::BitVec(32),
                    ClausePlace::MutParamExit { index: 1 },
                ),
                ("p_entry", ClauseSort::BitVec(32), pointee(1)),
            ],
        )],
        vec![formula(
            "x_entry",
            vec![("x_entry", ClauseSort::Int, pointee(0))],
        )],
    );
    assert_eq!(validate_module(&m), vec![]);
}

/// Only a REFERENCE has a pointee the format vouches for at entry. Every other
/// parameter type is refused by name — including the raw `*mut T` whose EXIT
/// value `MutParamExit` reads, because nothing in a raw pointer's type says
/// its pointee exists at entry.
#[test]
fn every_parameter_that_is_not_a_reference_is_refused_by_name() {
    let refused = [
        Ty::U64,
        Ty::PtrMut(Box::new(Ty::U64)),
        Ty::PtrConst(Box::new(Ty::U64)),
        Ty::Ptr,
        Ty::FatPtr(FatPtrKind::Str),
        Ty::Rc(Box::new(Ty::U64)),
    ];
    for ty in refused {
        assert_only_summary_refusal(
            &requires(vec![ty.clone()], one(BV64, pointee(0))),
            &format!(
                "requires clause 0 binding 'q' uses ParamPointeeEntry on parameter 0 of type \
                 {ty}, which is not a & / &mut reference"
            ),
        );
    }
    // Control: the same clause over `&u64` and `&mut u64` validates.
    assert_eq!(
        requires(vec![reference(Ty::U64)], one(BV64, pointee(0))),
        vec![]
    );
    assert_eq!(
        requires(vec![reference_mut(Ty::U64)], one(BV64, pointee(0))),
        vec![]
    );
}

/// The sort is checked against the POINTEE: `BitVec(32)` over a `&u64` is a
/// width strip; a reference to a reference reads a reference, which no sort
/// admits; a pointer-width pointee needs `target_info`.
#[test]
fn the_sort_is_checked_against_the_pointee() {
    assert_only_summary_refusal(
        &requires(
            vec![reference(Ty::U64)],
            one(ClauseSort::BitVec(32), pointee(0)),
        ),
        "requires clause 0 binding 'q' has sort BitVec(32) but ParamPointeeEntry 0 is u64",
    );
    assert_only_summary_refusal(
        &requires(
            vec![reference(reference(Ty::U8))],
            one(ClauseSort::Int, pointee(0)),
        ),
        "requires clause 0 binding 'q' has sort Int but ParamPointeeEntry 0 is &u8",
    );
    assert_only_summary_refusal(
        &requires(vec![reference(Ty::Bool)], one(BV64, pointee(0))),
        "has sort BitVec(64) but ParamPointeeEntry 0 is bool",
    );
    assert_eq!(
        requires(vec![reference(Ty::Bool)], one(ClauseSort::Bool, pointee(0))),
        vec![]
    );
    assert_only_summary_refusal(
        &requires(vec![reference(Ty::Usize)], one(BV64, pointee(0))),
        "has sort BitVec(64) but ParamPointeeEntry 0 is usize, whose width is unknown without \
         target_info",
    );
    assert_eq!(
        validate_module(&probe(
            vec![reference(Ty::Usize)],
            Some(aarch64()),
            vec![one(BV64, pointee(0))],
            vec![],
            vec![],
        )),
        vec![]
    );
}

/// An index past the signature is ONE refusal (the arity rule), not two.
#[test]
fn an_index_past_the_signature_is_refused_once() {
    assert_only_summary_refusal(
        &requires(vec![reference(Ty::U64)], one(BV64, pointee(1))),
        "requires clause 0 binding 'q' names parameter 1 but the signature declares 1 \
         parameter(s)",
    );
}

/// The WS5.5 mutation (roadmap §WS5.5, Tests): `requires *x > 0` on
/// `fn f(x: &mut u64)`, bound as `Param { 0 }: BitVec(64)`, reads the `&mut`
/// itself at a 64-bit sort — the width/type lie the binding check exists to
/// refuse. Bound at this place, the same clause validates.
#[test]
fn ws5_5_mutation_binding_a_deref_as_the_parameter_is_refused() {
    let params = || vec![reference_mut(Ty::U64)];
    let clause = |place| formula("(bvugt x #x0000000000000000)", vec![("x", BV64, place)]);
    assert_only_summary_refusal(
        &requires(params(), clause(ClausePlace::Param { index: 0 })),
        "requires clause 0 binding 'x' has sort BitVec(64) but Param 0 is &mut u64",
    );
    assert_eq!(requires(params(), clause(pointee(0))), vec![]);
}

/// A body-less declaration's summary may bind the entry pointee (unlike a
/// `Value`, which needs a body): the place is part of the signature.
#[test]
fn a_declaration_may_bind_the_entry_pointee() {
    let mut m = Module::new("pointee_declaration");
    let sig = m
        .add_func_type(trust_ir::ty::FuncTy {
            abi: None,
            params: vec![reference(Ty::U64)],
            returns: vec![],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    m.target_info = Some(aarch64());
    m.try_add_function(Function::declaration(
        FuncId::new(0),
        "reads",
        sig,
        FunctionSummary::new()
            .with_params(vec!["x".to_string()])
            .requiring(one(BV64, pointee(0))),
    ))
    .expect("Module::try_add_function: test fixture");
    assert_eq!(validate_module(&m), vec![]);
    m.functions[0].summary.as_mut().unwrap().requires[0].bindings[0]
        .1
        .place = ClausePlace::Value(trust_ir::value::ValueId::new(0));
    assert!(
        validate_module(&m).iter().any(|e| matches!(
            e,
            ValidationError::InvalidFunctionSummary { detail, .. }
                if detail.contains("on a body-less declaration")
        )),
        "control: a Value place on a declaration is refused"
    );
}

/// The obligation side (roadmap WS4.4's rule): a module obligation scoped to
/// the function binds the entry pointee on every kind, typed exactly as a
/// summary clause is, and is refused by name on a non-reference, past the
/// signature, and with no function to resolve against.
#[test]
fn a_module_obligation_binds_the_entry_pointee_under_the_same_rules() {
    let row = |kind: ObligationKind, scoped: bool, sort: ClauseSort, place: ClausePlace| {
        let mut m = probe(
            vec![Ty::U64, reference(Ty::U64)],
            None,
            vec![],
            vec![],
            vec![],
        );
        let mut obligation =
            ProofObligation::new(ProofId::new(0), kind, ProofStatus::Pending, "entry pointee")
                .with_formula(one(sort, place));
        if scoped {
            obligation = obligation.with_function(FuncId::new(0));
        }
        m.proof_obligations.push(obligation);
        validate_module(&m)
    };
    for kind in [
        ObligationKind::Precondition,
        ObligationKind::Postcondition,
        ObligationKind::Termination,
        ObligationKind::LoopInvariant,
        ObligationKind::GiveBackRefinement,
    ] {
        assert_eq!(
            row(kind.clone(), true, BV64, pointee(1)),
            vec![],
            "{kind:?}"
        );
    }
    let refused = |errors: Vec<ValidationError>, needle: &str| {
        assert!(
            matches!(
                errors.as_slice(),
                [ValidationError::InvalidObligationBinding { obligation: 0, detail }]
                    if detail.contains(needle)
            ),
            "expected one InvalidObligationBinding mentioning {needle:?}; got {errors:?}"
        );
    };
    refused(
        row(ObligationKind::Precondition, true, BV64, pointee(0)),
        "binding \"q\" uses ParamPointeeEntry on parameter 0 of type u64, which is not a & / \
         &mut reference",
    );
    refused(
        row(
            ObligationKind::Precondition,
            true,
            ClauseSort::BitVec(8),
            pointee(1),
        ),
        "binding \"q\" has sort BitVec(8) but ParamPointeeEntry 1 is u64",
    );
    refused(
        row(ObligationKind::Precondition, true, BV64, pointee(2)),
        "binds \"q\" to ParamPointeeEntry 2 but function #0's signature declares 2 parameter(s)",
    );
    refused(
        row(ObligationKind::Precondition, false, BV64, pointee(1)),
        "an unscoped obligation may bind only World",
    );
}

/// A spec carrier has no signature, so it refuses the place by name rather
/// than resolve it to whatever parameter shares the number.
#[test]
fn a_spec_carrier_refuses_the_entry_pointee() {
    let mut m = probe(vec![reference(Ty::U64)], None, vec![], vec![], vec![]);
    let typed = |place| formula("(<= seq 7)", vec![("seq", ClauseSort::Int, place)]);
    let mut machine = SpecModule::design_only("ring");
    machine.vars = vec![SpecVar::new("seq", "0..7").with_sort(ClauseSort::Int)];
    machine.invariants =
        vec![SpecInvariant::new("BoundedSeq", "(<= seq 7)").with_typed(typed(pointee(0)))];
    m.spec_modules.push(machine);
    let errors = validate_module(&m);
    assert!(
        matches!(
            errors.as_slice(),
            [ValidationError::InvalidSpecStructure {
                violation: SpecLinkViolation::SpecTypedBindingInvalid { binding, detail, .. }
            }] if binding == "seq"
                && detail.contains("ParamPointeeEntry")
                && detail.contains("a spec carrier may bind only SpecVar / SpecVarNext")
        ),
        "{errors:?}"
    );
    // Control: the same carrier over the machine's own variable validates.
    m.spec_modules[0].invariants[0].typed = Some(typed(ClausePlace::SpecVar { index: 0 }));
    assert_eq!(validate_module(&m), vec![]);
}
