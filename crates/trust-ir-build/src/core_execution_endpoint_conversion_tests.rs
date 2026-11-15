// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Endpoint presentation changes are candidate assembly, never admission.
//! Each output is checked against an independently constructed proposition in
//! the actual shared kernel, with unsafe/partial disabled. These controls claim
//! no source or native execution, and install no alternative byte vocabulary.

use super::*;
use clean_kernel::{BinderInfo, KernelTypeError};
use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};

fn limits() -> Limits {
    Limits {
        max_operations: 1_000,
        max_locals: 100,
        max_list_items: 100,
        max_lookup_candidates: 32,
        lookup_heartbeats: 5_000_000,
        lookup_cache_entries: 100_000,
    }
}

fn environment() -> &'static Environment {
    shared_specification_with_stack(EvalIrVocabulary::ByteV1)
        .unwrap()
        .env()
}

fn checker() -> TypeChecker<'static> {
    let mut checker = TypeChecker::new(environment());
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    checker.set_heartbeat_limit(5_000_000);
    checker.set_max_cache_entries(100_000);
    checker
}

fn closed(scope: &Scope, parameters: &[Local], expression: Expr, proof: bool) -> Expr {
    scope
        .close(&parameters.iter().rev().fold(expression, |body, local| {
            if proof {
                local.lam(body)
            } else {
                local.pi(body)
            }
        }))
        .unwrap()
}

fn replay(
    scope: &Scope,
    parameters: &[Local],
    proof: &PendingEquality,
    independent_claim: Expr,
    accepted: bool,
) {
    assert_eq!(proof.proposition(), independent_claim);
    let claim = closed(scope, parameters, independent_claim, false);
    let term = closed(scope, parameters, proof.term().clone(), true);
    assert!(!claim.has_fvar_quick() && !term.has_fvar_quick());
    checker()
        .check_type(&claim, &Expr::sort(Level::zero()))
        .unwrap();

    // Serialize the real complete terms, not metadata or a cached verdict.
    let term_bytes = trust_ir::proof::encode_clean_expr_dag_v2(&term).unwrap();
    let claim_bytes = trust_ir::proof::encode_clean_expr_dag_v2(&claim).unwrap();
    let decoded_term = trust_ir::proof::decode_clean_expr_dag_v2(&term_bytes).unwrap();
    let decoded_claim = trust_ir::proof::decode_clean_expr_dag_v2(&claim_bytes).unwrap();
    assert_eq!(decoded_term, term);
    assert_eq!(decoded_claim, claim);
    for actual_term in [&term, &decoded_term] {
        let kernel = checker();
        if accepted {
            kernel.check_type(actual_term, &claim).unwrap();
            let audit = environment().audit_certification(&claim, actual_term);
            assert!(audit.is_certified(), "{audit:#?}");
            for dependency in &audit.dependencies {
                assert!(environment().axiom_deps(dependency).unwrap().is_empty());
                assert!(
                    environment()
                        .trust_marker_deps(dependency)
                        .unwrap()
                        .is_empty()
                );
            }
        } else {
            let error = kernel.check_type(actual_term, &claim).unwrap_err();
            assert!(
                matches!(error, KernelTypeError::TypeMismatch { .. }),
                "semantic refusal, not a resource stop: {error:?}"
            );
            assert!(!kernel.heartbeat_spent());
        }
    }
}

#[test]
fn definitionally_equal_endpoints_reuse_exact_type_and_term_with_one_charge() {
    let original = PendingEquality::candidate(
        constant("Nat"),
        app("Nat.add", [nat(2), nat(2)]),
        nat(4),
        refl(&constant("Nat"), nat(4)),
    );
    let left = app("Nat.add", [nat(0), app("Nat.add", [nat(2), nat(2)])]);
    let right = app("Nat.succ", [nat(3)]);
    let claim = eq(&constant("Nat"), left.clone(), right.clone());
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let converted = assembler
        .convert_endpoints(original.clone(), left, right)
        .unwrap();
    assert_eq!(converted.ty, original.ty);
    assert_eq!(converted.term(), original.term());
    assert_eq!(assembler.operations(), 1);
    assert_eq!(assembler.locals, 0);
    assert_eq!(assembler.local_scope().allocated(), 0);
    replay(assembler.local_scope(), &[], &converted, claim, true);
}

#[test]
fn independently_false_left_and_right_endpoints_are_refused_by_strict_replay() {
    let original = PendingEquality::reflexive(constant("Nat"), nat(4));
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    for (left, right) in [(nat(5), nat(4)), (nat(4), nat(5)), (nat(5), nat(5))] {
        let claim = eq(&constant("Nat"), left.clone(), right.clone());
        let candidate = assembler
            .convert_endpoints(original.clone(), left, right)
            .unwrap();
        assert_eq!(candidate.ty, constant("Nat"));
        assert_eq!(candidate.term(), original.term());
        replay(assembler.local_scope(), &[], &candidate, claim, false);
    }
    assert_eq!(assembler.operations(), 3);
    assert_eq!(assembler.locals, 0);
}

#[test]
fn true_endpoint_metadata_does_not_certify_a_forged_proof_term() {
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    for term in [
        refl(&constant("Nat"), nat(5)),
        refl(&constant("Bool"), constant("Bool.true")),
        nat(4),
    ] {
        let original = PendingEquality::candidate(constant("Nat"), nat(4), nat(4), term);
        let candidate = assembler
            .convert_endpoints(original.clone(), nat(4), nat(4))
            .unwrap();
        assert_eq!(candidate.ty, original.ty);
        assert_eq!(candidate.term(), original.term());
        replay(
            assembler.local_scope(),
            &[],
            &candidate,
            eq(&constant("Nat"), nat(4), nat(4)),
            false,
        );
    }
    assert_eq!(assembler.operations(), 3);
    assert_eq!(assembler.locals, 0);
}

#[test]
fn converted_output_claim_is_checked_not_the_old_untrusted_metadata_claim() {
    // A false input metadata claim is not authority. Its actual term proves
    // only 4=4. Relabeling to that true output must not be advertised as
    // having certified the original false 4=5 proposition.
    let original = PendingEquality::candidate(
        constant("Nat"),
        nat(4),
        nat(5),
        refl(&constant("Nat"), nat(4)),
    );
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    replay(
        assembler.local_scope(),
        &[],
        &original,
        eq(&constant("Nat"), nat(4), nat(5)),
        false,
    );
    let converted = assembler
        .convert_endpoints(original, nat(4), nat(4))
        .unwrap();
    replay(
        assembler.local_scope(),
        &[],
        &converted,
        eq(&constant("Nat"), nat(4), nat(4)),
        true,
    );
    assert_eq!(assembler.operations(), 1);
}

fn halted(host: u64, cursor: u64, owners: &[Expr]) -> Expr {
    let memory = app(
        "IRByteMemoryV1.mk",
        [
            list("IRByteAllocationV1", &[]),
            Expr::lam(
                BinderInfo::Default,
                constant("Nat"),
                app("IROption.none", [constant("Nat")]),
            ),
            nat(cursor),
        ],
    );
    let world = app(
        "IRByteWorldV1.mk",
        [
            constant("Nat"),
            memory,
            nat(host),
            list("Nat", owners),
            nat(2),
        ],
    );
    app(
        "IRByteConfigV1.halted",
        [
            constant("Nat"),
            app("IROutcome.ret", [list("IRScalar", &[])]),
            world,
        ],
    )
}

#[test]
fn nonconvertible_host_memory_and_owner_worlds_cannot_replace_either_endpoint() {
    let ty = app("IRByteConfigV1", [constant("Nat")]);
    let actual = halted(0, 1, &[]);
    let original = PendingEquality::reflexive(ty.clone(), actual.clone());
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    replay(
        assembler.local_scope(),
        &[],
        &original,
        eq(&ty, actual.clone(), actual.clone()),
        true,
    );
    for wrong in [
        halted(1, 1, &[]),
        halted(0, 2, &[]),
        halted(0, 1, &[nat(1)]),
    ] {
        for (left, right) in [
            (wrong.clone(), actual.clone()),
            (actual.clone(), wrong.clone()),
        ] {
            let claim = eq(&ty, left.clone(), right.clone());
            let candidate = assembler
                .convert_endpoints(original.clone(), left, right)
                .unwrap();
            assert_eq!(candidate.ty, ty);
            assert_eq!(candidate.term(), original.term());
            replay(assembler.local_scope(), &[], &candidate, claim, false);
        }
    }
    assert_eq!(assembler.operations(), 6);
    assert_eq!(assembler.locals, 0);
    assert_eq!(assembler.local_scope().allocated(), 0);
}

#[test]
fn compound_proof_and_scoped_dependency_survive_without_another_trans_node() {
    let mut scope = Scope::new();
    let x = scope.try_local(constant("Nat")).unwrap();
    let y = scope.try_local(constant("Nat")).unwrap();
    let hypothesis = scope
        .try_local(eq(&constant("Nat"), x.term().clone(), y.term().clone()))
        .unwrap();
    let parameters = [x, y, hypothesis];
    let successor_x = app("Nat.succ", [parameters[0].term().clone()]);
    let successor_y = app("Nat.succ", [parameters[1].term().clone()]);
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let mapped = assembler
        .congruence_function(
            PendingEquality::candidate(
                constant("Nat"),
                parameters[0].term().clone(),
                parameters[1].term().clone(),
                parameters[2].term().clone(),
            ),
            constant("Nat"),
            constant("Nat.succ"),
        )
        .unwrap();
    let compound = assembler
        .compose(
            mapped,
            PendingEquality::reflexive(constant("Nat"), successor_y.clone()),
        )
        .unwrap();
    assert!(matches!(
        compound.term().get_app_fn().kind(),
        ExprKind::Const(name, _) if name == &Name::from_string("Eq.trans")
    ));
    let identity = Expr::lam(BinderInfo::Default, constant("Nat"), Expr::bvar(0));
    let left = Expr::app(identity.clone(), successor_x);
    let right = app(
        "Nat.succ",
        [Expr::app(identity, parameters[1].term().clone())],
    );
    let claim = eq(&constant("Nat"), left.clone(), right.clone());
    let converted = assembler
        .convert_endpoints(compound.clone(), left, right)
        .unwrap();
    assert_eq!(converted.ty, compound.ty);
    assert_eq!(
        converted.term(),
        compound.term(),
        "keep the whole original proof DAG"
    );
    assert_eq!(assembler.operations(), 3);
    assert_eq!(assembler.locals, 0);
    assert_eq!(assembler.local_scope().allocated(), parameters.len());
    replay(
        assembler.local_scope(),
        &parameters,
        &converted,
        claim,
        true,
    );
}

#[test]
fn exact_middle_and_type_checks_of_composition_are_not_relaxed() {
    let original = PendingEquality::reflexive(constant("Nat"), nat(4));
    let different_presentation = app("Nat.add", [nat(0), nat(4)]);
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let converted = assembler
        .convert_endpoints(original.clone(), nat(4), different_presentation.clone())
        .unwrap();
    replay(
        assembler.local_scope(),
        &[],
        &converted,
        eq(&constant("Nat"), nat(4), different_presentation.clone()),
        true,
    );
    let error = assembler
        .compose(converted.clone(), original)
        .err()
        .unwrap();
    assert!(error.contains("composition middle endpoint"), "{error}");
    assert_eq!(
        assembler.operations(),
        2,
        "failed construction remains charged"
    );
    let error = assembler
        .compose(
            converted,
            PendingEquality::reflexive(constant("Bool"), constant("Bool.true")),
        )
        .err()
        .unwrap();
    assert!(error.contains("composition type"), "{error}");
    assert_eq!(assembler.operations(), 3);
    assert_eq!(assembler.locals, 0);
}

#[test]
fn endpoint_conversion_never_changes_type_or_makes_mistyped_endpoints_well_formed() {
    let original = PendingEquality::reflexive(constant("Nat"), nat(4));
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let candidate = assembler
        .convert_endpoints(
            original.clone(),
            constant("Bool.true"),
            constant("Bool.true"),
        )
        .unwrap();
    assert_eq!(candidate.ty, original.ty);
    assert_eq!(candidate.term(), original.term());
    assert_eq!(
        candidate.proposition(),
        eq(
            &constant("Nat"),
            constant("Bool.true"),
            constant("Bool.true")
        )
    );
    let kernel = checker();
    let error = kernel
        .check_type(&candidate.proposition(), &Expr::sort(Level::zero()))
        .unwrap_err();
    assert!(
        matches!(error, KernelTypeError::TypeMismatch { .. }),
        "{error:?}"
    );
    assert!(!kernel.heartbeat_spent());
    assert_eq!(assembler.operations(), 1);
    assert_eq!(assembler.locals, 0);
}

#[test]
fn conversion_at_the_local_cap_keeps_one_charge_and_fails_closed_at_the_operation_cap() {
    let mut policy = limits();
    policy.max_operations = 2;
    policy.max_locals = 1;
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, policy).unwrap();
    let existing = assembler.local(constant("Nat")).unwrap();
    let original = PendingEquality::reflexive(constant("Nat"), nat(4));
    let converted = assembler
        .convert_endpoints(original.clone(), app("Nat.add", [nat(0), nat(4)]), nat(4))
        .unwrap();
    assert_eq!(assembler.operations(), 2);
    assert_eq!(assembler.locals, 1);
    assert_eq!(assembler.local_scope().allocated(), 1);
    assert!(assembler.local_scope().owns(&existing));
    replay(
        assembler.local_scope(),
        &[],
        &converted,
        eq(&constant("Nat"), app("Nat.add", [nat(0), nat(4)]), nat(4)),
        true,
    );
    let error = assembler
        .convert_endpoints(original, nat(4), nat(4))
        .err()
        .unwrap();
    assert!(error.contains("operation budget"), "{error}");
    assert_eq!(assembler.operations(), 2);
    assert_eq!(
        assembler.operations(),
        2,
        "observation cannot reset the ledger"
    );
    assert_eq!(assembler.locals, 1);
    assert_eq!(assembler.local_scope().allocated(), 1);
    assert!(assembler.local_scope().owns(&existing));
}
