// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Generic candidate-construction checks using existing kernel prerequisites.
//! List aliases exercise the polymorphic cons proof; Bool/Nat/Exists exercise
//! proposition branching. Neither gives semantics to the byte machine.
//! Actual run/fetch/call candidates require the consuming byte-profile environment
//! and actual-program replay; these tests deliberately do not invent one.

use super::*;
use crate::term_scope::TermScopeLimits;
use clean_kernel::env::{ConstantKind, Declaration};

fn limits() -> Limits {
    Limits {
        max_operations: 20_000,
        max_locals: 1_000,
        max_list_items: 1_000,
        max_lookup_candidates: 1_000,
        lookup_heartbeats: 1_000_000,
        lookup_cache_entries: 16_384,
    }
}

fn list_env() -> Environment {
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_list().unwrap();
    for (name, original) in [
        ("IRList", "List"),
        ("IRList.cons", "List.cons"),
        ("IRList.nil", "List.nil"),
    ] {
        let value = Expr::const_(Name::from_string(original), vec![Level::zero()]);
        let ty = TypeChecker::new(&env).infer_type(&value).unwrap();
        env.add_decl(Declaration::Definition {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
        .unwrap();
    }
    env
}

fn cons_claim() -> Expr {
    let mut scope = Scope::new();
    let a = scope.try_local(Expr::type_()).unwrap();
    let x = scope.try_local(a.term().clone()).unwrap();
    let y = scope.try_local(a.term().clone()).unwrap();
    let list_ty = app("IRList", [a.term().clone()]);
    let xs = scope.try_local(list_ty.clone()).unwrap();
    let ys = scope.try_local(list_ty.clone()).unwrap();
    let hx = scope
        .try_local(eq(a.term(), x.term().clone(), y.term().clone()))
        .unwrap();
    let hs = scope
        .try_local(eq(&list_ty, xs.term().clone(), ys.term().clone()))
        .unwrap();
    let body = eq(
        &list_ty,
        app(
            "IRList.cons",
            [a.term().clone(), x.term().clone(), xs.term().clone()],
        ),
        app(
            "IRList.cons",
            [a.term().clone(), y.term().clone(), ys.term().clone()],
        ),
    );
    let parameters = [a, x, y, xs, ys, hx, hs];
    let claim = parameters
        .iter()
        .rev()
        .fold(body, |body, local| local.pi(body));
    scope.close(&claim).unwrap()
}

#[test]
fn polymorphic_cons_candidate_kernel_checks_and_has_no_axiom_closure() {
    let env = list_env();
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let proof = assembler.cons_congruence().unwrap();
    let locals = assembler.locals;
    assert_eq!(assembler.cons_congruence().unwrap(), proof);
    assert_eq!(
        assembler.locals, locals,
        "cached generic helper allocates no new binders"
    );
    let claim = cons_claim();
    TypeChecker::new(&env).check_type(&proof, &claim).unwrap();
    let audit = env.audit_certification(&claim, &proof);
    assert!(audit.is_certified(), "{audit:#?}");
    assert!(
        audit
            .dependencies
            .iter()
            .all(|dependency| env.get_const(dependency).unwrap().kind != ConstantKind::Axiom)
    );
}

#[test]
fn cons_instantiation_preserves_both_arguments_and_rejects_changed_tail_or_head() {
    let env = list_env();
    let mut scope = Scope::new();
    let proof = Assembler::new(&mut scope, limits())
        .unwrap()
        .cons_congruence()
        .unwrap();
    let scalar = constant("Nat");
    let ty = app("IRList", [scalar.clone()]);
    let tail = list("Nat", &[nat(9)]);
    let expected = app("IRList.cons", [scalar.clone(), nat(4), tail.clone()]);
    let application = Expr::apps(
        proof,
        [
            scalar.clone(),
            nat(4),
            nat(4),
            tail.clone(),
            tail.clone(),
            refl(&scalar, nat(4)),
            refl(&ty, tail),
        ],
    );
    let claim = eq(&ty, expected.clone(), expected.clone());
    TypeChecker::new(&env)
        .check_type(&application, &claim)
        .unwrap();
    for changed in [
        list("Nat", &[nat(5), nat(9)]),
        list("Nat", &[nat(4), nat(10)]),
    ] {
        let error = TypeChecker::new(&env)
            .check_type(&application, &eq(&ty, expected.clone(), changed))
            .unwrap_err();
        assert!(
            matches!(error, clean_kernel::TypeError::TypeMismatch { .. }),
            "expected type mismatch, got {error:?}"
        );
    }
}

#[test]
fn repeated_cons_applications_do_not_capture_actual_suffixes_under_new_binders() {
    let mut scope = Scope::new();
    let value = scope.try_local(constant("Nat")).unwrap();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let helper = assembler.cons_congruence().unwrap();
    let local_count = assembler.locals;
    let build = |count: usize| {
        let ty = app("IRList", [constant("Nat")]);
        let mut tail = list("Nat", &[]);
        let mut proof = refl(&ty, tail.clone());
        for _ in 0..count {
            proof = Expr::apps(
                helper.clone(),
                [
                    constant("Nat"),
                    value.term().clone(),
                    value.term().clone(),
                    tail.clone(),
                    tail.clone(),
                    refl(&constant("Nat"), value.term().clone()),
                    proof,
                ],
            );
            tail = app("IRList.cons", [constant("Nat"), value.term().clone(), tail]);
        }
        value.lam(proof)
    };
    let small = build(32);
    let large = build(64);
    assert_eq!(assembler.locals, local_count);
    drop(assembler);
    let small = scope
        .close_with_limits(&small, TermScopeLimits::default())
        .unwrap();
    let large = scope
        .close_with_limits(&large, TermScopeLimits::default())
        .unwrap();
    assert!(
        large.stats.visits <= small.stats.visits * 3,
        "closing visits grew from {} to {}",
        small.stats.visits,
        large.stats.visits
    );
    // This regression measures the closing graph only, not total checker work.
    assert_eq!(large.stats.max_binder_depth, small.stats.max_binder_depth);
}

#[test]
fn ordered_list_congruence_checks_pointwise_proofs_and_strict_mutations() {
    let env = list_env();
    let mut scope = Scope::new();
    let x = scope.try_local(constant("Nat")).unwrap();
    let y = scope.try_local(constant("Nat")).unwrap();
    let h = scope
        .try_local(eq(&constant("Nat"), x.term().clone(), y.term().clone()))
        .unwrap();
    let pointwise = PendingEquality::candidate(
        constant("Nat"),
        x.term().clone(),
        y.term().clone(),
        h.term().clone(),
    );
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let result = assembler
        .list_congruence(
            constant("Nat"),
            &[
                pointwise.clone(),
                PendingEquality::reflexive(constant("Nat"), nat(9)),
                pointwise,
            ],
        )
        .unwrap();
    let left = list("Nat", &[x.term().clone(), nat(9), x.term().clone()]);
    let right = list("Nat", &[y.term().clone(), nat(9), y.term().clone()]);
    let ty = app("IRList", [constant("Nat")]);
    assert_eq!(result.left(), &left);
    assert_eq!(result.right(), &right);
    let claim = eq(&ty, left.clone(), right);
    let changed = [
        list("Nat", &[y.term().clone(), y.term().clone(), nat(9)]),
        list("Nat", &[y.term().clone(), nat(9)]),
        list("Nat", &[y.term().clone(), nat(10), y.term().clone()]),
    ];
    drop(assembler);
    let parameters = [x, y, h];
    let close_claim = |claim| {
        scope
            .close(&parameters.iter().rev().fold(claim, |body, p| p.pi(body)))
            .unwrap()
    };
    let proof = scope
        .close(
            &parameters
                .iter()
                .rev()
                .fold(result.term().clone(), |body, p| p.lam(body)),
        )
        .unwrap();
    let claim = close_claim(claim);
    TypeChecker::new(&env).check_type(&proof, &claim).unwrap();
    assert!(env.audit_certification(&claim, &proof).is_certified());
    // Inhabit all original domains jointly, not just the conditional theorem.
    let witnesses = [nat(4), nat(4), refl(&constant("Nat"), nat(4))];
    let instance = Expr::apps(proof.clone(), witnesses.clone());
    let instantiate = |claim: Expr| {
        witnesses.iter().fold(claim, |claim, witness| {
            let ExprKind::Pi(_, domain, body) = claim.kind() else {
                panic!("original list telescope")
            };
            TypeChecker::new(&env).check_type(witness, domain).unwrap();
            body.instantiate(witness)
        })
    };
    TypeChecker::new(&env)
        .check_type(&instance, &instantiate(claim))
        .unwrap();
    for changed in changed {
        let mutant = close_claim(eq(&ty, left.clone(), changed));
        for (proof, claim) in [(&proof, mutant.clone()), (&instance, instantiate(mutant))] {
            let error = TypeChecker::new(&env)
                .check_type(proof, &claim)
                .unwrap_err();
            assert!(
                matches!(error, clean_kernel::TypeError::TypeMismatch { .. }),
                "{error:?}"
            );
        }
    }
    // A Rust equality carrier does not establish its supplied pointwise proof.
    let mut bad_scope = Scope::new();
    let bad = Assembler::new(&mut bad_scope, limits())
        .unwrap()
        .list_congruence(
            constant("Nat"),
            &[PendingEquality::candidate(
                constant("Nat"),
                nat(4),
                nat(5),
                refl(&constant("Nat"), nat(4)),
            )],
        )
        .unwrap();
    let error = TypeChecker::new(&env)
        .check_type(bad.term(), &bad.proposition())
        .unwrap_err();
    assert!(
        matches!(error, clean_kernel::TypeError::TypeMismatch { .. }),
        "{error:?}"
    );
}

#[test]
fn list_congruence_preserves_empty_case_and_construction_limits() {
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let empty = assembler.list_congruence(constant("Nat"), &[]).unwrap();
    assert_eq!(empty.left(), &list("Nat", &[]));
    assert_eq!(empty.left(), empty.right());
    assert_eq!(assembler.locals, 0);
    TypeChecker::new(&list_env())
        .check_type(empty.term(), &empty.proposition())
        .unwrap();
    let wrong_type = PendingEquality::reflexive(constant("Bool"), constant("Bool.true"));
    assert!(
        assembler
            .list_congruence(constant("Nat"), &[wrong_type])
            .err()
            .expect("wrong list element type")
            .contains("element type")
    );
    let mut capped = limits();
    capped.max_list_items = 2;
    let mut capped_scope = Scope::new();
    let mut capped_assembler = Assembler::new(&mut capped_scope, capped).unwrap();
    let facts = vec![PendingEquality::reflexive(constant("Nat"), nat(4)); 3];
    assert!(
        capped_assembler
            .list_congruence(constant("Nat"), &facts)
            .is_err()
    );
    assert_eq!(
        capped_assembler.locals, 0,
        "oversized input refused before helper construction"
    );
    let mut capped = limits();
    capped.max_operations = 1;
    let mut capped_scope = Scope::new();
    assert!(
        Assembler::new(&mut capped_scope, capped)
            .unwrap()
            .list_congruence(constant("Nat"), &facts[..1])
            .is_err()
    );
}

#[test]
fn list_congruence_reuses_one_helper_and_closes_shared_suffixes_linearly() {
    let mut scope = Scope::new();
    let x = scope.try_local(constant("Nat")).unwrap();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let facts: Vec<_> = (0..256)
        .map(|i| {
            PendingEquality::reflexive(
                constant("Nat"),
                if i % 3 == 0 {
                    x.term().clone()
                } else {
                    nat((i % 7) as u64)
                },
            )
        })
        .collect();
    let small = assembler
        .list_congruence(constant("Nat"), &facts[..128])
        .unwrap();
    let locals = assembler.locals;
    let scope_locals = assembler.scope.allocated();
    let large = assembler.list_congruence(constant("Nat"), &facts).unwrap();
    assert_eq!(assembler.locals, locals);
    assert_eq!(assembler.scope.allocated(), scope_locals);
    assert_eq!(
        large.left(),
        &list(
            "Nat",
            &facts.iter().map(|p| p.left().clone()).collect::<Vec<_>>()
        )
    );
    drop(assembler);
    let small = scope
        .close_with_limits(&x.lam(small.term().clone()), TermScopeLimits::default())
        .unwrap();
    let large = scope
        .close_with_limits(&x.lam(large.term().clone()), TermScopeLimits::default())
        .unwrap();
    assert!(
        large.stats.visits <= small.stats.visits * 3,
        "closing visits {} -> {}",
        small.stats.visits,
        large.stats.visits
    );
    assert_eq!(large.stats.max_binder_depth, small.stats.max_binder_depth);
    // Structural graph/closure evidence only: not total kernel or compiler time.
}

#[test]
fn actual_resolve_preserves_order_and_shares_suffixes_without_per_operand_binders() {
    // Structural construction/closure coverage, not a kernel check of ir_getd
    // or ir_resolve. Those actual byte definitions belong to the real consumer.
    let mut scope = Scope::new();
    let machine = scope.try_local(constant("IRMachine")).unwrap();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let empty = assembler.resolve(machine.term(), &[]).unwrap();
    assert_eq!(assembler.locals, 0, "empty resolution needs no cons helper");
    assert_eq!(
        empty.left(),
        &app("ir_resolve", [machine.term().clone(), list("Nat", &[])])
    );
    assert_eq!(empty.right(), &list("IRScalar", &[]));

    let facts = |count: usize| {
        (0..count)
            .map(|index| {
                // Deliberately nonmonotonic, with repetitions: operand order
                // and multiplicity must survive, not sorting/deduplication.
                let id = ValueId::new(u32::try_from(41 + (index * 17) % 31).unwrap());
                let value = app(
                    "ir_getd",
                    [machine.term().clone(), nat(u64::from(id.index()))],
                );
                LookupFact::candidate(
                    machine.term().clone(),
                    id,
                    value.clone(),
                    PendingEquality::reflexive(constant("IRScalar"), value),
                )
                .unwrap()
            })
            .collect::<Vec<_>>()
    };
    let small_facts = facts(128);
    let large_facts = facts(256);
    let small = assembler.resolve(machine.term(), &small_facts).unwrap();
    let helper_locals = assembler.locals;
    let scope_locals = assembler.scope.allocated();
    assert!(
        helper_locals > 0,
        "first nonempty resolve constructs the helper"
    );
    let large = assembler.resolve(machine.term(), &large_facts).unwrap();
    assert_eq!(assembler.locals, helper_locals);
    assert_eq!(assembler.scope.allocated(), scope_locals);
    for (resolution, facts) in [(&small, &small_facts), (&large, &large_facts)] {
        let ids = facts
            .iter()
            .map(|fact| nat(u64::from(fact.id.index())))
            .collect::<Vec<_>>();
        let values = facts
            .iter()
            .map(|fact| fact.value.clone())
            .collect::<Vec<_>>();
        assert_eq!(
            resolution.left(),
            &app("ir_resolve", [machine.term().clone(), list("Nat", &ids)])
        );
        assert_eq!(resolution.right(), &list("IRScalar", &values));
    }
    let empty_term = machine.lam(empty.term().clone());
    let small_term = machine.lam(small.term().clone());
    let large_term = machine.lam(large.term().clone());
    drop(assembler);
    assert!(!scope.close(&empty_term).unwrap().has_fvar_quick());
    let small = scope
        .close_with_limits(&small_term, TermScopeLimits::default())
        .unwrap();
    let large = scope
        .close_with_limits(&large_term, TermScopeLimits::default())
        .unwrap();
    assert!(
        large.stats.visits <= small.stats.visits * 3,
        "actual resolve closing visits grew from {} to {}",
        small.stats.visits,
        large.stats.visits
    );
    assert_eq!(large.stats.max_binder_depth, small.stats.max_binder_depth);
}

#[test]
fn construction_limits_and_wrong_typed_fuel_fail_without_panics() {
    let mut scope = Scope::new();
    let ty = scope.try_local(Expr::type_()).unwrap();
    assert!(NatTerm::local(&ty).is_err());
    let mut invalid = limits();
    invalid.max_operations = 0;
    assert!(Assembler::new(&mut scope, invalid).is_err());
    let mut bounded = limits();
    bounded.max_locals = 1;
    let mut assembler = Assembler::new(&mut scope, bounded).unwrap();
    assert!(assembler.cons_congruence().is_err());
    assert!(
        assembler
            .bindings(&[ValueId::new(1)], &[], list("IRBinding", &[]))
            .is_err()
    );
    let a = PendingEquality::reflexive(constant("Nat"), nat(0));
    let b = PendingEquality::reflexive(constant("Nat"), nat(1));
    assert!(assembler.compose(a, b).is_err());
}

#[test]
fn exact_run_branch_closes_with_fixed_fuel_and_external_worlds() {
    // Structural endpoint/closure regression. The two run premises are explicit
    // arbitrary inputs, not proofs of any byte-machine execution in this test.
    let mut scope = Scope::new();
    let world = scope.try_local(Expr::type_()).unwrap();
    let model = MachineModel::from_terms(
        world.term().clone(),
        constant("test_context"),
        constant("test_providers"),
    );
    let flag = scope.try_local(constant("Bool")).unwrap();
    let initial = scope.try_local(model.config_type()).unwrap();
    let false_world = scope.try_local(model.config_type()).unwrap();
    let true_world = scope.try_local(model.config_type()).unwrap();
    let false_fuel = NatTerm::literal(3);
    let true_fuel = NatTerm::literal(7);
    let false_proof = scope
        .try_local(eq(
            &model.config_type(),
            model.run(&false_fuel, initial.term().clone()),
            false_world.term().clone(),
        ))
        .unwrap();
    let true_proof = scope
        .try_local(eq(
            &model.config_type(),
            model.run(&true_fuel, initial.term().clone()),
            true_world.term().clone(),
        ))
        .unwrap();
    let candidate = |fuel: NatTerm, reached: Expr, proof: Expr| {
        ExactRun::candidate(
            model.clone(),
            initial.term().clone(),
            reached.clone(),
            fuel.clone(),
            PendingEquality::candidate(
                model.config_type(),
                model.run(&fuel, initial.term().clone()),
                reached,
                proof,
            ),
        )
    };
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let branched = assembler
        .branch(
            &model,
            flag.term().clone(),
            initial.term().clone(),
            |_, _| {
                candidate(
                    false_fuel,
                    false_world.term().clone(),
                    false_proof.term().clone(),
                )
            },
            |_, _| {
                candidate(
                    true_fuel,
                    true_world.term().clone(),
                    true_proof.term().clone(),
                )
            },
        )
        .unwrap();
    assert_eq!(
        branched.fuel().term(),
        &choose(&constant("Nat"), flag.term().clone(), nat(7), nat(3))
    );
    assert_eq!(
        branched.reached(),
        &choose(
            &model.config_type(),
            flag.term().clone(),
            true_world.term().clone(),
            false_world.term().clone(),
        )
    );
    assert_eq!(
        branched.equality().left(),
        &model.run(branched.fuel(), initial.term().clone())
    );
    assert_eq!(branched.equality().right(), branched.reached());
    drop(assembler);
    let parameters = [
        world,
        flag,
        initial,
        false_world,
        true_world,
        false_proof,
        true_proof,
    ];
    let proof = parameters
        .iter()
        .rev()
        .fold(branched.equality().term().clone(), |body, p| p.lam(body));
    let claim = parameters
        .iter()
        .rev()
        .fold(branched.equality().proposition(), |body, p| p.pi(body));
    assert!(!scope.close(&proof).unwrap().has_fvar_quick());
    assert!(!scope.close(&claim).unwrap().has_fvar_quick());
}

#[test]
fn one_step_caches_closed_case_candidate_and_retains_exact_neutral_endpoint() {
    // Actual byte-kernel replay belongs to the consuming environment. Here the
    // public method is exercised structurally on an arbitrary neutral config;
    // no alternate byte definitions are installed just to make this test pass.
    let mut scope = Scope::new();
    let model = MachineModel::from_terms(
        constant("Nat"),
        constant("test_context"),
        constant("test_providers"),
    );
    let initial = scope.try_local(model.config_type()).unwrap();
    let step = model.step(initial.term().clone());
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let first = assembler
        .one_step(
            &model,
            initial.term().clone(),
            PendingEquality::reflexive(model.config_type(), step.clone()),
        )
        .unwrap();
    let locals = assembler.locals;
    let allocated = assembler.scope.allocated();
    assert_eq!(
        locals, 0,
        "the fixed closed helper allocates no caller locals"
    );
    assert!(!assembler.run_one_candidate().unwrap().has_fvar_quick());
    let second = assembler
        .one_step(
            &model,
            initial.term().clone(),
            PendingEquality::reflexive(model.config_type(), step.clone()),
        )
        .unwrap();
    assert_eq!(assembler.locals, locals);
    assert_eq!(assembler.scope.allocated(), allocated);
    assert_eq!(first.equality().term(), second.equality().term());
    assert_eq!(first.fuel().term(), &nat(1));
    assert_eq!(
        first.equality().left(),
        &model.run(&NatTerm::literal(1), initial.term().clone())
    );
    assert_eq!(first.reached(), &step);
    assert_eq!(first.equality().right(), &step);
    assert!(
        assembler
            .one_step(
                &model,
                initial.term().clone(),
                PendingEquality::reflexive(model.config_type(), initial.term().clone()),
            )
            .is_err(),
        "a candidate about a different step endpoint must be refused"
    );
    drop(assembler);
    assert!(
        !scope
            .close(&initial.lam(first.equality().term().clone()))
            .unwrap()
            .has_fvar_quick()
    );
}

#[test]
fn exact_run_branch_rejects_arm_local_fuel_and_world_escape() {
    use crate::{scoped_local::LocalScopeError, term_scope::TermScopeError};
    for escape_fuel in [false, true] {
        let mut scope = Scope::new();
        let model = MachineModel::from_terms(
            constant("Nat"),
            constant("test_context"),
            constant("test_providers"),
        );
        let flag = scope.try_local(constant("Bool")).unwrap();
        let initial = scope.try_local(model.config_type()).unwrap();
        let reached = scope.try_local(model.config_type()).unwrap();
        let fuel = NatTerm::literal(3);
        let premise = scope
            .try_local(eq(
                &model.config_type(),
                model.run(&fuel, initial.term().clone()),
                reached.term().clone(),
            ))
            .unwrap();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let mut escaped_id = None;
        let branch = assembler
            .branch(
                &model,
                flag.term().clone(),
                initial.term().clone(),
                |assembler, _| {
                    let witness = assembler.local(if escape_fuel {
                        constant("Nat")
                    } else {
                        model.config_type()
                    })?;
                    escaped_id = Some(witness.id());
                    let local_fuel = if escape_fuel {
                        NatTerm::local(&witness)?
                    } else {
                        fuel.clone()
                    };
                    let local_world = if escape_fuel {
                        reached.term().clone()
                    } else {
                        witness.term().clone()
                    };
                    // The witness is bound only inside this arm's proof, but the
                    // malformed candidate attempts to export it in fuel/world.
                    let proof = witness.let_(
                        if escape_fuel {
                            nat(3)
                        } else {
                            reached.term().clone()
                        },
                        premise.term().clone(),
                    );
                    ExactRun::candidate(
                        model.clone(),
                        initial.term().clone(),
                        local_world.clone(),
                        local_fuel.clone(),
                        PendingEquality::candidate(
                            model.config_type(),
                            model.run(&local_fuel, initial.term().clone()),
                            local_world,
                            proof,
                        ),
                    )
                },
                |_, _| {
                    ExactRun::candidate(
                        model.clone(),
                        initial.term().clone(),
                        reached.term().clone(),
                        fuel.clone(),
                        PendingEquality::candidate(
                            model.config_type(),
                            model.run(&fuel, initial.term().clone()),
                            reached.term().clone(),
                            premise.term().clone(),
                        ),
                    )
                },
            )
            .unwrap();
        drop(assembler);
        let parameters = [flag, initial, reached, premise];
        let proof = parameters
            .iter()
            .rev()
            .fold(branch.equality().term().clone(), |body, p| p.lam(body));
        assert_eq!(
            scope.close(&proof),
            Err(LocalScopeError::Closure(TermScopeError::OutOfScope(
                escaped_id.unwrap()
            )))
        );
    }
}

fn existential_branch_candidate(corrupt_arm: Option<bool>) -> (Expr, Expr) {
    existential_branch_candidate_with_context(corrupt_arm, false)
}

fn existential_branch_candidate_with_context(
    corrupt_arm: Option<bool>,
    with_context: bool,
) -> (Expr, Expr) {
    let mut scope = Scope::new();
    let flag = scope.try_local(constant("Bool")).unwrap();
    let number = scope.try_local(constant("Nat")).unwrap();
    let selected = choose(&constant("Nat"), flag.term().clone(), nat(7), nat(3));
    let predicate = number.lam(eq(
        &constant("Nat"),
        selected.clone(),
        number.term().clone(),
    ));
    let exists = |name: &str, arguments: Vec<Expr>| {
        Expr::apps(
            Expr::const_(Name::from_string(name), vec![Level::succ(Level::zero())]),
            arguments,
        )
    };
    let goal = exists("Exists", vec![constant("Nat"), predicate.clone()]);
    let build_arm = |assembler: &mut Assembler<'_>,
                     hypothesis: PendingEquality,
                     is_true: bool|
     -> Result<PendingProof> {
        let expected = if is_true { 7 } else { 3 };
        let mapped = assembler.congruence(hypothesis, constant("Nat"), |b| {
            choose(&constant("Nat"), b, nat(7), nat(3))
        })?;
        let before =
            assembler.conversion(constant("Nat"), selected.clone(), mapped.left().clone())?;
        let after = assembler.conversion(constant("Nat"), mapped.right().clone(), nat(expected))?;
        let proof = assembler.compose(before, mapped)?;
        let proof = assembler.compose(proof, after)?;
        let witness = assembler.local(constant("Nat"))?;
        let introduced = exists(
            "Exists.intro",
            vec![
                constant("Nat"),
                predicate.clone(),
                witness.term().clone(),
                proof.term().clone(),
            ],
        );
        let value = if corrupt_arm == Some(is_true) {
            99
        } else {
            expected
        };
        Ok(PendingProof::candidate(
            goal.clone(),
            witness.let_(nat(value), introduced),
        ))
    };
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let candidate = if with_context {
        // Deliberately not Clone: neither callback owns a snapshot of this state.
        struct Context {
            visited: Vec<bool>,
        }
        let mut context = Context { visited: vec![] };
        let candidate = assembler
            .branch_proposition_with_context(
                &mut context,
                flag.term().clone(),
                goal.clone(),
                |a, context, h| {
                    assert!(context.visited.is_empty());
                    context.visited.push(false);
                    build_arm(a, h, false)
                },
                |a, context, h| {
                    assert_eq!(context.visited, [false]);
                    context.visited.push(true);
                    build_arm(a, h, true)
                },
            )
            .unwrap();
        assert_eq!(context.visited, [false, true]);
        candidate
    } else {
        assembler
            .branch_proposition(
                flag.term().clone(),
                goal.clone(),
                |a, h| build_arm(a, h, false),
                |a, h| build_arm(a, h, true),
            )
            .unwrap()
    };
    assert_eq!(candidate.proposition(), &goal);
    drop(assembler);
    (
        scope.close(&flag.lam(candidate.term().clone())).unwrap(),
        scope.close(&flag.pi(goal)).unwrap(),
    )
}

#[test]
fn proposition_branch_kernel_checks_local_existentials_and_rejects_either_wrong_arm() {
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_bool().unwrap();
    env.init_nat().unwrap();
    env.init_exists().unwrap();
    let (proof, claim) = existential_branch_candidate(None);
    TypeChecker::new(&env).check_type(&proof, &claim).unwrap();
    let audit = env.audit_certification(&claim, &proof);
    assert!(audit.is_certified(), "{audit:#?}");
    assert!(
        audit
            .dependencies
            .iter()
            .all(|name| env.get_const(name).unwrap().kind != ConstantKind::Axiom)
    );
    // Each minor premise must prove the SAME actual existential goal. Changing
    // either arm's local witness is rejected, even though the other is correct.
    for arm in [false, true] {
        let (changed, same_claim) = existential_branch_candidate(Some(arm));
        assert_eq!(same_claim, claim);
        let error = TypeChecker::new(&env)
            .check_type(&changed, &claim)
            .unwrap_err();
        assert!(
            matches!(error, clean_kernel::TypeError::TypeMismatch { .. }),
            "expected type mismatch, got {error:?}"
        );
    }
}

#[test]
fn proposition_branch_context_preserves_closed_kernel_proof_and_strict_wrong_arm_refusals() {
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_bool().unwrap();
    env.init_nat().unwrap();
    env.init_exists().unwrap();
    let (proof, claim) = existential_branch_candidate_with_context(None, true);
    assert_eq!(
        (proof.clone(), claim.clone()),
        existential_branch_candidate(None)
    );
    TypeChecker::new(&env).check_type(&proof, &claim).unwrap();
    let audit = env.audit_certification(&claim, &proof);
    assert!(audit.is_certified(), "{audit:#?}");
    assert!(
        audit
            .dependencies
            .iter()
            .all(|name| { env.get_const(name).unwrap().kind != ConstantKind::Axiom })
    );
    for arm in [false, true] {
        let (changed, same_claim) = existential_branch_candidate_with_context(Some(arm), true);
        assert_eq!(same_claim, claim);
        let error = TypeChecker::new(&env)
            .check_type(&changed, &claim)
            .unwrap_err();
        assert!(
            matches!(error, clean_kernel::TypeError::TypeMismatch { .. }),
            "expected type mismatch, got {error:?}"
        );
    }
}

#[test]
fn proposition_branch_context_shares_arm_order_and_unchanged_construction_budget() {
    struct Context {
        visits: Vec<(bool, usize, usize)>,
    }
    let mut results = Vec::new();
    for with_context in [false, true] {
        let mut scope = Scope::new();
        let flag = scope.try_local(constant("Bool")).unwrap();
        let goal = eq(&constant("Nat"), nat(0), nat(0));
        let arm = |a: &mut Assembler<'_>, _: PendingEquality| -> Result<PendingProof> {
            a.local(constant("Nat"))?;
            Ok(PendingProof::candidate(
                goal.clone(),
                refl(&constant("Nat"), nat(0)),
            ))
        };
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let candidate = if with_context {
            let mut context = Context { visits: vec![] };
            let candidate = assembler
                .branch_proposition_with_context(
                    &mut context,
                    flag.term().clone(),
                    goal.clone(),
                    |a, context, h| {
                        assert!(context.visits.is_empty());
                        context.visits.push((false, a.operations, a.locals));
                        arm(a, h)
                    },
                    |a, context, h| {
                        assert_eq!(context.visits, [(false, 3, 2)]);
                        context.visits.push((true, a.operations, a.locals));
                        arm(a, h)
                    },
                )
                .unwrap();
            assert_eq!(context.visits, [(false, 3, 2), (true, 4, 3)]);
            candidate
        } else {
            assembler
                .branch_proposition(
                    flag.term().clone(),
                    goal.clone(),
                    |a, h| arm(a, h),
                    |a, h| arm(a, h),
                )
                .unwrap()
        };
        let spent = (assembler.operations, assembler.locals);
        assert_eq!(spent, (7, 6));
        drop(assembler);
        results.push((
            scope.close(&flag.lam(candidate.term().clone())).unwrap(),
            spent,
        ));
    }
    assert_eq!(
        results[0], results[1],
        "the legacy entry has the same proof and charges"
    );
}

#[test]
fn proposition_branch_context_second_arm_exhaustion_preserves_both_owners() {
    struct Context {
        visited: Vec<bool>,
    }
    for local_budget in [false, true] {
        let mut policy = limits();
        if local_budget {
            policy.max_locals = 3;
        } else {
            policy.max_operations = 4;
        }
        let mut scope = Scope::new();
        let flag = scope.try_local(constant("Bool")).unwrap();
        let goal = eq(&constant("Nat"), nat(0), nat(0));
        let mut context = Context { visited: vec![] };
        let mut assembler = Assembler::new(&mut scope, policy).unwrap();
        let error = assembler
            .branch_proposition_with_context(
                &mut context,
                flag.term().clone(),
                goal.clone(),
                |a, context, _| {
                    context.visited.push(false);
                    a.local(constant("Nat"))?;
                    Ok(PendingProof::candidate(
                        goal.clone(),
                        refl(&constant("Nat"), nat(0)),
                    ))
                },
                |a, context, _| {
                    assert_eq!(context.visited, [false]);
                    assert_eq!((a.operations, a.locals), (4, 3));
                    context.visited.push(true);
                    a.local(constant("Nat"))?;
                    panic!("second-arm local must exhaust the shared budget");
                },
            )
            .err()
            .unwrap();
        assert_eq!(context.visited, [false, true]);
        let expected = if local_budget {
            "execution construction local budget exceeded"
        } else {
            "execution construction operation budget exceeded"
        };
        assert_eq!(error, expected);
        assert_eq!(
            (assembler.operations, assembler.locals),
            (if local_budget { 5 } else { 4 }, 3)
        );
        assert_eq!(assembler.local(constant("Nat")).err().unwrap(), expected);
        assert_eq!(
            (assembler.operations, assembler.locals),
            (if local_budget { 6 } else { 4 }, 3)
        );
        assert_eq!(
            context.visited,
            [false, true],
            "failure must not roll back caller state"
        );
    }
}

#[test]
fn proposition_branch_rejects_different_arm_goal_and_arm_local_goal_escape() {
    use crate::{scoped_local::LocalScopeError, term_scope::TermScopeError};
    let mut scope = Scope::new();
    let flag = scope.try_local(constant("Bool")).unwrap();
    let goal = eq(&constant("Nat"), nat(0), nat(0));
    let different = eq(&constant("Nat"), nat(1), nat(1));
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    for changed_arm in [false, true] {
        let make = |is_true| {
            PendingProof::candidate(
                if changed_arm == is_true {
                    different.clone()
                } else {
                    goal.clone()
                },
                refl(
                    &constant("Nat"),
                    nat(if changed_arm == is_true { 1 } else { 0 }),
                ),
            )
        };
        let error = assembler
            .branch_proposition(
                flag.term().clone(),
                goal.clone(),
                |_, _| Ok(make(false)),
                |_, _| Ok(make(true)),
            )
            .err()
            .unwrap();
        assert_eq!(
            error,
            if changed_arm {
                "true branch proposition: different candidate terms; supply an explicit equality transport"
            } else {
                "false branch proposition: different candidate terms; supply an explicit equality transport"
            }
        );
    }
    let witness = assembler.local(constant("Nat")).unwrap();
    let escaping_goal = eq(
        &constant("Nat"),
        witness.term().clone(),
        witness.term().clone(),
    );
    let candidate = assembler
        .branch_proposition(
            flag.term().clone(),
            escaping_goal.clone(),
            |_, _| {
                Ok(PendingProof::candidate(
                    escaping_goal.clone(),
                    witness.let_(nat(3), refl(&constant("Nat"), witness.term().clone())),
                ))
            },
            |_, _| {
                Ok(PendingProof::candidate(
                    escaping_goal.clone(),
                    witness.let_(nat(7), refl(&constant("Nat"), witness.term().clone())),
                ))
            },
        )
        .unwrap();
    drop(assembler);
    let expected = Err(LocalScopeError::Closure(TermScopeError::OutOfScope(
        witness.id(),
    )));
    assert_eq!(scope.close(&flag.lam(candidate.term().clone())), expected);
    assert_eq!(
        scope.close(&flag.pi(candidate.proposition().clone())),
        expected
    );
}
