// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Strict controls for the closed fourteen-parameter Alloca
//! dispatcher. Reuse the existing typed-Alloca environment/5M/100K checker;
//! no alternate byte evaluator, successful allocation or native claim.

use super::*;

fn strict_replay(claim: &Expr, term: &Expr, accepted: bool) {
    for expression in [claim, term] {
        assert!(!expression.has_fvar_quick() && !expression.has_loose_bvars());
    }
    checker()
        .check_type(claim, &Expr::sort(Level::zero()))
        .unwrap();
    let encoded = trust_ir::proof::encode_clean_expr_dag_v2(term).unwrap();
    let decoded = trust_ir::proof::decode_clean_expr_dag_v2(&encoded).unwrap();
    assert_eq!(&decoded, term);
    for actual in [term, &decoded] {
        let kernel = checker();
        let result = kernel.check_type(actual, claim);
        assert!(
            !kernel.heartbeat_spent(),
            "resource refusal is not a semantic negative"
        );
        if accepted {
            result.unwrap();
            let audit = environment().audit_certification(claim, actual);
            assert!(audit.is_certified(), "{audit:#?}");
            for dependency in &audit.dependencies {
                assert!(environment().axiom_deps(dependency).unwrap().is_empty());
                assert!(
                    environment()
                        .foundational_axiom_deps(dependency)
                        .unwrap()
                        .is_empty()
                );
                assert!(
                    environment()
                        .trust_marker_deps(dependency)
                        .unwrap()
                        .is_empty()
                );
            }
        } else {
            assert!(
                matches!(result.unwrap_err(), KernelTypeError::TypeMismatch { .. }),
                "false evidence must fail the ordinary type checker"
            );
        }
    }
}

#[test]
fn closed_alloca_choose_motive_lifts_neutral_world_type_without_caller_capture() {
    // Under W : Type, yes : W, no : W, flag : Bool, the independent
    // selector's motive sees W at index4, not its outer-context index3.
    let world_type = Expr::bvar(3);
    let yes = Expr::bvar(2);
    let no = Expr::bvar(1);
    let flag = Expr::bvar(0);
    let selector = |motive_world| {
        Expr::apps(
            Expr::const_(
                Name::from_string("Bool.rec"),
                vec![Level::succ(Level::zero())],
            ),
            [
                Expr::lam(BinderInfo::Default, constant("Bool"), motive_world),
                no.clone(),
                yes.clone(),
                flag.clone(),
            ],
        )
    };
    let independent = selector(Expr::bvar(4));
    let actual = choose(&world_type, flag.clone(), yes.clone(), no.clone());
    assert_eq!(actual, independent);
    let domains = [
        Expr::type_(),
        Expr::bvar(0),
        Expr::bvar(1),
        constant("Bool"),
    ];
    let close = |body, term| {
        domains.iter().rev().fold(body, |body, domain| {
            if term {
                Expr::lam(BinderInfo::Default, domain.clone(), body)
            } else {
                Expr::pi(BinderInfo::Default, domain.clone(), body)
            }
        })
    };
    let claim = close(eq(&world_type, independent.clone(), independent), false);
    strict_replay(&claim, &close(refl(&world_type, actual), true), true);
    // The old unlifted motive is rejected against the same welltyped claim,
    // including after DAG transport. It must not become a resource refusal.
    let captured = selector(Expr::bvar(3));
    strict_replay(&claim, &close(refl(&world_type, captured), true), false);
}

fn symbolic_inputs(scope: &mut Scope) -> (Dispatch, Vec<Local>, AllocationDispatchPremises) {
    let world_type = scope.try_local(Expr::type_()).unwrap();
    let context = scope.try_local(constant("IRByteContextV1")).unwrap();
    let machine = scope.try_local(constant("IRMachine")).unwrap();
    let world = scope
        .try_local(app("IRByteWorldV1", [world_type.term().clone()]))
        .unwrap();
    let results = scope.try_local(nat_list()).unwrap();
    let site = scope.try_local(constant("IRByteSiteV1")).unwrap();
    let pointee = scope.try_local(constant("IRTy")).unwrap();
    let optional_count = scope.try_local(app("IROption", [constant("Nat")])).unwrap();
    let owner = scope.try_local(constant("Nat")).unwrap();
    let count = scope.try_local(constant("Nat")).unwrap();
    let owner_tail = scope.try_local(nat_list()).unwrap();
    let data = Dispatch {
        world_type: world_type.term().clone(),
        context: context.term().clone(),
        machine: machine.term().clone(),
        world: world.term().clone(),
        results: results.term().clone(),
        site: site.term().clone(),
        pointee: pointee.term().clone(),
        optional_count: optional_count.term().clone(),
        owner: owner.term().clone(),
        count: count.term().clone(),
        owner_tail: owner_tail.term().clone(),
    };
    let checks = data.checks();
    let owners = scope
        .try_local(eq(
            &checks.owners.0,
            checks.owners.1.clone(),
            checks.owners.2.clone(),
        ))
        .unwrap();
    let resolved_count = scope
        .try_local(eq(
            &checks.count.0,
            checks.count.1.clone(),
            checks.count.2.clone(),
        ))
        .unwrap();
    let count_bound = scope.try_local(checks.count_bound.clone()).unwrap();
    let premises = AllocationDispatchPremises {
        owners: PendingEquality::candidate(
            checks.owners.0,
            checks.owners.1,
            checks.owners.2,
            owners.term().clone(),
        ),
        count: PendingEquality::candidate(
            checks.count.0,
            checks.count.1,
            checks.count.2,
            resolved_count.term().clone(),
        ),
        count_bound: PendingProof::candidate(checks.count_bound, count_bound.term().clone()),
    };
    (
        data,
        vec![
            world_type,
            context,
            machine,
            world,
            results,
            site,
            pointee,
            optional_count,
            owner,
            count,
            owner_tail,
            owners,
            resolved_count,
            count_bound,
        ],
        premises,
    )
}

fn close_expression(scope: &Scope, parameters: &[Local], body: Expr, term: bool) -> Expr {
    let body = parameters.iter().rev().fold(body, |body, local| {
        if term {
            local.lam(body)
        } else {
            local.pi(body)
        }
    });
    scope.close(&body).unwrap()
}

// The complete statement is reconstructed from its inputs, not copied from
// the generated equality or a normalized output. Providers are not a dispatch
// argument; the original complete world, memory, SSA/results and site are.
fn independent_statement(data: &Dispatch) -> Expr {
    let config = app("IRByteConfigV1", [data.world_type.clone()]);
    let left = app(
        "ir_byte_alloca_exec_v1",
        [
            data.world_type.clone(),
            data.context.clone(),
            data.machine.clone(),
            data.world.clone(),
            data.results.clone(),
            data.site.clone(),
            data.pointee.clone(),
            data.optional_count.clone(),
        ],
    );
    let allocated = app(
        "ir_byte_alloc_v1",
        [
            data.context.clone(),
            data.pointee.clone(),
            data.count.clone(),
            app("ir_byte_site_align_v1", [data.site.clone()]),
            data.owner.clone(),
            app(
                "ir_byte_world_memory_v1",
                [data.world_type.clone(), data.world.clone()],
            ),
        ],
    );
    let right = app(
        "ir_byte_memory_result_v1",
        [
            data.world_type.clone(),
            data.context.clone(),
            data.machine.clone(),
            data.world.clone(),
            data.results.clone(),
            app("ir_byte_site_results_v1", [data.site.clone()]),
            constant("Bool.false"),
            allocated,
        ],
    );
    eq(&config, left, right)
}

fn concrete_dispatch_premises(
    site: &FetchedSite,
    model: &MachineModel,
    before: &Current,
    input: &AllocationInput,
    tail: Expr,
) -> AllocationDispatchPremises {
    let checks = site
        .allocation_dispatch_checks(model, before, input, tail)
        .unwrap();
    let (ty, left, right) = checks.owners;
    let owners = conversion(ty, left, right);
    let (ty, left, right) = checks.count;
    AllocationDispatchPremises {
        owners,
        count: conversion(ty, left, right),
        count_bound: PendingProof::candidate(
            checks.count_bound,
            app(
                "Nat.le_add_right",
                [
                    app("Nat.succ", [input.count.clone()]),
                    nat((1_u64 << 63) - 2),
                ],
            ),
        ),
    }
}

#[test]
fn closed_alloca_fixed_telescope_matches_scoped_oracle_and_replays_neutral_world() {
    let mut old_scope = Scope::new();
    let mut old = Assembler::new(&mut old_scope, limits()).unwrap();
    let old_term = scoped_oracle_helper(&mut old).unwrap();
    assert_eq!((old.operations(), old.locals), (39, 29));
    drop(old);
    assert_eq!(old_scope.allocated(), 29);
    let mut new_scope = Scope::new();
    let mut new = Assembler::new(&mut new_scope, limits()).unwrap();
    let new_term = new.allocation_dispatch_helper().unwrap();
    assert_eq!((new.operations(), new.locals), (39, 0));
    assert_eq!(new.local_scope().allocated(), 0);
    assert_eq!(new_term, old_term, "only the binder construction changes");
    drop(new);
    let mut inputs = Scope::new();
    let (data, parameters, premises) = symbolic_inputs(&mut inputs);
    assert_eq!(parameters.len(), 14);
    let claim = close_expression(&inputs, &parameters, independent_statement(&data), false);
    strict_replay(&claim, &old_term, true);
    strict_replay(&claim, &new_term, true);
    let applied = Expr::apps(
        new_term,
        data.arguments().into_iter().chain([
            premises.owners.term,
            premises.count.term,
            premises.count_bound.term,
        ]),
    );
    let applied = close_expression(&inputs, &parameters, applied, true);
    strict_replay(&claim, &applied, true);
}

#[test]
fn closed_alloca_cold_warm_preserve_charges_at_an_exhausted_caller_local_cap() {
    let f = fixture(1, Ty::I64, 8);
    let reflected = typed_reflection(&f, 4096);
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let site = Catalog::new(environment(), &reflected, limits())
        .unwrap()
        .fetch(f.coordinate(1))
        .unwrap();
    let before = f.after_const(memory(rows(), bytes(), 65), app("IRScalar.int_", [nat(1)]));
    let input = AllocationInput {
        owner: nat(8),
        count: nat(1),
    };
    let mut scope = Scope::new();
    let mut policy = limits();
    policy.max_locals = 1;
    let mut assembler = Assembler::new(&mut scope, policy).unwrap();
    let used = assembler.local(constant("Nat")).unwrap();
    let allocated = assembler.local_scope().allocated();
    let mut proofs = Vec::new();
    let mut cached: Option<Expr> = None;
    for expected_operations in [41, 42] {
        proofs.push(dispatch(&mut assembler, &site, &model, &before, &input, 1));
        assert_eq!(assembler.operations(), expected_operations);
        assert_eq!(assembler.locals, 1);
        assert_eq!(assembler.local_scope().allocated(), allocated);
        let actual = assembler.allocation_dispatch_candidate.as_ref().unwrap();
        assert!(!actual.has_fvar_quick() && !actual.has_loose_bvars());
        if let Some(previous) = &cached {
            let (ExprKind::Lam(_, left_ty, left_body), ExprKind::Lam(_, right_ty, right_body)) =
                (actual.kind(), previous.kind())
            else {
                panic!("closed factory must be a lambda");
            };
            assert!(std::sync::Arc::ptr_eq(left_ty, right_ty));
            assert!(std::sync::Arc::ptr_eq(left_body, right_body));
        }
        cached = Some(actual.clone());
    }
    assert_eq!(
        assembler.local(constant("Nat")).err().unwrap(),
        "execution construction local budget exceeded"
    );
    assert_eq!((assembler.operations(), assembler.locals), (43, 1));
    assert_eq!(assembler.local_scope().allocated(), allocated);
    drop(assembler);
    for proof in &proofs {
        let (term, claim) = close(&scope, std::slice::from_ref(&used), proof);
        strict_replay(&claim, &term, true);
    }
}

#[test]
fn closed_alloca_cold_failed_charges_are_sticky_and_do_not_publish_a_cache() {
    let f = fixture(1, Ty::I64, 8);
    let reflected = typed_reflection(&f, 4096);
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let site = Catalog::new(environment(), &reflected, limits())
        .unwrap()
        .fetch(f.coordinate(1))
        .unwrap();
    let before = f.after_const(memory(rows(), bytes(), 65), app("IRScalar.int_", [nat(1)]));
    let input = AllocationInput {
        owner: nat(8),
        count: nat(1),
    };
    let premises = concrete_dispatch_premises(&site, &model, &before, &input, list("Nat", &[]));
    for cap in [1, 14, 29, 30, 34, 39] {
        let mut scope = Scope::new();
        let mut policy = limits();
        policy.max_operations = cap;
        policy.max_locals = 1;
        let mut assembler = Assembler::new(&mut scope, policy).unwrap();
        for _ in 0..2 {
            let error = site
                .allocation_dispatch(
                    &mut assembler,
                    &model,
                    &before,
                    &input,
                    list("Nat", &[]),
                    premises.clone(),
                )
                .err()
                .unwrap();
            assert_eq!(error, "execution construction operation budget exceeded");
            assert_eq!((assembler.operations(), assembler.locals), (cap, 0));
            assert_eq!(assembler.local_scope().allocated(), 0);
            assert!(assembler.allocation_dispatch_candidate.is_none());
        }
    }
    let mut scope = Scope::new();
    let mut policy = limits();
    policy.max_operations = 40;
    policy.max_locals = 1;
    let mut assembler = Assembler::new(&mut scope, policy).unwrap();
    let proof = site
        .allocation_dispatch(
            &mut assembler,
            &model,
            &before,
            &input,
            list("Nat", &[]),
            premises.clone(),
        )
        .unwrap();
    let cached = assembler.allocation_dispatch_candidate.clone().unwrap();
    assert_eq!((assembler.operations(), assembler.locals), (40, 0));
    assert_eq!(
        site.allocation_dispatch(
            &mut assembler,
            &model,
            &before,
            &input,
            list("Nat", &[]),
            premises,
        )
        .err()
        .unwrap(),
        "execution construction operation budget exceeded"
    );
    assert_eq!((assembler.operations(), assembler.locals), (40, 0));
    assert_eq!(
        assembler.allocation_dispatch_candidate.as_ref().unwrap(),
        &cached
    );
    drop(assembler);
    let (term, claim) = close(&scope, &[], &proof);
    strict_replay(&claim, &term, true);
}

#[test]
fn closed_alloca_foreign_context_endpoint_and_malformed_spines_keep_preflight_order() {
    let f = fixture(1, Ty::I64, 8);
    let reflected = typed_reflection(&f, 4096);
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let site = Catalog::new(environment(), &reflected, limits())
        .unwrap()
        .fetch(f.coordinate(1))
        .unwrap();
    let before = f.after_const(memory(rows(), bytes(), 65), app("IRScalar.int_", [nat(1)]));
    let input = AllocationInput {
        owner: nat(8),
        count: nat(1),
    };
    let premises = concrete_dispatch_premises(&site, &model, &before, &input, list("Nat", &[]));
    for mutant in 0..6 {
        let mut actual_site = site.clone();
        let mut actual_premises = premises.clone();
        match mutant {
            0 => actual_site.context = constant("Bool.true"),
            1 => actual_site.instruction = constant("IRInst.alloca"),
            2 => actual_site.instruction = app("IRInst.alloca", [nat(0)]),
            3 => actual_site.instruction = Expr::app(site.instruction.clone(), nat(0)),
            4 => {
                actual_premises.count =
                    PendingEquality::reflexive(constant("IRScalar"), app("IRScalar.int_", [nat(1)]))
            }
            5 => {
                actual_premises.count_bound = PendingProof::candidate(
                    constant("Bool.true"),
                    refl(&constant("Bool"), constant("Bool.true")),
                )
            }
            _ => unreachable!(),
        }
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let error = actual_site
            .allocation_dispatch(
                &mut assembler,
                &model,
                &before,
                &input,
                list("Nat", &[]),
                actual_premises,
            )
            .err()
            .unwrap();
        match mutant {
            0 => assert_eq!(
                error,
                "allocation dispatch fetched context: different candidate terms; supply an explicit equality transport"
            ),
            1..=3 => assert_eq!(error, "allocation dispatch requires fetched Alloca"),
            4 => assert_eq!(
                error,
                "equality left endpoint: different candidate terms; supply an explicit equality transport"
            ),
            5 => assert_eq!(
                error,
                "allocation dispatch count bound: different candidate terms; supply an explicit equality transport"
            ),
            _ => unreachable!(),
        }
        assert_eq!((assembler.operations(), assembler.locals), (1, 0));
        assert_eq!(assembler.local_scope().allocated(), 0);
        assert!(assembler.allocation_dispatch_candidate.is_none());
    }
}

#[test]
fn closed_alloca_some_none_and_false_unused_proofs_replay_strictly_original_and_dag() {
    for explicit in [true, false] {
        let f = fixture_with_count(1, Ty::I64, 8, explicit);
        let reflected = typed_reflection(&f, 4096);
        let model = MachineModel::new(constant("Nat"), &reflected, providers());
        let site = Catalog::new(environment(), &reflected, limits())
            .unwrap()
            .fetch(f.coordinate(1))
            .unwrap();
        let before = f.after_const(memory(rows(), bytes(), 65), app("IRScalar.int_", [nat(1)]));
        let input = AllocationInput {
            owner: nat(8),
            count: nat(1),
        };
        let tail = list("Nat", &[]);
        let data = site
            .allocation_dispatch_input(&model, &before, &input, tail.clone())
            .unwrap();
        let premises = concrete_dispatch_premises(&site, &model, &before, &input, tail.clone());
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let positive = site
            .allocation_dispatch(
                &mut assembler,
                &model,
                &before,
                &input,
                tail,
                premises.clone(),
            )
            .unwrap();
        assert_eq!((assembler.operations(), assembler.locals), (40, 0));
        let helper = assembler.allocation_dispatch_candidate.clone().unwrap();
        drop(assembler);
        let claim = independent_statement(&data);
        assert_eq!(claim, positive.proposition());
        strict_replay(&claim, positive.term(), true);
        for mutant in 0..5 {
            let mut arguments: Vec<_> = data
                .arguments()
                .into_iter()
                .chain([
                    premises.owners.term.clone(),
                    premises.count.term.clone(),
                    premises.count_bound.term.clone(),
                ])
                .collect();
            if mutant < 3 {
                // Correct endpoint METADATA never promotes a supplied term:
                // each of the three actual proof arguments remains typechecked.
                arguments[11 + mutant] = refl(&constant("Nat"), nat(0));
            } else {
                // The statement remains independently welltyped. Only the
                // PROOF carries a false unused LET in the machine (unused by
                // None) or owner-tail argument, retaining strict input checks.
                let position = if mutant == 3 { 2 } else { 10 };
                arguments[position] = Expr::let_named(
                    Name::anon(),
                    eq(&constant("Nat"), nat(0), nat(1)),
                    refl(&constant("Nat"), nat(0)),
                    arguments[position].lift(1),
                    false,
                );
            }
            strict_replay(&claim, &Expr::apps(helper.clone(), arguments), false);
        }
        // Keep an independently welltyped statement for each full-world
        // mutation. None is not permission to ignore the machine/world or to
        // substitute a different allocation/result cursor.
        for mutant in 0..5 {
            let mut changed = site
                .allocation_dispatch_input(&model, &before, &input, list("Nat", &[]))
                .unwrap();
            match mutant {
                0 => changed.world = world(memory(rows(), bytes(), 97), list("Nat", &[nat(8)])),
                1 => {
                    changed.world = app(
                        "IRByteWorldV1.mk",
                        [
                            constant("Nat"),
                            memory(rows(), bytes(), 65),
                            nat(38),
                            list("Nat", &[nat(8)]),
                            nat(9),
                        ],
                    )
                }
                2 => {
                    changed.world = app(
                        "IRByteWorldV1.mk",
                        [
                            constant("Nat"),
                            memory(rows(), bytes(), 65),
                            nat(37),
                            list("Nat", &[nat(8)]),
                            nat(10),
                        ],
                    )
                }
                3 => {
                    changed.machine = f
                        .current(
                            memory(rows(), bytes(), 65),
                            list("Nat", &[nat(8)]),
                            2,
                            list(
                                "IRBinding",
                                &[binding(f.count, app("IRScalar.int_", [nat(1)]))],
                            ),
                        )
                        .machine()
                }
                4 => changed.results = list("Nat", &[nat(f.count.index().into())]),
                _ => unreachable!(),
            }
            let changed_claim = eq(
                &data.config_type(),
                data.dispatch(),
                changed.dispatched_with(changed.count.clone(), changed.owner.clone()),
            );
            strict_replay(&changed_claim, positive.term(), false);
        }
        assert_eq!(f.module.functions[0].blocks[0].body[1].results, [f.pointer]);
        assert!(matches!(f.module.functions[0].blocks[0].body[1].inst,
            Inst::Alloca { count, .. } if count == explicit.then_some(f.count)));
    }
}

// Independent old construction oracle, test-only. This is the original
// Scope-based producer verbatim apart from method-to-free-function plumbing;
// it is never registered as another execution path or evaluator.
fn scoped_oracle_helper(assembler: &mut Assembler<'_>) -> Result<Expr> {
    let world_type = assembler.local(Expr::type_())?;
    let context = assembler.local(constant("IRByteContextV1"))?;
    let machine = assembler.local(constant("IRMachine"))?;
    let world = assembler.local(app("IRByteWorldV1", [world_type.term().clone()]))?;
    let results = assembler.local(nat_list())?;
    let site = assembler.local(constant("IRByteSiteV1"))?;
    let pointee = assembler.local(constant("IRTy"))?;
    let optional_count = assembler.local(app("IROption", [constant("Nat")]))?;
    let owner = assembler.local(constant("Nat"))?;
    let count = assembler.local(constant("Nat"))?;
    let owner_tail = assembler.local(nat_list())?;
    let data = Dispatch {
        world_type: world_type.term().clone(),
        context: context.term().clone(),
        machine: machine.term().clone(),
        world: world.term().clone(),
        results: results.term().clone(),
        site: site.term().clone(),
        pointee: pointee.term().clone(),
        optional_count: optional_count.term().clone(),
        owner: owner.term().clone(),
        count: count.term().clone(),
        owner_tail: owner_tail.term().clone(),
    };
    let checks = data.checks();
    let owners = assembler.local(eq(
        &checks.owners.0,
        checks.owners.1.clone(),
        checks.owners.2.clone(),
    ))?;
    let resolved_count = assembler.local(eq(
        &checks.count.0,
        checks.count.1.clone(),
        checks.count.2.clone(),
    ))?;
    let count_bound = assembler.local(checks.count_bound.clone())?;
    let owners_proof = PendingEquality::candidate(
        checks.owners.0,
        checks.owners.1,
        checks.owners.2,
        owners.term().clone(),
    );
    let count_proof = PendingEquality::candidate(
        checks.count.0,
        checks.count.1,
        checks.count.2,
        resolved_count.term().clone(),
    );
    let proof = scoped_oracle_term(
        assembler,
        &data,
        owners_proof,
        count_proof,
        count_bound.term().clone(),
    )?;
    let parameters = [
        world_type,
        context,
        machine,
        world,
        results,
        site,
        pointee,
        optional_count,
        owner,
        count,
        owner_tail,
        owners,
        resolved_count,
        count_bound,
    ];
    let term = parameters
        .iter()
        .rev()
        .fold(proof.term, |body, local| local.lam(body));
    let closed = assembler
        .scope
        .close(&term)
        .map_err(|error| error.to_string())?;
    Ok(closed)
}

// Spell the original scalar match via the existing recursor; like the
// shared CondBr construction, recursive noninteger cases ignore their IHs
// and retain the actual type-error endpoint. This is a print/proof view,
// never an independently chosen evaluator or an execution fast path.
fn scoped_oracle_count_handler(
    assembler: &mut Assembler<'_>,
    data: &Dispatch,
    owner: Expr,
) -> Result<Expr> {
    let config = data.config_type();
    let failure = data.halted("type_error", "not_int");
    let scalar = assembler.local(constant("IRScalar"))?;
    let motive = assembler.local(constant("IRScalar"))?;
    let field = assembler.local(constant("IRScalar"))?;
    let bool_value = assembler.local(constant("Bool"))?;
    let word = assembler.local(constant("Nat"))?;
    let second_word = assembler.local(constant("Nat"))?;
    let other_scalar = assembler.local(constant("IRScalar"))?;
    let recursive = assembler.local(config.clone())?;
    let second_recursive = assembler.local(config.clone())?;
    let word_case = word.lam(failure.clone());
    let cases = Expr::apps(
        Expr::const_(
            Name::from_string("IRScalar.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [
            motive.lam(config),
            failure.clone(),
            bool_value.lam(failure.clone()),
            word.lam(data.integer_branch(word.term().clone(), owner)),
            word_case.clone(),
            failure.clone(),
            word_case.clone(),
            failure.clone(),
            word.lam(second_word.lam(failure.clone())),
            word_case,
            field.lam(recursive.lam(failure.clone())),
            failure.clone(),
            field.lam(other_scalar.lam(recursive.lam(second_recursive.lam(failure)))),
            scalar.term().clone(),
        ],
    );
    Ok(scalar.lam(cases))
}

fn scoped_oracle_term(
    assembler: &mut Assembler<'_>,
    data: &Dispatch,
    owners: PendingEquality,
    count: PendingEquality,
    count_bound: Expr,
) -> Result<PendingEquality> {
    let config = data.config_type();
    let factory_owner = assembler.local(constant("Nat"))?;
    let count_handler = scoped_oracle_count_handler(assembler, data, factory_owner.term().clone())?;
    let count_factory = factory_owner.lam(count_handler);
    // The factory occurs beneath the list branch's owner binder. Separate
    // locals preserve the shared scope's no-active-shadowing invariant.
    let owner = assembler.local(constant("Nat"))?;
    let scalar_branch = Expr::app(
        Expr::app(count_factory.clone(), owner.term().clone()),
        data.resolved_count(),
    );
    let tail = assembler.local(nat_list())?;
    let recursive = assembler.local(config.clone())?;
    let motive = assembler.local(nat_list())?;
    let source = assembler.local(nat_list())?;
    let owners_handler = source.lam(Expr::apps(
        Expr::const_(
            Name::from_string("IRList.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [
            constant("Nat"),
            motive.lam(config.clone()),
            data.halted("stuck", "no_frame"),
            owner.lam(tail.lam(recursive.lam(scalar_branch))),
            source.term().clone(),
        ],
    ));
    let owners = assembler.congruence_function(owners, config.clone(), owners_handler)?;
    let first = assembler.conversion(config.clone(), data.dispatch(), owners.left.clone())?;
    let count = assembler.congruence_function(
        count,
        config.clone(),
        Expr::app(count_factory, data.owner.clone()),
    )?;
    let bridge = assembler.conversion(config.clone(), owners.right.clone(), count.left.clone())?;
    let integer = data.integer_branch(data.count.clone(), data.owner.clone());
    let integer_start =
        assembler.conversion(config.clone(), count.right.clone(), integer.clone())?;
    let target = data.dispatched_with(data.count.clone(), data.owner.clone());
    let bound = app(
        "ir_byte_ltb_of_lt_v1",
        [data.count.clone(), nat(1_u64 << 63), count_bound],
    );
    let selected = PendingEquality::candidate(
        config.clone(),
        integer,
        target.clone(),
        app(
            "ir_byte_case_true_v1",
            [
                config.clone(),
                app("ir_nat_ltb", [data.count.clone(), nat(1_u64 << 63)]),
                data.halted("unmodelled", "width_bounded"),
                target.clone(),
                target.clone(),
                bound,
                refl(&config, target),
            ],
        ),
    );
    let mut proof = first;
    for part in [owners, bridge, count, integer_start, selected] {
        proof = assembler.compose(proof, part)?;
    }
    Ok(proof)
}
