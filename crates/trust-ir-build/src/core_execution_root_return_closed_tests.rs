// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Authored fetched Return and neutral-function controls only. Strict original
//! and DAG replay is not source-to-native, full TY Return, or runtime evidence.

use super::*;

fn strict(scope: &Scope, term: &Expr, goal: &Expr, accepted: bool) {
    let term = scope.close(term).unwrap();
    let goal = scope.close(goal).unwrap();
    assert!(!term.has_fvar_quick() && !term.has_loose_bvars());
    assert!(!goal.has_fvar_quick() && !goal.has_loose_bvars());
    let decoded_term = trust_ir::proof::decode_clean_expr_dag_v2(
        &trust_ir::proof::encode_clean_expr_dag_v2(&term).unwrap(),
    )
    .unwrap();
    let decoded_goal = trust_ir::proof::decode_clean_expr_dag_v2(
        &trust_ir::proof::encode_clean_expr_dag_v2(&goal).unwrap(),
    )
    .unwrap();
    assert_eq!(decoded_term, term);
    assert_eq!(decoded_goal, goal);
    for (term, goal) in [(term, goal), (decoded_term, decoded_goal)] {
        let mut checker = TypeChecker::new(environment());
        checker.set_allow_unsafe(false);
        checker.set_allow_partial(false);
        assert_eq!(checker.heartbeat_limit(), 2_000_000);
        checker
            .check_type(&goal, &Expr::sort(Level::zero()))
            .unwrap();
        let checked = checker.check_type(&term, &goal);
        assert!(
            !checker.heartbeat_spent(),
            "resource stop is not a verdict: {checked:?}"
        );
        assert!(!clean_kernel::tc::declaration_budget_exhausted());
        if accepted {
            checked.unwrap();
            let audit = environment().audit_certification(&goal, &term);
            assert!(audit.is_certified());
            for dependency in audit.dependencies {
                assert!(environment().axiom_deps(&dependency).unwrap().is_empty());
                assert!(
                    environment()
                        .foundational_axiom_deps(&dependency)
                        .unwrap()
                        .is_empty()
                );
                assert!(
                    environment()
                        .trust_marker_deps(&dependency)
                        .unwrap()
                        .is_empty()
                );
            }
        } else {
            assert!(matches!(
                checked.unwrap_err(),
                KernelTypeError::TypeMismatch { .. }
            ));
        }
    }
}

fn close_types(types: &[Expr], term: Expr, proposition: bool) -> Expr {
    types.iter().rev().fold(term, |body, ty| {
        if proposition {
            Expr::pi(BinderInfo::Default, ty.clone(), body)
        } else {
            Expr::lam(BinderInfo::Default, ty.clone(), body)
        }
    })
}

#[test]
fn root_return_closed_functions_keep_dependent_world_domains() {
    let scalar_list = app("IRList", [constant("IRScalar")]);
    let signature = constant("IRByteSignatureV1");
    let types_and_terms = [
        (
            vec![
                constant("IRByteContextV1"),
                constant("IRFrame"),
                signature.clone(),
                scalar_list.clone(),
            ],
            constant("Bool"),
            closed_guard_function(),
        ),
        (
            vec![
                Expr::type_(),
                app("IRByteWorldV1", [Expr::bvar(0)]),
                scalar_list.clone(),
            ],
            app("IRByteConfigV1", [Expr::bvar(2)]),
            closed_halted_function(),
        ),
        (
            vec![
                Expr::type_(),
                constant("IRByteContextV1"),
                constant("IRFrame"),
                scalar_list,
                app("IRByteConfigV1", [Expr::bvar(3)]),
                app("IRByteConfigV1", [Expr::bvar(4)]),
                signature.clone(),
            ],
            app("IRByteConfigV1", [Expr::bvar(6)]),
            closed_signature_function(),
        ),
        (
            vec![
                Expr::type_(),
                constant("IRByteContextV1"),
                app("IRByteConfigV1", [Expr::bvar(1)]),
                Expr::pi(
                    BinderInfo::Default,
                    signature,
                    app("IRByteConfigV1", [Expr::bvar(3)]),
                ),
                constant("IRByteFunctionV1"),
            ],
            app("IRByteConfigV1", [Expr::bvar(4)]),
            closed_binding_function(),
        ),
    ];
    for (types, result_type, function) in types_and_terms {
        let function_type = close_types(&types, result_type, true);
        assert!(!function.has_fvar_quick() && !function.has_loose_bvars());
        let decoded = trust_ir::proof::decode_clean_expr_dag_v2(
            &trust_ir::proof::encode_clean_expr_dag_v2(&function).unwrap(),
        )
        .unwrap();
        assert_eq!(decoded, function);
        for function in [function, decoded] {
            let mut checker = TypeChecker::new(environment());
            checker.set_allow_unsafe(false);
            checker.set_allow_partial(false);
            assert_eq!(checker.heartbeat_limit(), 2_000_000);
            let _ = checker.infer_type_full(&function_type).unwrap();
            checker.check_type(&function, &function_type).unwrap();
            assert!(!checker.heartbeat_spent());
            assert!(!clean_kernel::tc::declaration_budget_exhausted());
        }
    }
}

// The model's actual W is passed to a CLOSED total provider. No caller W is
// captured by a newly constructed body beneath its four argument binders.
fn inert_providers(world_type: Expr) -> Expr {
    let types = [
        Expr::type_(),
        constant("Nat"),
        app("IRList", [constant("IRScalar")]),
        constant("IRByteMemoryV1"),
        Expr::bvar(3),
    ];
    let function = types.into_iter().rev().fold(
        app(
            "IRByteImportResultV1.mk",
            [
                Expr::bvar(4),
                app("IROutcome.stuck", [constant("IRFault.no_func")]),
                Expr::bvar(1),
                Expr::bvar(0),
            ],
        ),
        |body, ty| Expr::lam(BinderInfo::Default, ty, body),
    );
    assert!(!function.has_fvar_quick() && !function.has_loose_bvars());
    Expr::app(function, world_type)
}

// Deliberately unlike every template's parameter order: unrelated Nat, W,
// host:W, complete memory, owner, next, word; three original prestate proofs.
fn symbolic_data(f: &Fixture, context: Expr, depth: u32) -> (MachineModel, RootReturnFrame, Expr) {
    let at = |position| Expr::bvar(depth - position - 1);
    let world_type = at(1);
    let model = MachineModel {
        providers: inert_providers(world_type.clone()),
        world_type,
        context,
    };
    let word = int_term(at(6));
    let frame = RootReturnFrame {
        returning: app(
            "IRFrame.mk",
            [
                nat(u64::from(f.function.index())),
                nat(u64::from(f.block.index())),
                nat(f.pc as u64),
                list("IRBinding", &[binding(f.arguments[0], word.clone())]),
                list("Nat", &[]),
            ],
        ),
        legacy_memory: list("IRMemSlot", &[]),
        legacy_cursor: nat(0),
        memory: at(3),
        host: at(2),
        owner: at(4),
        next: at(5),
    };
    (model, frame, list("IRScalar", &[word]))
}

fn int_term(word: Expr) -> Expr {
    app("IRScalar.int_", [word])
}

#[test]
fn root_return_closed_functions_replay_reordered_symbolic_world_and_premises() {
    let f = returning(1);
    let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
    let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
    let target = catalog.call_target(f.function).unwrap();
    let site = catalog.fetch(f.coordinate()).unwrap();
    let context = reflected.context_term().clone();
    let mut types = vec![
        constant("Nat"),
        Expr::type_(),
        Expr::bvar(0),
        constant("IRByteMemoryV1"),
        constant("Nat"),
        constant("Nat"),
        constant("Nat"),
    ];
    let (model, frame, values) = symbolic_data(&f, context.clone(), 7);
    types.push(f.resolved(&model, &frame, values).proposition());
    let (model, frame, _) = symbolic_data(&f, context.clone(), 8);
    types.push(eq(
        &constant("Bool"),
        frame.current(&model).valid(&model),
        constant("Bool.true"),
    ));
    let (model, frame, values) = symbolic_data(&f, context.clone(), 9);
    types.push(eq(
        &constant("Bool"),
        site.root_return_admission(&model, &target, &frame, values)
            .unwrap(),
        constant("Bool.true"),
    ));
    let (model, frame, values) = symbolic_data(&f, context, 10);
    let mut resolved = f.resolved(&model, &frame, values.clone());
    resolved.term = Expr::bvar(2);
    let before = PendingEquality::candidate(
        constant("Bool"),
        frame.current(&model).valid(&model),
        constant("Bool.true"),
        Expr::bvar(1),
    );
    let admitted = PendingEquality::candidate(
        constant("Bool"),
        site.root_return_admission(&model, &target, &frame, values.clone())
            .unwrap(),
        constant("Bool.true"),
        Expr::bvar(0),
    );
    let initial = frame.current(&model).running(&model);
    let independent = app(
        "IRByteConfigV1.halted",
        [
            model.world_type.clone(),
            app("IROutcome.ret", [values]),
            app(
                "IRByteWorldV1.mk",
                [
                    model.world_type.clone(),
                    app(
                        "ir_byte_retire_v1",
                        [frame.owner.clone(), frame.memory.clone()],
                    ),
                    frame.host.clone(),
                    list("Nat", &[]),
                    frame.next.clone(),
                ],
            ),
        ],
    );
    let goal = eq(
        &model.config_type(),
        model.run(&NatTerm::literal(1), initial),
        independent,
    );
    let mut scope = Scope::new();
    let mut a = Assembler::new(&mut scope, limits()).unwrap();
    let transfer = site
        .return_from_root(&mut a, &model, &target, &frame, resolved, admitted, before)
        .unwrap();
    assert_eq!(a.locals, 0);
    assert_eq!(
        a.operations(),
        23,
        "static cold forecast must be checked by actual execution"
    );
    let proof = close_types(&types, transfer.run().equality().term().clone(), false);
    let goal = close_types(&types, goal, true);
    strict(a.local_scope(), &proof, &goal, true);
}

#[test]
fn root_return_closed_functions_preserve_paid_slots_and_real_local_exhaustion() {
    let f = returning(1);
    let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
    let target = catalog.call_target(f.function).unwrap();
    let site = catalog.fetch(f.coordinate()).unwrap();
    let frame = f.frame();
    let values = list("IRScalar", &f.values);
    let mut scope = Scope::new();
    let mut policy = limits();
    policy.max_locals = 1;
    let mut a = Assembler::new(&mut scope, policy).unwrap();
    let held = a.local(constant("Nat")).unwrap();
    let initial = a.operations();
    let transfer = candidate(&mut a, &f, &site, &target, &model, &frame, values.clone()).unwrap();
    assert_eq!(a.operations() - initial, 23);
    assert_eq!(a.locals, 1);
    strict(
        a.local_scope(),
        transfer.run().equality().term(),
        &transfer.run().equality().proposition(),
        true,
    );
    let spent = a.operations();
    let _warm = candidate(&mut a, &f, &site, &target, &model, &frame, values).unwrap();
    assert_eq!(
        a.operations() - spent,
        14,
        "only the EXISTING run-one template is warm"
    );
    for _ in 0..2 {
        let spent = a.operations();
        assert_eq!(
            a.local(constant("Nat")).err().unwrap(),
            "execution construction local budget exceeded"
        );
        assert_eq!(a.operations(), spent + 1);
        assert_eq!(a.locals, 1);
        assert!(held.term().has_fvar_quick());
    }
}

#[test]
fn root_return_closed_functions_partial_operations_never_refund_or_return_a_candidate() {
    let f = returning(1);
    let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
    let target = catalog.call_target(f.function).unwrap();
    let site = catalog.fetch(f.coordinate()).unwrap();
    let frame = f.frame();
    for cap in 1..23 {
        let mut scope = Scope::new();
        let mut policy = limits();
        policy.max_operations = cap;
        let mut a = Assembler::new(&mut scope, policy).unwrap();
        for _ in 0..2 {
            assert_eq!(
                candidate(
                    &mut a,
                    &f,
                    &site,
                    &target,
                    &model,
                    &frame,
                    list("IRScalar", &f.values)
                )
                .err()
                .unwrap(),
                "execution construction operation budget exceeded"
            );
            assert_eq!(a.operations(), cap);
            assert_eq!(a.locals, 0);
        }
        // Existing run_one_candidate may publish after its OWN complete paid
        // construction. Do not roll it back just because a later compose fails.
    }
    let mut scope = Scope::new();
    let mut a = Assembler::new(&mut scope, limits()).unwrap();
    a.operations = usize::MAX;
    assert_eq!(
        candidate(
            &mut a,
            &f,
            &site,
            &target,
            &model,
            &frame,
            list("IRScalar", &f.values)
        )
        .err()
        .unwrap(),
        "operation counter overflow"
    );
    assert_eq!(a.operations(), usize::MAX);
    assert_eq!(a.locals, 0);
}

#[test]
fn root_return_closed_functions_retain_false_premises_and_complete_retired_world() {
    let f = returning(3);
    let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
    let target = catalog.call_target(f.function).unwrap();
    let site = catalog.fetch(f.coordinate()).unwrap();
    let frame = f.frame();
    let values = list("IRScalar", &f.values);
    // Independent original pre-state/run/retired-world goal, authored BEFORE
    // constructing a Return candidate. No returned transfer metadata is used.
    let original_run = model.run(&NatTerm::literal(1), frame.current(&model).running(&model));
    let expected = app(
        "IRByteConfigV1.halted",
        [
            model.world_type.clone(),
            app("IROutcome.ret", [values.clone()]),
            app(
                "IRByteWorldV1.mk",
                [
                    model.world_type.clone(),
                    app(
                        "ir_byte_retire_v1",
                        [frame.owner.clone(), frame.memory.clone()],
                    ),
                    frame.host.clone(),
                    list("Nat", &[]),
                    frame.next.clone(),
                ],
            ),
        ],
    );
    let independent_goal = eq(&model.config_type(), original_run.clone(), expected);
    assert!(!independent_goal.has_fvar_quick() && !independent_goal.has_loose_bvars());
    for mutation in 0..3 {
        let mut scope = Scope::new();
        let mut a = Assembler::new(&mut scope, limits()).unwrap();
        let mut resolved = f.resolved(&model, &frame, values.clone());
        let mut admitted = truth(
            site.root_return_admission(&model, &target, &frame, values.clone())
                .unwrap(),
        );
        let mut before = truth(frame.current(&model).valid(&model));
        let bad = refl(&constant("Nat"), nat(0));
        match mutation {
            0 => resolved.term = bad,
            1 => admitted.term = bad,
            _ => before.term = bad,
        }
        let transfer = site
            .return_from_root(&mut a, &model, &target, &frame, resolved, admitted, before)
            .unwrap();
        assert_eq!(a.locals, 0);
        strict(
            a.local_scope(),
            transfer.run().equality().term(),
            &independent_goal,
            false,
        );
    }
    let mut scope = Scope::new();
    let mut a = Assembler::new(&mut scope, limits()).unwrap();
    let transfer = candidate(&mut a, &f, &site, &target, &model, &frame, values.clone()).unwrap();
    strict(
        a.local_scope(),
        transfer.run().equality().term(),
        &independent_goal,
        true,
    );
    // This caller-owned proof LET is deliberately UNUSED by the valid body.
    // Its declaration is well-typed but false; its Refl value proves true=true.
    // Strict original AND decoded-DAG checking must still check that value.
    let unused_bad = Expr::let_named(
        Name::anon(),
        eq(
            &constant("Bool"),
            constant("Bool.true"),
            constant("Bool.false"),
        ),
        refl(&constant("Bool"), constant("Bool.true")),
        transfer.run().equality().term().clone().lift(1),
        false,
    );
    assert!(!unused_bad.has_fvar_quick() && !unused_bad.has_loose_bvars());
    strict(a.local_scope(), &unused_bad, &independent_goal, false);
    for wrong in [
        terminal(values.clone(), memory(true, true, false), 37, &[], 9),
        terminal(values.clone(), memory(false, false, false), 37, &[], 9),
        terminal(values.clone(), memory(false, true, true), 37, &[], 9),
        terminal(values.clone(), memory(false, true, false), 38, &[], 9),
        terminal(values.clone(), memory(false, true, false), 37, &[nat(8)], 9),
        terminal(values.clone(), memory(false, true, false), 37, &[], 10),
        terminal(
            list("IRScalar", &[int(7)]),
            memory(false, true, false),
            37,
            &[],
            9,
        ),
    ] {
        let goal = eq(&model.config_type(), original_run.clone(), wrong);
        strict(
            a.local_scope(),
            transfer.run().equality().term(),
            &goal,
            false,
        );
    }
}
