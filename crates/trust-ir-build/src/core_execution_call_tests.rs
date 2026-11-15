// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Structural adapter controls, not an installed replacement byte evaluator.
//! Actual byte-environment replay is a consuming integration obligation.

use super::*;

fn limits() -> Limits {
    Limits {
        max_operations: 10_000,
        max_locals: 1_000,
        max_list_items: 100,
        max_lookup_candidates: 100,
        lookup_heartbeats: 1_000_000,
        lookup_cache_entries: 16_384,
    }
}

struct Fixture {
    model: MachineModel,
    target: InternalTarget,
    site: FetchedSite,
    current: Current,
    values: Expr,
    premises: InternalCallPremises,
    parameters: Vec<Local>,
}

fn fixture(scope: &mut Scope, args: usize, results: usize, indirect: bool) -> Fixture {
    let model = MachineModel {
        world_type: constant("Nat"),
        context: constant("test_call_context"),
        providers: constant("test_call_providers"),
    };
    let target = InternalTarget {
        target: CallTarget {
            context: model.context.clone(),
            function_id: nat(41),
            binding: constant("test_call_binding"),
            signature: constant("test_call_signature"),
        },
        function: constant("test_call_callee"),
    };
    let ids = list(
        "Nat",
        &(0..args)
            .map(|i| nat(300 + u64::try_from(i).unwrap() * 7))
            .collect::<Vec<_>>(),
    );
    let destinations = list(
        "Nat",
        &(0..results)
            .map(|i| nat(700 + u64::try_from(i).unwrap() * 11))
            .collect::<Vec<_>>(),
    );
    let inst = if indirect {
        app(
            "IRInst.callindirect",
            [nat(99), nat(17), ids.clone(), nat(1)],
        )
    } else {
        app("IRInst.call", [nat(41), ids.clone()])
    };
    let site = FetchedSite {
        context: model.context.clone(),
        coordinate: Coordinate {
            function: FuncId::new(80),
            block: BlockId::new(29),
            instruction: 9,
        },
        function: constant("test_call_function"),
        block: constant("test_call_block"),
        node: app("IRNode.mk", [inst.clone(), destinations.clone()]),
        instruction: inst,
        results: destinations,
        site: constant("test_call_site"),
    };
    let mut parameters = Vec::new();
    let mut local = |ty| {
        let p = scope.try_local(ty).unwrap();
        parameters.push(p.clone());
        p.term().clone()
    };
    let current = Current {
        frame: app(
            "IRFrame.mk",
            [
                nat(80),
                nat(29),
                nat(9),
                local(app("IRList", [constant("IRBinding")])),
                list("Nat", &[]),
            ],
        ),
        tail: local(app("IRList", [constant("IRFrame")])),
        legacy_memory: local(app("IRList", [constant("IRMemSlot")])),
        legacy_cursor: local(constant("Nat")),
        world: local(app("IRByteWorldV1", [constant("Nat")])),
    };
    let values = list(
        "IRScalar",
        &(0..args)
            .map(|_| local(constant("IRScalar")))
            .collect::<Vec<_>>(),
    );
    let actual = app("ir_resolve", [current.machine(), ids]);
    let resolved_type = app("IRList", [constant("IRScalar")]);
    let resolved = PendingEquality::candidate(
        resolved_type.clone(),
        actual.clone(),
        values.clone(),
        local(eq(&resolved_type, actual, values.clone())),
    );
    let checks = target.checks(&model, &site, values.clone()).unwrap();
    let mut hypothesis = |guard: Expr, result: Expr| {
        let term = local(eq(&constant("Bool"), guard.clone(), result.clone()));
        PendingEquality::candidate(constant("Bool"), guard, result, term)
    };
    let local_binding = hypothesis(checks.local_binding, constant("Bool.false"));
    let arity = hypothesis(checks.arity, constant("Bool.true"));
    let admitted = hypothesis(checks.admitted, constant("Bool.true"));
    let before = hypothesis(current.valid(&model), constant("Bool.true"));
    let indirect_guard = hypothesis(
        target.call_target().indirect_guard(nat(17), nat(1), &site),
        constant("Bool.true"),
    );
    let callback_term = local(eq(
        &constant("IRScalar"),
        app("ir_getd", [current.machine(), nat(99)]),
        app("IRScalar.fnptr_", [nat(41)]),
    ));
    let callback = LookupFact::candidate(
        current.machine(),
        ValueId::new(99),
        app("IRScalar.fnptr_", [nat(41)]),
        PendingEquality::candidate(
            constant("IRScalar"),
            app("ir_getd", [current.machine(), nat(99)]),
            app("IRScalar.fnptr_", [nat(41)]),
            callback_term,
        ),
    )
    .unwrap();
    let mut assembler = Assembler::new(scope, limits()).unwrap();
    let dispatch = if indirect {
        target
            .call_target()
            .indirect(
                &mut assembler,
                &model,
                &current,
                &site,
                &callback,
                indirect_guard,
            )
            .unwrap()
    } else {
        target
            .call_target()
            .direct(&mut assembler, &model, &current, &site)
            .unwrap()
    };
    Fixture {
        model,
        target,
        site,
        current,
        values,
        premises: InternalCallPremises {
            dispatch,
            resolved,
            local_binding,
            arity,
            admitted,
            before,
        },
        parameters,
    }
}

fn transfer(scope: &mut Scope, f: &Fixture) -> Result<InternalCallTransfer> {
    f.site.call_internal(
        &mut Assembler::new(scope, limits())?,
        &f.model,
        &f.target,
        &f.current,
        f.premises.clone(),
    )
}

#[test]
fn internal_call_derives_exact_entry_continuation_and_symbolic_owner() {
    for (args, results) in [(0, 0), (1, 1), (3, 5), (7, 2)] {
        for indirect in [false, true] {
            let mut scope = Scope::new();
            let f = fixture(&mut scope, args, results, indirect);
            let got = transfer(&mut scope, &f).unwrap();
            let [memory, host, owners, next] = world_fields(&f.model, f.current.world.clone());
            let frame = app(
                "IRFrame.mk",
                [
                    app("ir_func_id", [f.target.function.clone()]),
                    app("ir_func_entry", [f.target.function.clone()]),
                    nat(0),
                    app(
                        "ir_bind_params",
                        [
                            app("ir_func_params", [f.target.function.clone()]),
                            f.values.clone(),
                            list("IRBinding", &[]),
                        ],
                    ),
                    f.site.results.clone(),
                ],
            );
            let caller = app("ir_frame_advance", [f.current.frame.clone()]);
            assert_eq!(got.current().frame, frame);
            assert_eq!(
                got.current().tail,
                app(
                    "IRList.cons",
                    [constant("IRFrame"), caller.clone(), f.current.tail.clone()]
                )
            );
            assert_eq!(
                got.current().world,
                world_constructor(
                    &f.model,
                    [
                        memory.clone(),
                        host.clone(),
                        app(
                            "IRList.cons",
                            [constant("Nat"), next.clone(), owners.clone()]
                        ),
                        app("Nat.succ", [next.clone()])
                    ]
                )
            );
            assert_eq!(got.return_frame().caller, caller);
            assert_eq!(got.return_frame().owner, next);
            assert_eq!(got.return_frame().owners, owners);
            assert_eq!(got.return_frame().memory, memory);
            assert_eq!(got.return_frame().host, host);
            assert_eq!(
                got.return_frame().current(&f.model).running(&f.model),
                got.current().running(&f.model)
            );
            assert_eq!(got.current().legacy_memory, f.current.legacy_memory);
            assert_eq!(got.current().legacy_cursor, f.current.legacy_cursor);
            assert_eq!(got.step().left, f.model.step(f.current.running(&f.model)));
            assert_eq!(got.step().right, got.current().running(&f.model));
            assert_eq!(got.run().initial(), &f.current.running(&f.model));
            assert_eq!(got.run().reached(), &got.current().running(&f.model));
            assert_eq!(got.run().fuel().term(), &nat(1));
            assert_eq!(got.valid().left, got.current().valid(&f.model));
            assert_eq!(got.valid().right, constant("Bool.true"));
            let fields = got.valid().term.get_app_args();
            assert_eq!(fields.len(), 12);
            assert_eq!(
                got.valid().term.get_app_fn(),
                &constant("ir_byte_world_push_shape_v1")
            );
            assert_eq!(*fields[3], frame);
            assert_eq!(*fields[6], f.current.frame);
            assert_eq!(*fields[7], caller);
            assert_ne!(got.valid().term, f.premises.before.term);
            for term in [
                got.step().term.clone(),
                got.run().equality().term.clone(),
                got.valid().term.clone(),
            ] {
                let closed = f
                    .parameters
                    .iter()
                    .rev()
                    .fold(term, |body, local| local.lam(body));
                assert!(!scope.close(&closed).unwrap().has_fvar_quick());
            }
        }
    }
}

#[test]
fn internal_call_refuses_wrong_actual_site_values_and_guard_endpoints() {
    for mutation in 0..15 {
        let mut scope = Scope::new();
        let mut f = fixture(&mut scope, 3, 5, false);
        match mutation {
            0 => f.site.instruction = app("IRInst.ret", [list("Nat", &[])]),
            1 => f.site.instruction = app("IRInst.call", [nat(42), list("Nat", &[])]),
            2 => f.site.instruction = app("IRInst.call", [nat(41)]),
            3 => f.site.context = constant("other_context"),
            4 => f.target.target.context = constant("other_context"),
            5 => {
                f.premises.resolved.left =
                    app("ir_resolve", [f.current.machine(), list("Nat", &[])])
            }
            6 => f.premises.resolved.ty = constant("IRScalar"),
            7 => f.premises.local_binding.right = constant("Bool.true"),
            8 => f.premises.arity.left = constant("Bool.true"),
            9 => f.premises.admitted.right = constant("Bool.false"),
            10 => f.premises.before.left = constant("Bool.true"),
            11 => f.premises.dispatch.left = constant("other_dispatch"),
            12 => f.site.results = list("Nat", &[]),
            13 => f.current.world = constant("other_world"),
            14 => f.premises.resolved.right = list("IRScalar", &[]),
            _ => unreachable!(),
        }
        assert!(transfer(&mut scope, &f).is_err(), "mutation {mutation}");
    }
}

#[test]
fn internal_call_keeps_unchecked_proof_values_and_respects_construction_limits() {
    let mut scope = Scope::new();
    let mut f = fixture(&mut scope, 3, 5, true);
    // A candidate container is not a proof certificate. Changed proof terms
    // with the same stated endpoints must survive to independent kernel replay.
    f.premises.before.term = constant("deliberately_unchecked_before");
    assert!(transfer(&mut scope, &f).is_ok());
    for policy in [
        Limits {
            max_operations: 1,
            ..limits()
        },
        Limits {
            max_locals: 1,
            ..limits()
        },
    ] {
        let mut assembler = Assembler::new(&mut scope, policy).unwrap();
        assert!(
            f.site
                .call_internal(
                    &mut assembler,
                    &f.model,
                    &f.target,
                    &f.current,
                    f.premises.clone()
                )
                .is_err()
        );
    }
}

#[test]
fn internal_call_curried_prevalidity_and_argument_lifts_save_two_locals_per_call() {
    for indirect in [false, true] {
        let mut scope = Scope::new();
        let f = fixture(&mut scope, 3, 5, indirect);
        let mut policy = limits();
        policy.max_operations = 1_000;
        policy.max_locals = 100;
        let mut assembler = Assembler::new(&mut scope, policy).unwrap();
        let first = f
            .site
            .call_internal(
                &mut assembler,
                &f.model,
                &f.target,
                &f.current,
                f.premises.clone(),
            )
            .unwrap();
        // Only the seven cold eta locals remain. The closed owner mapper,
        // like the closed run-one helper, allocates no caller locals.
        // The world-last validity and values-last known-call primitives need
        // no new locals; both retain their original checked endpoints.
        assert_eq!(assembler.locals, 7);
        assert_eq!(assembler.limits.max_locals, 100);
        assert_eq!(first.valid().left(), &first.current().valid(&f.model));
        assert_eq!(first.valid().right(), &constant("Bool.true"));
        let before = assembler.locals;
        let second = f
            .site
            .call_internal(
                &mut assembler,
                &f.model,
                &f.target,
                &f.current,
                f.premises.clone(),
            )
            .unwrap();
        assert_eq!(assembler.locals - before, 0);
        assert_eq!(first.step().left(), second.step().left());
        assert_eq!(first.step().right(), second.step().right());
        assert_eq!(first.valid().left(), second.valid().left());
        assert_eq!(first.valid().right(), second.valid().right());
        // These fixtures check the actual adapter's resource/endpoints only.
        // They do not authenticate its deliberately uninstalled source names.
    }
}

#[test]
fn internal_call_closed_world_mapper_keeps_exact_cold_and_warm_construction_caps() {
    for indirect in [false, true] {
        // The call still charges 40 cold operations and 24 warm operations:
        // seven eta-local charges and nine run-one charges are cold only.
        // Closing the owner mapper changes neither charge into a refund.
        for (operation_cap, local_cap, accepted_calls, expected_error) in [
            (
                39,
                7,
                0,
                Some("execution construction operation budget exceeded"),
            ),
            (40, 7, 1, None),
            (
                63,
                7,
                1,
                Some("execution construction operation budget exceeded"),
            ),
            (64, 7, 2, None),
            (
                1_000,
                6,
                0,
                Some("execution construction local budget exceeded"),
            ),
        ] {
            let mut scope = Scope::new();
            let f = fixture(&mut scope, 3, 5, indirect);
            let allocated = scope.allocated();
            let mut assembler = Assembler::new(
                &mut scope,
                Limits {
                    max_operations: operation_cap,
                    max_locals: local_cap,
                    ..limits()
                },
            )
            .unwrap();
            let first = f.site.call_internal(
                &mut assembler,
                &f.model,
                &f.target,
                &f.current,
                f.premises.clone(),
            );
            let result = if accepted_calls == 0 {
                first.map(|_| ())
            } else {
                let first = first.unwrap();
                assert_eq!(assembler.operations(), 40);
                assert_eq!(assembler.locals, 7);
                assert_eq!(first.valid().left(), &first.current().valid(&f.model));
                assert_eq!(first.valid().right(), &constant("Bool.true"));
                if operation_cap == 40 {
                    Ok(())
                } else {
                    let second = f.site.call_internal(
                        &mut assembler,
                        &f.model,
                        &f.target,
                        &f.current,
                        f.premises.clone(),
                    );
                    second.map(|second| {
                        assert_eq!(first.step().left(), second.step().left());
                        assert_eq!(first.step().right(), second.step().right());
                        assert_eq!(first.valid().left(), second.valid().left());
                        assert_eq!(first.valid().right(), second.valid().right());
                    })
                }
            };
            match expected_error {
                Some(error) => assert_eq!(result.unwrap_err(), error),
                None => result.unwrap(),
            }
            assert_eq!(assembler.locals, local_cap);
            assert_eq!(assembler.local_scope().allocated(), allocated + local_cap);
            assert_eq!(
                assembler.operations(),
                if local_cap == 6 { 18 } else { operation_cap }
            );
        }
    }
}

#[test]
fn internal_call_curried_prevalidity_eta_lift_replays_the_actual_kernel_predicate() {
    use clean_kernel::KernelTypeError;
    use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};

    let env = shared_specification_with_stack(EvalIrVocabulary::ByteV1)
        .unwrap()
        .env();
    let mut scope = Scope::new();
    let world_type = scope.try_local(Expr::type_()).unwrap();
    let machine = scope.try_local(constant("IRMachine")).unwrap();
    let other_machine = scope.try_local(constant("IRMachine")).unwrap();
    let world = scope
        .try_local(app("IRByteWorldV1", [world_type.term().clone()]))
        .unwrap();
    let other_world = scope.try_local(world.ty().clone()).unwrap();
    let model = MachineModel {
        world_type: world_type.term().clone(),
        context: constant("prevalidity_unused_context"),
        providers: constant("prevalidity_unused_providers"),
    };
    let mut policy = limits();
    policy.max_operations = 1_000;
    policy.max_locals = 100;
    policy.lookup_heartbeats = 5_000_000;
    policy.lookup_cache_entries = 100_000;
    let mut assembler = Assembler::new(&mut scope, policy).unwrap();
    let eta = world_eta(&mut assembler, &model, world.term().clone()).unwrap();
    let original = app(
        "ir_byte_world_valid_v1",
        [
            world_type.term().clone(),
            machine.term().clone(),
            world.term().clone(),
        ],
    );
    let rebuilt_world = eta.right().clone();
    let rebuilt = app(
        "ir_byte_world_valid_v1",
        [
            world_type.term().clone(),
            machine.term().clone(),
            rebuilt_world.clone(),
        ],
    );
    let function = app(
        "ir_byte_world_valid_v1",
        [world_type.term().clone(), machine.term().clone()],
    );
    let locals = assembler.locals;
    let operations = assembler.operations;
    let mapped = assembler
        .congruence_function(eta, constant("Bool"), function.clone())
        .unwrap();
    assert_eq!(assembler.locals, locals);
    assert_eq!(assembler.operations, operations + 1);
    assert_eq!(*mapped.term().get_app_args()[4], function);
    let start = assembler
        .conversion(constant("Bool"), original, mapped.left().clone())
        .unwrap();
    let end = assembler
        .conversion(constant("Bool"), mapped.right().clone(), rebuilt)
        .unwrap();
    let proof = assembler.compose(start, mapped).unwrap();
    let proof = assembler.compose(proof, end).unwrap();
    drop(assembler);
    let parameters = [
        world_type.clone(),
        machine.clone(),
        other_machine.clone(),
        world,
        other_world.clone(),
    ];
    let close = |proof: &PendingEquality| {
        let term = parameters
            .iter()
            .rev()
            .fold(proof.term().clone(), |body, local| local.lam(body));
        let claim = parameters
            .iter()
            .rev()
            .fold(proof.proposition(), |body, local| local.pi(body));
        (scope.close(&term).unwrap(), scope.close(&claim).unwrap())
    };
    let (term, claim) = close(&proof);
    assert!(!term.has_fvar_quick() && !claim.has_fvar_quick());
    let mut checker = TypeChecker::new(env);
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    checker.set_heartbeat_limit(5_000_000);
    checker.set_max_cache_entries(100_000);
    checker
        .check_type(&claim, &Expr::sort(Level::zero()))
        .unwrap();
    checker.check_type(&term, &claim).unwrap();
    assert!(env.audit_certification(&claim, &term).is_certified());
    let encoded = trust_ir::proof::encode_clean_expr_dag_v2(&term).unwrap();
    let decoded = trust_ir::proof::decode_clean_expr_dag_v2(&encoded).unwrap();
    assert_eq!(decoded, term);
    checker.check_type(&decoded, &claim).unwrap();
    assert!(env.audit_certification(&claim, &decoded).is_certified());
    for changed in [
        app(
            "ir_byte_world_valid_v1",
            [
                world_type.term().clone(),
                other_machine.term().clone(),
                rebuilt_world,
            ],
        ),
        app(
            "ir_byte_world_valid_v1",
            [
                world_type.term().clone(),
                machine.term().clone(),
                other_world.term().clone(),
            ],
        ),
    ] {
        let forged = PendingEquality::candidate(
            constant("Bool"),
            proof.left().clone(),
            changed,
            proof.term().clone(),
        );
        let (term, claim) = close(&forged);
        checker
            .check_type(&claim, &Expr::sort(Level::zero()))
            .unwrap();
        let error = checker.check_type(&term, &claim).unwrap_err();
        assert!(
            matches!(error, KernelTypeError::TypeMismatch { .. }),
            "{error:?}"
        );
    }
}
