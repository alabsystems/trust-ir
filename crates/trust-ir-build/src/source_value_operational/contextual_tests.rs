// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::core_execution::{InternalCallPremises, NatTerm};
use trust_ir::{FuncId, Module};

fn limits() -> Limits {
    Limits {
        max_operations: 20000,
        max_locals: 4096,
        max_list_items: 4096,
        max_lookup_candidates: 1024,
        lookup_heartbeats: 1000000,
        lookup_cache_entries: 100000,
    }
}

fn with_subject(run: impl FnOnce(&CheckedSourceValueOperational<'_>)) {
    macro_rules! data {
        ($file:literal) => {
            include_bytes!(concat!(
                "../../tests/fixtures/source_value_equations/boundActualEquation/",
                $file
            ))
        };
    }
    let decode = |b: &[u8]| trust_ir::proof::decode_clean_expr_v1(b).unwrap();
    let name = |b: &[u8]| {
        let e = decode(b);
        let clean_kernel::ExprKind::Const(n, levels) = e.kind() else {
            panic!("name")
        };
        assert!(levels.is_empty());
        n.clone()
    };
    let module: Module = trust_ir::binary::deserialize_module(data!("module.bin")).unwrap();
    assert_eq!((module.functions.len(), module.func_types.len()), (72, 73));
    assert_eq!(
        (
            module.proof_obligations.len(),
            module.proof_certificates.len()
        ),
        (1, 1)
    );
    let mut environment = Environment::with_prelude();
    let original = name(data!("definition-0.name.bin"));
    environment
        .add_decl(Declaration::Definition {
            name: original.clone(),
            level_params: vec![],
            type_: decode(data!("definition-0.type.bin")),
            value: decode(data!("definition-0.value.bin")),
            is_reducible: false,
        })
        .unwrap();
    assert_eq!(
        environment.closure_digest(&original).unwrap().as_slice(),
        data!("source-closure-digest.bin")
    );
    let equation = Declaration::Theorem {
        name: name(data!("theorem.name.bin")),
        level_params: vec![],
        type_: decode(data!("theorem.type.bin")),
        value: decode(data!("theorem.value.bin")),
    };
    let source = crate::check_uint_source_value_equation(
        &module,
        FuncId(70),
        &environment,
        &original,
        &equation,
    )
    .unwrap();
    let addresses: Vec<_> = module
        .functions
        .iter()
        .enumerate()
        .map(|(i, f)| (f.id, 4096 + 8 * i as u64))
        .collect();
    let checked = crate::check_u32_straight_line_source_value_with_validated_runtime_context(
        &source,
        &addresses,
        limits(),
    )
    .unwrap();
    assert!(core::ptr::eq(checked.source_value().module(), &module));
    run(&checked);
}

fn binding(id: u64, value: Expr) -> Expr {
    app("IRBinding.mk", [nat(id), value])
}
fn memory() -> Expr {
    let allocation = |base, size, owner, live| {
        app(
            "IRByteAllocationV1.mk",
            [
                nat(base),
                nat(size),
                nat(owner),
                c(if live { "Bool.true" } else { "Bool.false" }),
            ],
        )
    };
    app(
        "IRByteMemoryV1.mk",
        [
            list(
                "IRByteAllocationV1",
                [allocation(8192, 8, 8, true), allocation(9000, 4, 7, false)],
            ),
            Expr::lam(
                BinderInfo::Default,
                c("Nat"),
                app("IROption.none", [c("Nat")]),
            ),
            nat(10000),
        ],
    )
}
fn caller_bindings(x: Expr, y: Expr) -> Expr {
    let tag = |n| {
        app(
            "IRScalar.ptr_",
            [app("Nat.add", [app("Nat.mul", [nat(2), n]), nat(1)])],
        )
    };
    list(
        "IRBinding",
        [
            binding(0, tag(x.clone())),
            binding(1, tag(y.clone())),
            binding(2, int(x)),
            binding(3, int(y)),
        ],
    )
}

#[test]
fn full_actual_caller_composes_internal_body_and_reached_return_with_strict_replay() {
    // Conditional pc4 witness, not a proof that the preceding helper prefix ran.
    // Callee9 has no allocation here; the actual retirement rule and wrong-owner8
    // refusal exercise framing without claiming a callee deallocation example.
    with_subject(|checked| {
        let mut scope = LocalScope::new();
        let mut a = Assembler::new(&mut scope, limits()).unwrap();
        let w = a.local(Expr::type_()).unwrap();
        let host = a.local(w.term().clone()).unwrap();
        let providers = a
            .local(app("IRByteProvidersV1", [w.term().clone()]))
            .unwrap();
        let outer = a.local(c("IRFrame")).unwrap();
        let x = a.local(c("UInt32")).unwrap();
        let y = a.local(c("UInt32")).unwrap();
        let xn = app("UInt32.toNat", [x.term().clone()]);
        let yn = app("UInt32.toNat", [y.term().clone()]);
        let model = MachineModel::new(
            w.term().clone(),
            &checked.subject.reflected,
            providers.term().clone(),
        );
        let mut catalog =
            Catalog::new(checked.environment(), &checked.subject.reflected, limits()).unwrap();
        let current = Current {
            frame: app(
                "IRFrame.mk",
                [
                    nat(71),
                    nat(0),
                    nat(4),
                    caller_bindings(xn.clone(), yn.clone()),
                    list("Nat", []),
                ],
            ),
            tail: list("IRFrame", [outer.term().clone()]),
            legacy_memory: list("IRMemSlot", []),
            legacy_cursor: nat(123),
            world: app(
                "IRByteWorldV1.mk",
                [
                    w.term().clone(),
                    memory(),
                    host.term().clone(),
                    list("Nat", [nat(8), nat(6)]),
                    nat(9),
                ],
            ),
        };
        let site = catalog
            .fetch(Coordinate {
                function: FuncId(71),
                block: trust_ir::BlockId(0),
                instruction: 4,
            })
            .unwrap();
        let target = catalog.internal_target(FuncId(70)).unwrap();
        let values = list("IRScalar", [int(xn.clone()), int(yn.clone())]);
        let checks = target.checks(&model, &site, values.clone()).unwrap();
        let xf = body::fits(
            ScalarProfile::U32ConstAddMul,
            &mut a,
            &model,
            &input(ScalarProfile::U32ConstAddMul, x.term().clone()),
        )
        .unwrap();
        let yf = body::fits(
            ScalarProfile::U32ConstAddMul,
            &mut a,
            &model,
            &input(ScalarProfile::U32ConstAddMul, y.term().clone()),
        )
        .unwrap();
        let yf = body::both(&mut a, yf, pending(c("Bool"), c("Bool.true"))).unwrap();
        let fits = body::both(&mut a, xf, yf).unwrap();
        let admitted = a
            .convert_endpoints(fits, checks.admitted, c("Bool.true"))
            .unwrap();
        let resolved = a
            .conversion(
                app("IRList", [c("IRScalar")]),
                app(
                    "ir_resolve",
                    [current.machine(), list("Nat", [nat(2), nat(3)])],
                ),
                values,
            )
            .unwrap();
        let local_binding = a
            .conversion(c("Bool"), checks.local_binding, c("Bool.false"))
            .unwrap();
        let arity = truth(&mut a, checks.arity).unwrap();
        let before = truth(&mut a, current.valid(&model)).unwrap();
        let dispatch = target
            .call_target()
            .direct(&mut a, &model, &current, &site)
            .unwrap();
        let entered = site
            .call_internal(
                &mut a,
                &model,
                &target,
                &current,
                InternalCallPremises {
                    dispatch,
                    resolved,
                    local_binding,
                    arity,
                    admitted,
                    before,
                },
            )
            .unwrap();
        let prefix = body_after_call(
            checked,
            &mut a,
            &mut catalog,
            &model,
            &entered,
            x.term().clone(),
            y.term().clone(),
        )
        .unwrap();
        assert!(core::ptr::eq(prefix.source(), checked));
        assert_eq!(prefix.steps().len(), checked.instruction_count() - 1);
        assert_eq!(prefix.states().len(), checked.instruction_count());
        assert_eq!(
            prefix.return_frame().current(&model).running(&model),
            prefix.current().running(&model)
        );
        let returning = catalog
            .fetch(Coordinate {
                function: FuncId(70),
                block: trust_ir::BlockId(0),
                instruction: 3,
            })
            .unwrap();
        let call_target = catalog.call_target(FuncId(70)).unwrap();
        let returned_values = list("IRScalar", [int(prefix.result().clone())]);
        let resolved_return = a
            .conversion(
                app("IRList", [c("IRScalar")]),
                app(
                    "ir_resolve",
                    [prefix.current().machine(), list("Nat", [nat(4)])],
                ),
                returned_values.clone(),
            )
            .unwrap();
        let fit = body::fits(
            ScalarProfile::U32ConstAddMul,
            &mut a,
            &model,
            &prefix.result,
        )
        .unwrap();
        let fit = body::both(&mut a, fit, pending(c("Bool"), c("Bool.true"))).unwrap();
        let fit = body::both(&mut a, fit, pending(c("Bool"), c("Bool.true"))).unwrap();
        let guard = returning
            .return_admission(&model, &call_target, prefix.return_frame(), returned_values)
            .unwrap();
        let admitted_return = a.convert_endpoints(fit, guard, c("Bool.true")).unwrap();
        let returned = returning
            .return_to_caller(
                &mut a,
                &model,
                &call_target,
                prefix.return_frame(),
                resolved_return,
                admitted_return,
                prefix.valid().clone(),
            )
            .unwrap();
        let run = a
            .concatenate(entered.run().clone(), prefix.run().clone())
            .unwrap();
        let run = a.concatenate(run, returned.run().clone()).unwrap();
        // Independent complete post-state: actual caller resumes at5, receives4,
        // retains its live owner8 allocation and historical owner7 row. Callee9
        // is retired, ownerstack8,6 and next10 are preserved; cursor is123.
        let expected = |result: Expr, next, retired, pc| {
            app(
                "IRByteConfigV1.running",
                [
                    w.term().clone(),
                    app(
                        "IRMachine.mk",
                        [
                            list(
                                "IRFrame",
                                [
                                    app(
                                        "IRFrame.mk",
                                        [
                                            nat(71),
                                            nat(0),
                                            nat(pc),
                                            app(
                                                "IRList.cons",
                                                [
                                                    c("IRBinding"),
                                                    binding(4, int(result)),
                                                    caller_bindings(xn.clone(), yn.clone()),
                                                ],
                                            ),
                                            list("Nat", []),
                                        ],
                                    ),
                                    outer.term().clone(),
                                ],
                            ),
                            list("IRMemSlot", []),
                            nat(123),
                        ],
                    ),
                    app(
                        "IRByteWorldV1.mk",
                        [
                            w.term().clone(),
                            app("ir_byte_retire_v1", [nat(retired), memory()]),
                            host.term().clone(),
                            list("Nat", [nat(8), nat(6)]),
                            nat(next),
                        ],
                    ),
                ],
            )
        };
        let bridge = a
            .conversion(
                model.config_type(),
                run.reached().clone(),
                expected(prefix.result().clone(), 10, 9, 5),
            )
            .unwrap();
        let proof = a.compose(run.equality().clone(), bridge).unwrap();
        let source_value = app(
            "UInt32.toNat",
            [Expr::apps(
                Expr::const_(checked.source_value().source().clone(), vec![]),
                [x.term().clone(), y.term().clone()],
            )],
        );
        let mapped = mapped(
            &mut a,
            symm(prefix.source_result_equation()),
            model.config_type(),
            |n| expected(n, 10, 9, 5),
        )
        .unwrap();
        let proof = a.compose(proof, mapped).unwrap();
        let proof = a
            .convert_endpoints(
                proof,
                model.run(&NatTerm::literal(5), current.running(&model)),
                expected(source_value.clone(), 10, 9, 5),
            )
            .unwrap();
        let parameters = [
            w.clone(),
            host.clone(),
            providers.clone(),
            outer.clone(),
            x.clone(),
            y.clone(),
        ];
        let claim = close(a.local_scope(), &parameters, proof.proposition(), false).unwrap();
        let term = close(a.local_scope(), &parameters, proof.term().clone(), true).unwrap();
        strict_replay(checked.environment(), &claim, &term).unwrap();
        for (next, retired, pc) in [(9, 9, 5), (10, 8, 5), (10, 9, 6)] {
            let wrong = eq(
                model.config_type(),
                model.run(&NatTerm::literal(5), current.running(&model)),
                expected(source_value.clone(), next, retired, pc),
            );
            let wrong = close(a.local_scope(), &parameters, wrong, false).unwrap();
            let error = strict_replay(checked.environment(), &wrong, &term).unwrap_err();
            assert_eq!(error, "operational proof failed strict kernel checking");
        }
        if let Some(directory) = std::env::var_os("TRUST_IR_CONTEXTUAL_EVIDENCE_DIR") {
            let directory = std::path::PathBuf::from(directory);
            std::fs::create_dir_all(&directory).unwrap();
            for (name, expression) in [("claim.dag", &claim), ("proof.dag", &term)] {
                std::fs::write(
                    directory.join(name),
                    trust_ir::proof::encode_clean_expr_dag_v2(expression).unwrap(),
                )
                .unwrap();
            }
        }
    });
}
