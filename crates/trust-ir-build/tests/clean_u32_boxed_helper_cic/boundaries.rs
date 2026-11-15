// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Closed model error/priority controls, not native ABI or raw-total claims.
use super::*;

fn world(memory: Expr, valid: bool) -> Expr {
    app(
        "IRByteWorldV1.mk",
        [
            c("Nat"),
            memory,
            nat(37),
            list("Nat", if valid { vec![nat(8)] } else { vec![] }),
            nat(9),
        ],
    )
}
fn state(config: Expr, left: bool, right: bool) -> Expr {
    app(
        "IRCleanTag32PrefixV1.mk",
        [
            c("Nat"),
            config,
            c(if left { "Bool.true" } else { "Bool.false" }),
            c(if right { "Bool.true" } else { "Bool.false" }),
        ],
    )
}
fn fault(world: Expr, name: &str, left: bool, right: bool) -> Expr {
    state(
        app(
            "IRByteConfigV1.halted",
            [c("Nat"), app("IROutcome.type_error", [c(name)]), world],
        ),
        left,
        right,
    )
}
fn model_step(context: &Expr, before: Expr) -> Expr {
    app(
        "ir_clean_tag32_helper_step_v1",
        [
            c("Nat"),
            context.clone(),
            nat(71),
            nat(0),
            nat(10),
            nat(4),
            nat(0),
            nat(1),
            before,
        ],
    )
}
fn model_run(context: &Expr, fuel: u64, before: Expr) -> Expr {
    app(
        "ir_clean_tag32_helper_run_v1",
        [
            c("Nat"),
            context.clone(),
            nat(71),
            nat(0),
            nat(10),
            nat(4),
            nat(0),
            nat(1),
            nat(fuel),
            before,
        ],
    )
}
fn running(pc: u64, first_word: u64, world: Expr) -> Expr {
    let binding = |id, value| app("IRBinding.mk", [nat(id), value]);
    let mut locals = vec![
        binding(0, app("IRScalar.ptr_", [nat(first_word)])),
        binding(1, app("IRScalar.ptr_", [nat(11)])),
    ];
    if pc == 4 {
        locals.insert(0, binding(2, app("IRScalar.int_", [nat(3)])));
        locals.insert(0, binding(3, app("IRScalar.int_", [nat(5)])));
    }
    let frame = app(
        "IRFrame.mk",
        [
            nat(71),
            nat(0),
            nat(pc),
            list("IRBinding", locals),
            list("Nat", []),
        ],
    );
    app(
        "IRByteConfigV1.running",
        [
            c("Nat"),
            app(
                "IRMachine.mk",
                [list("IRFrame", [frame]), list("IRMemSlot", []), nat(0)],
            ),
            world,
        ],
    )
}
fn confirms(
    env: &trust_ir_build::clean_kernel::Environment,
    ty: Expr,
    actual: Expr,
    expected: Expr,
) {
    assert!(check(
        env,
        &refl(ty.clone(), expected.clone()),
        &eq(ty, actual, expected)
    ));
}

#[test]
fn fixed_provider_error_priority_zero_fuel_and_resource_stop_are_exact() {
    subject(fixture(), |source| {
        let spec =
            clean_verify::eval_ir_tagged_u32_helper::build_tagged_u32_helper_spec_v1_with_stack()
                .unwrap();
        let env = spec.env();
        let bad = app(
            "IRByteImportResultV1.mk",
            [
                c("Nat"),
                app("IROutcome.type_error", [c("IRFault.bad_field")]),
                expected::memory(),
                nat(37),
            ],
        );
        // Exact arity, scalar carrier and bound; every refusal retains mem/host.
        for args in [
            vec![],
            vec![
                app("IRScalar.int_", [nat(3)]),
                app("IRScalar.int_", [nat(5)]),
            ],
            vec![app("IRScalar.ptr_", [nat(7)])],
            vec![app("IRScalar.int_", [nat(4294967296)])],
        ] {
            confirms(
                env,
                app("IRByteImportResultV1", [c("Nat")]),
                app(
                    "ir_clean_tag32_helper_provider_v1",
                    [
                        c("Nat"),
                        nat(10),
                        nat(4),
                        nat(4),
                        list("IRScalar", args),
                        expected::memory(),
                        nat(37),
                    ],
                ),
                bad.clone(),
            );
        }
        let ty = app("IRCleanTag32PrefixV1", [c("Nat")]);
        for valid in [true, false] {
            let w = world(expected::memory(), valid);
            let before = state(running(4, 7, w.clone()), true, false);
            // World validity precedes the stale occurrence slot in the tail.
            confirms(
                env,
                ty.clone(),
                model_step(source.context(), before),
                fault(
                    w,
                    if valid {
                        "IRFault.bad_field"
                    } else {
                        "IRFault.bad_addr"
                    },
                    true,
                    false,
                ),
            );
        }
        let w = world(expected::memory(), true);
        let before = state(running(0, 2, w.clone()), true, true);
        // The even positive pointer fits Ptr but is outside the tag domain.
        // Zero node fuel does not call the unbox provider; one node does.
        for fuel in [0, 1] {
            let reached = if fuel == 0 {
                before.clone()
            } else {
                fault(w.clone(), "IRFault.bad_field", true, true)
            };
            confirms(
                env,
                app("IRCleanTag32HelperRunV1", [c("Nat")]),
                model_run(source.context(), fuel, before.clone()),
                app("IRCleanTag32HelperRunV1.mk", [c("Nat"), reached, nat(0)]),
            );
        }
        // An inadmissible historical live owner wins over bad argument arity,
        // even when no node fuel is requested. Init still creates fresh owner8.
        let bad_memory = app(
            "IRByteMemoryV1.mk",
            [
                list(
                    "IRByteAllocationV1",
                    [app(
                        "IRByteAllocationV1.mk",
                        [nat(8192), nat(1), nat(7), c("Bool.true")],
                    )],
                ),
                Expr::lam(
                    BinderInfo::Default,
                    c("Nat"),
                    app("IROption.none", [c("Nat")]),
                ),
                nat(12288),
            ],
        );
        let initialized = app(
            "ir_clean_tag32_helper_init_v1",
            [
                c("Nat"),
                source.context().clone(),
                nat(71),
                list("IRScalar", []),
                bad_memory.clone(),
                nat(37),
            ],
        );
        confirms(
            env,
            app("IRCleanTag32HelperRunV1", [c("Nat")]),
            model_run(source.context(), 0, initialized),
            app(
                "IRCleanTag32HelperRunV1.mk",
                [
                    c("Nat"),
                    fault(world(bad_memory, true), "IRFault.bad_addr", true, true),
                    nat(0),
                ],
            ),
        );

        let mut stopped = limits();
        stopped.max_operations = 1;
        let Err(trust_ir_build::clean_u32_boxed_helper_cic::FullHelperCicError::Replay(detail)) =
            check_full_tagged_u32_boxed_helper_law(source, FuncId(71), &runtime_sources(), stopped)
        else {
            panic!("resource stop must not mint an opaque checked receipt")
        };
        assert!(detail.contains("operation budget exceeded"), "{detail}");
    });
}
