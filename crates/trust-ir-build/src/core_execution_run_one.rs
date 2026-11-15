// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Fixed closed proof of run-one = step, not a new byte evaluator or axiom.
//! The four shared inputs and both constructor cases use ordinary canonical
//! kernel binders. No program expression is captured under an invented local,
//! no caller scope is touched, and the result still requires strict replay.

use super::*;
use clean_kernel::BinderInfo;

#[cfg(test)]
#[path = "core_execution_run_one_tests.rs"]
mod tests;

fn model([world, context, providers]: [u32; 3]) -> MachineModel {
    MachineModel {
        world_type: Expr::bvar(world),
        context: Expr::bvar(context),
        providers: Expr::bvar(providers),
    }
}

pub(super) fn closed_candidate() -> Expr {
    // Under W, context, providers, config: indices are 3, 2, 1, 0.
    let outer = model([3, 2, 1]);
    // The motive additionally binds its arbitrary configuration.
    let motive_model = model([4, 3, 2]);
    let motive = Expr::lam(
        BinderInfo::Default,
        outer.config_type(),
        eq(
            &motive_model.config_type(),
            motive_model.run(&NatTerm::literal(1), Expr::bvar(0)),
            motive_model.step(Expr::bvar(0)),
        ),
    );
    // Each constructor case binds its payload, then its COMPLETE world.
    let case_model = model([5, 4, 3]);
    let case_world_type = app("IRByteWorldV1", [Expr::bvar(4)]);
    let case = |constructor, payload_type| {
        let configuration = app(constructor, [Expr::bvar(5), Expr::bvar(1), Expr::bvar(0)]);
        Expr::lam(
            BinderInfo::Default,
            constant(payload_type),
            Expr::lam(
                BinderInfo::Default,
                case_world_type.clone(),
                refl(&case_model.config_type(), case_model.step(configuration)),
            ),
        )
    };
    let cases = Expr::apps(
        Expr::const_(Name::from_string("IRByteConfigV1.rec"), vec![Level::zero()]),
        [
            outer.world_type,
            motive,
            case("IRByteConfigV1.running", "IRMachine"),
            case("IRByteConfigV1.halted", "IROutcome"),
            Expr::bvar(0),
        ],
    );
    Expr::lam(
        BinderInfo::Default,
        Expr::type_(),
        Expr::lam(
            BinderInfo::Default,
            constant("IRByteContextV1"),
            Expr::lam(
                BinderInfo::Default,
                app("IRByteProvidersV1", [Expr::bvar(1)]),
                Expr::lam(
                    BinderInfo::Default,
                    app("IRByteConfigV1", [Expr::bvar(2)]),
                    cases,
                ),
            ),
        ),
    )
}
