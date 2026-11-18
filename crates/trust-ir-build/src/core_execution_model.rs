// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Exact immutable model identity and constructor-role application prefixes.

use super::{Current, NatTerm, Result, app, require_same};
use crate::core_reflection::ReflectedCoreModuleV1;
use clean_kernel::Expr;
use std::sync::Arc;

/// Immutable execution semantics. World/frame changes do not retarget an
/// already-built equation to different providers or a different module.
/// Prefixes retain these exact terms; dynamic operands and proof obligations
/// are supplied afresh on every application. No proof fact is cached.
#[derive(Clone)]
pub struct MachineModel {
    terms: Arc<ModelTerms>,
}

struct ModelTerms {
    world_type: Expr,
    context: Expr,
    providers: Expr,
    config_type: Expr,
    run: Expr,
    step: Expr,
    running: Expr,
    valid: Expr,
    dispatch: Expr,
    fetched_step: Expr,
}

impl MachineModel {
    pub fn new(world_type: Expr, reflected: &ReflectedCoreModuleV1<'_>, providers: Expr) -> Self {
        Self::from_terms(world_type, reflected.context_term().clone(), providers)
    }

    // The same coherent constructor serves the module's ordinary symbolic
    // proof terms and false-identity controls. Identity fields are private to
    // this module so an internal caller cannot mutate them behind the cache.
    pub(super) fn from_terms(world_type: Expr, context: Expr, providers: Expr) -> Self {
        let model_prefix = |name| {
            app(
                name,
                [world_type.clone(), context.clone(), providers.clone()],
            )
        };
        Self {
            terms: Arc::new(ModelTerms {
                config_type: app("IRByteConfigV1", [world_type.clone()]),
                run: model_prefix("ir_byte_run_v1"),
                step: model_prefix("ir_byte_step_v1"),
                running: app("IRByteConfigV1.running", [world_type.clone()]),
                valid: app("ir_byte_world_valid_v1", [world_type.clone()]),
                dispatch: model_prefix("ir_byte_exec_v1"),
                fetched_step: model_prefix("ir_byte_step_fetched_v1"),
                world_type,
                context,
                providers,
            }),
        }
    }

    pub fn world_type(&self) -> &Expr {
        &self.terms.world_type
    }
    pub fn context(&self) -> &Expr {
        &self.terms.context
    }
    pub fn providers(&self) -> &Expr {
        &self.terms.providers
    }
    pub fn config_type(&self) -> Expr {
        self.terms.config_type.clone()
    }
    /// The actual run function with world, context, providers and fuel fixed.
    /// This is candidate syntax, not an execution or typing judgment.
    pub fn run_function(&self, fuel: &NatTerm) -> Expr {
        Expr::app(self.terms.run.clone(), fuel.0.clone())
    }
    pub fn run(&self, fuel: &NatTerm, initial: Expr) -> Expr {
        Expr::app(self.run_function(fuel), initial)
    }
    pub fn step(&self, initial: Expr) -> Expr {
        Expr::app(self.terms.step.clone(), initial)
    }
    pub(super) fn running(&self, machine: Expr, world: Expr) -> Expr {
        Expr::apps(self.terms.running.clone(), [machine, world])
    }
    pub(super) fn valid(&self, machine: Expr, world: Expr) -> Expr {
        Expr::apps(self.terms.valid.clone(), [machine, world])
    }
    pub(super) fn dispatch(
        &self,
        current: &Current,
        site: Expr,
        instruction: Expr,
        results: Expr,
    ) -> Expr {
        Expr::apps(
            self.terms.dispatch.clone(),
            [
                current.machine(),
                current.world.clone(),
                site,
                instruction,
                results,
            ],
        )
    }
    pub(super) fn fetched_step(&self, arguments: [Expr; 16]) -> Expr {
        Expr::apps(self.terms.fetched_step.clone(), arguments)
    }
    pub(super) fn same(&self, other: &Self) -> Result<()> {
        require_same(
            &self.terms.world_type,
            &other.terms.world_type,
            "run world type",
        )?;
        require_same(
            &self.terms.context,
            &other.terms.context,
            "run reflected context",
        )?;
        require_same(
            &self.terms.providers,
            &other.terms.providers,
            "run providers",
        )
    }
}
