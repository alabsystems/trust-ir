// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Actual Core halt composition after a variable-length source simulation.
//!
//! The source halt and the exact Core terminal suffix are separate mandatory
//! proof candidates. Neither follows from a finite prefix, a rank label, a
//! visited-node count or a proposed output. This assembles candidate terms;
//! the consumer must independently reconstruct and check its whole claim.

use super::*;

/// A terminal suffix over the SAME source state and actual Core configuration.
/// Every field is untrusted until the complete proof is independently replayed.
#[derive(Clone)]
pub struct SegmentedHaltProjection {
    /// S -> CoreConfig -> Nat. This can include a real wrapper's output stores.
    pub core_steps: Expr,
    /// S -> CoreConfig -> IROutcome, retaining the actual error/return outcome.
    pub outcome: Expr,
    /// S -> CoreConfig -> IRByteWorldV1 Host, including final memory and owners.
    pub world: Expr,
    /// Candidate for exactly [`Self::halt_proposition`], not an assumed halt.
    pub reaches_halt: PendingProof,
}

/// A complete actual-run equation, with its preceding source facts retained.
/// No affine execution token, certificate, provider lease or native permission
/// is constructed here. Terminal memory/representation clauses remain owed.
#[derive(Clone)]
pub struct SimulatedHalt {
    pub source_final: Expr,
    pub prefix_configuration: Expr,
    pub prefix_relation: PendingProof,
    pub source_halted: PendingProof,
    pub outcome: Expr,
    pub world: Expr,
    pub run: ExactRun,
}

impl SegmentedHaltProjection {
    /// `forall s c, R s c -> H s = true ->
    /// run (cost s c) c = halted (outcome s c) (world s c)`.
    /// Close the fixed telescope before inserting any caller expression, so
    /// caller locals cannot capture the statement's source/world binders.
    pub fn halt_proposition(
        &self,
        model: &MachineModel,
        simulation: &SegmentedPrefixSimulation,
    ) -> Expr {
        let mut scope = Scope::new();
        let mut parameters = Vec::new();
        let mut local = |ty| {
            let value = scope.try_local(ty).expect("fixed terminal telescope");
            parameters.push(value.clone());
            value
        };
        let source_type = local(Expr::type_());
        let config_type = local(Expr::type_());
        let world_type = local(Expr::type_());
        let halted = local(Expr::arrow(source_type.term().clone(), constant("Bool")));
        let relation = local(Expr::arrow(
            source_type.term().clone(),
            Expr::arrow(config_type.term().clone(), Expr::sort(Level::zero())),
        ));
        let run = local(Expr::arrow(
            constant("Nat"),
            Expr::arrow(config_type.term().clone(), config_type.term().clone()),
        ));
        let halt = local(Expr::arrow(
            constant("IROutcome"),
            Expr::arrow(world_type.term().clone(), config_type.term().clone()),
        ));
        let binary = |result| {
            Expr::arrow(
                source_type.term().clone(),
                Expr::arrow(config_type.term().clone(), result),
            )
        };
        let cost = local(binary(constant("Nat")));
        let outcome = local(binary(constant("IROutcome")));
        let world = local(binary(world_type.term().clone()));
        drop(local);
        let s = scope.try_local(source_type.term().clone()).unwrap();
        let c = scope.try_local(config_type.term().clone()).unwrap();
        let related = scope
            .try_local(Expr::apps(
                relation.term().clone(),
                [s.term().clone(), c.term().clone()],
            ))
            .unwrap();
        let stopped = scope
            .try_local(eq(
                &constant("Bool"),
                Expr::app(halted.term().clone(), s.term().clone()),
                constant("Bool.true"),
            ))
            .unwrap();
        let at = |function: &Local| {
            Expr::apps(
                function.term().clone(),
                [s.term().clone(), c.term().clone()],
            )
        };
        let body = eq(
            config_type.term(),
            Expr::apps(run.term().clone(), [at(&cost), c.term().clone()]),
            Expr::apps(halt.term().clone(), [at(&outcome), at(&world)]),
        );
        let body = s.pi(c.pi(related.pi(stopped.pi(body))));
        let template = scope
            .close(
                &parameters
                    .iter()
                    .rev()
                    .fold(body, |body, parameter| parameter.lam(body)),
            )
            .unwrap();
        Expr::apps(
            template,
            [
                simulation.source_type.clone(),
                model.config_type(),
                app("IRByteWorldV1", [model.world_type().clone()]),
                simulation.source_halted.clone(),
                simulation.relation.clone(),
                app(
                    "ir_byte_run_v1",
                    [
                        model.world_type().clone(),
                        model.context().clone(),
                        model.providers().clone(),
                    ],
                ),
                app("IRByteConfigV1.halted", [model.world_type().clone()]),
                self.core_steps.clone(),
                self.outcome.clone(),
                self.world.clone(),
            ],
        )
    }
}

impl Assembler<'_> {
    /// Compose the exact variable-cost prefix and a proven terminal suffix.
    /// Sufficient source fuel is required explicitly; the actual Core suffix
    /// must reach a real halted configuration with its actual outcome/world.
    /// The same assembler's construction counters and Scope remain in use.
    #[allow(clippy::too_many_arguments)] // Explicit simulation/termination telescope.
    pub fn simulate_segmented_halt(
        &mut self,
        model: &MachineModel,
        simulation: &SegmentedPrefixSimulation,
        terminal: &SegmentedHaltProjection,
        fuel: &NatTerm,
        source_initial: Expr,
        core_initial: Expr,
        initial: PendingProof,
        source_halted: PendingProof,
    ) -> Result<SimulatedHalt> {
        self.charge()?;
        require_same(
            source_halted.proposition(),
            &simulation.halted_after_proposition(fuel, source_initial.clone()),
            "segmented source sufficient fuel",
        )?;
        require_same(
            terminal.reaches_halt.proposition(),
            &terminal.halt_proposition(model, simulation),
            "segmented actual Core terminal suffix",
        )?;
        let prefix = self.simulate_segmented_prefix(
            model,
            simulation,
            fuel,
            source_initial.clone(),
            core_initial.clone(),
            initial,
        )?;
        let source_final = simulation.source_run(fuel.term().clone(), source_initial);
        let prefix_configuration = model.run(&prefix.core_fuel, core_initial.clone());
        let at = |function: &Expr| {
            Expr::apps(
                function.clone(),
                [source_final.clone(), prefix_configuration.clone()],
            )
        };
        let suffix_fuel = NatTerm(at(&terminal.core_steps));
        let outcome = at(&terminal.outcome);
        let world = at(&terminal.world);
        let halted = app(
            "IRByteConfigV1.halted",
            [model.world_type().clone(), outcome.clone(), world.clone()],
        );
        let terminal_equality = PendingEquality::candidate(
            model.config_type(),
            model.run(&suffix_fuel, prefix_configuration.clone()),
            halted.clone(),
            Expr::apps(
                terminal.reaches_halt.term().clone(),
                [
                    source_final.clone(),
                    prefix_configuration.clone(),
                    prefix.proof.term().clone(),
                    source_halted.term().clone(),
                ],
            ),
        );
        let first = ExactRun::candidate(
            model.clone(),
            core_initial,
            prefix_configuration.clone(),
            prefix.core_fuel,
            PendingEquality::reflexive(model.config_type(), prefix_configuration.clone()),
        )?;
        let last = ExactRun::candidate(
            model.clone(),
            prefix_configuration.clone(),
            halted,
            suffix_fuel,
            terminal_equality,
        )?;
        let run = self.concatenate(first, last)?;
        Ok(SimulatedHalt {
            source_final,
            prefix_configuration,
            prefix_relation: prefix.proof,
            source_halted,
            outcome,
            world,
            run,
        })
    }
}

#[cfg(test)]
#[path = "core_execution_segmented_halt_tests.rs"]
mod tests;
