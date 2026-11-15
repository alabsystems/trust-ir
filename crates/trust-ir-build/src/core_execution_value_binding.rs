// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! The existing checked, ordered value binding, independently of its producer.
//! A successful binding requires the actual destination arity and site-result
//! matching guard, not an instruction's nominal type or an overflow flag.
//! All terms remain pending until the consumer closes and replays its claim.

use super::*;

#[cfg(test)]
#[path = "core_execution_value_binding_tests.rs"]
mod tests;

/// Evidence for the original binding guard and unchanged pre-world.
pub struct ValueBindingPremises {
    pub result: PendingEquality,
    pub before: PendingEquality,
}

/// A pending Bind→running equality. This is not a fetched instruction step;
/// binding itself consumes no additional machine fuel or runtime execution.
pub struct ValueBinding {
    model: MachineModel,
    equality: PendingEquality,
    current: Current,
    valid: PendingEquality,
}

impl ValueBinding {
    pub fn equality(&self) -> &PendingEquality {
        &self.equality
    }

    pub fn current(&self) -> &Current {
        &self.current
    }

    pub fn valid(&self) -> &PendingEquality {
        &self.valid
    }

    /// Rewrite a run that actually reaches this exact binding. Preserve its
    /// initial configuration and fuel: binding is not a second machine step.
    /// Matching endpoints never validate the supplied run or guard proof.
    pub fn complete_run(&self, assembler: &mut Assembler<'_>, run: ExactRun) -> Result<ExactRun> {
        assembler.charge()?;
        self.model.same(&run.model)?;
        require_same(
            run.reached(),
            self.equality.left(),
            "value binding run boundary",
        )?;
        let equality = assembler.compose(run.equality, self.equality.clone())?;
        ExactRun::candidate(
            run.model,
            run.initial,
            self.equality.right.clone(),
            run.fuel,
            equality,
        )
    }
}

// One original predicate for single- and multi-result consumers. Keep its
// ordering, actual destination list and nominal site-result catalog intact.
pub(super) fn result_guard(site: &FetchedSite, model: &MachineModel, values: Expr) -> Expr {
    app(
        "Bool.and",
        [
            app(
                "ir_nat_eqb",
                [
                    app("ir_byte_length_v1", [constant("Nat"), site.results.clone()]),
                    app("ir_byte_length_v1", [constant("IRScalar"), values.clone()]),
                ],
            ),
            app(
                "ir_byte_values_match_v1",
                [
                    model.context.clone(),
                    app("ir_byte_site_results_v1", [site.site.clone()]),
                    values,
                ],
            ),
        ],
    )
}

impl FetchedSite {
    /// Expose the actual evaluator predicate, without asserting that it holds.
    pub fn value_binding_check(&self, model: &MachineModel, values: &[Expr]) -> Result<Expr> {
        require_same(
            &self.context,
            &model.context,
            "value binding fetched context",
        )?;
        Ok(result_guard(self, model, list("IRScalar", values)))
    }

    /// Build only the original checked binding's successful branch. The caller
    /// must supply its actual full guard and pre-world facts, then independently
    /// replay them. The destination IDs and all lanes are retained in order.
    /// Charge the existing operation/list limits before checking metadata;
    /// refusal does not refund work. No vocabulary, local or cache is installed.
    pub fn bind_values(
        &self,
        assembler: &mut Assembler<'_>,
        model: &MachineModel,
        current: &Current,
        values: &[Expr],
        premises: ValueBindingPremises,
    ) -> Result<ValueBinding> {
        assembler.charge()?;
        assembler.items(values.len())?;
        require_same(
            &self.context,
            &model.context,
            "value binding fetched context",
        )?;
        let values = list("IRScalar", values);
        let guard = result_guard(self, model, values.clone());
        premises
            .result
            .endpoints(&constant("Bool"), &guard, &constant("Bool.true"))?;
        premises.before.endpoints(
            &constant("Bool"),
            &current.valid(model),
            &constant("Bool.true"),
        )?;
        let next = Current {
            frame: app(
                "ir_frame_advance",
                [app(
                    "ir_frame_set_many",
                    [current.frame.clone(), self.results.clone(), values.clone()],
                )],
            ),
            ..current.clone()
        };
        let bound = app(
            "ir_byte_bind_values_v1",
            [
                model.world_type.clone(),
                model.context.clone(),
                current.machine(),
                current.world.clone(),
                self.results.clone(),
                app("ir_byte_site_results_v1", [self.site.clone()]),
                values,
            ],
        );
        let running = next.running(model);
        let bad_field = app(
            "IRByteConfigV1.halted",
            [
                model.world_type.clone(),
                app("IROutcome.type_error", [constant("IRFault.bad_field")]),
                current.world.clone(),
            ],
        );
        let equality = PendingEquality::candidate(
            model.config_type(),
            bound,
            running.clone(),
            app(
                "ir_byte_case_true_v1",
                [
                    model.config_type(),
                    guard,
                    bad_field,
                    running.clone(),
                    running.clone(),
                    premises.result.term,
                    refl(&model.config_type(), running),
                ],
            ),
        );
        // Validity observes frame count, not its PC or SSA bindings. The new
        // machine keeps its explicit head, exact tail, legacy state and world.
        let valid = assembler.convert_endpoints(
            premises.before,
            next.valid(model),
            constant("Bool.true"),
        )?;
        Ok(ValueBinding {
            model: model.clone(),
            equality,
            current: next,
            valid,
        })
    }
}
