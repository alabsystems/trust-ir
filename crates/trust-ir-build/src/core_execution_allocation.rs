// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fetched Alloca candidates in the actual byte evaluator. Allocation changes
//! the allocation history and cursor: it cannot use `MemoryPremises`' unchanged
//! allocation-list premise. Instead the caller supplies the returned memory's
//! owner invariant, as well as the actual guarded dispatch and allocation
//! equations. These are untrusted candidates, not an assumed successful step.
//! A consumer must independently replay the complete closed claim.

use super::*;

#[derive(Clone)]
pub struct AllocationInput {
    /// Active lexical owner, not a new/global owner chosen by the consumer.
    pub owner: Expr,
    /// Resolved bounded I64/U64 carrier (one for an absent count operand).
    /// ByteV1 dispatch separately requires this actual count below 2^63.
    pub count: Expr,
}

pub struct AllocationChecks {
    /// Exact actual helper, retaining fetched optional SSA count and owner stack.
    pub dispatch: Expr,
    /// Expected dispatch endpoint, before performing the allocation.
    pub dispatched: Expr,
    /// Typed allocation with fetched pointee layout, alignment and actual memory.
    pub evaluation: Expr,
    /// Destination arity and actual site result-type matching.
    pub result: Expr,
    /// Returned memory ownership for the unchanged active owners/next identity.
    pub owners: Expr,
}

#[derive(Clone)]
pub struct AllocationPremises {
    /// Eq Config checks.dispatch checks.dispatched. This proves the real
    /// nonempty-owner, integer-count and count < 2^63 dispatch, not just layout.
    pub dispatch: PendingEquality,
    /// Eq IRByteMemoryResultV1 checks.evaluation result.result().
    pub evaluated: PendingEquality,
    pub result: PendingEquality,
    pub owners: PendingEquality,
    pub before: PendingEquality,
}

/// Actual one-step allocation, including its changed memory and owner validity.
/// No allocation-list, cursor or byte-map preservation is asserted.
pub struct AllocationTransfer {
    step: PendingEquality,
    run: ExactRun,
    current: Current,
    valid: PendingEquality,
    result: MemoryResult,
}

impl AllocationTransfer {
    pub fn step(&self) -> &PendingEquality {
        &self.step
    }
    pub fn run(&self) -> &ExactRun {
        &self.run
    }
    pub fn current(&self) -> &Current {
        &self.current
    }
    pub fn valid(&self) -> &PendingEquality {
        &self.valid
    }
    pub fn result(&self) -> &MemoryResult {
        &self.result
    }
    pub fn memory(&self) -> &Expr {
        &self.result.memory
    }
}

fn projection(model: &MachineModel, current: &Current, field: &str) -> Expr {
    app(
        &format!("ir_byte_world_{field}_v1"),
        [model.world_type.clone(), current.world.clone()],
    )
}

fn memory_result(
    model: &MachineModel,
    current: &Current,
    site: &FetchedSite,
    result: Expr,
) -> Expr {
    app(
        "ir_byte_memory_result_v1",
        [
            model.world_type.clone(),
            model.context.clone(),
            current.machine(),
            current.world.clone(),
            site.results.clone(),
            app("ir_byte_site_results_v1", [site.site.clone()]),
            constant("Bool.false"),
            result,
        ],
    )
}

impl FetchedSite {
    pub fn allocation_checks(
        &self,
        model: &MachineModel,
        current: &Current,
        input: &AllocationInput,
        result: &MemoryResult,
    ) -> Result<AllocationChecks> {
        require_same(&self.context, &model.context, "allocation fetched context")?;
        let fields = self.instruction.get_app_args();
        let ExprKind::Const(name, _) = self.instruction.get_app_fn().kind() else {
            return Err("allocation assembler requires fetched Alloca".into());
        };
        let [ty, count] = fields.as_slice() else {
            return Err("allocation assembler requires fetched Alloca".into());
        };
        if name.to_string() != "IRInst.alloca" {
            return Err("allocation assembler requires fetched Alloca".into());
        }
        let evaluation = app(
            "ir_byte_alloc_v1",
            [
                model.context.clone(),
                (*ty).clone(),
                input.count.clone(),
                app("ir_byte_site_align_v1", [self.site.clone()]),
                input.owner.clone(),
                projection(model, current, "memory"),
            ],
        );
        let values = list("IRScalar", std::slice::from_ref(&result.value));
        Ok(AllocationChecks {
            dispatch: app(
                "ir_byte_alloca_exec_v1",
                [
                    model.world_type.clone(),
                    model.context.clone(),
                    current.machine(),
                    current.world.clone(),
                    self.results.clone(),
                    self.site.clone(),
                    (*ty).clone(),
                    (*count).clone(),
                ],
            ),
            dispatched: memory_result(model, current, self, evaluation.clone()),
            evaluation,
            result: app(
                "Bool.and",
                [
                    app(
                        "ir_nat_eqb",
                        [
                            app("ir_byte_length_v1", [constant("Nat"), self.results.clone()]),
                            nat(1),
                        ],
                    ),
                    app(
                        "ir_byte_values_match_v1",
                        [
                            model.context.clone(),
                            app("ir_byte_site_results_v1", [self.site.clone()]),
                            values,
                        ],
                    ),
                ],
            ),
            owners: app(
                "ir_byte_memory_owners_v1",
                [
                    result.memory.clone(),
                    projection(model, current, "owners"),
                    projection(model, current, "next"),
                ],
            ),
        })
    }

    pub fn allocation_value(
        &self,
        assembler: &mut Assembler<'_>,
        model: &MachineModel,
        current: &Current,
        input: AllocationInput,
        result: MemoryResult,
        premises: AllocationPremises,
    ) -> Result<AllocationTransfer> {
        assembler.charge()?;
        let checks = self.allocation_checks(model, current, &input, &result)?;
        premises
            .dispatch
            .endpoints(&model.config_type(), &checks.dispatch, &checks.dispatched)?;
        premises.evaluated.endpoints(
            &constant("IRByteMemoryResultV1"),
            &checks.evaluation,
            &result.result(),
        )?;
        for (proof, expected) in [
            (&premises.result, &checks.result),
            (&premises.owners, &checks.owners),
            (&premises.before, &current.valid(model)),
        ] {
            proof.endpoints(&constant("Bool"), expected, &constant("Bool.true"))?;
        }
        let world = app(
            "ir_byte_with_memory_v1",
            [
                model.world_type.clone(),
                current.world.clone(),
                result.memory.clone(),
            ],
        );
        let values = list("IRScalar", std::slice::from_ref(&result.value));
        let mut after = Current {
            frame: app(
                "ir_frame_advance",
                [app(
                    "ir_frame_set_many",
                    [current.frame.clone(), self.results.clone(), values.clone()],
                )],
            ),
            world: world.clone(),
            ..current.clone()
        };
        let bound = app(
            "ir_byte_bind_values_v1",
            [
                model.world_type.clone(),
                model.context.clone(),
                current.machine(),
                world.clone(),
                self.results.clone(),
                app("ir_byte_site_results_v1", [self.site.clone()]),
                values,
            ],
        );
        let fetched = self.step(assembler, model, current, premises.before.clone())?;
        let dispatch_start = assembler.conversion(
            model.config_type(),
            fetched.right.clone(),
            checks.dispatch.clone(),
        )?;
        let lifted = assembler.congruence(premises.evaluated, model.config_type(), |r| {
            memory_result(model, current, self, r)
        })?;
        let evaluation_start =
            assembler.conversion(model.config_type(), checks.dispatched, lifted.left.clone())?;
        let evaluation_end =
            assembler.conversion(model.config_type(), lifted.right.clone(), bound.clone())?;
        let binding = PendingEquality::candidate(
            model.config_type(),
            bound,
            after.running(model),
            app(
                "ir_byte_case_true_v1",
                [
                    model.config_type(),
                    checks.result,
                    app(
                        "IRByteConfigV1.halted",
                        [
                            model.world_type.clone(),
                            app("IROutcome.type_error", [constant("IRFault.bad_field")]),
                            world,
                        ],
                    ),
                    after.running(model),
                    after.running(model),
                    premises.result.term,
                    refl(&model.config_type(), after.running(model)),
                ],
            ),
        );
        let mut step = assembler.compose(fetched, dispatch_start)?;
        for part in [
            premises.dispatch,
            evaluation_start,
            lifted,
            evaluation_end,
            binding,
        ] {
            step = assembler.compose(step, part)?;
        }
        // Reconstruct an opaque world using the shared recursor, not eta by fiat.
        let eta = calling::world_eta(assembler, model, current.world.clone())?;
        let changed = assembler.congruence(eta, model.config_type(), |w| {
            Current {
                world: app(
                    "ir_byte_with_memory_v1",
                    [model.world_type.clone(), w, result.memory.clone()],
                ),
                ..after.clone()
            }
            .running(model)
        })?;
        let start = assembler.conversion(
            model.config_type(),
            after.running(model),
            changed.left.clone(),
        )?;
        after.world = app(
            "IRByteWorldV1.mk",
            [
                model.world_type.clone(),
                result.memory.clone(),
                projection(model, current, "host"),
                projection(model, current, "owners"),
                projection(model, current, "next"),
            ],
        );
        let end = assembler.conversion(
            model.config_type(),
            changed.right.clone(),
            after.running(model),
        )?;
        for part in [start, changed, end] {
            step = assembler.compose(step, part)?;
        }
        let run = assembler.one_step(model, current.running(model), step.clone())?;
        let valid = PendingEquality::candidate(
            constant("Bool"),
            after.valid(model),
            constant("Bool.true"),
            app(
                "ir_byte_import_world_shape_v1",
                [
                    model.world_type.clone(),
                    current.world.clone(),
                    current.frame.clone(),
                    after.frame.clone(),
                    current.tail.clone(),
                    current.legacy_memory.clone(),
                    current.legacy_cursor.clone(),
                    result.memory.clone(),
                    projection(model, current, "host"),
                    premises.before.term,
                    premises.owners.term,
                ],
            ),
        );
        Ok(AllocationTransfer {
            step,
            run,
            current: after,
            valid,
            result,
        })
    }
}

#[cfg(test)]
#[path = "core_execution_allocation_tests.rs"]
mod tests;
