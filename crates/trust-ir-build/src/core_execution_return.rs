// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Actual fetched return-to-caller candidate construction. These expression
//! records do not establish a call-stack, ABI, lifetime, or execution fact.
//! The independently reconstructed whole-model claim must kernel-check the
//! completed candidate, including its newly derived world-validity equation.

use super::*;

/// An explicit return boundary. `caller` is the frame ALREADY advanced by the
/// original call push; returning binds its destinations without advancing again.
/// The current activation owner is the head of the actual world owner list.
/// There is no assumed post-return state or validity field.
#[derive(Clone)]
pub struct ReturnFrame {
    pub returning: Expr,
    pub caller: Expr,
    pub tail: Expr,
    pub legacy_memory: Expr,
    pub legacy_cursor: Expr,
    pub memory: Expr,
    pub host: Expr,
    pub owner: Expr,
    pub owners: Expr,
    pub next: Expr,
}

impl ReturnFrame {
    pub fn current(&self, model: &MachineModel) -> Current {
        Current {
            frame: self.returning.clone(),
            tail: app(
                "IRList.cons",
                [constant("IRFrame"), self.caller.clone(), self.tail.clone()],
            ),
            legacy_memory: self.legacy_memory.clone(),
            legacy_cursor: self.legacy_cursor.clone(),
            world: app(
                "IRByteWorldV1.mk",
                [
                    model.world_type.clone(),
                    self.memory.clone(),
                    self.host.clone(),
                    app(
                        "IRList.cons",
                        [constant("Nat"), self.owner.clone(), self.owners.clone()],
                    ),
                    self.next.clone(),
                ],
            ),
        }
    }

    fn resumed(&self, model: &MachineModel, values: Expr) -> Current {
        Current {
            frame: app(
                "ir_frame_set_many",
                [
                    self.caller.clone(),
                    app("ir_frame_dests", [self.returning.clone()]),
                    values,
                ],
            ),
            tail: self.tail.clone(),
            legacy_memory: self.legacy_memory.clone(),
            legacy_cursor: self.legacy_cursor.clone(),
            world: app(
                "IRByteWorldV1.mk",
                [
                    model.world_type.clone(),
                    app(
                        "ir_byte_retire_v1",
                        [self.owner.clone(), self.memory.clone()],
                    ),
                    self.host.clone(),
                    self.owners.clone(),
                    self.next.clone(),
                ],
            ),
        }
    }
}

/// Three coherent candidate outputs, not an authority token. The exact run is
/// one fetched Return instruction, not execution of the callee body. The fresh
/// validity equation concerns `resumed`, never the former callee configuration.
pub struct ReturnTransfer {
    run: ExactRun,
    resumed: Current,
    valid: PendingEquality,
}

impl ReturnTransfer {
    pub fn run(&self) -> &ExactRun {
        &self.run
    }
    pub fn resumed(&self) -> &Current {
        &self.resumed
    }
    pub fn valid(&self) -> &PendingEquality {
        &self.valid
    }
}

impl FetchedSite {
    pub(super) fn return_arguments(
        &self,
        model: &MachineModel,
        target: &CallTarget,
    ) -> Result<Expr> {
        require_same(&self.context, &model.context, "return fetched context")?;
        require_same(&target.context, &model.context, "return function context")?;
        require_same(
            &target.function_id,
            &nat(u64::from(self.coordinate.function.index())),
            "return function identity",
        )?;
        if !matches!(self.instruction.get_app_fn().kind(), ExprKind::Const(name, _) if name == &Name::from_string("IRInst.ret"))
        {
            return Err("return assembler requires an actual IRInst.ret".into());
        }
        let fields = self.instruction.get_app_args();
        let [arguments] = fields.as_slice() else {
            return Err("actual return has wrong constructor arity".into());
        };
        require_same(
            &self.results,
            &list("Nat", &[]),
            "return instruction result destinations",
        )?;
        Ok((*arguments).clone())
    }

    fn return_guard(
        &self,
        model: &MachineModel,
        target: &CallTarget,
        frame: &ReturnFrame,
        arguments: Expr,
        values: Expr,
    ) -> Expr {
        app(
            "Bool.and",
            [
                app(
                    "ir_byte_values_match_v1",
                    [
                        model.context.clone(),
                        app("ir_byte_signature_returns_v1", [target.signature.clone()]),
                        values,
                    ],
                ),
                app(
                    "ir_nat_eqb",
                    [
                        app(
                            "ir_byte_length_v1",
                            [
                                constant("Nat"),
                                app("ir_frame_dests", [frame.returning.clone()]),
                            ],
                        ),
                        app("ir_byte_length_v1", [constant("Nat"), arguments]),
                    ],
                ),
            ],
        )
    }

    /// Actual return typing/arity obligation on the explicit operand values.
    /// No guard proof is manufactured by exposing this expression. There is no
    /// fixed lane count: the actual returning signature and destinations govern.
    pub fn return_admission(
        &self,
        model: &MachineModel,
        target: &CallTarget,
        frame: &ReturnFrame,
        values: Expr,
    ) -> Result<Expr> {
        Ok(self.return_guard(
            model,
            target,
            frame,
            self.return_arguments(model, target)?,
            values,
        ))
    }

    /// Compose actual fetch, return dispatch, operand resolution and world pop.
    /// `resolved` must read the actual Ret operand IDs from `frame.current()`;
    /// `admitted` proves [`Self::return_admission`] for its explicit values;
    /// `before` is the pre-return world-validity equation. All remain candidates
    /// until final replay. An arbitrary opaque frame position may require the
    /// caller's explicit transport before the fetched lookup equations reduce.
    pub fn return_to_caller(
        &self,
        assembler: &mut Assembler<'_>,
        model: &MachineModel,
        target: &CallTarget,
        frame: &ReturnFrame,
        resolved: PendingEquality,
        admitted: PendingEquality,
        before: PendingEquality,
    ) -> Result<ReturnTransfer> {
        assembler.charge()?;
        let arguments = self.return_arguments(model, target)?;
        let current = frame.current(model);
        let actual_values = app("ir_resolve", [current.machine(), arguments.clone()]);
        let values = resolved.right.clone();
        resolved.endpoints(
            &app("IRList", [constant("IRScalar")]),
            &actual_values,
            &values,
        )?;
        before.endpoints(
            &constant("Bool"),
            &current.valid(model),
            &constant("Bool.true"),
        )?;
        let guard = |values| self.return_guard(model, target, frame, arguments.clone(), values);
        admitted.endpoints(
            &constant("Bool"),
            &guard(values.clone()),
            &constant("Bool.true"),
        )?;

        // The checked rule tests actual ir_resolve. Transport its guard from
        // the supplied pointwise reads; do not assume reduction of symbolic SSA.
        let mapped_guard = assembler.congruence(resolved.clone(), constant("Bool"), guard)?;
        let guard_proof = assembler.convert_endpoints(
            mapped_guard,
            guard(actual_values.clone()),
            admitted.left.clone(),
        )?;
        let guard_proof = assembler.compose(guard_proof, admitted)?;

        let fetched = self.step(assembler, model, &current, before.clone())?;
        let returned = app(
            "ir_byte_return_v1",
            [
                model.world_type.clone(),
                model.context.clone(),
                current.machine(),
                current.world.clone(),
                arguments.clone(),
            ],
        );
        let dispatch =
            assembler.conversion(model.config_type(), fetched.right.clone(), returned.clone())?;
        let after_actual = frame.resumed(model, actual_values.clone()).running(model);
        let rule = PendingEquality::candidate(
            model.config_type(),
            returned,
            after_actual.clone(),
            app(
                "ir_byte_return_to_caller_v1",
                [
                    model.world_type.clone(),
                    model.context.clone(),
                    frame.returning.clone(),
                    frame.caller.clone(),
                    frame.tail.clone(),
                    frame.legacy_memory.clone(),
                    frame.legacy_cursor.clone(),
                    frame.memory.clone(),
                    frame.host.clone(),
                    frame.owner.clone(),
                    frame.owners.clone(),
                    frame.next.clone(),
                    arguments,
                    target.binding.clone(),
                    target.signature.clone(),
                    target.binding_found(),
                    target.signature_found(),
                    guard_proof.term,
                ],
            ),
        );
        let mapped_result = assembler.congruence(resolved, model.config_type(), |values| {
            frame.resumed(model, values).running(model)
        })?;
        let resumed = frame.resumed(model, values);
        let mapped_result =
            assembler.convert_endpoints(mapped_result, after_actual, resumed.running(model))?;
        let step = assembler.compose(fetched, dispatch)?;
        let step = assembler.compose(step, rule)?;
        let step = assembler.compose(step, mapped_result)?;
        let run = assembler.one_step(model, current.running(model), step)?;

        // Real pre→post ownership preservation. Return retires the current
        // owner, retains host/next/history, and never advances the caller again.
        let valid = PendingEquality::candidate(
            constant("Bool"),
            resumed.valid(model),
            constant("Bool.true"),
            app(
                "ir_byte_world_pop_shape_v1",
                [
                    model.world_type.clone(),
                    frame.memory.clone(),
                    frame.host.clone(),
                    frame.owner.clone(),
                    frame.returning.clone(),
                    frame.owners.clone(),
                    frame.next.clone(),
                    frame.caller.clone(),
                    resumed.frame.clone(),
                    frame.tail.clone(),
                    frame.legacy_memory.clone(),
                    frame.legacy_cursor.clone(),
                    before.term,
                ],
            ),
        );
        Ok(ReturnTransfer {
            run,
            resumed,
            valid,
        })
    }
}

#[cfg(test)]
#[path = "core_execution_return_tests.rs"]
mod tests;
