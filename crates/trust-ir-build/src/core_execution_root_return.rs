// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Candidates for the existing byte machine's singleton-frame Return case.
//! There is no fabricated caller, replacement evaluator, or assumed terminal
//! world. Actual fetch, operand resolution, signature admission and pre-world
//! validity remain part of the closed claim a consumer must kernel-check.

use super::*;

/// The current root activation, with exactly one frame and one owner. This is
/// an explicit expression shape, not evidence of entry execution or lifetime.
/// A consumer starting at entry can derive it from [`Initialization`]; a suffix
/// consumer must retain its real preceding execution and current-state proof.
#[derive(Clone)]
pub struct RootReturnFrame {
    pub returning: Expr,
    pub legacy_memory: Expr,
    pub legacy_cursor: Expr,
    pub memory: Expr,
    pub host: Expr,
    pub owner: Expr,
    pub next: Expr,
}

impl RootReturnFrame {
    pub fn current(&self, model: &MachineModel) -> Current {
        Current {
            frame: self.returning.clone(),
            tail: list("IRFrame", &[]),
            legacy_memory: self.legacy_memory.clone(),
            legacy_cursor: self.legacy_cursor.clone(),
            world: app(
                "IRByteWorldV1.mk",
                [
                    model.world_type.clone(),
                    self.memory.clone(),
                    self.host.clone(),
                    list("Nat", std::slice::from_ref(&self.owner)),
                    self.next.clone(),
                ],
            ),
        }
    }

    fn retired_memory(&self) -> Expr {
        app(
            "ir_byte_retire_v1",
            [self.owner.clone(), self.memory.clone()],
        )
    }

    fn retired_world(&self, model: &MachineModel) -> Expr {
        app(
            "IRByteWorldV1.mk",
            [
                model.world_type.clone(),
                self.retired_memory(),
                self.host.clone(),
                list("Nat", &[]),
                self.next.clone(),
            ],
        )
    }

    fn halted(&self, model: &MachineModel, values: Expr) -> Expr {
        root_halted(model.world_type.clone(), self.retired_world(model), values)
    }
}

/// One actual fetched Return, ending in `halted (ret values)`. The memory is
/// EXACTLY the incoming memory with the root owner retired: bytes, allocation
/// history, cursor, host and next-owner counter are not replaced. No live
/// `Current` or post-running validity equation is claimed for this terminal.
pub struct RootReturnTransfer {
    run: ExactRun,
    values: Expr,
    memory: Expr,
    world: Expr,
    halted: Expr,
}

impl RootReturnTransfer {
    pub fn run(&self) -> &ExactRun {
        &self.run
    }
    pub fn values(&self) -> &Expr {
        &self.values
    }
    pub fn memory(&self) -> &Expr {
        &self.memory
    }
    pub fn world(&self) -> &Expr {
        &self.world
    }
    pub fn halted(&self) -> &Expr {
        &self.halted
    }
}

fn guard(model: &MachineModel, frame: &RootReturnFrame, signature: Expr, values: Expr) -> Expr {
    root_guard(
        model.context.clone(),
        frame.returning.clone(),
        signature,
        values,
    )
}

fn root_guard(context: Expr, returning: Expr, signature: Expr, values: Expr) -> Expr {
    app(
        "Bool.and",
        [
            app(
                "ir_byte_values_match_v1",
                [
                    context,
                    app("ir_byte_signature_returns_v1", [signature]),
                    values,
                ],
            ),
            app(
                "ir_nat_eqb",
                [
                    app(
                        "ir_byte_length_v1",
                        [constant("Nat"), app("ir_frame_dests", [returning])],
                    ),
                    nat(0),
                ],
            ),
        ],
    )
}

fn root_halted(world_type: Expr, world: Expr, values: Expr) -> Expr {
    app(
        "IRByteConfigV1.halted",
        [world_type, app("IROutcome.ret", [values]), world],
    )
}

// Fixed expression recipes, not proof, admission or caller-Scope allocations.
// Domains name only the earlier neutral parameters. Actual operands are applied
// AFTER these functions are closed, including dependent W/world/failure terms.
fn close_root_function<const N: usize>(types: [Expr; N], body: Expr) -> Expr {
    types.into_iter().rev().fold(body, |body, ty| {
        Expr::lam(clean_kernel::BinderInfo::Default, ty, body)
    })
}

fn closed_guard_function() -> Expr {
    close_root_function(
        [
            constant("IRByteContextV1"),
            constant("IRFrame"),
            constant("IRByteSignatureV1"),
            app("IRList", [constant("IRScalar")]),
        ],
        root_guard(Expr::bvar(3), Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)),
    )
}

fn closed_halted_function() -> Expr {
    close_root_function(
        [
            Expr::type_(),
            app("IRByteWorldV1", [Expr::bvar(0)]),
            app("IRList", [constant("IRScalar")]),
        ],
        root_halted(Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)),
    )
}

fn closed_signature_function() -> Expr {
    close_root_function(
        [
            Expr::type_(),
            constant("IRByteContextV1"),
            constant("IRFrame"),
            app("IRList", [constant("IRScalar")]),
            app("IRByteConfigV1", [Expr::bvar(3)]),
            app("IRByteConfigV1", [Expr::bvar(4)]),
            constant("IRByteSignatureV1"),
        ],
        choose(
            &app("IRByteConfigV1", [Expr::bvar(6)]),
            root_guard(Expr::bvar(5), Expr::bvar(4), Expr::bvar(0), Expr::bvar(3)),
            Expr::bvar(2),
            Expr::bvar(1),
        ),
    )
}

fn closed_binding_function() -> Expr {
    let signature = constant("IRByteSignatureV1");
    close_root_function(
        [
            Expr::type_(),
            constant("IRByteContextV1"),
            app("IRByteConfigV1", [Expr::bvar(1)]),
            Expr::pi(
                clean_kernel::BinderInfo::Default,
                signature.clone(),
                app("IRByteConfigV1", [Expr::bvar(3)]),
            ),
            constant("IRByteFunctionV1"),
        ],
        Expr::apps(
            Expr::const_(
                Name::from_string("IROption.rec"),
                vec![Level::succ(Level::zero())],
            ),
            [
                signature.clone(),
                Expr::lam(
                    clean_kernel::BinderInfo::Default,
                    app("IROption", [signature]),
                    app("IRByteConfigV1", [Expr::bvar(5)]),
                ),
                Expr::bvar(2),
                Expr::bvar(1),
                app(
                    "ir_byte_signature_v1",
                    [
                        Expr::bvar(3),
                        app("ir_byte_binding_sig_v1", [Expr::bvar(0)]),
                    ],
                ),
            ],
        ),
    )
}

impl FetchedSite {
    /// The actual returning signature must admit the resolved scalar list, and
    /// a root frame must have zero caller destinations. Unlike an internal
    /// return, the latter count is NOT compared with the number of Ret operands.
    pub fn root_return_admission(
        &self,
        model: &MachineModel,
        target: &CallTarget,
        frame: &RootReturnFrame,
        values: Expr,
    ) -> Result<Expr> {
        // Validate the fetched return IDs; the guard consumes resolved values.
        let _ = self.return_arguments(model, target)?;
        Ok(guard(model, frame, target.signature.clone(), values))
    }

    /// Bind the actual fetched Return operand IDs and pre-state to the existing
    /// empty-tail semantics. All supplied equalities are Pending candidates,
    /// including their proof terms; endpoint checks here do not certify them.
    pub fn return_from_root(
        &self,
        assembler: &mut Assembler<'_>,
        model: &MachineModel,
        target: &CallTarget,
        frame: &RootReturnFrame,
        resolved: PendingEquality,
        admitted: PendingEquality,
        before: PendingEquality,
    ) -> Result<RootReturnTransfer> {
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
        let actual_guard = |values| guard(model, frame, target.signature.clone(), values);
        admitted.endpoints(
            &constant("Bool"),
            &actual_guard(values.clone()),
            &constant("Bool.true"),
        )?;

        // Same paid slot as the old guard congruence local.
        let guard_function = Expr::apps(
            closed_guard_function(),
            [
                model.context.clone(),
                frame.returning.clone(),
                target.signature.clone(),
            ],
        );
        let mapped =
            assembler.congruence_function(resolved.clone(), constant("Bool"), guard_function)?;
        let guard_proof = assembler.convert_endpoints(
            mapped,
            actual_guard(actual_values.clone()),
            admitted.left.clone(),
        )?;
        let guard_proof = assembler.compose(guard_proof, admitted)?;

        let fetched = self.step(assembler, model, &current, before)?;
        let returned = app(
            "ir_byte_return_v1",
            [
                model.world_type.clone(),
                model.context.clone(),
                current.machine(),
                current.world.clone(),
                arguments,
            ],
        );
        let dispatch =
            assembler.conversion(model.config_type(), fetched.right.clone(), returned.clone())?;
        let expected = frame.halted(model, actual_values.clone());
        let failure = |outcome| {
            app(
                "IRByteConfigV1.halted",
                [model.world_type.clone(), outcome, current.world.clone()],
            )
        };
        let no_function = failure(app("IROutcome.stuck", [constant("IRFault.no_func")]));
        let not_function = failure(app("IROutcome.type_error", [constant("IRFault.not_fnptr")]));
        let bad_field = failure(app("IROutcome.type_error", [constant("IRFault.bad_field")]));
        let success = app(
            "ir_byte_lift_v1",
            [
                model.world_type.clone(),
                app(
                    "ir_byte_pop_owner_v1",
                    [model.world_type.clone(), current.world.clone()],
                ),
                app("ir_ret_vals", [current.machine(), actual_values.clone()]),
            ],
        );

        // Assemble the existing checked case rules, not a new semantic lemma.
        // The final refl reduces ONLY the singleton pop/ret/lift constructors;
        // signature and function lookup remain exact catalog equations.
        let admitted_case = app(
            "ir_byte_case_true_v1",
            [
                model.config_type(),
                actual_guard(actual_values.clone()),
                bad_field.clone(),
                success.clone(),
                expected.clone(),
                guard_proof.term,
                refl(&model.config_type(), expected.clone()),
            ],
        );
        // Preserve the old signature-local charge at the SAME construction
        // stage. The actual success/failure worlds stay outside every binder.
        assembler.charge()?;
        let signature_branch = Expr::apps(
            closed_signature_function(),
            [
                model.world_type.clone(),
                model.context.clone(),
                frame.returning.clone(),
                actual_values.clone(),
                success,
                bad_field,
            ],
        );
        let signature_lookup = |binding| {
            app(
                "ir_byte_signature_v1",
                [
                    model.context.clone(),
                    app("ir_byte_binding_sig_v1", [binding]),
                ],
            )
        };
        let signature_case = app(
            "ir_byte_case_some_v1",
            [
                constant("IRByteSignatureV1"),
                model.config_type(),
                signature_lookup(target.binding.clone()),
                target.signature.clone(),
                not_function.clone(),
                signature_branch.clone(),
                expected.clone(),
                target.signature_found(),
                admitted_case,
            ],
        );
        // Same paid slot as the old binding local; no fresh Scope or refund.
        assembler.charge()?;
        let binding_branch = Expr::apps(
            closed_binding_function(),
            [
                model.world_type.clone(),
                model.context.clone(),
                not_function,
                signature_branch,
            ],
        );
        let rule = PendingEquality::candidate(
            model.config_type(),
            returned,
            expected.clone(),
            app(
                "ir_byte_case_some_v1",
                [
                    constant("IRByteFunctionV1"),
                    model.config_type(),
                    app(
                        "ir_byte_function_v1",
                        [
                            model.context.clone(),
                            app("ir_frame_func", [frame.returning.clone()]),
                        ],
                    ),
                    target.binding.clone(),
                    no_function,
                    binding_branch,
                    expected.clone(),
                    target.binding_found(),
                    signature_case,
                ],
            ),
        );
        // The existing retirement function remains the only memory transform.
        // This last mapper's charge replaces precisely the old paid local.
        let halted_function = Expr::apps(
            closed_halted_function(),
            [model.world_type.clone(), frame.retired_world(model)],
        );
        let result =
            assembler.congruence_function(resolved, model.config_type(), halted_function)?;
        let halted = frame.halted(model, values.clone());
        let result = assembler.convert_endpoints(result, expected, halted.clone())?;
        let step = assembler.compose(fetched, dispatch)?;
        let step = assembler.compose(step, rule)?;
        let step = assembler.compose(step, result)?;
        let run = assembler.one_step(model, current.running(model), step)?;
        Ok(RootReturnTransfer {
            run,
            values,
            memory: frame.retired_memory(),
            world: frame.retired_world(model),
            halted,
        })
    }
}

#[cfg(test)]
#[path = "core_execution_root_return_tests.rs"]
mod tests;
