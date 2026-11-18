// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Candidate transfer through an actual imported Call returning normally.
//!
//! A pointwise equation supplies the provider's actual returned memory/host and
//! result list. It is not an assumed final configuration or callee-body proof.
//! Public byte laws check the input ABI, returned lanes and allocation owners;
//! these candidates gain authority only through independent whole-claim replay.

use super::*;

/// Explicit ordinary provider return. A C aggregate is one element of `values`,
/// not a separate result per field. Memory and host may differ from their inputs.
/// Administrative provider faults are not normal returns and are not covered by
/// this adapter; a language error encoded in typed return values may be.
#[derive(Clone)]
pub struct ImportResult {
    pub values: Expr,
    pub memory: Expr,
    pub host: Expr,
}

impl ImportResult {
    pub fn provider_result(&self, model: &MachineModel) -> Expr {
        app(
            "IRByteImportResultV1.mk",
            [
                model.world_type().clone(),
                app("IROutcome.ret", [self.values.clone()]),
                self.memory.clone(),
                self.host.clone(),
            ],
        )
    }

    fn world(&self, model: &MachineModel, current: &Current) -> Expr {
        app(
            "IRByteWorldV1.mk",
            [
                model.world_type().clone(),
                self.memory.clone(),
                self.host.clone(),
                app(
                    "ir_byte_world_owners_v1",
                    [model.world_type().clone(), current.world.clone()],
                ),
                app(
                    "ir_byte_world_next_v1",
                    [model.world_type().clone(), current.world.clone()],
                ),
            ],
        )
    }
}

/// The actual import/result checks, exposed as expressions rather than truth.
pub struct ImportChecks {
    pub imported: Expr,
    pub memory_owners: Expr,
    pub arity: Expr,
    pub typed: Expr,
}

/// Untrusted proof candidates with exact, checked-by-the-assembler endpoints.
/// Final kernel replay still checks their terms and all scope dependencies.
#[derive(Clone)]
pub struct ImportPremises {
    /// `ir_resolve current.machine actual_call_operands = explicit_arguments`.
    pub resolved: PendingEquality,
    /// The actual catalog binding's import flag is true.
    pub imported: PendingEquality,
    /// `target.admission(model, site, explicit_arguments) = true`.
    pub admitted: PendingEquality,
    /// Actual provider invocation equals the explicit `ImportResult` constructor.
    pub provided: PendingEquality,
    pub memory_owners: PendingEquality,
    pub arity: PendingEquality,
    pub typed: PendingEquality,
    /// World validity before executing this fetched instruction.
    pub before: PendingEquality,
}

/// Coherent candidate results for exactly one fetched imported Call. The new
/// current frame advances once; no activation is pushed, popped or retired.
pub struct ImportTransfer {
    step: PendingEquality,
    run: ExactRun,
    current: Current,
    valid: PendingEquality,
}

impl ImportTransfer {
    /// The exact fetched-step candidate used to construct `run`, for callers
    /// already composing a step-indexed interval. No run/step conversion is
    /// assumed here: both accessors retain the same assembled transition.
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
}

impl FetchedSite {
    fn import_arguments(&self, model: &MachineModel, target: &CallTarget) -> Result<Expr> {
        require_same(&self.context, model.context(), "import fetched context")?;
        require_same(&target.context, model.context(), "import target context")?;
        if !matches!(self.instruction.get_app_fn().kind(), ExprKind::Const(name, _) if name == &Name::from_string("IRInst.call"))
        {
            return Err("import assembler requires an actual direct IRInst.call".into());
        }
        let fields = self.instruction.get_app_args();
        let [fid, arguments] = fields.as_slice() else {
            return Err("actual imported call has wrong constructor arity".into());
        };
        require_same(fid, &target.function_id, "actual imported call identity")?;
        Ok((*arguments).clone())
    }

    /// Exact pointwise provider invocation required at this actual Call site.
    /// This performs no provider evaluation and grants no import authority.
    pub fn import_provider_call(
        &self,
        model: &MachineModel,
        target: &CallTarget,
        current: &Current,
        arguments: Expr,
    ) -> Result<Expr> {
        let _arguments = self.import_arguments(model, target)?;
        Ok(Expr::apps(
            model.providers().clone(),
            [
                app("ir_byte_binding_fid_v1", [target.binding.clone()]),
                arguments,
                app(
                    "ir_byte_world_memory_v1",
                    [model.world_type().clone(), current.world.clone()],
                ),
                app(
                    "ir_byte_world_host_v1",
                    [model.world_type().clone(), current.world.clone()],
                ),
            ],
        ))
    }

    pub fn import_result_checks(
        &self,
        model: &MachineModel,
        target: &CallTarget,
        current: &Current,
        result: &ImportResult,
    ) -> Result<ImportChecks> {
        let _arguments = self.import_arguments(model, target)?;
        Ok(ImportChecks {
            imported: app("ir_byte_binding_import_v1", [target.binding.clone()]),
            memory_owners: app(
                "ir_byte_memory_owners_v1",
                [
                    result.memory.clone(),
                    app(
                        "ir_byte_world_owners_v1",
                        [model.world_type().clone(), current.world.clone()],
                    ),
                    app(
                        "ir_byte_world_next_v1",
                        [model.world_type().clone(), current.world.clone()],
                    ),
                ],
            ),
            arity: app(
                "ir_nat_eqb",
                [
                    app("ir_byte_length_v1", [constant("Nat"), self.results.clone()]),
                    app(
                        "ir_byte_length_v1",
                        [constant("IRScalar"), result.values.clone()],
                    ),
                ],
            ),
            typed: app(
                "ir_byte_values_match_v1",
                [
                    model.context().clone(),
                    app("ir_byte_signature_returns_v1", [target.signature.clone()]),
                    result.values.clone(),
                ],
            ),
        })
    }

    fn import_result_dispatch(
        &self,
        model: &MachineModel,
        target: &CallTarget,
        current: &Current,
        result: Expr,
    ) -> Expr {
        Expr::app(self.import_result_function(model, target, current), result)
    }

    // The actual primitive takes the provider result last. Its existing
    // partial application retains all source operands outside any new binder.
    fn import_result_function(
        &self,
        model: &MachineModel,
        target: &CallTarget,
        current: &Current,
    ) -> Expr {
        app(
            "ir_byte_import_result_v1",
            [
                model.world_type().clone(),
                model.context().clone(),
                current.machine(),
                current.world.clone(),
                self.results.clone(),
                app("ir_byte_signature_returns_v1", [target.signature.clone()]),
            ],
        )
    }

    fn map_import_provider_result(
        &self,
        assembler: &mut Assembler<'_>,
        model: &MachineModel,
        target: &CallTarget,
        current: &Current,
        provided: PendingEquality,
    ) -> Result<PendingEquality> {
        assembler.congruence_function(
            provided,
            model.config_type(),
            self.import_result_function(model, target, current),
        )
    }

    /// Compose real fetch/catalog dispatch, pointwise argument/provider facts,
    /// actual normal import return, and independently derived world validity.
    /// Neither `ImportResult` nor `ImportPremises` is a checked proof token.
    /// Opaque frame coordinates may need caller transport before fetched lookup
    /// equalities reduce; the adapter never treats missing lookup proofs as true.
    pub fn import_return(
        &self,
        assembler: &mut Assembler<'_>,
        model: &MachineModel,
        target: &CallTarget,
        current: &Current,
        result: &ImportResult,
        premises: ImportPremises,
    ) -> Result<ImportTransfer> {
        let shared_current = current.shared_machine();
        let current = &shared_current;
        assembler.charge()?;
        let operand_ids = self.import_arguments(model, target)?;
        let arguments = premises.resolved.right.clone();
        let actual_arguments = app("ir_resolve", [current.machine(), operand_ids]);
        premises.resolved.endpoints(
            &app("IRList", [constant("IRScalar")]),
            &actual_arguments,
            &arguments,
        )?;
        let provider = self.import_provider_call(model, target, current, arguments.clone())?;
        premises.provided.endpoints(
            &app("IRByteImportResultV1", [model.world_type().clone()]),
            &provider,
            &result.provider_result(model),
        )?;
        let checks = self.import_result_checks(model, target, current, result)?;
        for (proof, expression) in [
            (&premises.imported, &checks.imported),
            (
                &premises.admitted,
                &target.admission(model, self, arguments.clone()),
            ),
            (&premises.memory_owners, &checks.memory_owners),
            (&premises.arity, &checks.arity),
            (&premises.typed, &checks.typed),
            (&premises.before, &current.valid(model)),
        ] {
            proof.endpoints(&constant("Bool"), expression, &constant("Bool.true"))?;
        }

        let fetched = self.step(assembler, model, current, premises.before.clone())?;
        let direct = target.direct(assembler, model, current, self)?;
        let mapped_arguments =
            target.map_known_arguments(assembler, model, current, self, premises.resolved)?;
        let arguments_start = assembler.conversion(
            model.config_type(),
            direct.right.clone(),
            mapped_arguments.left.clone(),
        )?;
        let known = target.known(model, current, self, arguments.clone());
        let arguments_end = assembler.conversion(
            model.config_type(),
            mapped_arguments.right.clone(),
            known.clone(),
        )?;
        let imported = self.import_result_dispatch(model, target, current, provider);
        let import_rule = PendingEquality::candidate(
            model.config_type(),
            known,
            imported.clone(),
            app(
                "ir_byte_import_call_rule_v1",
                [
                    model.world_type().clone(),
                    model.context().clone(),
                    model.providers().clone(),
                    current.machine(),
                    current.world.clone(),
                    self.results.clone(),
                    self.site.clone(),
                    target.binding.clone(),
                    target.signature.clone(),
                    arguments,
                    premises.imported.term,
                    premises.admitted.term,
                ],
            ),
        );

        let mapped_provider =
            self.map_import_provider_result(assembler, model, target, current, premises.provided)?;
        let provider_start =
            assembler.conversion(model.config_type(), imported, mapped_provider.left.clone())?;
        let returned =
            self.import_result_dispatch(model, target, current, result.provider_result(model));
        let provider_end = assembler.conversion(
            model.config_type(),
            mapped_provider.right.clone(),
            returned.clone(),
        )?;
        let after = Current {
            frame: app(
                "ir_frame_advance",
                [app(
                    "ir_frame_set_many",
                    [
                        current.frame.clone(),
                        self.results.clone(),
                        result.values.clone(),
                    ],
                )],
            ),
            tail: current.tail.clone(),
            legacy_memory: current.legacy_memory.clone(),
            legacy_cursor: current.legacy_cursor.clone(),
            world: result.world(model, current),
        };
        let return_rule = PendingEquality::candidate(
            model.config_type(),
            returned,
            after.running(model),
            app(
                "ir_byte_import_return_rule_v1",
                [
                    model.world_type().clone(),
                    model.context().clone(),
                    current.frame.clone(),
                    current.tail.clone(),
                    current.legacy_memory.clone(),
                    current.legacy_cursor.clone(),
                    current.world.clone(),
                    self.results.clone(),
                    app("ir_byte_signature_returns_v1", [target.signature.clone()]),
                    result.values.clone(),
                    result.memory.clone(),
                    result.host.clone(),
                    premises.memory_owners.term.clone(),
                    premises.arity.term,
                    premises.typed.term,
                ],
            ),
        );
        let step = assembler.compose(fetched, direct)?;
        let step = assembler.compose(step, arguments_start)?;
        let step = assembler.compose(step, mapped_arguments)?;
        let step = assembler.compose(step, arguments_end)?;
        let step = assembler.compose(step, import_rule)?;
        let step = assembler.compose(step, provider_start)?;
        let step = assembler.compose(step, mapped_provider)?;
        let step = assembler.compose(step, provider_end)?;
        let step = assembler.compose(step, return_rule)?;
        let run = assembler.one_step(model, current.running(model), step.clone())?;
        let valid = PendingEquality::candidate(
            constant("Bool"),
            after.valid(model),
            constant("Bool.true"),
            app(
                "ir_byte_import_world_shape_v1",
                [
                    model.world_type().clone(),
                    current.world.clone(),
                    current.frame.clone(),
                    after.frame.clone(),
                    current.tail.clone(),
                    current.legacy_memory.clone(),
                    current.legacy_cursor.clone(),
                    result.memory.clone(),
                    result.host.clone(),
                    premises.before.term,
                    premises.memory_owners.term,
                ],
            ),
        );
        Ok(ImportTransfer {
            step,
            run,
            current: after,
            valid,
        })
    }
}

#[cfg(test)]
#[path = "core_execution_import_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "core_execution_import_mapper_tests.rs"]
mod mapper_tests;

#[cfg(test)]
#[path = "core_execution_call_arguments_mapper_tests.rs"]
mod argument_mapper_tests;
