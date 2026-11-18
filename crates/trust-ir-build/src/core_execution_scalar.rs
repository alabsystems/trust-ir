// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Candidate transfers for the actual byte profile's scalar and branch paths.
//!
//! These adapters install no vocabulary and certify no instruction. They expose
//! the existing evaluator's checks, compose supplied pointwise facts, and retain
//! the exact fetched instruction in a one-step candidate. Independent replay of
//! the consumer's whole claim remains mandatory. In particular module validation
//! supplies static branch typing; the byte jump itself checks only target arity.

use super::*;

/// Exact evaluator expressions, not facts inferred from an instruction's type.
pub struct ScalarChecks {
    pub evaluation: Expr,
    /// Real BinOp/ICmp/Select carrier checks; `Bool.true` for Const/ExtractField
    /// and Cast/Copy/pointer parts (whose byte evaluators check their carriers).
    pub operands: Expr,
    /// Actual destination arity AND actual site-result lane matching.
    pub result: Expr,
}

#[derive(Clone)]
pub struct ScalarPremises {
    /// The actual pure evaluator returns `IRStepResult.value value`.
    pub evaluated: PendingEquality,
    pub operands: PendingEquality,
    pub result: PendingEquality,
    pub before: PendingEquality,
}

/// One fetched scalar instruction, with once-only binding/advance and the
/// unchanged byte world. Validity is derived for this new frame, not assumed.
pub struct ScalarTransfer {
    step: PendingEquality,
    run: ExactRun,
    current: Current,
    valid: PendingEquality,
}

impl ScalarTransfer {
    /// The same actual step equation composed into `run`, for existing segment
    /// builders that already own their checked run-one composition.
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

fn replace_frame(current: &Current, frame: Expr) -> Current {
    Current {
        frame,
        ..current.clone()
    }
}

fn bad_field(model: &MachineModel, current: &Current) -> Expr {
    app(
        "IRByteConfigV1.halted",
        [
            model.world_type().clone(),
            app("IROutcome.type_error", [constant("IRFault.bad_field")]),
            current.world.clone(),
        ],
    )
}

/// Present congruence's beta-redex endpoints as the exact consumer expressions.
/// Conversion reuses the pending term; only whole-claim replay checks it.
fn mapped(
    assembler: &mut Assembler<'_>,
    equality: PendingEquality,
    ty: Expr,
    map: impl Fn(Expr) -> Expr,
) -> Result<PendingEquality> {
    let left = map(equality.left.clone());
    let right = map(equality.right.clone());
    let proof = assembler.congruence(equality, ty, map)?;
    assembler.convert_endpoints(proof, left, right)
}

fn unchanged_world_valid(
    assembler: &mut Assembler<'_>,
    model: &MachineModel,
    old: &Current,
    new: &Current,
    before: PendingEquality,
) -> Result<PendingEquality> {
    before.endpoints(&constant("Bool"), &old.valid(model), &constant("Bool.true"))?;
    // World validity observes frame COUNT, not a frame's PC/bindings. Both
    // machines have one explicit head and the identical tail/legacy/world.
    assembler.convert_endpoints(before, new.valid(model), constant("Bool.true"))
}

impl FetchedSite {
    pub fn scalar_checks(
        &self,
        model: &MachineModel,
        current: &Current,
        value: Expr,
    ) -> Result<ScalarChecks> {
        let shared_current = current.shared_machine();
        let current = &shared_current;
        require_same(&self.context, model.context(), "scalar fetched context")?;
        let fields = self.instruction.get_app_args();
        let ExprKind::Const(name, _) = self.instruction.get_app_fn().kind() else {
            return Err("scalar assembler requires an actual instruction constructor".into());
        };
        let read = |id: &Expr| app("ir_getd", [current.machine(), id.clone()]);
        let fit = |ty: &Expr, id: &Expr| {
            app(
                "ir_byte_value_matches_v1",
                [model.context().clone(), ty.clone(), read(id)],
            )
        };
        let (evaluation, operands) = match (name.to_string().as_str(), fields.as_slice()) {
            ("IRInst.const_", [ty, c]) => (
                // Byte constants admit the distinct target-indexed Usize64
                // carrier; the legacy constant evaluator deliberately does not.
                app("ir_byte_const_eval_v1", [(*ty).clone(), (*c).clone()]),
                constant("Bool.true"),
            ),
            ("IRInst.extractfield", [ty, source, field]) => (
                // The actual ByteV1 dispatcher's nominal field evaluator over
                // the fetched site's operand catalog (Clean `ee4dff170`), not
                // the untyped `ir_ef_at`: it checks the aggregate's admission,
                // the lane's nominal type and the result lane itself.
                app(
                    "ir_byte_extract_field_v1",
                    [
                        model.context().clone(),
                        self.site.clone(),
                        (*ty).clone(),
                        (*source).clone(),
                        read(source),
                        (*field).clone(),
                    ],
                ),
                constant("Bool.true"),
            ),
            ("IRInst.copy", [ty, operand]) => (
                app(
                    "ir_byte_copy_eval_v1",
                    [model.context().clone(), (*ty).clone(), read(operand)],
                ),
                // The byte evaluator checks the complete canonical carrier;
                // the legacy cell model's shape-only Copy is not authoritative.
                constant("Bool.true"),
            ),
            ("IRInst.ptrdata", [ty, operand]) => (
                app(
                    "ir_byte_ptrdata_eval_v1",
                    [model.context().clone(), (*ty).clone(), read(operand)],
                ),
                constant("Bool.true"),
            ),
            ("IRInst.ptrmetadata", [ty, metadata_ty, operand]) => (
                app(
                    "ir_byte_ptrmetadata_eval_v1",
                    [
                        model.context().clone(),
                        (*ty).clone(),
                        (*metadata_ty).clone(),
                        read(operand),
                    ],
                ),
                constant("Bool.true"),
            ),
            ("IRInst.ptrfromparts", [ty, metadata_ty, data, metadata]) => (
                app(
                    "ir_byte_ptrfromparts_eval_v1",
                    [
                        model.context().clone(),
                        (*ty).clone(),
                        (*metadata_ty).clone(),
                        read(data),
                        read(metadata),
                    ],
                ),
                // The Byte evaluator, unlike legacy pointer assembly, checks
                // the exact metadata sort and never turns a function ID into
                // an address. Fetched destination/site checks remain below.
                constant("Bool.true"),
            ),
            ("IRInst.cast", [op, src, dst, operand]) => (
                app(
                    "ir_byte_cast_eval_v1",
                    [
                        model.context().clone(),
                        (*op).clone(),
                        (*src).clone(),
                        (*dst).clone(),
                        read(operand),
                    ],
                ),
                // The byte dispatcher has no separate operand guard: this
                // evaluator checks its own supported profile and BOTH source
                // and destination carriers. Do not substitute legacy casts or
                // infer pointer/allocation authority from a declared type.
                constant("Bool.true"),
            ),
            ("IRInst.binop", [op, ty, a, b]) => (
                app(
                    "ir_binop_eval",
                    [(*op).clone(), (*ty).clone(), read(a), read(b)],
                ),
                app("Bool.and", [fit(ty, a), fit(ty, b)]),
            ),
            ("IRInst.icmp", [op, ty, a, b]) => (
                app(
                    // Match the actual ByteV1 dispatcher: nominal Usize64/Ugt
                    // is distinct from U64, and other cases retain its refusals.
                    "ir_byte_icmp_eval_v1",
                    [(*op).clone(), (*ty).clone(), read(a), read(b)],
                ),
                app("Bool.and", [fit(ty, a), fit(ty, b)]),
            ),
            ("IRInst.select", [ty, condition, a, b]) => (
                app("ir_select_eval", [read(condition), read(a), read(b)]),
                app("Bool.and", [fit(ty, a), fit(ty, b)]),
            ),
            _ => {
                return Err(
                    "scalar assembler supports only actual Const/ExtractField/Cast/Copy/pointer parts/BinOp/ICmp/Select"
                        .into(),
                );
            }
        };
        let values = list("IRScalar", &[value]);
        Ok(ScalarChecks {
            evaluation,
            operands,
            result: value_binding::result_guard(self, model, values),
        })
    }

    pub fn scalar_value(
        &self,
        assembler: &mut Assembler<'_>,
        model: &MachineModel,
        current: &Current,
        value: Expr,
        premises: ScalarPremises,
    ) -> Result<ScalarTransfer> {
        let shared_current = current.shared_machine();
        let current = &shared_current;
        assembler.charge()?;
        let checks = self.scalar_checks(model, current, value.clone())?;
        premises.evaluated.endpoints(
            &constant("IRStepResult"),
            &checks.evaluation,
            &app("IRStepResult.value", [value.clone()]),
        )?;
        premises
            .operands
            .endpoints(&constant("Bool"), &checks.operands, &constant("Bool.true"))?;
        premises
            .result
            .endpoints(&constant("Bool"), &checks.result, &constant("Bool.true"))?;
        let values = list("IRScalar", &[value]);
        let next = replace_frame(
            current,
            app(
                "ir_frame_advance",
                [app(
                    "ir_frame_set_many",
                    [current.frame.clone(), self.results.clone(), values.clone()],
                )],
            ),
        );
        let bound = app(
            "ir_byte_bind_values_v1",
            [
                model.world_type().clone(),
                model.context().clone(),
                current.machine(),
                current.world.clone(),
                self.results.clone(),
                app("ir_byte_site_results_v1", [self.site.clone()]),
                values,
            ],
        );
        // The real evaluator result is the final curried argument. Lift its
        // equality directly, without capturing this whole current under a
        // fresh scoped-local lambda for every successive instruction.
        let scalar_result = app(
            "ir_byte_scalar_result_v1",
            [
                model.world_type().clone(),
                model.context().clone(),
                current.machine(),
                current.world.clone(),
                self.results.clone(),
                app("ir_byte_site_results_v1", [self.site.clone()]),
            ],
        );
        let evaluated = assembler.congruence_function(
            premises.evaluated,
            model.config_type(),
            scalar_result,
        )?;
        let evaluated_left = evaluated.left.clone();
        let evaluated = assembler.convert_endpoints(evaluated, evaluated_left, bound.clone())?;
        let fetched = self.step(assembler, model, current, premises.before.clone())?;
        let guarded = choose(
            &model.config_type(),
            checks.operands.clone(),
            evaluated.left.clone(),
            bad_field(model, current),
        );
        let fetched_left = fetched.left.clone();
        let fetched = assembler.convert_endpoints(fetched, fetched_left, guarded.clone())?;
        let selected = PendingEquality::candidate(
            model.config_type(),
            guarded,
            bound.clone(),
            app(
                "ir_byte_case_true_v1",
                [
                    model.config_type(),
                    checks.operands,
                    bad_field(model, current),
                    evaluated.left.clone(),
                    bound.clone(),
                    premises.operands.term,
                    evaluated.term,
                ],
            ),
        );
        let binding = PendingEquality::candidate(
            model.config_type(),
            bound,
            next.running(model),
            app(
                "ir_byte_case_true_v1",
                [
                    model.config_type(),
                    checks.result,
                    bad_field(model, current),
                    next.running(model),
                    next.running(model),
                    premises.result.term,
                    refl(&model.config_type(), next.running(model)),
                ],
            ),
        );
        let proof = assembler.compose(fetched, selected)?;
        let proof = assembler.compose(proof, binding)?;
        let run = assembler.one_step(model, current.running(model), proof.clone())?;
        let valid = unchanged_world_valid(assembler, model, current, &next, premises.before)?;
        Ok(ScalarTransfer {
            step: proof,
            run,
            current: next,
            valid,
        })
    }
}

/// Actual function-local branch destination discovered through the same catalog
/// as instruction fetch. Discovery is not a proof that the branch was taken.
#[derive(Clone)]
pub struct BranchTarget {
    context: Expr,
    function: FuncId,
    block_id: BlockId,
    block: Expr,
}

impl BranchTarget {
    pub fn function(&self) -> FuncId {
        self.function
    }
    pub fn block_id(&self) -> BlockId {
        self.block_id
    }
    pub fn parameters(&self) -> Expr {
        app("ir_block_params", [self.block.clone()])
    }

    /// Necessary syntactic recognition only. Opaque or malformed catalog
    /// candidates take the ordinary path; this never authenticates a lookup.
    fn has_explicit_empty_parameters(&self) -> bool {
        let ExprKind::App(with_parameters, _) = self.block.kind() else {
            return false;
        };
        let ExprKind::App(with_id, parameters) = with_parameters.kind() else {
            return false;
        };
        let ExprKind::App(head, _) = with_id.kind() else {
            return false;
        };
        matches!(head.kind(), ExprKind::Const(name, levels)
            if name == &Name::from_string("IRBlock.mk") && levels.is_empty())
            && parameters.as_ref() == &list("Nat", &[])
    }
}

/// Closed constant mapper: (W : Type) -> IRByteConfigV1 W ->
/// IRList IRScalar -> IRByteConfigV1 W. Apply actual operands outside every
/// binder, so arbitrary source locals/bvars cannot be captured.
fn empty_branch_mapper(world_type: Expr, reached: Expr) -> Expr {
    let closed = Expr::lam(
        clean_kernel::BinderInfo::Default,
        Expr::type_(),
        Expr::lam(
            clean_kernel::BinderInfo::Default,
            app("IRByteConfigV1", [Expr::bvar(0)]),
            Expr::lam(
                clean_kernel::BinderInfo::Default,
                app("IRList", [constant("IRScalar")]),
                Expr::bvar(1),
            ),
        ),
    );
    Expr::apps(closed, [world_type, reached])
}

fn branch_argument_transport(
    assembler: &mut Assembler<'_>,
    model: &MachineModel,
    target: &BranchTarget,
    equality: PendingEquality,
    map: impl Fn(Expr) -> Expr,
) -> Result<PendingEquality> {
    if !target.has_explicit_empty_parameters() {
        return mapped(assembler, equality, model.config_type(), map);
    }
    let left = map(equality.left.clone());
    let right = map(equality.right.clone());
    // ir_bind_params on the actual nil parameter list ignores values. Keep
    // the endpoint conversion; the kernel, not the recognizer, establishes
    // that this constant mapper is the real destination-frame transport.
    let function = empty_branch_mapper(model.world_type().clone(), map(list("IRScalar", &[])));
    let proof = assembler.congruence_function(equality, model.config_type(), function)?;
    assembler.convert_endpoints(proof, left, right)
}

impl Catalog<'_, '_> {
    pub fn branch_target(&mut self, function: FuncId, block_id: BlockId) -> Result<BranchTarget> {
        let body = self.function(function)?;
        let key = (function, block_id);
        let block = if let Some(block) = self.blocks.get(&key) {
            block.clone()
        } else {
            let block = self.found(
                "IRBlock",
                app(
                    "ir_block_find",
                    [
                        app("ir_func_blocks", [body]),
                        nat(u64::from(block_id.index())),
                    ],
                ),
            )?;
            self.blocks.insert(key, block.clone());
            block
        };
        Ok(BranchTarget {
            context: self.reflected.context_term().clone(),
            function,
            block_id,
            block,
        })
    }
}

pub struct BranchChecks {
    pub arguments: Expr,
    /// Actual `ir_getd` on CondBr's condition ID, absent for Br.
    pub condition: Option<Expr>,
    pub arity: Expr,
}

#[derive(Clone)]
pub struct BranchPremises {
    /// On CondBr, actual condition lookup equals `IRScalar.bool_ taken`.
    /// A scalar integer is not accepted in place of a Boolean carrier.
    pub condition: Option<PendingEquality>,
    /// Actual selected-arm `ir_resolve` equals the explicit block arguments.
    pub resolved: PendingEquality,
    pub arity: PendingEquality,
    pub before: PendingEquality,
}

pub struct BranchTransfer {
    step: PendingEquality,
    run: ExactRun,
    current: Current,
    valid: PendingEquality,
}

impl BranchTransfer {
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
    /// `None` selects Br; `Some(false/true)` selects that exact CondBr arm.
    /// This checks the selected nominal block but does not prove its condition.
    pub fn branch_checks(
        &self,
        model: &MachineModel,
        current: &Current,
        target: &BranchTarget,
        taken: Option<bool>,
    ) -> Result<BranchChecks> {
        require_same(&self.context, model.context(), "branch fetched context")?;
        require_same(&target.context, model.context(), "branch target context")?;
        if target.function != self.coordinate.function {
            return Err("branch destination belongs to a different function".into());
        }
        require_same(
            &self.results,
            &list("Nat", &[]),
            "branch result destinations",
        )?;
        let fields = self.instruction.get_app_args();
        let ExprKind::Const(name, _) = self.instruction.get_app_fn().kind() else {
            return Err("branch requires an actual instruction constructor".into());
        };
        let (block, arguments, condition) =
            match (name.to_string().as_str(), fields.as_slice(), taken) {
                ("IRInst.br", [block, args], None) => (*block, *args, None),
                ("IRInst.condbr", [condition, yes, yes_args, no, no_args], Some(taken)) => {
                    let (block, args) = if taken {
                        (*yes, *yes_args)
                    } else {
                        (*no, *no_args)
                    };
                    (
                        block,
                        args,
                        Some(app("ir_getd", [current.machine(), (*condition).clone()])),
                    )
                }
                _ => return Err("branch kind/arm does not match actual Br/CondBr".into()),
            };
        require_same(
            block,
            &nat(u64::from(target.block_id.index())),
            "actual selected branch target",
        )?;
        Ok(BranchChecks {
            arguments: arguments.clone(),
            condition,
            arity: app(
                "ir_nat_eqb",
                [
                    app("ir_byte_length_v1", [constant("Nat"), target.parameters()]),
                    app("ir_byte_length_v1", [constant("Nat"), arguments.clone()]),
                ],
            ),
        })
    }

    /// One actual branch, binding its target block parameters and resetting PC
    /// to zero. It never advances the old block or drops its binding history.
    /// Actual function/block lookups remain conversion obligations in the final
    /// replay; an opaque frame at a different coordinate cannot bypass them.
    pub fn branch_to(
        &self,
        assembler: &mut Assembler<'_>,
        model: &MachineModel,
        current: &Current,
        target: &BranchTarget,
        taken: Option<bool>,
        premises: BranchPremises,
    ) -> Result<BranchTransfer> {
        let shared_current = current.shared_machine();
        let current = &shared_current;
        assembler.charge()?;
        let checks = self.branch_checks(model, current, target, taken)?;
        let actual_values = app("ir_resolve", [current.machine(), checks.arguments.clone()]);
        let values = premises.resolved.right.clone();
        premises.resolved.endpoints(
            &app("IRList", [constant("IRScalar")]),
            &actual_values,
            &values,
        )?;
        premises
            .arity
            .endpoints(&constant("Bool"), &checks.arity, &constant("Bool.true"))?;
        let jump = app(
            "ir_byte_jump_v1",
            [
                model.world_type().clone(),
                model.context().clone(),
                current.machine(),
                current.world.clone(),
                nat(u64::from(target.block_id.index())),
                checks.arguments.clone(),
            ],
        );
        let fetched = self.step(assembler, model, current, premises.before.clone())?;
        let selected = match (checks.condition, premises.condition, taken) {
            (None, None, None) => {
                assembler.conversion(model.config_type(), fetched.right.clone(), jump.clone())?
            }
            (Some(condition), Some(proof), Some(taken)) => {
                let expected = app(
                    "IRScalar.bool_",
                    [constant(if taken { "Bool.true" } else { "Bool.false" })],
                );
                proof.endpoints(&constant("IRScalar"), &condition, &expected)?;
                // This is only the eliminator exposed by the ACTUAL CondBr
                // definition, not a new instruction semantics declaration.
                let expression = self.condition_eliminator(assembler, model, current)?;
                let selected =
                    assembler.congruence_function(proof, model.config_type(), expression)?;
                assembler.convert_endpoints(selected, fetched.right.clone(), jump.clone())?
            }
            _ => return Err("branch condition premise does not match Br/CondBr".into()),
        };
        let resumed = |values| {
            replace_frame(
                current,
                app(
                    "ir_frame_goto",
                    [
                        current.frame.clone(),
                        nat(u64::from(target.block_id.index())),
                        app(
                            "ir_bind_params",
                            [
                                target.parameters(),
                                values,
                                app("ir_frame_locals", [current.frame.clone()]),
                            ],
                        ),
                    ],
                ),
            )
        };
        let actual_reached = resumed(actual_values).running(model);
        let guarded = choose(
            &model.config_type(),
            checks.arity.clone(),
            actual_reached.clone(),
            bad_field(model, current),
        );
        // Refl checks the real ir_cur_func and function-local ir_block_find
        // against the catalog candidate. No lookup result is assumed as truth.
        let lookup = assembler.conversion(model.config_type(), jump, guarded.clone())?;
        let admitted = PendingEquality::candidate(
            model.config_type(),
            guarded,
            actual_reached.clone(),
            app(
                "ir_byte_case_true_v1",
                [
                    model.config_type(),
                    checks.arity,
                    bad_field(model, current),
                    actual_reached.clone(),
                    actual_reached,
                    premises.arity.term,
                    refl(
                        &model.config_type(),
                        resumed(premises.resolved.left.clone()).running(model),
                    ),
                ],
            ),
        );
        let bound =
            branch_argument_transport(assembler, model, target, premises.resolved, |values| {
                resumed(values).running(model)
            })?;
        let next = resumed(values);
        let step = assembler.compose(fetched, selected)?;
        let step = assembler.compose(step, lookup)?;
        let step = assembler.compose(step, admitted)?;
        let step = assembler.compose(step, bound)?;
        let run = assembler.one_step(model, current.running(model), step.clone())?;
        let valid = unchanged_world_valid(assembler, model, current, &next, premises.before)?;
        Ok(BranchTransfer {
            step,
            run,
            current: next,
            valid,
        })
    }

    fn condition_eliminator(
        &self,
        assembler: &mut Assembler<'_>,
        model: &MachineModel,
        current: &Current,
    ) -> Result<Expr> {
        let fields = self.instruction.get_app_args();
        let [_condition, yes, yes_args, no, no_args] = fields.as_slice() else {
            return Err("actual CondBr has wrong constructor arity".into());
        };
        let jump = |target: &Expr, arguments: &Expr| {
            app(
                "ir_byte_jump_v1",
                [
                    model.world_type().clone(),
                    model.context().clone(),
                    current.machine(),
                    current.world.clone(),
                    target.clone(),
                    arguments.clone(),
                ],
            )
        };
        let failure = app(
            "IRByteConfigV1.halted",
            [
                model.world_type().clone(),
                app("IROutcome.type_error", [constant("IRFault.not_bool")]),
                current.world.clone(),
            ],
        );
        assembler.charge()?;
        Ok(condition_mapper(
            model.world_type().clone(),
            jump(yes, yes_args),
            jump(no, no_args),
            failure,
        ))
    }
}

/// Closed implementation of the actual ByteV1 condition match:
/// `(W : Type) -> Config W -> Config W -> Config W -> IRScalar -> Config W`.
/// Apply the actual world type and complete arms outside every binder, keeping
/// arbitrary source locals and dependent bound variables out of the template.
fn condition_mapper(world_type: Expr, yes: Expr, no: Expr, failure: Expr) -> Expr {
    let lam = |ty, body| Expr::lam(clean_kernel::BinderInfo::Default, ty, body);
    let config = |world_index| app("IRByteConfigV1", [Expr::bvar(world_index)]);
    let scalar = constant("IRScalar");
    // At the match: scalar=0, failure=1, no=2, yes=3, W=4.
    let bool_case = lam(
        constant("Bool"),
        Expr::apps(
            Expr::const_(
                Name::from_string("Bool.rec"),
                vec![Level::succ(Level::zero())],
            ),
            [
                lam(constant("Bool"), config(6)),
                Expr::bvar(3),
                Expr::bvar(4),
                Expr::bvar(0),
            ],
        ),
    );
    let word_case = lam(constant("Nat"), Expr::bvar(2));
    // Recursive scalar fields have induction hypotheses, typed at the exact
    // constant Config-W motive. They never change the non-Boolean failure.
    let cases = Expr::apps(
        Expr::const_(
            Name::from_string("IRScalar.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [
            lam(scalar.clone(), config(5)),
            Expr::bvar(1),
            bool_case,
            word_case.clone(),
            word_case.clone(),
            Expr::bvar(1),
            word_case.clone(),
            Expr::bvar(1),
            lam(constant("Nat"), lam(constant("Nat"), Expr::bvar(3))),
            word_case,
            lam(scalar.clone(), lam(config(5), Expr::bvar(3))),
            Expr::bvar(1),
            lam(
                scalar.clone(),
                lam(
                    scalar.clone(),
                    lam(config(6), lam(config(7), Expr::bvar(5))),
                ),
            ),
            Expr::bvar(0),
        ],
    );
    let closed = lam(
        Expr::type_(),
        lam(
            config(0),
            lam(config(1), lam(config(2), lam(scalar, cases))),
        ),
    );
    Expr::apps(closed, [world_type, yes, no, failure])
}

#[cfg(test)]
#[path = "core_execution_condition_eliminator_tests.rs"]
mod condition_eliminator_tests;

#[cfg(test)]
#[path = "core_execution_empty_branch_mapper_tests.rs"]
mod empty_branch_mapper_tests;

#[cfg(test)]
#[path = "core_execution_scalar_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "core_execution_cast_tests.rs"]
mod cast_tests;
