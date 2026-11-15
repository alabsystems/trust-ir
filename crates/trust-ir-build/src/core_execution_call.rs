// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Actual fetched local-call entry, never an assumed callee answer. These
//! candidates push the real parameter bindings and owner, advance the caller
//! once, and derive validity of that entered state. Body/summary execution and
//! all provider/source relations remain separate consuming obligations.

use super::*;

/// Independently discovered actual body and its nominal catalog identity.
#[derive(Clone)]
pub struct InternalTarget {
    target: CallTarget,
    function: Expr,
}

pub struct InternalCallChecks {
    /// Must equal false, not true: an imported function has no local body.
    pub local_binding: Expr,
    pub arity: Expr,
    pub admitted: Expr,
}

#[derive(Clone)]
pub struct InternalCallPremises {
    /// Exact `CallTarget::direct` or `CallTarget::indirect` dispatch candidate.
    pub dispatch: PendingEquality,
    /// Pointwise resolution of this instruction's actual argument IDs.
    pub resolved: PendingEquality,
    pub local_binding: PendingEquality,
    pub arity: PendingEquality,
    pub admitted: PendingEquality,
    pub before: PendingEquality,
}

/// Coherent untrusted outputs of one fetched call, with arbitrary lane counts.
/// The return boundary is the START of the callee: a later return must use its
/// actually reached frame/memory/host, not silently reuse these entry values.
pub struct InternalCallTransfer {
    step: PendingEquality,
    run: ExactRun,
    current: Current,
    valid: PendingEquality,
    return_frame: ReturnFrame,
}

impl InternalCallTransfer {
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
    pub fn return_frame(&self) -> &ReturnFrame {
        &self.return_frame
    }
}

impl Catalog<'_, '_> {
    /// Shares the actual function cache with fetch/initialization. This does not
    /// inherit initialization's no-globals restriction or assert any call guard.
    pub fn internal_target(&mut self, fid: FuncId) -> Result<InternalTarget> {
        Ok(InternalTarget {
            target: self.call_target(fid)?,
            function: self.function(fid)?,
        })
    }
}

impl InternalTarget {
    pub fn call_target(&self) -> &CallTarget {
        &self.target
    }

    pub fn checks(
        &self,
        model: &MachineModel,
        site: &FetchedSite,
        values: Expr,
    ) -> Result<InternalCallChecks> {
        let _arguments = site.internal_arguments(model, self)?;
        Ok(InternalCallChecks {
            local_binding: app("ir_byte_binding_import_v1", [self.target.binding.clone()]),
            arity: app(
                "ir_nat_eqb",
                [
                    app(
                        "ir_byte_length_v1",
                        [
                            constant("Nat"),
                            app("ir_func_params", [self.function.clone()]),
                        ],
                    ),
                    app("ir_byte_length_v1", [constant("IRScalar"), values.clone()]),
                ],
            ),
            admitted: self.target.admission(model, site, values),
        })
    }
}

fn world_fields(model: &MachineModel, world: Expr) -> [Expr; 4] {
    world_fields_at(&model.world_type, world)
}

fn world_fields_at(world_type: &Expr, world: Expr) -> [Expr; 4] {
    ["memory", "host", "owners", "next"].map(|field| {
        app(
            &format!("ir_byte_world_{field}_v1"),
            [world_type.clone(), world.clone()],
        )
    })
}

fn world_constructor(model: &MachineModel, fields: [Expr; 4]) -> Expr {
    world_constructor_at(&model.world_type, fields)
}

fn world_constructor_at(world_type: &Expr, fields: [Expr; 4]) -> Expr {
    app(
        "IRByteWorldV1.mk",
        std::iter::once(world_type.clone()).chain(fields),
    )
}

// Keep the actual host type and pushed configuration outside every binder.
// Under U / config / world: U=#2, config=#1, world=#0; the world domain
// beneath U / config uses U=#1. This is a typed candidate, not call authority.
fn push_world_mapper(world_type: &Expr, pushed: Expr) -> Expr {
    let closed = [
        Expr::type_(),
        constant("IRConfig"),
        app("IRByteWorldV1", [Expr::bvar(1)]),
    ]
    .into_iter()
    .rev()
    .fold(
        app(
            "ir_byte_lift_v1",
            [
                Expr::bvar(2),
                app("ir_byte_push_owner_v1", [Expr::bvar(2), Expr::bvar(0)]),
                Expr::bvar(1),
            ],
        ),
        |body, ty| Expr::lam(clean_kernel::BinderInfo::Default, ty, body),
    );
    Expr::apps(closed, [world_type.clone(), pushed])
}

/// Select only a directly spelled world constructor at the actual host type.
/// Inspect a fixed number of borrowed application links: no argument-vector
/// clone, normalization or typing/validity judgment is performed here.
pub(super) fn is_explicit_world(model: &MachineModel, world: &Expr) -> bool {
    let mut first_application = world;
    for _ in 0..4 {
        let ExprKind::App(function, _) = first_application.kind() else {
            return false;
        };
        first_application = function;
    }
    let ExprKind::App(constructor, world_type) = first_application.kind() else {
        return false;
    };
    matches!(constructor.kind(), ExprKind::Const(name, levels)
        if name == &Name::from_string("IRByteWorldV1.mk") && levels.is_empty())
        && world_type.as_ref() == &model.world_type
}

/// Constructor reconstruction by checked conversion for an explicit world,
/// or induction through the actual public recursor for an opaque world. This
/// is a term candidate, not a new declaration or a definitional-eta assumption.
pub(super) fn world_eta(
    assembler: &mut Assembler<'_>,
    model: &MachineModel,
    world: Expr,
) -> Result<PendingEquality> {
    assembler.charge()?;
    let ty = app("IRByteWorldV1", [model.world_type.clone()]);
    let rebuilt = world_constructor(model, world_fields(model, world.clone()));
    if is_explicit_world(model, &world) {
        // Projections of the actual constructor reduce to its own fields.
        // Preserve the same endpoints and application charge, but do not
        // construct a recursor factory that this conversion does not use.
        // The consumer must still kernel-check the complete equality.
        let proof = refl(&ty, rebuilt.clone());
        return Ok(PendingEquality::candidate(ty, world, rebuilt, proof));
    }
    let helper = world_eta_helper(assembler)?;
    let proof = Expr::apps(helper, [model.world_type.clone(), world.clone()]);
    Ok(PendingEquality::candidate(ty, world, rebuilt, proof))
}

/// Cache only the closed inductive theorem candidate. Its type and actual
/// world are parameters, never values captured from a consuming call. A hit
/// therefore allocates no locals, while every application still charges the
/// ordinary operation budget. Kernel replay remains the consumer's authority.
fn world_eta_helper(assembler: &mut Assembler<'_>) -> Result<Expr> {
    if let Some(candidate) = &assembler.world_eta_candidate {
        return Ok(candidate.clone());
    }
    let world_type = assembler.local(Expr::type_())?;
    let ty = app("IRByteWorldV1", [world_type.term().clone()]);
    let w = assembler.local(ty.clone())?;
    // The recursor motive is nested beneath the actual-world parameter.
    // Distinct named locals prevent rebinding that parameter in one scope.
    let motive_world = assembler.local(ty.clone())?;
    let memory = assembler.local(constant("IRByteMemoryV1"))?;
    let host = assembler.local(world_type.term().clone())?;
    let owners = assembler.local(app("IRList", [constant("Nat")]))?;
    let next = assembler.local(constant("Nat"))?;
    let explicit = world_constructor_at(
        world_type.term(),
        [
            memory.term().clone(),
            host.term().clone(),
            owners.term().clone(),
            next.term().clone(),
        ],
    );
    let motive = motive_world.lam(eq(
        &ty,
        motive_world.term().clone(),
        world_constructor_at(
            world_type.term(),
            world_fields_at(world_type.term(), motive_world.term().clone()),
        ),
    ));
    let minor = memory.lam(host.lam(owners.lam(next.lam(refl(&ty, explicit)))));
    let proof = Expr::apps(
        Expr::const_(Name::from_string("IRByteWorldV1.rec"), vec![Level::zero()]),
        [world_type.term().clone(), motive, minor, w.term().clone()],
    );
    let template = world_type.lam(w.lam(proof));
    let closed = assembler
        .scope
        .close(&template)
        .map_err(|error| error.to_string())?;
    assembler.world_eta_candidate = Some(closed.clone());
    Ok(closed)
}

impl FetchedSite {
    fn internal_arguments(&self, model: &MachineModel, target: &InternalTarget) -> Result<Expr> {
        require_same(&self.context, &model.context, "internal fetched context")?;
        require_same(
            &target.target.context,
            &model.context,
            "internal target context",
        )?;
        let fields = self.instruction.get_app_args();
        match self.instruction.get_app_fn().kind() {
            ExprKind::Const(name, _) if name == &Name::from_string("IRInst.call") => {
                let [fid, args] = fields.as_slice() else {
                    return Err("actual direct call constructor arity".into());
                };
                require_same(
                    fid,
                    &target.target.function_id,
                    "actual internal direct identity",
                )?;
                Ok((*args).clone())
            }
            ExprKind::Const(name, _) if name == &Name::from_string("IRInst.callindirect") => {
                let [_, _, args, _] = fields.as_slice() else {
                    return Err("actual indirect call constructor arity".into());
                };
                Ok((*args).clone())
            }
            _ => Err("internal entry requires actual Call or CallIndirect".into()),
        }
    }

    /// Compose existing catalog dispatch, local-call, fetched-step and push
    /// laws. No memory/host equality follows from world validity: the actual
    /// call push itself retains both. Owner freshness follows the existing
    /// world-owner predicate; native activation/relocation remains out of scope.
    pub fn call_internal(
        &self,
        assembler: &mut Assembler<'_>,
        model: &MachineModel,
        target: &InternalTarget,
        current: &Current,
        premises: InternalCallPremises,
    ) -> Result<InternalCallTransfer> {
        assembler.charge()?;
        let arguments = self.internal_arguments(model, target)?;
        let values = premises.resolved.right.clone();
        premises.resolved.endpoints(
            &app("IRList", [constant("IRScalar")]),
            &app("ir_resolve", [current.machine(), arguments]),
            &values,
        )?;
        premises.before.endpoints(
            &constant("Bool"),
            &current.valid(model),
            &constant("Bool.true"),
        )?;
        let body_lookup = PendingEquality::candidate(
            app("IROption", [constant("IRFunc")]),
            app(
                "ir_func_find",
                [
                    app(
                        "ir_mod_funcs",
                        [app("ir_byte_context_module_v1", [model.context.clone()])],
                    ),
                    app("ir_byte_binding_fid_v1", [target.target.binding.clone()]),
                ],
            ),
            some("IRFunc", target.function.clone()),
            refl(
                &app("IROption", [constant("IRFunc")]),
                some("IRFunc", target.function.clone()),
            ),
        );
        let fetched = self.step(assembler, model, current, premises.before.clone())?;
        let entered = target.target.enter_internal(
            assembler,
            model,
            current,
            self,
            premises.dispatch,
            premises.resolved,
            target.function.clone(),
            body_lookup,
            premises.local_binding,
            premises.arity,
            premises.admitted,
        )?;
        let [memory, host, owners, next] = world_fields(model, current.world.clone());
        let return_frame = ReturnFrame {
            returning: app(
                "IRFrame.mk",
                [
                    app("ir_func_id", [target.function.clone()]),
                    app("ir_func_entry", [target.function.clone()]),
                    nat(0),
                    app(
                        "ir_bind_params",
                        [
                            app("ir_func_params", [target.function.clone()]),
                            values.clone(),
                            list("IRBinding", &[]),
                        ],
                    ),
                    self.results.clone(),
                ],
            ),
            caller: app("ir_frame_advance", [current.frame.clone()]),
            tail: current.tail.clone(),
            legacy_memory: current.legacy_memory.clone(),
            legacy_cursor: current.legacy_cursor.clone(),
            memory: memory.clone(),
            host: host.clone(),
            owner: next.clone(),
            owners: owners.clone(),
            next: app("Nat.succ", [next.clone()]),
        };
        let after = return_frame.current(model);
        let eta = world_eta(assembler, model, current.world.clone())?;
        let pushed_machine = app(
            "ir_push",
            [
                current.machine(),
                self.results.clone(),
                target.function.clone(),
                values.clone(),
            ],
        );
        let push_world = assembler.congruence_function(
            eta.clone(),
            model.config_type(),
            push_world_mapper(&model.world_type, pushed_machine),
        )?;
        let start = assembler.conversion(
            model.config_type(),
            entered.right.clone(),
            push_world.left.clone(),
        )?;
        let pushed = PendingEquality::candidate(
            model.config_type(),
            push_world.right.clone(),
            after.running(model),
            app(
                "ir_byte_push_frame_v1",
                [
                    model.world_type.clone(),
                    memory.clone(),
                    host.clone(),
                    owners.clone(),
                    next.clone(),
                    current.frame.clone(),
                    current.tail.clone(),
                    current.legacy_memory.clone(),
                    current.legacy_cursor.clone(),
                    self.results.clone(),
                    target.function.clone(),
                    values,
                ],
            ),
        );
        let step = assembler.compose(fetched, entered)?;
        let step = assembler.compose(step, start)?;
        let step = assembler.compose(step, push_world)?;
        let step = assembler.compose(step, pushed)?;
        let run = assembler.one_step(model, current.running(model), step.clone())?;

        let normalized = Current {
            world: eta.right.clone(),
            ..current.clone()
        };
        // The actual validity primitive takes world last, so use its existing
        // curried application instead of recapturing Current under a binder.
        let before_map = assembler.congruence_function(
            eta,
            constant("Bool"),
            app(
                "ir_byte_world_valid_v1",
                [model.world_type.clone(), current.machine()],
            ),
        )?;
        let mapped_start = assembler.conversion(
            constant("Bool"),
            current.valid(model),
            before_map.left.clone(),
        )?;
        let mapped_end = assembler.conversion(
            constant("Bool"),
            before_map.right.clone(),
            normalized.valid(model),
        )?;
        let mapped = assembler.compose(mapped_start, before_map)?;
        let mapped = assembler.compose(mapped, mapped_end)?;
        let reversed = PendingEquality::candidate(
            constant("Bool"),
            mapped.right.clone(),
            mapped.left.clone(),
            Expr::apps(
                Expr::const_(
                    Name::from_string("Eq.symm"),
                    vec![Level::succ(Level::zero())],
                ),
                [constant("Bool"), mapped.left, mapped.right, mapped.term],
            ),
        );
        let normalized_before = assembler.compose(reversed, premises.before)?;
        let valid = PendingEquality::candidate(
            constant("Bool"),
            after.valid(model),
            constant("Bool.true"),
            app(
                "ir_byte_world_push_shape_v1",
                [
                    model.world_type.clone(),
                    memory,
                    host,
                    return_frame.returning.clone(),
                    owners,
                    next,
                    current.frame.clone(),
                    return_frame.caller.clone(),
                    current.tail.clone(),
                    current.legacy_memory.clone(),
                    current.legacy_cursor.clone(),
                    normalized_before.term,
                ],
            ),
        );
        Ok(InternalCallTransfer {
            step,
            run,
            current: after,
            valid,
            return_frame,
        })
    }
}

#[cfg(test)]
#[path = "core_execution_call_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "core_execution_world_eta_tests.rs"]
mod world_eta_tests;

#[cfg(test)]
#[path = "core_execution_call_world_mapper_tests.rs"]
mod world_mapper_tests;
