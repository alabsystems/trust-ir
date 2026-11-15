// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Candidate transfers for successful actual byte Load/Store/GEP instructions
//! and the explicitly sequential Add/Relaxed/U64 and Usize64 projections.
//!
//! This module does not evaluate memory, install vocabulary or certify a proof.
//! It composes a pointwise equation for the fetched instruction's existing
//! evaluator with its real result guard. Allocation-list equality is a narrow
//! framing premise, not an assumed post-world invariant or byte-map equality.
//! The consumer must derive these candidates from the actual memory laws and
//! independently replay its complete claim. Allocation and fault transfers are
//! deliberately outside this adapter.

use super::*;

#[cfg(test)]
#[path = "core_execution_memory_world_mapper.rs"]
mod world_mapper;

#[path = "core_execution_memory_world_presentation.rs"]
mod world_presentation;

#[derive(Clone)]
pub struct MemoryResult {
    pub value: Expr,
    pub memory: Expr,
}

impl MemoryResult {
    pub fn result(&self) -> Expr {
        app(
            "IRByteMemoryResultV1.value",
            [self.value.clone(), self.memory.clone()],
        )
    }
}

pub struct MemoryChecks {
    /// Actual typed evaluator, including fetched SSA operands and metadata.
    pub evaluation: Expr,
    /// Destination arity AND actual site-result matching; stores bind no value.
    pub result: Expr,
    /// Exact equality of the returned and incoming allocation-list projections.
    pub allocations: Expr,
}

#[derive(Clone)]
pub struct MemoryPremises {
    pub evaluated: PendingEquality,
    pub result: PendingEquality,
    /// Eq (IRList IRByteAllocationV1) (mem_allocs returned) (mem_allocs incoming).
    /// Byte contents and address cursors are not equated by this premise.
    pub allocations: PendingEquality,
    pub before: PendingEquality,
}

/// One fetched operation; the exact returned memory replaces only memory in
/// the world. Host, active owners, next-owner identity and stack tail survive.
pub struct MemoryTransfer {
    step: PendingEquality,
    run: ExactRun,
    current: Current,
    valid: PendingEquality,
    result: MemoryResult,
}

impl MemoryTransfer {
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

fn projection(model: &MachineModel, world: &Expr, field: &str) -> Expr {
    app(
        &format!("ir_byte_world_{field}_v1"),
        [model.world_type.clone(), world.clone()],
    )
}

fn allocations(memory: Expr) -> Expr {
    app("ir_byte_mem_allocs_v1", [memory])
}

/// Preserve the explicit-world conversion fastpath and use the closed shared
/// constructor-case proof for an opaque world. Actual fields and memory remain
/// arguments; this supplies no validity, accessibility or allocation premise.
fn normalize_memory_world(
    assembler: &mut Assembler<'_>,
    model: &MachineModel,
    world: &Expr,
    memory: Expr,
) -> Result<PendingEquality> {
    world_presentation::replace(assembler, model, world, memory)
}

/// Closed mapper over the exact returned memory, owners, next owner and rows.
/// Source operands are applied only outside its binders. No scoped local is
/// allocated, and the ordinary kernel still checks the mapper and endpoints.
fn allocation_owner_mapper(memory: Expr, owners: Expr, next: Expr) -> Expr {
    // Under four binders: memory=3, owners=2, next=1, rows=0.
    let body = app(
        "ir_byte_memory_owners_v1",
        [
            app(
                "IRByteMemoryV1.mk",
                [
                    Expr::bvar(0),
                    app("ir_byte_mem_bytes_v1", [Expr::bvar(3)]),
                    app("ir_byte_mem_next_v1", [Expr::bvar(3)]),
                ],
            ),
            Expr::bvar(2),
            Expr::bvar(1),
        ],
    );
    let closed = [
        constant("IRByteMemoryV1"),
        app("IRList", [constant("Nat")]),
        constant("Nat"),
        app("IRList", [constant("IRByteAllocationV1")]),
    ]
    .into_iter()
    .rev()
    .fold(body, |body, ty| {
        Expr::lam(clean_kernel::BinderInfo::Default, ty, body)
    });
    Expr::apps(closed, [memory, owners, next])
}

/// Extract the actual final conjunct of pre-validity, then transport only the
/// allocation list. memory_owners observes no bytes or allocation cursor.
fn returned_memory_owners(
    assembler: &mut Assembler<'_>,
    model: &MachineModel,
    current: &Current,
    memory: &Expr,
    same_allocations: PendingEquality,
    before: &PendingEquality,
) -> Result<PendingEquality> {
    let owners = projection(model, &current.world, "owners");
    let next = projection(model, &current.world, "next");
    let old_memory = projection(model, &current.world, "memory");
    let memory_guard = |mem| {
        app(
            "ir_byte_memory_owners_v1",
            [mem, owners.clone(), next.clone()],
        )
    };
    let old_guard = memory_guard(old_memory);
    let active = app("ir_byte_owners_valid_v1", [owners.clone(), next.clone()]);
    let length = |ty, values| app("ir_byte_length_v1", [constant(ty), values]);
    let count = app(
        "ir_nat_eqb",
        [
            length("IRFrame", app("ir_mach_frames", [current.machine()])),
            length("Nat", owners.clone()),
        ],
    );
    let empty = app(
        "ir_nat_eqb",
        [
            length("IRMemSlot", app("ir_mach_mem", [current.machine()])),
            nat(0),
        ],
    );
    let both = app("Bool.and", [active.clone(), old_guard.clone()]);
    let suffix = app("Bool.and", [count.clone(), both.clone()]);
    let tail = app(
        "ir_byte_world_and_right_v1",
        [empty, suffix, before.term.clone()],
    );
    let tail = app("ir_byte_world_and_right_v1", [count, both, tail]);
    let old = PendingEquality::candidate(
        constant("Bool"),
        old_guard.clone(),
        constant("Bool.true"),
        app(
            "ir_byte_world_and_right_v1",
            [active, old_guard.clone(), tail],
        ),
    );
    let transported = assembler.congruence_function(
        same_allocations,
        constant("Bool"),
        allocation_owner_mapper(memory.clone(), owners.clone(), next.clone()),
    )?;
    // The actual guard observes allocation rows, not bytes/cursor. Re-present
    // the pending congruence directly; final replay still checks both complete
    // guards and the supplied row equality, including opaque memories.
    let proof =
        assembler.convert_endpoints(transported, memory_guard(memory.clone()), old_guard)?;
    assembler.compose(proof, old)
}

impl FetchedSite {
    fn memory_operation(&self, model: &MachineModel, current: &Current) -> Result<(Expr, bool)> {
        require_same(&self.context, &model.context, "memory fetched context")?;
        let fields = self.instruction.get_app_args();
        let ExprKind::Const(name, _) = self.instruction.get_app_fn().kind() else {
            return Err("memory assembler requires an actual instruction constructor".into());
        };
        let read = |id: &Expr| app("ir_getd", [current.machine(), id.clone()]);
        let align = app("ir_byte_site_align_v1", [self.site.clone()]);
        let memory = projection(model, &current.world, "memory");
        match (name.to_string().as_str(), fields.as_slice()) {
            ("IRInst.load", [ty, pointer, volatile]) => Ok((
                app(
                    "ir_byte_load_v1",
                    [
                        model.context.clone(),
                        (*ty).clone(),
                        read(pointer),
                        align,
                        (*volatile).clone(),
                        memory,
                    ],
                ),
                false,
            )),
            ("IRInst.store", [ty, pointer, value, volatile]) => Ok((
                app(
                    "ir_byte_store_v1",
                    [
                        model.context.clone(),
                        (*ty).clone(),
                        read(pointer),
                        read(value),
                        align,
                        (*volatile).clone(),
                        memory,
                    ],
                ),
                true,
            )),
            ("IRInst.gep", [ty, base, indices, inbounds]) => {
                let evaluation = if self.site.get_app_fn() == &constant("IRByteSiteV1.mki") {
                    if exact_constructor_fields::<7>(&self.site, "IRByteSiteV1.mki").is_none() {
                        return Err("typed integer GEP requires actual mki site arity".into());
                    }
                    app(
                        "ir_byte_gep_site_v1",
                        [
                            model.context.clone(),
                            self.site.clone(),
                            (*ty).clone(),
                            current.machine(),
                            (*base).clone(),
                            (*indices).clone(),
                            (*inbounds).clone(),
                            memory,
                        ],
                    )
                } else {
                    // Exact historical mk/mkt endpoint and argument order.
                    app(
                        "ir_byte_gep_v1",
                        [
                            model.context.clone(),
                            (*ty).clone(),
                            read(base),
                            app("ir_resolve", [current.machine(), (*indices).clone()]),
                            (*inbounds).clone(),
                            memory,
                        ],
                    )
                };
                Ok((evaluation, false))
            }
            ("IRInst.atomic_fetch_add_relaxed_u64_seq", [pointer, value]) => Ok((
                app(
                    "ir_byte_fetch_add_relaxed_u64_seq_v1",
                    [model.context.clone(), read(pointer), read(value), memory],
                ),
                // RMW writes memory but also binds the OLD value. The bool
                // selects result binding, not whether the operation can write.
                false,
            )),
            ("IRInst.atomic_fetch_add_relaxed_usize_seq", [bits, pointer, value]) => Ok((
                app(
                    "ir_byte_fetch_add_relaxed_usize_seq_v1",
                    [
                        (*bits).clone(),
                        model.context.clone(),
                        read(pointer),
                        read(value),
                        memory,
                    ],
                ),
                // Width is fetched syntax, not inferred from a U64 layout.
                // The shared primitive refuses every width other than 64.
                false,
            )),
            _ => Err(
                "memory assembler requires Load/Store/GEP or sequential Add/Relaxed/U64/Usize64"
                    .into(),
            ),
        }
    }

    /// Transport a nominal GEP decoder equality through the checked selected
    /// `mki` law, then compose an exact typed-evaluator result candidate.
    ///
    /// `decoded` must name the original site rows, current machine and ordered
    /// fetched SSA IDs, with right endpoint `IROption.some Nat index`.
    /// `evaluated` must start at that exact typed evaluator with the original
    /// pointee, base read, inbounds flag and full incoming memory. No nominal
    /// profile label, legacy singleton theorem, output permission or supplied
    /// equality metadata is proof authority. Complete fetched replay remains
    /// necessary, including actual site lookup and the result/validity guards.
    /// One existing operation is charged before every shape/endpoint check,
    /// then the existing compose operation charges once more on success (two
    /// operations total). Failed preflight is not refunded. No local, list
    /// construction charge, cache or declaration is introduced.
    pub fn typed_gep_evaluation(
        &self,
        assembler: &mut Assembler<'_>,
        model: &MachineModel,
        current: &Current,
        index: Expr,
        decoded: PendingEquality,
        evaluated: PendingEquality,
    ) -> Result<PendingEquality> {
        assembler.charge()?;
        require_same(
            &self.context,
            &model.context,
            "typed integer GEP fetched context",
        )?;
        let site = exact_constructor_fields::<7>(&self.site, "IRByteSiteV1.mki")
            .ok_or("typed integer GEP requires actual mki site")?;
        for (actual, expected) in site[..3].iter().zip([
            nat(u64::from(self.coordinate.function.index())),
            nat(u64::from(self.coordinate.block.index())),
            nat(u64::try_from(self.coordinate.instruction).map_err(|_| "typed GEP PC overflow")?),
        ]) {
            require_same(actual, &expected, "typed integer GEP site coordinate")?;
        }
        let [pointee, base, indices, inbounds] =
            exact_constructor_fields::<4>(&self.instruction, "IRInst.gep")
                .ok_or("typed integer GEP requires actual GEP")?;
        let memory = projection(model, &current.world, "memory");
        let selected = app("IROption.some", [constant("Nat"), index.clone()]);
        decoded.endpoints(
            &app("IROption", [constant("Nat")]),
            &app(
                "ir_byte_gep_typed_indices_v1",
                [site[6].clone(), current.machine(), indices.clone()],
            ),
            &selected,
        )?;
        let typed = app(
            "ir_byte_gep_typed_v1",
            [
                model.context.clone(),
                pointee.clone(),
                app("ir_getd", [current.machine(), base.clone()]),
                selected,
                inbounds.clone(),
                memory.clone(),
            ],
        );
        evaluated.endpoints(&constant("IRByteMemoryResultV1"), &typed, evaluated.right())?;
        let (actual, _) = self.memory_operation(model, current)?;
        // Feed the exact telescope directly to Expr::apps. A temporary growing
        // Vec would allocate and copy this fixed argument list on each call;
        // the chained iterator retains order without that buffer.
        let arguments = std::iter::once(model.context.clone())
            .chain(site.iter().map(|field| (**field).clone()))
            .chain([
                pointee.clone(),
                current.machine(),
                base.clone(),
                indices.clone(),
                inbounds.clone(),
                memory,
                index,
                decoded.term().clone(),
            ]);
        let selected = PendingEquality::candidate(
            constant("IRByteMemoryResultV1"),
            actual,
            typed,
            app("ir_byte_gep_site_mki_selected_v1", arguments),
        );
        assembler.compose(selected, evaluated)
    }

    pub fn memory_checks(
        &self,
        model: &MachineModel,
        current: &Current,
        result: &MemoryResult,
    ) -> Result<MemoryChecks> {
        let (evaluation, store) = self.memory_operation(model, current)?;
        let values = if store {
            list("IRScalar", &[])
        } else {
            list("IRScalar", std::slice::from_ref(&result.value))
        };
        Ok(MemoryChecks {
            evaluation,
            result: app(
                "Bool.and",
                [
                    app(
                        "ir_nat_eqb",
                        [
                            app("ir_byte_length_v1", [constant("Nat"), self.results.clone()]),
                            app("ir_byte_length_v1", [constant("IRScalar"), values.clone()]),
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
            allocations: eq(
                &app("IRList", [constant("IRByteAllocationV1")]),
                allocations(result.memory.clone()),
                allocations(projection(model, &current.world, "memory")),
            ),
        })
    }

    pub fn memory_value(
        &self,
        assembler: &mut Assembler<'_>,
        model: &MachineModel,
        current: &Current,
        result: MemoryResult,
        premises: MemoryPremises,
    ) -> Result<MemoryTransfer> {
        assembler.charge()?;
        let checks = self.memory_checks(model, current, &result)?;
        premises.evaluated.endpoints(
            &constant("IRByteMemoryResultV1"),
            &checks.evaluation,
            &result.result(),
        )?;
        premises
            .result
            .endpoints(&constant("Bool"), &checks.result, &constant("Bool.true"))?;
        premises.allocations.endpoints(
            &app("IRList", [constant("IRByteAllocationV1")]),
            &allocations(result.memory.clone()),
            &allocations(projection(model, &current.world, "memory")),
        )?;
        premises.before.endpoints(
            &constant("Bool"),
            &current.valid(model),
            &constant("Bool.true"),
        )?;
        let (_, store) = self.memory_operation(model, current)?;
        let values = if store {
            list("IRScalar", &[])
        } else {
            list("IRScalar", std::slice::from_ref(&result.value))
        };
        let world = app(
            "ir_byte_with_memory_v1",
            [
                model.world_type.clone(),
                current.world.clone(),
                result.memory.clone(),
            ],
        );
        let updated = app(
            "ir_frame_advance",
            [app(
                "ir_frame_set_many",
                [current.frame.clone(), self.results.clone(), values.clone()],
            )],
        );
        let mut after = Current {
            frame: updated,
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
        // The changed result is the final argument of the existing evaluator.
        // Use that actual partial application instead of allocating a fresh
        // closure local and then converting its beta-reduced endpoints.
        let lifted = assembler.congruence_function(
            premises.evaluated,
            model.config_type(),
            app(
                "ir_byte_memory_result_v1",
                [
                    model.world_type.clone(),
                    model.context.clone(),
                    current.machine(),
                    current.world.clone(),
                    self.results.clone(),
                    app("ir_byte_site_results_v1", [self.site.clone()]),
                    constant(if store { "Bool.true" } else { "Bool.false" }),
                ],
            ),
        )?;
        let fetched = self.step(assembler, model, current, premises.before.clone())?;
        let lifted = assembler.convert_endpoints(lifted, fetched.right.clone(), bound.clone())?;
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
        let step = assembler.compose(fetched, lifted)?;
        let step = assembler.compose(step, binding)?;

        let changed =
            normalize_memory_world(assembler, model, &current.world, result.memory.clone())?;
        after.world = changed.right.clone();
        let changed = assembler.congruence_function(
            changed,
            model.config_type(),
            app(
                "IRByteConfigV1.running",
                [model.world_type.clone(), after.machine()],
            ),
        )?;
        let step = assembler.compose(step, changed)?;
        let run = assembler.one_step(model, current.running(model), step.clone())?;
        let owners = returned_memory_owners(
            assembler,
            model,
            current,
            &result.memory,
            premises.allocations,
            &premises.before,
        )?;
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
                    projection(model, &current.world, "host"),
                    premises.before.term,
                    owners.term,
                ],
            ),
        );
        Ok(MemoryTransfer {
            step,
            run,
            current: after,
            valid,
            result,
        })
    }
}

#[cfg(test)]
#[path = "core_execution_memory_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "core_execution_memory_constructor_tests.rs"]
mod constructor_tests;

#[cfg(test)]
#[path = "core_execution_memory_world_mapper_tests.rs"]
mod world_mapper_tests;

#[cfg(test)]
#[path = "core_execution_owner_mapper_tests.rs"]
mod owner_mapper_tests;

#[cfg(test)]
#[path = "core_execution_memory_typed_index_tests.rs"]
mod typed_index_tests;
