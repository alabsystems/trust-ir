// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Compositional candidates for the actual ByteV1 allocation dispatch.
//! Exact owners and the fetched optional SSA count remain semantic inputs;
//! selecting its integer/low-half branch proves no successful allocation,
//! world validity, memory accessibility, caller contract or native authority.
//! Complete fetched transfers still use `allocation_value` and independent
//! replay. Nominal I64/U64 admission remains the reflection's separate TCB.

use super::*;

#[cfg(test)]
#[path = "core_execution_typed_alloca_tests.rs"]
mod tests;

/// Plain exact claims, not checked facts. Equality triples are (type, left,
/// right), ready for `PendingEquality::candidate` with a separately supplied
/// proof term. No field supplies a proof or establishes a successful access.
pub struct AllocationDispatchChecks {
    pub owners: (Expr, Expr, Expr),
    pub count: (Expr, Expr, Expr),
    pub count_bound: Expr,
    pub dispatch: Expr,
    pub dispatched: Expr,
}

#[derive(Clone)]
pub struct AllocationDispatchPremises {
    pub owners: PendingEquality,
    pub count: PendingEquality,
    /// The actual resolved carrier is below 2^63, not merely below 2^64.
    pub count_bound: PendingProof,
}

struct Dispatch {
    world_type: Expr,
    context: Expr,
    machine: Expr,
    world: Expr,
    results: Expr,
    site: Expr,
    pointee: Expr,
    optional_count: Expr,
    owner: Expr,
    count: Expr,
    owner_tail: Expr,
}

fn nat_list() -> Expr {
    app("IRList", [constant("Nat")])
}

impl Dispatch {
    fn config_type(&self) -> Expr {
        app("IRByteConfigV1", [self.world_type.clone()])
    }

    fn halted(&self, kind: &str, fault: &str) -> Expr {
        app(
            "IRByteConfigV1.halted",
            [
                self.world_type.clone(),
                app(
                    &format!("IROutcome.{kind}"),
                    [constant(&format!("IRFault.{fault}"))],
                ),
                self.world.clone(),
            ],
        )
    }

    fn world_field(&self, field: &str) -> Expr {
        app(
            &format!("ir_byte_world_{field}_v1"),
            [self.world_type.clone(), self.world.clone()],
        )
    }

    fn resolved_count(&self) -> Expr {
        // A partial application, rather than a binder capturing the caller's
        // machine, spells the original `fun id => ir_getd machine id`.
        Expr::apps(
            Expr::const_(
                Name::from_string("IROption.rec"),
                vec![Level::succ(Level::zero())],
            ),
            [
                constant("Nat"),
                Expr::lam(
                    clean_kernel::BinderInfo::Default,
                    app("IROption", [constant("Nat")]),
                    constant("IRScalar"),
                ),
                app("IRScalar.int_", [nat(1)]),
                app("ir_getd", [self.machine.clone()]),
                self.optional_count.clone(),
            ],
        )
    }

    fn dispatch(&self) -> Expr {
        app(
            "ir_byte_alloca_exec_v1",
            [
                self.world_type.clone(),
                self.context.clone(),
                self.machine.clone(),
                self.world.clone(),
                self.results.clone(),
                self.site.clone(),
                self.pointee.clone(),
                self.optional_count.clone(),
            ],
        )
    }

    fn dispatched_with(&self, count: Expr, owner: Expr) -> Expr {
        let allocated = app(
            "ir_byte_alloc_v1",
            [
                self.context.clone(),
                self.pointee.clone(),
                count,
                app("ir_byte_site_align_v1", [self.site.clone()]),
                owner,
                self.world_field("memory"),
            ],
        );
        app(
            "ir_byte_memory_result_v1",
            [
                self.world_type.clone(),
                self.context.clone(),
                self.machine.clone(),
                self.world.clone(),
                self.results.clone(),
                app("ir_byte_site_results_v1", [self.site.clone()]),
                constant("Bool.false"),
                allocated,
            ],
        )
    }

    fn integer_branch(&self, count: Expr, owner: Expr) -> Expr {
        choose(
            &self.config_type(),
            app("ir_nat_ltb", [count.clone(), nat(1_u64 << 63)]),
            self.dispatched_with(count, owner),
            self.halted("unmodelled", "width_bounded"),
        )
    }

    fn checks(&self) -> AllocationDispatchChecks {
        AllocationDispatchChecks {
            owners: (
                nat_list(),
                self.world_field("owners"),
                app(
                    "IRList.cons",
                    [constant("Nat"), self.owner.clone(), self.owner_tail.clone()],
                ),
            ),
            count: (
                constant("IRScalar"),
                self.resolved_count(),
                app("IRScalar.int_", [self.count.clone()]),
            ),
            count_bound: app("Nat.lt", [self.count.clone(), nat(1_u64 << 63)]),
            dispatch: self.dispatch(),
            dispatched: self.dispatched_with(self.count.clone(), self.owner.clone()),
        }
    }

    fn arguments(&self) -> [Expr; 11] {
        [
            self.world_type.clone(),
            self.context.clone(),
            self.machine.clone(),
            self.world.clone(),
            self.results.clone(),
            self.site.clone(),
            self.pointee.clone(),
            self.optional_count.clone(),
            self.owner.clone(),
            self.count.clone(),
            self.owner_tail.clone(),
        ]
    }
}

impl FetchedSite {
    fn allocation_dispatch_input(
        &self,
        model: &MachineModel,
        current: &Current,
        input: &AllocationInput,
        owner_tail: Expr,
    ) -> Result<Dispatch> {
        require_same(
            &self.context,
            model.context(),
            "allocation dispatch fetched context",
        )?;
        // Inspect exactly two application fields. Do not allocate an arbitrary
        // argument vector to diagnose a malformed public candidate expression.
        let ExprKind::App(first, optional_count) = self.instruction.kind() else {
            return Err("allocation dispatch requires fetched Alloca".into());
        };
        let ExprKind::App(head, pointee) = first.kind() else {
            return Err("allocation dispatch requires fetched Alloca".into());
        };
        if !matches!(head.kind(), ExprKind::Const(name, _) if name == &Name::from_string("IRInst.alloca"))
        {
            return Err("allocation dispatch requires fetched Alloca".into());
        }
        Ok(Dispatch {
            world_type: model.world_type().clone(),
            context: model.context().clone(),
            machine: current.machine(),
            world: current.world.clone(),
            results: self.results.clone(),
            site: self.site.clone(),
            pointee: pointee.as_ref().clone(),
            optional_count: optional_count.as_ref().clone(),
            owner: input.owner.clone(),
            count: input.count.clone(),
            owner_tail,
        })
    }

    pub fn allocation_dispatch_checks(
        &self,
        model: &MachineModel,
        current: &Current,
        input: &AllocationInput,
        owner_tail: Expr,
    ) -> Result<AllocationDispatchChecks> {
        Ok(self
            .allocation_dispatch_input(model, current, input, owner_tail)?
            .checks())
    }

    /// Construct the exact guarded dispatch equality from explicit current
    /// owner/count facts. The returned term is still independently unchecked;
    /// allocation evaluation, result/world validity and the fetched step are
    /// separate premises of `allocation_value`. Some and None are retained.
    pub fn allocation_dispatch(
        &self,
        assembler: &mut Assembler<'_>,
        model: &MachineModel,
        current: &Current,
        input: &AllocationInput,
        owner_tail: Expr,
        premises: AllocationDispatchPremises,
    ) -> Result<PendingEquality> {
        assembler.charge()?;
        let data = self.allocation_dispatch_input(model, current, input, owner_tail)?;
        let checks = data.checks();
        for (proof, (ty, left, right)) in [
            (&premises.owners, &checks.owners),
            (&premises.count, &checks.count),
        ] {
            proof.endpoints(ty, left, right)?;
        }
        require_same(
            premises.count_bound.proposition(),
            &checks.count_bound,
            "allocation dispatch count bound",
        )?;
        let helper = assembler.allocation_dispatch_helper()?;
        Ok(PendingEquality::candidate(
            model.config_type(),
            checks.dispatch,
            checks.dispatched,
            Expr::apps(
                helper,
                data.arguments().into_iter().chain([
                    premises.owners.term,
                    premises.count.term,
                    premises.count_bound.term,
                ]),
            ),
        ))
    }
}

// Every expression here is a fixed neutral template. Its fourteen parameters
// are W, context, machine, world, results, site, pointee, optional_count,
// owner, count, owner_tail, owners_eq, count_eq, count_bound, in that order.
// No actual caller expression is placed beneath any of these binders.
fn neutral_dispatch(depth: u32) -> Dispatch {
    let parameter = |position| Expr::bvar(depth - position - 1);
    Dispatch {
        world_type: parameter(0),
        context: parameter(1),
        machine: parameter(2),
        world: parameter(3),
        results: parameter(4),
        site: parameter(5),
        pointee: parameter(6),
        optional_count: parameter(7),
        owner: parameter(8),
        count: parameter(9),
        owner_tail: parameter(10),
    }
}

fn closed_dispatch_parameters() -> [Expr; 14] {
    // A parameter type lives OUTSIDE its own binder. In particular the world
    // type sees W at index2, and each proof sees only its preceding inputs.
    let owners = neutral_dispatch(11).checks().owners;
    let count = neutral_dispatch(12).checks().count;
    [
        Expr::type_(),
        constant("IRByteContextV1"),
        constant("IRMachine"),
        app("IRByteWorldV1", [Expr::bvar(2)]),
        nat_list(),
        constant("IRByteSiteV1"),
        constant("IRTy"),
        app("IROption", [constant("Nat")]),
        constant("Nat"),
        constant("Nat"),
        nat_list(),
        eq(&owners.0, owners.1, owners.2),
        eq(&count.0, count.1, count.2),
        neutral_dispatch(13).checks().count_bound,
    ]
}

fn close_dispatch_body(body: Expr) -> Expr {
    closed_dispatch_parameters()
        .into_iter()
        .rev()
        .fold(body, |body, ty| {
            Expr::lam(clean_kernel::BinderInfo::Default, ty, body)
        })
}

// These constant-sized failure branches retain ALL original constructor
// arguments, including the ignored recursive hypotheses. Lifting affects
// only the neutral template's outer binders, never caller data or proofs.
fn closed_failure_case(domains: &[Expr], body: &Expr) -> Expr {
    let body = body.lift(domains.len() as u32);
    domains
        .iter()
        .enumerate()
        .rev()
        .fold(body, |body, (index, ty)| {
            Expr::lam(
                clean_kernel::BinderInfo::Default,
                ty.lift(index as u32),
                body,
            )
        })
}

fn closed_count_factory() -> Expr {
    // The recursor lives beneath the fourteen inputs, then owner and scalar.
    let data = neutral_dispatch(16);
    let config = data.config_type();
    let failure = data.halted("type_error", "not_int");
    let word_case = closed_failure_case(&[constant("Nat")], &failure);
    // The integer case adds its word after owner/scalar: owner is index2.
    let integer_case = Expr::lam(
        clean_kernel::BinderInfo::Default,
        constant("Nat"),
        neutral_dispatch(17).integer_branch(Expr::bvar(0), Expr::bvar(2)),
    );
    let cases = Expr::apps(
        Expr::const_(
            Name::from_string("IRScalar.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [
            Expr::lam(
                clean_kernel::BinderInfo::Default,
                constant("IRScalar"),
                config.lift(1),
            ),
            failure.clone(),
            closed_failure_case(&[constant("Bool")], &failure),
            integer_case,
            word_case.clone(),
            failure.clone(),
            word_case.clone(),
            failure.clone(),
            closed_failure_case(&[constant("Nat"), constant("Nat")], &failure),
            word_case,
            closed_failure_case(&[constant("IRScalar"), config.clone()], &failure),
            failure.clone(),
            closed_failure_case(
                &[
                    constant("IRScalar"),
                    constant("IRScalar"),
                    config.clone(),
                    config,
                ],
                &failure,
            ),
            Expr::bvar(0),
        ],
    );
    Expr::lam(
        clean_kernel::BinderInfo::Default,
        constant("Nat"),
        Expr::lam(
            clean_kernel::BinderInfo::Default,
            constant("IRScalar"),
            cases,
        ),
    )
}

fn closed_owners_handler(count_factory: Expr) -> Expr {
    // Under source, owner, tail and recursive result, the factory's neutral
    // inputs are lifted four slots; the actual list owner is index2.
    let data = neutral_dispatch(15);
    let config = data.config_type();
    let scalar_branch = Expr::apps(
        count_factory.lift(4),
        [Expr::bvar(2), neutral_dispatch(18).resolved_count()],
    );
    let cons_case = Expr::lam(
        clean_kernel::BinderInfo::Default,
        constant("Nat"),
        Expr::lam(
            clean_kernel::BinderInfo::Default,
            nat_list(),
            Expr::lam(
                clean_kernel::BinderInfo::Default,
                config.lift(2),
                scalar_branch,
            ),
        ),
    );
    let cases = Expr::apps(
        Expr::const_(
            Name::from_string("IRList.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [
            constant("Nat"),
            Expr::lam(
                clean_kernel::BinderInfo::Default,
                nat_list(),
                config.lift(1),
            ),
            data.halted("stuck", "no_frame"),
            cons_case,
            Expr::bvar(0),
        ],
    );
    Expr::lam(clean_kernel::BinderInfo::Default, nat_list(), cases)
}

impl Assembler<'_> {
    fn allocation_dispatch_helper(&mut self) -> Result<Expr> {
        if let Some(candidate) = &self.allocation_dispatch_candidate {
            return Ok(candidate.clone());
        }
        // Preserve the original 29 local-construction charges. Only their
        // caller-Scope allocations disappear; primitive proof composition
        // below retains its original ten charged operations. As with run_one,
        // a failed cold construction cannot publish a partial cache entry.
        for _ in 0..29 {
            self.charge()?;
        }
        let proof = self.allocation_dispatch_term()?;
        let closed = close_dispatch_body(proof.term);
        self.allocation_dispatch_candidate = Some(closed.clone());
        Ok(closed)
    }

    fn allocation_dispatch_term(&mut self) -> Result<PendingEquality> {
        let data = neutral_dispatch(14);
        let checks = data.checks();
        let owners = PendingEquality::candidate(
            checks.owners.0,
            checks.owners.1,
            checks.owners.2,
            Expr::bvar(2),
        );
        let count = PendingEquality::candidate(
            checks.count.0,
            checks.count.1,
            checks.count.2,
            Expr::bvar(1),
        );
        let config = data.config_type();
        let count_factory = closed_count_factory();
        let owners_handler = closed_owners_handler(count_factory.clone());
        let owners = self.congruence_function(owners, config.clone(), owners_handler)?;
        let first = self.conversion(config.clone(), data.dispatch(), owners.left.clone())?;
        let count = self.congruence_function(
            count,
            config.clone(),
            Expr::app(count_factory, data.owner.clone()),
        )?;
        let bridge = self.conversion(config.clone(), owners.right.clone(), count.left.clone())?;
        let integer = data.integer_branch(data.count.clone(), data.owner.clone());
        let integer_start =
            self.conversion(config.clone(), count.right.clone(), integer.clone())?;
        let target = data.dispatched_with(data.count.clone(), data.owner.clone());
        let bound = app(
            "ir_byte_ltb_of_lt_v1",
            [data.count.clone(), nat(1_u64 << 63), Expr::bvar(0)],
        );
        let selected = PendingEquality::candidate(
            config.clone(),
            integer,
            target.clone(),
            app(
                "ir_byte_case_true_v1",
                [
                    config.clone(),
                    app("ir_nat_ltb", [data.count.clone(), nat(1_u64 << 63)]),
                    data.halted("unmodelled", "width_bounded"),
                    target.clone(),
                    target.clone(),
                    bound,
                    refl(&config, target),
                ],
            ),
        );
        let mut proof = first;
        for part in [owners, bridge, count, integer_start, selected] {
            proof = self.compose(proof, part)?;
        }
        Ok(proof)
    }
}
