// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Variable-length finite-prefix candidates over the actual Core run function.
//! No termination, sufficient-fuel, source completeness or native authority.

use super::*;
use clean_kernel::BinderInfo;

/// Explicit source semantics, a state-dependent Core step count, and an
/// untrusted proof candidate for each running source step. The consumer must
/// reconstruct and kernel-check the complete relation and every premise.
#[derive(Clone)]
pub struct SegmentedPrefixSimulation {
    /// Source configuration carrier (Type0).
    pub source_type: Expr,
    /// Source terminal-state predicate, S -> Bool.
    pub source_halted: Expr,
    /// Source transition, S -> S.
    pub source_step: Expr,
    /// Actual Core steps consumed by a running source transition, S -> Nat.
    pub core_steps: Expr,
    /// Complete consumer-owned relation, S -> CoreConfig -> Prop.
    pub relation: Expr,
    /// Candidate of the exact proposition returned by the premise getter.
    pub step_preserves: PendingProof,
}

/// A candidate relation at the exact derived Core fuel. A halted source adds
/// zero fuel; this does not say that the related Core configuration is halted.
#[derive(Clone)]
pub struct SimulatedPrefix {
    /// Derived exact fuel; later segment fuel is added before earlier fuel.
    pub core_fuel: NatTerm,
    /// Candidate relation after the source prefix and that actual Core run.
    pub proof: PendingProof,
}

impl SegmentedPrefixSimulation {
    /// `forall s c, R s c -> H s = false -> R (F s) (run (cost s) c)`.
    /// The fixed telescope is closed BEFORE inserting any caller expression.
    pub fn step_preservation_proposition(&self, model: &MachineModel) -> Expr {
        let mut scope = Scope::new();
        let mut parameters = Vec::new();
        let mut local = |ty| {
            let value = scope.try_local(ty).expect("fixed statement telescope");
            parameters.push(value.clone());
            value
        };
        let s_ty = local(Expr::type_());
        let c_ty = local(Expr::type_());
        let halted = local(Expr::arrow(s_ty.term().clone(), constant("Bool")));
        let step = local(Expr::arrow(s_ty.term().clone(), s_ty.term().clone()));
        let cost = local(Expr::arrow(s_ty.term().clone(), constant("Nat")));
        let run = local(Expr::arrow(
            constant("Nat"),
            Expr::arrow(c_ty.term().clone(), c_ty.term().clone()),
        ));
        let relation = local(Expr::arrow(
            s_ty.term().clone(),
            Expr::arrow(c_ty.term().clone(), Expr::sort(Level::zero())),
        ));
        drop(local);
        let s = scope.try_local(s_ty.term().clone()).unwrap();
        let c = scope.try_local(c_ty.term().clone()).unwrap();
        let related = scope
            .try_local(Expr::apps(
                relation.term().clone(),
                [s.term().clone(), c.term().clone()],
            ))
            .unwrap();
        let running = scope
            .try_local(eq(
                &constant("Bool"),
                Expr::app(halted.term().clone(), s.term().clone()),
                constant("Bool.false"),
            ))
            .unwrap();
        let body = Expr::apps(
            relation.term().clone(),
            [
                Expr::app(step.term().clone(), s.term().clone()),
                Expr::apps(
                    run.term().clone(),
                    [
                        Expr::app(cost.term().clone(), s.term().clone()),
                        c.term().clone(),
                    ],
                ),
            ],
        );
        let body = s.pi(c.pi(related.pi(running.pi(body))));
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
                self.source_type.clone(),
                model.config_type(),
                self.source_halted.clone(),
                self.source_step.clone(),
                self.core_steps.clone(),
                app(
                    "ir_byte_run_v1",
                    [
                        model.world_type.clone(),
                        model.context.clone(),
                        model.providers.clone(),
                    ],
                ),
                self.relation.clone(),
            ],
        )
    }

    fn source_run(&self, fuel: Expr, state: Expr) -> Expr {
        app(
            "ir_drive_v1",
            [
                self.source_type.clone(),
                self.source_halted.clone(),
                self.source_step.clone(),
                fuel,
                state,
            ],
        )
    }
    fn related(&self, source: Expr, core: Expr) -> Expr {
        Expr::apps(self.relation.clone(), [source, core])
    }
}

fn choose(ty: Expr, flag: Expr, yes: Expr, no: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Bool.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [
            Expr::lam(BinderInfo::Default, constant("Bool"), ty),
            no,
            yes,
            flag,
        ],
    )
}
fn at(function: &Expr, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(function.clone(), arguments)
}
fn subst(ty: Expr, predicate: Expr, left: Expr, right: Expr, equality: Expr, proof: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.subst"),
            vec![Level::succ(Level::zero())],
        ),
        [ty, predicate, left, right, equality, proof],
    )
}
fn symmetric(ty: Expr, left: Expr, right: Expr, proof: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.symm"),
            vec![Level::succ(Level::zero())],
        ),
        [ty, left, right, proof],
    )
}

impl Assembler<'_> {
    /// Compose state-dependent segments by structural induction on source fuel.
    /// Running segments use the actual `ir_byte_run_add_v1` law, with its exact
    /// later+earlier fuel order. All proof binders use this assembler's existing
    /// operation/local ledgers. No premise, endpoint, context or provider is
    /// changed, and no candidate is installed or treated as a checked fact.
    pub fn simulate_segmented_prefix(
        &mut self,
        model: &MachineModel,
        simulation: &SegmentedPrefixSimulation,
        fuel: &NatTerm,
        source_initial: Expr,
        core_initial: Expr,
        initial: PendingProof,
    ) -> Result<SimulatedPrefix> {
        self.charge()?;
        require_same(
            simulation.step_preserves.proposition(),
            &simulation.step_preservation_proposition(model),
            "segmented simulation step preservation",
        )?;
        require_same(
            initial.proposition(),
            &simulation.related(source_initial.clone(), core_initial.clone()),
            "segmented simulation initial relation",
        )?;
        let s_ty = simulation.source_type.clone();
        let c_ty = model.config_type();
        // Every nested telescope owns fresh identities. In particular the
        // cost/motive binders must not shadow the enclosing induction binders.
        let cost_k = self.local(constant("Nat"))?;
        let cost_zero_s = self.local(s_ty.clone())?;
        let cost_step_k = self.local(constant("Nat"))?;
        let cost_ih = self.local(Expr::arrow(s_ty.clone(), constant("Nat")))?;
        let cost_s = self.local(s_ty.clone())?;
        let cost_hs = Expr::app(simulation.source_halted.clone(), cost_s.term().clone());
        let cost_fs = Expr::app(simulation.source_step.clone(), cost_s.term().clone());
        let cost_ks = Expr::app(simulation.core_steps.clone(), cost_s.term().clone());
        let cost_motive = cost_k.lam(Expr::arrow(s_ty.clone(), constant("Nat")));
        let cost_zero = cost_zero_s.lam(nat(0));
        let tail_cost = Expr::app(cost_ih.term().clone(), cost_fs);
        let cost_step = cost_step_k.lam(cost_ih.lam(cost_s.lam(choose(
            constant("Nat"),
            cost_hs,
            nat(0),
            app("Nat.add", [tail_cost, cost_ks]),
        ))));
        let costs = Expr::const_(
            Name::from_string("Nat.rec"),
            vec![Level::succ(Level::zero())],
        );
        let costs = at(&costs, [cost_motive, cost_zero, cost_step]);

        let motive_k = self.local(constant("Nat"))?;
        let motive_s = self.local(s_ty.clone())?;
        let motive_c = self.local(c_ty.clone())?;
        let motive_h =
            self.local(simulation.related(motive_s.term().clone(), motive_c.term().clone()))?;
        let conclusion = simulation.related(
            simulation.source_run(motive_k.term().clone(), motive_s.term().clone()),
            model.run(
                &NatTerm(at(
                    &costs,
                    [motive_k.term().clone(), motive_s.term().clone()],
                )),
                motive_c.term().clone(),
            ),
        );
        let motive = motive_k.lam(motive_s.pi(motive_c.pi(motive_h.pi(conclusion))));

        let k = self.local(constant("Nat"))?;
        let s = self.local(s_ty.clone())?;
        let c = self.local(c_ty.clone())?;
        let h = self.local(simulation.related(s.term().clone(), c.term().clone()))?;
        let hs = Expr::app(simulation.source_halted.clone(), s.term().clone());
        let fs = Expr::app(simulation.source_step.clone(), s.term().clone());
        let ks = Expr::app(simulation.core_steps.clone(), s.term().clone());
        let tail_cost = at(&costs, [k.term().clone(), fs.clone()]);
        let total_cost = app("Nat.add", [tail_cost.clone(), ks.clone()]);
        let after_segment = model.run(&NatTerm(ks.clone()), c.term().clone());
        let nested = model.run(&NatTerm(tail_cost.clone()), after_segment.clone());
        let combined = model.run(&NatTerm(total_cost.clone()), c.term().clone());
        let source_tail = simulation.source_run(k.term().clone(), fs.clone());
        let ih = self.local(Expr::app(motive.clone(), k.term().clone()))?;
        let running = self.local(eq(&constant("Bool"), hs.clone(), constant("Bool.false")))?;
        let segment_related = at(
            simulation.step_preserves.term(),
            [
                s.term().clone(),
                c.term().clone(),
                h.term().clone(),
                running.term().clone(),
            ],
        );
        let recursive = at(ih.term(), [fs.clone(), after_segment, segment_related]);
        let reached = self.local(c_ty.clone())?;
        let predicate =
            reached.lam(simulation.related(source_tail.clone(), reached.term().clone()));
        let law = app(
            "ir_byte_run_add_v1",
            [
                model.world_type.clone(),
                model.context.clone(),
                model.providers.clone(),
                tail_cost,
                ks,
                c.term().clone(),
            ],
        );
        let no = running.lam(subst(
            c_ty.clone(),
            predicate,
            nested.clone(),
            combined.clone(),
            symmetric(c_ty.clone(), combined, nested, law),
            recursive,
        ));
        let halted = self.local(eq(&constant("Bool"), hs.clone(), constant("Bool.true")))?;
        let yes = halted.lam(h.term().clone());
        let flag = self.local(constant("Bool"))?;
        let flag_eq = self.local(eq(&constant("Bool"), hs.clone(), flag.term().clone()))?;
        let chosen = simulation.related(
            choose(s_ty, flag.term().clone(), s.term().clone(), source_tail),
            model.run(
                &NatTerm(choose(
                    constant("Nat"),
                    flag.term().clone(),
                    nat(0),
                    total_cost,
                )),
                c.term().clone(),
            ),
        );
        let by_flag = Expr::apps(
            Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
            [
                flag.lam(flag_eq.pi(chosen)),
                no,
                yes,
                hs.clone(),
                refl(&constant("Bool"), hs),
            ],
        );
        let successor = k.lam(ih.lam(s.lam(c.lam(h.lam(by_flag)))));
        let zero = s.lam(c.lam(h.lam(h.term().clone())));
        let induction = Expr::apps(
            Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            [motive, zero, successor, fuel.term().clone()],
        );
        let core_fuel = NatTerm(at(&costs, [fuel.term().clone(), source_initial.clone()]));
        let proposition = simulation.related(
            simulation.source_run(fuel.term().clone(), source_initial.clone()),
            model.run(&core_fuel, core_initial.clone()),
        );
        Ok(SimulatedPrefix {
            core_fuel,
            proof: PendingProof::candidate(
                proposition,
                at(
                    &induction,
                    [source_initial, core_initial, initial.term().clone()],
                ),
            ),
        })
    }
}

#[cfg(test)]
#[path = "core_execution_segmented_simulation_tests.rs"]
mod tests;
