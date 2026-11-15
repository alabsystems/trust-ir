// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Pending finite-prefix simulation through the existing checked fuel driver.
//! This is a closed Nat/Bool-recursion proof candidate, not another evaluator,
//! termination argument, loop oracle or installed declaration. The consumer
//! supplies and independently proves the complete relation and step premises.

use super::*;
use clean_kernel::BinderInfo;

/// Explicit source semantics and candidate simulation premises. No field is
/// proof authority. In particular a relation that forgets the world proves no
/// world preservation; the consumer must independently reconstruct its claim.
#[derive(Clone)]
pub struct PrefixSimulation {
    pub source_type: Expr,
    pub source_halted: Expr,
    pub source_step: Expr,
    pub relation: Expr,
    pub halt_agrees: PendingProof,
    pub step_preserves: PendingProof,
}

impl PrefixSimulation {
    fn arguments(&self, model: &MachineModel) -> [Expr; 7] {
        [
            self.source_type.clone(),
            model.config_type(),
            self.source_halted.clone(),
            app("ir_byte_halted_v1", [model.world_type.clone()]),
            self.source_step.clone(),
            app(
                "ir_byte_step_v1",
                [
                    model.world_type.clone(),
                    model.context.clone(),
                    model.providers.clone(),
                ],
            ),
            self.relation.clone(),
        ]
    }

    /// Exact expected halt premise, built with operands OUTSIDE the closed
    /// telescope. No supplied expression is captured beneath a raw binder.
    pub fn halt_agreement_proposition(&self, model: &MachineModel) -> Expr {
        Expr::apps(template(Template::Halt), self.arguments(model))
    }

    /// Exact running-step premise, including the source's false-halt witness.
    pub fn step_preservation_proposition(&self, model: &MachineModel) -> Expr {
        Expr::apps(template(Template::Step), self.arguments(model))
    }
}

impl Assembler<'_> {
    /// Assemble an arbitrary same-fuel prefix simulation. The output is only a
    /// candidate of `R (source_drive fuel s) (actual_byte_run fuel c)`.
    ///
    /// Exact premise shapes are checked after charging the existing caller
    /// operation ledger. Every binder of the fixed helper is charged there
    /// too; no caller local, cache, independent budget or refund is introduced.
    /// Both terminal states are retained without calling either step. There is
    /// no conclusion about termination, sufficient fuel or native execution.
    pub fn simulate_prefix(
        &mut self,
        model: &MachineModel,
        simulation: &PrefixSimulation,
        fuel: &NatTerm,
        source_initial: Expr,
        core_initial: Expr,
        initial: PendingProof,
    ) -> Result<PendingProof> {
        self.charge()?;
        require_same(
            simulation.halt_agrees.proposition(),
            &simulation.halt_agreement_proposition(model),
            "prefix simulation halt agreement",
        )?;
        require_same(
            simulation.step_preserves.proposition(),
            &simulation.step_preservation_proposition(model),
            "prefix simulation step preservation",
        )?;
        require_same(
            initial.proposition(),
            &Expr::apps(
                simulation.relation.clone(),
                [source_initial.clone(), core_initial.clone()],
            ),
            "prefix simulation initial relation",
        )?;
        let source_run = app(
            "ir_drive_v1",
            [
                simulation.source_type.clone(),
                simulation.source_halted.clone(),
                simulation.source_step.clone(),
                fuel.term().clone(),
                source_initial.clone(),
            ],
        );
        let proposition = Expr::apps(
            simulation.relation.clone(),
            [source_run, model.run(fuel, core_initial.clone())],
        );
        let helper = Closed {
            depth: 0,
            assembler: Some(self),
        }
        .theorem()?;
        let term = Expr::apps(
            helper,
            simulation.arguments(model).into_iter().chain([
                simulation.halt_agrees.term().clone(),
                simulation.step_preserves.term().clone(),
                fuel.term().clone(),
                source_initial,
                core_initial,
                initial.term().clone(),
            ]),
        );
        Ok(PendingProof::candidate(proposition, term))
    }
}

// Absolute positions of the fixed generic telescope. Each binder is built
// with its actual depth; no caller expression occurs inside this template.
const S: u32 = 0;
const C: u32 = 1;
const HS: u32 = 2;
const HC: u32 = 3;
const SS: u32 = 4;
const CS: u32 = 5;
const R: u32 = 6;
const HALT: u32 = 7;
const STEP: u32 = 8;

struct Closed<'a, 'scope> {
    depth: u32,
    assembler: Option<&'a mut Assembler<'scope>>,
}

#[derive(Clone, Copy)]
enum Template {
    Halt,
    Step,
}

fn template(kind: Template) -> Expr {
    // Pure, fixed-size proposition construction, just like MachineModel::run.
    // Actual proof assembly uses the SAME builder with caller-owned charges.
    Closed {
        depth: 0,
        assembler: None,
    }
    .parameters(7, |b| match kind {
        Template::Halt => b.halt_type(),
        Template::Step => b.step_type(),
    })
    .expect("fixed proposition telescope has no fallible allocator")
}

impl Closed<'_, '_> {
    fn v(&self, slot: u32) -> Expr {
        Expr::bvar(
            self.depth
                .checked_sub(slot + 1)
                .expect("fixed telescope slot is bound"),
        )
    }

    fn bind(
        &mut self,
        ty: Expr,
        pi: bool,
        body: impl FnOnce(&mut Self) -> Result<Expr>,
    ) -> Result<Expr> {
        if let Some(assembler) = &mut self.assembler {
            assembler.charge()?;
        }
        self.depth += 1;
        let result = body(self);
        self.depth -= 1;
        result.map(|value| {
            if pi {
                Expr::pi(BinderInfo::Default, ty, value)
            } else {
                Expr::lam(BinderInfo::Default, ty, value)
            }
        })
    }
    fn lam(&mut self, ty: Expr, body: impl FnOnce(&mut Self) -> Result<Expr>) -> Result<Expr> {
        self.bind(ty, false, body)
    }
    fn pi(&mut self, ty: Expr, body: impl FnOnce(&mut Self) -> Result<Expr>) -> Result<Expr> {
        self.bind(ty, true, body)
    }
    fn arrow(&mut self, from: u32, to: Option<u32>) -> Result<Expr> {
        self.pi(self.v(from), |b| {
            Ok(to.map_or_else(|| constant("Bool"), |slot| b.v(slot)))
        })
    }
    fn related(&self, s: Expr, c: Expr) -> Expr {
        Expr::apps(self.v(R), [s, c])
    }
    fn drive(&self, core: bool, fuel: Expr, initial: Expr) -> Expr {
        let (ty, halted, step) = if core { (C, HC, CS) } else { (S, HS, SS) };
        app(
            "ir_drive_v1",
            [self.v(ty), self.v(halted), self.v(step), fuel, initial],
        )
    }
    fn parameters(
        &mut self,
        end: u32,
        finish: impl FnOnce(&mut Self) -> Result<Expr>,
    ) -> Result<Expr> {
        if self.depth == end {
            return finish(self);
        }
        let ty = match self.depth {
            S | C => Expr::type_(),
            HS => self.arrow(S, None)?,
            HC => self.arrow(C, None)?,
            SS => self.arrow(S, Some(S))?,
            CS => self.arrow(C, Some(C))?,
            R => self.pi(self.v(S), |b| {
                b.pi(b.v(C), |_| Ok(Expr::sort(Level::zero())))
            })?,
            HALT => self.halt_type()?,
            STEP => self.step_type()?,
            9 => constant("Nat"),
            10 => self.v(S),
            11 => self.v(C),
            12 => self.related(self.v(10), self.v(11)),
            _ => unreachable!("fixed prefix telescope"),
        };
        self.lam(ty, |b| b.parameters(end, finish))
    }
    fn halt_type(&mut self) -> Result<Expr> {
        let s = self.depth;
        let c = s + 1;
        self.pi(self.v(S), |b| {
            b.pi(b.v(C), |b| {
                b.pi(b.related(b.v(s), b.v(c)), |b| {
                    Ok(eq(
                        &constant("Bool"),
                        Expr::app(b.v(HS), b.v(s)),
                        Expr::app(b.v(HC), b.v(c)),
                    ))
                })
            })
        })
    }
    fn step_type(&mut self) -> Result<Expr> {
        let s = self.depth;
        let c = s + 1;
        self.pi(self.v(S), |b| {
            b.pi(b.v(C), |b| {
                b.pi(b.related(b.v(s), b.v(c)), |b| {
                    b.pi(
                        eq(
                            &constant("Bool"),
                            Expr::app(b.v(HS), b.v(s)),
                            constant("Bool.false"),
                        ),
                        |b| Ok(b.related(Expr::app(b.v(SS), b.v(s)), Expr::app(b.v(CS), b.v(c)))),
                    )
                })
            })
        })
    }
    fn all_related(&mut self, k: u32) -> Result<Expr> {
        let s = self.depth;
        let c = s + 1;
        self.pi(self.v(S), |b| {
            b.pi(b.v(C), |b| {
                b.pi(b.related(b.v(s), b.v(c)), |b| {
                    Ok(b.related(
                        b.drive(false, b.v(k), b.v(s)),
                        b.drive(true, b.v(k), b.v(c)),
                    ))
                })
            })
        })
    }
    fn choice(&mut self, core: bool, k: u32, initial: u32, flag: Expr) -> Result<Expr> {
        let (ty, step) = if core { (C, CS) } else { (S, SS) };
        let motive = self.lam(constant("Bool"), |b| Ok(b.v(ty)))?;
        Ok(Expr::apps(
            Expr::const_(
                Name::from_string("Bool.rec"),
                vec![Level::succ(Level::zero())],
            ),
            [
                motive,
                self.drive(core, self.v(k), Expr::app(self.v(step), self.v(initial))),
                self.v(initial),
                flag,
            ],
        ))
    }
    fn chosen_relation(&mut self, k: u32, s: u32, c: u32, flag: u32) -> Result<Expr> {
        let source = self.choice(false, k, s, self.v(flag))?;
        let core = self.choice(true, k, c, self.v(flag))?;
        Ok(self.related(source, core))
    }
    fn theorem(&mut self) -> Result<Expr> {
        self.parameters(13, |b| b.induction())
    }
    fn induction(&mut self) -> Result<Expr> {
        let k = self.depth;
        let motive = self.lam(constant("Nat"), |b| b.all_related(k))?;
        let s = self.depth;
        let c = s + 1;
        let h = s + 2;
        let zero = self.lam(self.v(S), |b| {
            b.lam(b.v(C), |b| b.lam(b.related(b.v(s), b.v(c)), |b| Ok(b.v(h))))
        })?;
        let ih = k + 1;
        let successor = self.lam(constant("Nat"), |b| {
            let ih_type = b.all_related(k)?;
            b.lam(ih_type, |b| {
                let s = b.depth;
                let c = s + 1;
                let h = s + 2;
                b.lam(b.v(S), |b| {
                    b.lam(b.v(C), |b| {
                        b.lam(b.related(b.v(s), b.v(c)), |b| b.successor(k, ih, s, c, h))
                    })
                })
            })
        })?;
        let induction = Expr::apps(
            Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            [motive, zero, successor, self.v(9)],
        );
        Ok(Expr::apps(induction, [self.v(10), self.v(11), self.v(12)]))
    }
    fn successor(&mut self, k: u32, ih: u32, s: u32, c: u32, h: u32) -> Result<Expr> {
        let flag = self.depth;
        let motive = self.lam(constant("Bool"), |b| {
            b.pi(
                eq(&constant("Bool"), Expr::app(b.v(HS), b.v(s)), b.v(flag)),
                |b| b.chosen_relation(k, s, c, flag),
            )
        })?;
        let witness = self.depth;
        let no = self.lam(
            eq(
                &constant("Bool"),
                Expr::app(self.v(HS), self.v(s)),
                constant("Bool.false"),
            ),
            |b| {
                Ok(Expr::apps(
                    b.v(ih),
                    [
                        Expr::app(b.v(SS), b.v(s)),
                        Expr::app(b.v(CS), b.v(c)),
                        Expr::apps(b.v(STEP), [b.v(s), b.v(c), b.v(h), b.v(witness)]),
                    ],
                ))
            },
        )?;
        let yes = self.lam(
            eq(
                &constant("Bool"),
                Expr::app(self.v(HS), self.v(s)),
                constant("Bool.true"),
            ),
            |b| Ok(b.v(h)),
        )?;
        let by_flag = Expr::apps(
            Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
            [
                motive,
                no,
                yes,
                Expr::app(self.v(HS), self.v(s)),
                refl(&constant("Bool"), Expr::app(self.v(HS), self.v(s))),
            ],
        );
        let transport = self.lam(constant("Bool"), |b| {
            let source = b.drive(false, app("Nat.succ", [b.v(k)]), b.v(s));
            let core = b.choice(true, k, c, b.v(flag))?;
            Ok(b.related(source, core))
        })?;
        Ok(Expr::apps(
            Expr::const_(
                Name::from_string("Eq.subst"),
                vec![Level::succ(Level::zero())],
            ),
            [
                constant("Bool"),
                transport,
                Expr::app(self.v(HS), self.v(s)),
                Expr::app(self.v(HC), self.v(c)),
                Expr::apps(self.v(HALT), [self.v(s), self.v(c), self.v(h)]),
                by_flag,
            ],
        ))
    }
}
