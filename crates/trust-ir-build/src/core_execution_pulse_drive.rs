// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Connect the existing first-order pulse prefix with the existing fuel driver.
//! The proof is for every fuel and arbitrary pulse, including nontermination.
//! It supplies neither a terminating source witness nor any Core segment/halt.
//! All construction shares the caller's actual assembler/local budget.

use super::*;

/// Untrusted terms for the ordinary driver over `Sum State Done`.
/// `inl state` runs the supplied pulse; `inr done` is retained unchanged.
/// The final consumer must check the candidate under its original namespace.
#[derive(Clone)]
pub struct PulseDrive {
    state_type: Expr,
    done_type: Expr,
    pulse: Expr,
    source_type: Expr,
    halted: Expr,
    step: Expr,
}

impl PulseDrive {
    pub fn source_type(&self) -> &Expr {
        &self.source_type
    }
    pub fn source_halted(&self) -> &Expr {
        &self.halted
    }
    pub fn source_step(&self) -> &Expr {
        &self.step
    }

    pub fn initial(&self, state: Expr) -> Expr {
        self.side(false, state)
    }
    pub fn terminal(&self, done: Expr) -> Expr {
        self.side(true, done)
    }

    fn side(&self, terminal: bool, value: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string(if terminal { "Sum.inr" } else { "Sum.inl" }),
                vec![Level::zero(), Level::zero()],
            ),
            [self.state_type.clone(), self.done_type.clone(), value],
        )
    }

    /// The maintained first-order prefix, without inferring sufficient fuel.
    pub fn prefix(&self, fuel: &NatTerm, state: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string(crate::semantic_evaluation::LOOP_PREFIX),
                vec![Level::zero()],
            ),
            [
                self.state_type.clone(),
                self.done_type.clone(),
                self.pulse.clone(),
                fuel.term().clone(),
                state,
            ],
        )
    }

    pub fn run(&self, fuel: &NatTerm, subject: Expr) -> Expr {
        app(
            "ir_drive_v1",
            [
                self.source_type.clone(),
                self.halted.clone(),
                self.step.clone(),
                fuel.term().clone(),
                subject,
            ],
        )
    }

    fn cases(&self, motive: Expr, left: Expr, right: Expr, subject: Expr, prop: bool) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("Sum.rec"),
                vec![
                    if prop {
                        Level::zero()
                    } else {
                        Level::succ(Level::zero())
                    },
                    Level::zero(),
                    Level::zero(),
                ],
            ),
            [
                self.state_type.clone(),
                self.done_type.clone(),
                motive,
                left,
                right,
                subject,
            ],
        )
    }
}

impl Assembler<'_> {
    /// Construct the fixed Sum interpretation used by `ir_drive_v1`. State
    /// and Done inhabit Type0, exactly as SegmentedPrefixSimulation requires.
    /// No callback, completion premise or alternate evaluator is introduced.
    pub fn pulse_drive(
        &mut self,
        state_type: Expr,
        done_type: Expr,
        pulse: Expr,
    ) -> Result<PulseDrive> {
        self.charge()?;
        let source_type = Expr::apps(
            Expr::const_(Name::from_string("Sum"), vec![Level::zero(), Level::zero()]),
            [state_type.clone(), done_type.clone()],
        );
        let mut drive = PulseDrive {
            state_type,
            done_type,
            pulse,
            source_type,
            halted: constant("False"),
            step: constant("False"),
        };
        let subject = self.local(drive.source_type.clone())?;
        let ignored = self.local(drive.source_type.clone())?;
        let state = self.local(drive.state_type.clone())?;
        let done = self.local(drive.done_type.clone())?;
        drive.halted = subject.lam(drive.cases(
            ignored.lam(constant("Bool")),
            state.lam(constant("Bool.false")),
            done.lam(constant("Bool.true")),
            subject.term().clone(),
            false,
        ));
        let subject = self.local(drive.source_type.clone())?;
        let ignored = self.local(drive.source_type.clone())?;
        let state = self.local(drive.state_type.clone())?;
        let done = self.local(drive.done_type.clone())?;
        drive.step = subject.lam(drive.cases(
            ignored.lam(drive.source_type.clone()),
            state.lam(Expr::app(drive.pulse.clone(), state.term().clone())),
            done.lam(drive.terminal(done.term().clone())),
            subject.term().clone(),
            false,
        ));
        Ok(drive)
    }

    fn pulse_fold(&mut self, drive: &PulseDrive, fuel: &NatTerm, subject: Expr) -> Result<Expr> {
        let ignored = self.local(drive.source_type.clone())?;
        let state = self.local(drive.state_type.clone())?;
        let done = self.local(drive.done_type.clone())?;
        Ok(drive.cases(
            ignored.lam(drive.source_type.clone()),
            state.lam(drive.prefix(fuel, state.term().clone())),
            done.lam(drive.terminal(done.term().clone())),
            subject,
            false,
        ))
    }

    fn pulse_statement(
        &mut self,
        drive: &PulseDrive,
        fuel: &NatTerm,
        subject: Expr,
    ) -> Result<Expr> {
        let folded = self.pulse_fold(drive, fuel, subject.clone())?;
        Ok(eq(&drive.source_type, drive.run(fuel, subject), folded))
    }

    /// A Nat/Sum induction over the ORIGINAL two definitions. In the running
    /// case the induction hypothesis is applied to the actual `pulse state`;
    /// the terminal case retains that exact Done payload and consumes no step.
    fn pulse_induction(&mut self, drive: &PulseDrive, fuel: &NatTerm) -> Result<Expr> {
        let motive_n = self.local(constant("Nat"))?;
        let motive_p = self.local(drive.source_type.clone())?;
        let motive = motive_n.lam(motive_p.pi(self.pulse_statement(
            drive,
            &NatTerm(motive_n.term().clone()),
            motive_p.term().clone(),
        )?));

        let subject = self.local(drive.source_type.clone())?;
        let motive_p = self.local(drive.source_type.clone())?;
        let left = self.local(drive.state_type.clone())?;
        let right = self.local(drive.done_type.clone())?;
        let zero_motive =
            motive_p.lam(self.pulse_statement(drive, &NatTerm(nat(0)), motive_p.term().clone())?);
        let zero = subject.lam(drive.cases(
            zero_motive,
            left.lam(refl(&drive.source_type, drive.initial(left.term().clone()))),
            right.lam(refl(
                &drive.source_type,
                drive.terminal(right.term().clone()),
            )),
            subject.term().clone(),
            true,
        ));

        let previous = self.local(constant("Nat"))?;
        let ih_p = self.local(drive.source_type.clone())?;
        let induction_type = self.pulse_statement(
            drive,
            &NatTerm(previous.term().clone()),
            ih_p.term().clone(),
        )?;
        let induction = self.local(ih_p.pi(induction_type))?;
        let subject = self.local(drive.source_type.clone())?;
        let motive_p = self.local(drive.source_type.clone())?;
        let left = self.local(drive.state_type.clone())?;
        let right = self.local(drive.done_type.clone())?;
        let successor_fuel = NatTerm(app("Nat.succ", [previous.term().clone()]));
        let successor_motive =
            motive_p.lam(self.pulse_statement(drive, &successor_fuel, motive_p.term().clone())?);
        let running = left.lam(Expr::app(
            induction.term().clone(),
            Expr::app(drive.pulse.clone(), left.term().clone()),
        ));
        let terminal = right.lam(refl(
            &drive.source_type,
            drive.terminal(right.term().clone()),
        ));
        let successor = previous.lam(induction.lam(subject.lam(drive.cases(
            successor_motive,
            running,
            terminal,
            subject.term().clone(),
            true,
        ))));
        Ok(Expr::apps(
            Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            [motive, zero, successor, fuel.term().clone()],
        ))
    }

    /// Candidate of `drive k (inl state) = Loop.prefix pulse k state` for ANY
    /// k. No rank, completion, ready result or termination assumption is used.
    /// Installing the existing loop vocabulary and replaying this proof are
    /// the consumer's duties, just as for the existing simulation candidates.
    pub fn pulse_prefix_equality(
        &mut self,
        drive: &PulseDrive,
        fuel: &NatTerm,
        state: Expr,
    ) -> Result<PendingEquality> {
        self.charge()?;
        let proof = self.pulse_induction(drive, fuel)?;
        let initial = drive.initial(state.clone());
        Ok(PendingEquality::candidate(
            drive.source_type.clone(),
            drive.run(fuel, initial.clone()),
            drive.prefix(fuel, state),
            Expr::app(proof, initial),
        ))
    }

    /// The same induction retains a terminal payload for arbitrary fuel. This
    /// says nothing about whether a running pulse ever reaches that payload.
    pub fn pulse_terminal_equality(
        &mut self,
        drive: &PulseDrive,
        fuel: &NatTerm,
        done: Expr,
    ) -> Result<PendingEquality> {
        self.charge()?;
        let proof = self.pulse_induction(drive, fuel)?;
        let terminal = drive.terminal(done);
        Ok(PendingEquality::candidate(
            drive.source_type.clone(),
            drive.run(fuel, terminal.clone()),
            terminal.clone(),
            Expr::app(proof, terminal),
        ))
    }
}

#[cfg(test)]
#[path = "core_execution_pulse_drive_tests.rs"]
mod tests;
