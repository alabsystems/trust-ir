// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof-relevant presentation changes at actual execution boundaries.
//!
//! Normalizing a returned frame does not execute an instruction or restore an
//! earlier world. The equality remains an untrusted candidate, checked with
//! the complete consuming program. Actual environments, memories and proofs
//! are arguments to shared closed helpers, never captured under a fresh helper
//! binder at every instruction boundary.

use super::*;

/// The same running configuration with an explicitly equal frame presentation.
/// Tail, legacy fields and the complete world are retained verbatim.
pub struct FrameTransport {
    current: Current,
    configuration: PendingEquality,
    valid: PendingEquality,
}

impl FrameTransport {
    pub fn current(&self) -> &Current {
        &self.current
    }

    /// Eq Config (actual old running configuration) (new presentation).
    pub fn configuration(&self) -> &PendingEquality {
        &self.configuration
    }

    /// New validity, derived from frame equality and actual old validity.
    pub fn valid(&self) -> &PendingEquality {
        &self.valid
    }
}

impl Assembler<'_> {
    /// Present a definitionally equal reached configuration without composing
    /// another execution step. The original equality and the requested one
    /// both remain explicit typed declarations for independent strict replay.
    ///
    /// This is an untrusted conversion candidate, not a frame equality or a
    /// new run. The model, providers, original initial configuration and exact
    /// fuel are retained verbatim. Non-convertible endpoints must still use
    /// [`Self::transport_reached`] with their actual equality proof.
    /// Construction costs one operation and no temporary scoped locals.
    pub fn ascribe_reached(&mut self, run: ExactRun, reached: Expr) -> Result<ExactRun> {
        let left = run.equality.left.clone();
        let equality = self.ascribe_preserving_endpoints(run.equality, left, reached.clone())?;
        ExactRun::candidate(run.model, run.initial, reached, run.fuel, equality)
    }

    /// Change only an exact run's reached presentation. Its original model,
    /// providers, initial configuration and exact fuel remain unchanged.
    /// A different or reversed boundary requires its own explicit transport.
    pub fn transport_reached(
        &mut self,
        run: ExactRun,
        reached: PendingEquality,
    ) -> Result<ExactRun> {
        self.charge()?;
        reached.endpoints(&run.model.config_type(), &run.reached, &reached.right)?;
        let equality = self.compose(run.equality, reached)?;
        ExactRun::candidate(
            run.model,
            run.initial,
            equality.right.clone(),
            run.fuel,
            equality,
        )
    }

    /// Transport the ACTUAL current frame using Eq IRFrame current.frame new.
    /// This supplies neither frame normalization nor its proof. In particular
    /// it cannot replace returned SSA bindings with a desired saved frame.
    pub fn transport_frame(
        &mut self,
        model: &MachineModel,
        current: &Current,
        frame: PendingEquality,
        before: PendingEquality,
    ) -> Result<FrameTransport> {
        self.charge()?;
        frame.endpoints(&constant("IRFrame"), &current.frame, &frame.right)?;
        before.endpoints(
            &constant("Bool"),
            &current.valid(model),
            &constant("Bool.true"),
        )?;
        let after = Current {
            frame: frame.right.clone(),
            ..current.clone()
        };
        let (configuration_helper, valid_helper) = self.frame_transport_candidates()?;
        let arguments = [
            model.world_type.clone(),
            current.frame.clone(),
            frame.right,
            current.tail.clone(),
            current.legacy_memory.clone(),
            current.legacy_cursor.clone(),
            current.world.clone(),
            frame.term,
        ];
        let configuration = PendingEquality::candidate(
            model.config_type(),
            current.running(model),
            after.running(model),
            Expr::apps(configuration_helper, arguments.iter().cloned()),
        );
        let valid = PendingEquality::candidate(
            constant("Bool"),
            after.valid(model),
            constant("Bool.true"),
            Expr::apps(valid_helper, arguments.into_iter().chain([before.term])),
        );
        Ok(FrameTransport {
            current: after,
            configuration,
            valid,
        })
    }

    fn frame_transport_candidates(&mut self) -> Result<(Expr, Expr)> {
        if let Some(helpers) = &self.frame_transport_candidates {
            return Ok(helpers.clone());
        }
        let world_type = self.local(Expr::type_())?;
        let old_frame = self.local(constant("IRFrame"))?;
        let new_frame = self.local(constant("IRFrame"))?;
        let tail = self.local(app("IRList", [constant("IRFrame")]))?;
        let legacy_memory = self.local(app("IRList", [constant("IRMemSlot")]))?;
        let legacy_cursor = self.local(constant("Nat"))?;
        let world = self.local(app("IRByteWorldV1", [world_type.term().clone()]))?;
        let frame_type = constant("IRFrame");
        let same_frame = self.local(eq(
            &frame_type,
            old_frame.term().clone(),
            new_frame.term().clone(),
        ))?;
        let current = |frame| Current {
            frame,
            tail: tail.term().clone(),
            legacy_memory: legacy_memory.term().clone(),
            legacy_cursor: legacy_cursor.term().clone(),
            world: world.term().clone(),
        };
        // These two projections depend only on W, not on a module/provider.
        // State that smaller contract explicitly in the closed helpers.
        let configuration_type = app("IRByteConfigV1", [world_type.term().clone()]);
        let running = |frame| {
            app(
                "IRByteConfigV1.running",
                [
                    world_type.term().clone(),
                    current(frame).machine(),
                    world.term().clone(),
                ],
            )
        };
        let validity = |frame| {
            app(
                "ir_byte_world_valid_v1",
                [
                    world_type.term().clone(),
                    current(frame).machine(),
                    world.term().clone(),
                ],
            )
        };
        let before = self.local(eq(
            &constant("Bool"),
            validity(old_frame.term().clone()),
            constant("Bool.true"),
        ))?;
        let frame = PendingEquality::candidate(
            frame_type,
            old_frame.term().clone(),
            new_frame.term().clone(),
            same_frame.term().clone(),
        );
        let configuration = self.congruence(frame.clone(), configuration_type, running)?;
        let guard = self.congruence(frame, constant("Bool"), validity)?;
        let reverse_guard = Expr::apps(
            Expr::const_(
                Name::from_string("Eq.symm"),
                vec![Level::succ(Level::zero())],
            ),
            [
                constant("Bool"),
                guard.left.clone(),
                guard.right.clone(),
                guard.term,
            ],
        );
        let valid = trans(
            &constant("Bool"),
            guard.right,
            guard.left,
            constant("Bool.true"),
            reverse_guard,
            before.term().clone(),
        );
        let parameters = [
            world_type,
            old_frame,
            new_frame,
            tail,
            legacy_memory,
            legacy_cursor,
            world,
            same_frame,
        ];
        let close = |proof| {
            let proof = parameters.iter().rev().fold(proof, |body, p| p.lam(body));
            self.scope.close(&proof).map_err(|error| error.to_string())
        };
        let helpers = (close(configuration.term)?, close(before.lam(valid))?);
        self.frame_transport_candidates = Some(helpers.clone());
        Ok(helpers)
    }
}

#[cfg(test)]
#[path = "core_execution_transport_tests.rs"]
mod tests;
