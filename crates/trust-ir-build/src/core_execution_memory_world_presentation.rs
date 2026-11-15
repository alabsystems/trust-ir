// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Closed candidate for the existing ByteV1 memory-replacement presentation.
//! The actual host type, world and replacement memory are arguments, not captured
//! source locals, a new evaluator, allocation evidence or proof authority.

use super::*;
use clean_kernel::BinderInfo;

fn endpoints(world_type: Expr, world: Expr, memory: Expr) -> (Expr, Expr, Expr) {
    let project = |field: &str| {
        app(
            &format!("ir_byte_world_{field}_v1"),
            [world_type.clone(), world.clone()],
        )
    };
    (
        app("IRByteWorldV1", [world_type.clone()]),
        app(
            "ir_byte_with_memory_v1",
            [world_type.clone(), world.clone(), memory.clone()],
        ),
        app(
            "IRByteWorldV1.mk",
            [
                world_type.clone(),
                memory,
                project("host"),
                project("owners"),
                project("next"),
            ],
        ),
    )
}

pub(super) fn replace(
    assembler: &mut Assembler<'_>,
    model: &MachineModel,
    world: &Expr,
    memory: Expr,
) -> Result<PendingEquality> {
    // The public door stays paid before helper construction or any refusal.
    assembler.charge()?;
    let (ty, left, right) = endpoints(model.world_type.clone(), world.clone(), memory.clone());
    let term = if calling::is_explicit_world(model, world) {
        refl(&ty, right.clone())
    } else {
        Expr::apps(
            assembler.memory_world_presentation_candidate()?,
            [model.world_type.clone(), world.clone(), memory],
        )
    };
    Ok(PendingEquality::candidate(ty, left, right, term))
}

impl Assembler<'_> {
    fn memory_world_presentation_candidate(&mut self) -> Result<Expr> {
        if let Some(candidate) = &self.memory_world_presentation_candidate {
            return Ok(candidate.clone());
        }
        // Three input lambdas, one motive and four constructor-case lambdas.
        // These eight actual closed binders consume construction work, but no
        // caller Scope local. Partial charged construction is never published.
        for _ in 0..8 {
            self.charge()?;
        }
        // Under W / world / replacement: W=#2, world=#1, replacement=#0.
        // The motive adds its own world: W=#3, replacement=#1, world=#0.
        let (ty, left, right) = endpoints(Expr::bvar(3), Expr::bvar(0), Expr::bvar(1));
        let motive = Expr::lam(
            BinderInfo::Default,
            app("IRByteWorldV1", [Expr::bvar(2)]),
            eq(&ty, left, right),
        );
        // Under old-memory / host / owners / next: W=#6, replacement=#4.
        let rebuilt = app(
            "IRByteWorldV1.mk",
            [
                Expr::bvar(6),
                Expr::bvar(4),
                Expr::bvar(2),
                Expr::bvar(1),
                Expr::bvar(0),
            ],
        );
        let minor = [
            constant("IRByteMemoryV1"),
            Expr::bvar(3),
            app("IRList", [constant("Nat")]),
            constant("Nat"),
        ]
        .into_iter()
        .rev()
        .fold(
            refl(&app("IRByteWorldV1", [Expr::bvar(6)]), rebuilt),
            |body, ty| Expr::lam(BinderInfo::Default, ty, body),
        );
        let (ty, left, right) = endpoints(Expr::bvar(2), Expr::bvar(1), Expr::bvar(0));
        let term = Expr::apps(
            Expr::const_(Name::from_string("IRByteWorldV1.rec"), vec![Level::zero()]),
            [Expr::bvar(2), motive, minor, Expr::bvar(1)],
        );
        // Retain the original and requested exact complete equality as typed
        // declarations ONCE in the closed template, not at every application.
        let raw = PendingEquality::candidate(ty, left.clone(), right.clone(), term);
        let presented = self.ascribe_preserving_endpoints(raw, left, right)?;
        let template = [
            Expr::type_(),
            app("IRByteWorldV1", [Expr::bvar(0)]),
            constant("IRByteMemoryV1"),
        ]
        .into_iter()
        .rev()
        .fold(presented.term, |body, ty| {
            Expr::lam(BinderInfo::Default, ty, body)
        });
        let closed = self
            .scope
            .close(&template)
            .map_err(|error| error.to_string())?;
        self.memory_world_presentation_candidate = Some(closed.clone());
        Ok(closed)
    }
}
