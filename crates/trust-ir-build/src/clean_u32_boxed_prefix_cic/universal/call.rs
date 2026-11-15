// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Transfer the actual canonical import step into the named prefix profile.
use super::*;

pub(super) fn lift(
    asm: &mut Assembler<'_>,
    shape: &Shape,
    model: &MachineModel,
    current: &Current,
    before: &PendingEquality,
    byte_step: &PendingEquality,
    after: Expr,
) -> Result<PendingEquality, String> {
    let guard = current.valid(model);
    let bad = app(
        "IRByteConfigV1.halted",
        [
            shape.world_type.clone(),
            app("IROutcome.type_error", [c("IRFault.bad_addr")]),
            current.world.clone(),
        ],
    );
    let byte_fetch = app(
        "ir_byte_step_machine_v1",
        [
            shape.world_type.clone(),
            shape.context.clone(),
            model.providers().clone(),
            current.machine(),
            current.world.clone(),
        ],
    );
    // A constructor map cannot commute through an unknown Bool.rec by defeq.
    // Eliminate the ACTUAL canonical guard using the reached pre-state fact.
    let gate = PendingEquality::candidate(
        model.config_type(),
        model.step(current.running(model)),
        byte_fetch.clone(),
        app(
            "ir_byte_case_true_v1",
            [
                model.config_type(),
                guard.clone(),
                bad.clone(),
                byte_fetch.clone(),
                byte_fetch.clone(),
                before.term().clone(),
                refl(model.config_type(), byte_fetch.clone()),
            ],
        ),
    );
    let reverse = PendingEquality::candidate(
        model.config_type(),
        byte_fetch,
        gate.left().clone(),
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.symm"),
                vec![Level::succ(Level::zero())],
            ),
            [
                model.config_type(),
                gate.left().clone(),
                gate.right().clone(),
                gate.term().clone(),
            ],
        ),
    );
    let fetched_return = asm.compose(reverse, byte_step.clone())?;
    let wrapped = asm.congruence(fetched_return, shape.state_type(), |cfg| {
        shape.state(cfg, true, true)
    })?;
    let new_fetch = app(
        "ir_clean_tag32_fetch_v1",
        [
            shape.world_type.clone(),
            shape.context.clone(),
            nat(u64::from(shape.wrapper.index())),
            nat(u64::from(shape.block.index())),
            nat(u64::from(shape.unbox.index())),
            nat(u64::from(shape.parameters[0].index())),
            nat(u64::from(shape.parameters[1].index())),
            current.machine(),
            current.world.clone(),
            boolean(true),
            boolean(true),
        ],
    );
    let expected = shape.state(after, true, true);
    let inner = asm.convert_endpoints(wrapped, new_fetch.clone(), expected.clone())?;
    // Then eliminate the NEW profile's outer guard with the SAME fact. No
    // provider-equality assumption or successful post-state premise is added.
    let proof = app(
        "ir_byte_case_true_v1",
        [
            shape.state_type(),
            guard,
            shape.state(bad, true, true),
            new_fetch,
            expected.clone(),
            before.term().clone(),
            inner.term().clone(),
        ],
    );
    Ok(PendingEquality::candidate(
        shape.state_type(),
        shape.step(shape.state(current.running(model), true, true)),
        expected,
        proof,
    ))
}
