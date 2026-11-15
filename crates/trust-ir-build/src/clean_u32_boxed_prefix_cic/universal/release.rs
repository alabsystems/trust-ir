// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
use super::*;
pub(super) fn release(
    asm: &mut Assembler<'_>,
    shape: &Shape,
    model: &MachineModel,
    current: &Current,
    before: &PendingEquality,
    payload: Expr,
    bound: Expr,
    index: usize,
) -> Result<(PendingEquality, Current, PendingEquality), String> {
    let flags = if index == 0 {
        (true, true)
    } else {
        (false, true)
    };
    let after = Current {
        frame: app("ir_frame_advance", [current.frame.clone()]),
        ..current.clone()
    };
    let start = shape.state(current.running(model), flags.0, flags.1);
    let expected = shape.state(after.running(model), false, index == 0);
    let word = app("ir_clean_tag32_encode_v1", [payload.clone()]);
    let tagged = app("ir_clean_tag32_encoded_domain_v1", [payload, bound]);
    let bad_field = app(
        "ir_clean_tag32_fault_v1",
        [
            shape.world_type.clone(),
            current.world.clone(),
            boolean(flags.0),
            boolean(flags.1),
        ],
    );
    let inner = app(
        "ir_byte_case_true_v1",
        [
            shape.state_type(),
            app("ir_clean_tag32_word_v1", [word]),
            bad_field,
            expected.clone(),
            expected.clone(),
            tagged,
            refl(shape.state_type(), expected.clone()),
        ],
    );
    let bad_addr = shape.state(
        app(
            "IRByteConfigV1.halted",
            [
                shape.world_type.clone(),
                app("IROutcome.type_error", [c("IRFault.bad_addr")]),
                current.world.clone(),
            ],
        ),
        flags.0,
        flags.1,
    );
    let fetch = app(
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
            boolean(flags.0),
            boolean(flags.1),
        ],
    );
    let proof = app(
        "ir_byte_case_true_v1",
        [
            shape.state_type(),
            current.valid(model),
            bad_addr,
            fetch,
            expected.clone(),
            before.term().clone(),
            inner,
        ],
    );
    let step = PendingEquality::candidate(shape.state_type(), shape.step(start), expected, proof);
    let valid = asm.convert_endpoints(before.clone(), after.valid(model), c("Bool.true"))?;
    Ok((step, after, valid))
}
