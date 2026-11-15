// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Typed memory replacement through an existing equality. Actual type/memory
//! operands remain outside closed binders; no caller local or premise is added.

use super::*;

pub(super) fn replace_memory(
    assembler: &mut Assembler<'_>,
    world_type: &Expr,
    equality: PendingEquality,
    memory: Expr,
) -> Result<PendingEquality> {
    let [left, right] = [equality.left.clone(), equality.right.clone()].map(|world| {
        app(
            "ir_byte_with_memory_v1",
            [world_type.clone(), world, memory.clone()],
        )
    });
    // Under U / memory / world: U=#2, memory=#1, world=#0. The dependent
    // world domain is beneath U / memory only, so its U is #1. Apply actual
    // operands outside ALL three binders, including any external loose BVars.
    let closed = [
        Expr::type_(),
        constant("IRByteMemoryV1"),
        app("IRByteWorldV1", [Expr::bvar(1)]),
    ]
    .into_iter()
    .rev()
    .fold(
        app(
            "ir_byte_with_memory_v1",
            [Expr::bvar(2), Expr::bvar(0), Expr::bvar(1)],
        ),
        |body, ty| Expr::lam(clean_kernel::BinderInfo::Default, ty, body),
    );
    let mapped = assembler.congruence_function(
        equality,
        app("IRByteWorldV1", [world_type.clone()]),
        Expr::apps(closed, [world_type.clone(), memory]),
    )?;
    // Preserve the original direct endpoints and the existing second charge.
    // Neither candidate operation confers checking or world-validity authority.
    assembler.convert_endpoints(mapped, left, right)
}
