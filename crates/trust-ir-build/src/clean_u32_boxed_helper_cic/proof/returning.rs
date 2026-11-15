// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::core_execution::{ReturnTransfer, RootReturnFrame, RootReturnTransfer};
use crate::source_value_operational::contextual::ContextualBodyPrefix;
fn return_ids(source: &CheckedSourceValueOperational<'_>) -> Result<Vec<Expr>, String> {
    let f = source.source_value().function();
    let last = f
        .blocks
        .iter()
        .find(|b| b.id == f.entry)
        .and_then(|b| b.body.last())
        .ok_or("missing scalar Return")?;
    let trust_ir::Inst::Return { values } = &last.inst else {
        return Err("selected scalar last node is not Return".into());
    };
    Ok(values.iter().map(|id| nat(id.index().into())).collect())
}
pub(super) fn callee(
    source: &CheckedSourceValueOperational<'_>,
    asm: &mut Assembler<'_>,
    catalog: &mut Catalog<'_, '_>,
    model: &MachineModel,
    body: &ContextualBodyPrefix<'_, '_>,
) -> Result<ReturnTransfer, String> {
    let f = source.source_value().function();
    let index = source
        .instruction_count()
        .checked_sub(1)
        .ok_or("empty scalar")?;
    let site = catalog.fetch(Coordinate {
        function: f.id,
        block: f.entry,
        instruction: index,
    })?;
    let target = catalog.call_target(f.id)?;
    let values = list("IRScalar", [app("IRScalar.int_", [body.result().clone()])]);
    let resolved = asm.conversion(
        app("IRList", [c("IRScalar")]),
        app(
            "ir_resolve",
            [body.current().machine(), list("Nat", return_ids(source)?)],
        ),
        values.clone(),
    )?;
    let fits = both(
        both(
            uint_fits(body.result().clone(), body.result_bound()),
            truth(),
        ),
        truth(),
    );
    let admitted = asm.convert_endpoints(
        fits,
        site.return_admission(model, &target, body.return_frame(), values)?,
        boolean(true),
    )?;
    site.return_to_caller(
        asm,
        model,
        &target,
        body.return_frame(),
        resolved,
        admitted,
        body.valid().clone(),
    )
}
pub(super) fn root(
    source: &CheckedSourceValueOperational<'_>,
    asm: &mut Assembler<'_>,
    catalog: &mut Catalog<'_, '_>,
    shape: &Shape,
    model: &MachineModel,
    current: &Current,
    valid: &PendingEquality,
    value: Expr,
    bound: &PendingProof,
    owner: Expr,
) -> Result<RootReturnTransfer, String> {
    let site = catalog.fetch(Coordinate {
        function: shape.wrapper,
        block: shape.block,
        instruction: 6,
    })?;
    let target = catalog.call_target(shape.wrapper)?;
    let field = |name: &str| app(name, [shape.world_type.clone(), current.world.clone()]);
    let frame = RootReturnFrame {
        returning: current.frame.clone(),
        legacy_memory: current.legacy_memory.clone(),
        legacy_cursor: current.legacy_cursor.clone(),
        memory: field("ir_byte_world_memory_v1"),
        host: field("ir_byte_world_host_v1"),
        owner,
        next: field("ir_byte_world_next_v1"),
    };
    let values = list(
        "IRScalar",
        [app(
            "IRScalar.ptr_",
            [app("ir_clean_tag32_encode_v1", [value.clone()])],
        )],
    );
    let prepared =
        prepare_tagged_u32_boxed_prefix(source, shape.wrapper).map_err(|e| e.to_string())?;
    let trust_ir::Inst::Return { values: ids } = &prepared.wrapper().blocks[0].body[6].inst else {
        return Err("actual wrapper final node is not Return".into());
    };
    let resolved = asm.conversion(
        app("IRList", [c("IRScalar")]),
        app(
            "ir_resolve",
            [
                current.machine(),
                list("Nat", ids.iter().map(|id| nat(id.index().into()))),
            ],
        ),
        values.clone(),
    )?;
    let admitted = asm.convert_endpoints(
        both(
            both(pointer_fits(shape.context.clone(), value, bound), truth()),
            truth(),
        ),
        site.root_return_admission(model, &target, &frame, values)?,
        boolean(true),
    )?;
    let before = asm.convert_endpoints(
        valid.clone(),
        frame.current(model).valid(model),
        boolean(true),
    )?;
    site.return_from_root(asm, model, &target, &frame, resolved, admitted, before)
}
