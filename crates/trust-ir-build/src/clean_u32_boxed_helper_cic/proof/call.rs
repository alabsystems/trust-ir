// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::core_execution::{ImportPremises, ImportResult, ImportTransfer, InternalCallPremises};
fn call_args(
    source: &CheckedSourceValueOperational<'_>,
    wrapper: FuncId,
    index: usize,
) -> Result<Vec<Expr>, String> {
    let prepared = prepare_tagged_u32_boxed_prefix(source, wrapper).map_err(|e| e.to_string())?;
    let node = prepared.wrapper().blocks[0]
        .body
        .get(index)
        .ok_or("missing actual wrapper call")?;
    let trust_ir::Inst::Call { args, .. } = &node.inst else {
        return Err("wrapper position is not an actual call".into());
    };
    Ok(args.iter().map(|id| nat(id.index().into())).collect())
}
pub(super) fn enter(
    source: &CheckedSourceValueOperational<'_>,
    asm: &mut Assembler<'_>,
    catalog: &mut Catalog<'_, '_>,
    model: &MachineModel,
    shape: &Shape,
    current: &Current,
    valid: &PendingEquality,
    inputs: [Expr; 2],
) -> Result<crate::core_execution::InternalCallTransfer, String> {
    let site = catalog.fetch(Coordinate {
        function: shape.wrapper,
        block: shape.block,
        instruction: 4,
    })?;
    let target = catalog.internal_target(source.source_value().function().id)?;
    let nums = inputs.clone().map(u32_nat);
    let values = list("IRScalar", nums.clone().map(|n| app("IRScalar.int_", [n])));
    let checks = target.checks(model, &site, values.clone())?;
    let bounds = inputs.map(|x| {
        PendingProof::candidate(
            app("Nat.lt", [u32_nat(x.clone()), nat(4294967296)]),
            u32_bound(x),
        )
    });
    let admitted = asm.convert_endpoints(
        both(
            uint_fits(nums[0].clone(), &bounds[0]),
            both(uint_fits(nums[1].clone(), &bounds[1]), truth()),
        ),
        checks.admitted,
        boolean(true),
    )?;
    let resolved = asm.conversion(
        app("IRList", [c("IRScalar")]),
        app(
            "ir_resolve",
            [
                current.machine(),
                list("Nat", call_args(source, shape.wrapper, 4)?),
            ],
        ),
        values,
    )?;
    let local_binding = asm.conversion(c("Bool"), checks.local_binding, boolean(false))?;
    let arity = asm.conversion(c("Bool"), checks.arity, boolean(true))?;
    let dispatch = target.call_target().direct(asm, model, current, &site)?;
    site.call_internal(
        asm,
        model,
        &target,
        current,
        InternalCallPremises {
            dispatch,
            resolved,
            local_binding,
            arity,
            admitted,
            before: valid.clone(),
        },
    )
}
pub(super) fn box_result(
    source: &CheckedSourceValueOperational<'_>,
    asm: &mut Assembler<'_>,
    catalog: &mut Catalog<'_, '_>,
    shape: &Shape,
    model: &MachineModel,
    current: &Current,
    valid: &PendingEquality,
    value: Expr,
    bound: &PendingProof,
) -> Result<ImportTransfer, String> {
    let site = catalog.fetch(Coordinate {
        function: shape.wrapper,
        block: shape.block,
        instruction: 5,
    })?;
    let target = catalog.call_target(shape.boxer)?;
    let args = list("IRScalar", [app("IRScalar.int_", [value.clone()])]);
    let boxed = app(
        "IRScalar.ptr_",
        [app("ir_clean_tag32_encode_v1", [value.clone()])],
    );
    let memory = app(
        "ir_byte_world_memory_v1",
        [shape.world_type.clone(), current.world.clone()],
    );
    let host = app(
        "ir_byte_world_host_v1",
        [shape.world_type.clone(), current.world.clone()],
    );
    let result = ImportResult {
        values: list("IRScalar", [boxed]),
        memory: memory.clone(),
        host: host.clone(),
    };
    let checks = site.import_result_checks(model, &target, current, &result)?;
    // The fetched call's original argument IDs are extracted by the existing
    // catalog. Its resolved values are proved, not supplied as a premise.
    let resolved = asm.conversion(
        app("IRList", [c("IRScalar")]),
        app(
            "ir_resolve",
            [
                current.machine(),
                list("Nat", call_args(source, shape.wrapper, 5)?),
            ],
        ),
        args.clone(),
    )?;
    let imported = asm.conversion(c("Bool"), checks.imported, boolean(true))?;
    let admitted = asm.convert_endpoints(
        both(uint_fits(value.clone(), bound), truth()),
        target.admission(model, &site, args.clone()),
        boolean(true),
    )?;
    let provided = PendingEquality::candidate(
        app("IRByteImportResultV1", [shape.world_type.clone()]),
        site.import_provider_call(model, &target, current, args)?,
        result.provider_result(model),
        app(
            "ir_clean_tag32_helper_box_v1",
            [
                shape.world_type.clone(),
                nat(shape.unbox.index().into()),
                nat(shape.boxer.index().into()),
                value.clone(),
                memory,
                host,
                bound.term().clone(),
            ],
        ),
    );
    let owners = crate::clean_u32_boxed_prefix_cic::universal::memory_owners(model, current, valid);
    let memory_owners = asm.convert_endpoints(owners, checks.memory_owners, boolean(true))?;
    let arity = asm.conversion(c("Bool"), checks.arity, boolean(true))?;
    let typed = asm.convert_endpoints(
        both(pointer_fits(shape.context.clone(), value, bound), truth()),
        checks.typed,
        boolean(true),
    )?;
    site.import_return(
        asm,
        model,
        &target,
        current,
        &result,
        ImportPremises {
            resolved,
            imported,
            admitted,
            provided,
            memory_owners,
            arity,
            typed,
            before: valid.clone(),
        },
    )
}
