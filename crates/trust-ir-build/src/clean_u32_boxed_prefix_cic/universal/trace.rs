// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Private same-ledger initialized prefix data; candidates confer no authority.
use super::*;

pub(crate) struct OpenPrefixTrace {
    pub(crate) initial: PendingEquality,
    pub(crate) states: Vec<Expr>,
    pub(crate) steps: Vec<PendingEquality>,
    pub(crate) current: Current,
    pub(crate) valid: PendingEquality,
}

/// Reuse the actual four-node prefix construction in the caller's ONE ledger
/// and scope. No public constructor/provider/environment premise is introduced.
pub(crate) fn initialized_trace(
    source: &CheckedSourceValueOperational<'_>,
    wrapper: FuncId,
    asm: &mut Assembler<'_>,
    catalog: &mut Catalog<'_, '_>,
    world_type: Expr,
    memory: Expr,
    host: Expr,
    payloads: [Expr; 2],
    bounds: [Expr; 2],
    memory_admission: PendingEquality,
) -> Result<OpenPrefixTrace, String> {
    let prepared = prepare_tagged_u32_boxed_prefix(source, wrapper).map_err(|e| e.to_string())?;
    let body = &prepared.wrapper().blocks[0];
    let shape = Shape {
        context: source.context().clone(),
        world_type: world_type.clone(),
        wrapper,
        block: body.id,
        unbox: prepared.unbox_id(),
        parameters: [body.params[0].0, body.params[1].0],
    };
    let model = MachineModel::new(
        world_type.clone(),
        source.reflected(),
        app(
            "ir_clean_tag32_provider_v1",
            [
                world_type.clone(),
                nat(u64::from(prepared.unbox_id().index())),
            ],
        ),
    );
    let entry = catalog.entry(wrapper)?;
    let pointers = payloads
        .clone()
        .map(|n| app("IRScalar.ptr_", [app("ir_clean_tag32_encode_v1", [n])]));
    let arguments = list("IRScalar", pointers.clone());
    let fits = [
        pointer_fit(&shape, payloads[0].clone(), bounds[0].clone()),
        pointer_fit(&shape, payloads[1].clone(), bounds[1].clone()),
    ];
    let admitted = and(fits[0].clone(), and(fits[1].clone(), true_value()));
    let admitted = asm.convert_endpoints(
        admitted,
        entry.admission(&model, arguments.clone())?,
        c("Bool.true"),
    )?;
    let initialized = entry.initialize(
        asm,
        &model,
        arguments.clone(),
        memory.clone(),
        host.clone(),
        memory_admission,
        admitted,
    )?;
    let initial = asm.congruence(initialized.equality().clone(), shape.state_type(), |cfg| {
        shape.state(cfg, true, true)
    })?;
    let actual_init = app(
        "ir_clean_tag32_init_v1",
        [
            world_type.clone(),
            shape.context.clone(),
            nat(u64::from(wrapper.index())),
            arguments,
            memory.clone(),
            host.clone(),
        ],
    );
    let initial = asm.convert_endpoints(
        initial,
        actual_init,
        shape.state(initialized.current().running(&model), true, true),
    )?;
    let mut current = initialized.current().clone();
    let mut before = initialized.valid().clone();
    let mut states = vec![shape.state(current.running(&model), true, true)];
    let mut steps = vec![];
    for i in 0..2 {
        let site = catalog.fetch(Coordinate {
            function: wrapper,
            block: body.id,
            instruction: i,
        })?;
        let target = catalog.call_target(prepared.unbox_id())?;
        let args = list("IRScalar", [pointers[i].clone()]);
        let result = ImportResult {
            values: list("IRScalar", [app("IRScalar.int_", [payloads[i].clone()])]),
            memory: memory.clone(),
            host: host.clone(),
        };
        let checks = site.import_result_checks(&model, &target, &current, &result)?;
        let resolved = asm.conversion(
            app("IRList", [c("IRScalar")]),
            app(
                "ir_resolve",
                [
                    current.machine(),
                    list("Nat", [nat(u64::from(shape.parameters[i].index()))]),
                ],
            ),
            args.clone(),
        )?;
        let imported = asm.conversion(c("Bool"), checks.imported, c("Bool.true"))?;
        let arg_fit = and(fits[i].clone(), true_value());
        let admitted = asm.convert_endpoints(
            arg_fit,
            target.admission(&model, &site, args.clone()),
            c("Bool.true"),
        )?;
        let provided = PendingEquality::candidate(
            app("IRByteImportResultV1", [world_type.clone()]),
            site.import_provider_call(&model, &target, &current, args)?,
            result.provider_result(&model),
            app(
                "ir_clean_tag32_provider_encoded_v1",
                [
                    world_type.clone(),
                    nat(u64::from(prepared.unbox_id().index())),
                    payloads[i].clone(),
                    memory.clone(),
                    host.clone(),
                    bounds[i].clone(),
                ],
            ),
        );
        let owners = memory_owners(&model, &current, &before);
        let owners = asm.convert_endpoints(owners, checks.memory_owners, c("Bool.true"))?;
        let arity = asm.conversion(c("Bool"), checks.arity, c("Bool.true"))?;
        let fit = PendingEquality::candidate(
            c("Bool"),
            app("ir_nat_ltb", [payloads[i].clone(), nat(4294967296)]),
            c("Bool.true"),
            app(
                "ir_byte_ltb_of_lt_v1",
                [payloads[i].clone(), nat(4294967296), bounds[i].clone()],
            ),
        );
        let typed = asm.convert_endpoints(and(fit, true_value()), checks.typed, c("Bool.true"))?;
        let transfer = site.import_return(
            asm,
            &model,
            &target,
            &current,
            &result,
            ImportPremises {
                resolved,
                imported,
                admitted,
                provided,
                memory_owners: owners,
                arity,
                typed,
                before: before.clone(),
            },
        )?;
        let next = shape.state(transfer.current().running(&model), true, true);
        let lifted = call::lift(
            asm,
            &shape,
            &model,
            &current,
            &before,
            transfer.step(),
            transfer.current().running(&model),
        )?;
        steps.push(lifted);
        states.push(next);
        current = transfer.current().clone();
        before = transfer.valid().clone();
    }
    for i in 0..2 {
        let (step, next, valid) = release(
            asm,
            &shape,
            &model,
            &current,
            &before,
            payloads[i].clone(),
            bounds[i].clone(),
            i,
        )?;
        steps.push(step);
        current = next;
        before = valid;
        states.push(shape.state(current.running(&model), false, i == 0));
    }
    Ok(OpenPrefixTrace {
        initial,
        states,
        steps,
        current,
        valid: before,
    })
}
