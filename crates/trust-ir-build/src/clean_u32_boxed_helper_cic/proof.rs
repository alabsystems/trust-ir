// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
use super::{syntax::*, *};
use crate::core_execution::{
    Assembler, Catalog, Coordinate, Current, EntryTarget, MachineModel, PendingEquality,
    PendingProof,
};
use crate::scoped_local::LocalScope;
use clean_kernel::{BinderInfo, Level, Name};
mod call;
mod lift;
mod returning;
mod run;

pub(super) struct Candidates {
    pub(super) steps: usize,
    pub(super) prefixes: Vec<(Expr, Expr)>,
    pub(super) complete: (Expr, Expr),
}
struct Shape {
    world_type: Expr,
    context: Expr,
    wrapper: FuncId,
    block: trust_ir::BlockId,
    unbox: FuncId,
    boxer: FuncId,
    parameters: [trust_ir::ValueId; 2],
}
impl Shape {
    fn state_type(&self) -> Expr {
        app("IRCleanTag32PrefixV1", [self.world_type.clone()])
    }
    fn run_type(&self) -> Expr {
        app("IRCleanTag32HelperRunV1", [self.world_type.clone()])
    }
    fn state(&self, cfg: Expr, left: bool, right: bool) -> Expr {
        app(
            "IRCleanTag32PrefixV1.mk",
            [self.world_type.clone(), cfg, boolean(left), boolean(right)],
        )
    }
    fn args(&self) -> Vec<Expr> {
        vec![
            self.world_type.clone(),
            self.context.clone(),
            nat(self.wrapper.index().into()),
            nat(self.block.index().into()),
            nat(self.unbox.index().into()),
            nat(self.boxer.index().into()),
            nat(self.parameters[0].index().into()),
            nat(self.parameters[1].index().into()),
        ]
    }
    fn step(&self, state: Expr) -> Expr {
        let mut a = self.args();
        a.push(state);
        app("ir_clean_tag32_helper_step_v1", a)
    }
    fn run(&self, fuel: Expr, state: Expr) -> Expr {
        let mut a = self.args();
        a.extend([fuel, state]);
        app("ir_clean_tag32_helper_run_v1", a)
    }
    fn result(&self, state: Expr, remaining: Expr) -> Expr {
        app(
            "IRCleanTag32HelperRunV1.mk",
            [self.world_type.clone(), state, remaining],
        )
    }
    fn expected_final(&self, mem: Expr, host: Expr, result: Expr) -> Expr {
        let owner = app("ir_byte_fresh_owner_v1", [mem.clone()]);
        let nested = app(
            "ir_byte_retire_v1",
            [
                owner.clone(),
                app("ir_byte_retire_v1", [app("Nat.succ", [owner.clone()]), mem]),
            ],
        );
        let world = app(
            "IRByteWorldV1.mk",
            [
                self.world_type.clone(),
                nested,
                host,
                list("Nat", []),
                app("Nat.succ", [app("Nat.succ", [owner])]),
            ],
        );
        let outcome = app(
            "IROutcome.ret",
            [list(
                "IRScalar",
                [app(
                    "IRScalar.ptr_",
                    [app("ir_clean_tag32_encode_v1", [result])],
                )],
            )],
        );
        self.state(
            app(
                "IRByteConfigV1.halted",
                [self.world_type.clone(), outcome, world],
            ),
            false,
            false,
        )
    }
}

pub(super) fn derive(
    source: &CheckedSourceValueOperational<'_>,
    wrapper: FuncId,
    environment: &Environment,
    limits: Limits,
) -> Result<Candidates, String> {
    let prepared = prepare_tagged_u32_boxed_prefix(source, wrapper).map_err(|e| e.to_string())?;
    let block = &prepared.wrapper().blocks[0];
    let mut scope = LocalScope::new();
    let mut asm = Assembler::new(&mut scope, limits)?;
    let w = asm.local(Expr::type_())?;
    let mem = asm.local(c("IRByteMemoryV1"))?;
    let host = asm.local(w.term().clone())?;
    let x = asm.local(c("UInt32"))?;
    let y = asm.local(c("UInt32"))?;
    let hm = asm.local(equation(
        c("Bool"),
        EntryTarget::memory_admission(mem.term().clone()),
        boolean(true),
    ))?;
    let globals = [
        w.clone(),
        mem.clone(),
        host.clone(),
        x.clone(),
        y.clone(),
        hm.clone(),
    ];
    let shape = Shape {
        world_type: w.term().clone(),
        context: source.context().clone(),
        wrapper,
        block: block.id,
        unbox: prepared.unbox_id(),
        boxer: prepared.box_id(),
        parameters: [block.params[0].0, block.params[1].0],
    };
    let mut catalog = Catalog::new(environment, source.reflected(), limits)?;
    let trace = crate::clean_u32_boxed_prefix_cic::universal::initialized_trace(
        source,
        wrapper,
        &mut asm,
        &mut catalog,
        w.term().clone(),
        mem.term().clone(),
        host.term().clone(),
        [u32_nat(x.term().clone()), u32_nat(y.term().clone())],
        [u32_bound(x.term().clone()), u32_bound(y.term().clone())],
        PendingEquality::candidate(
            c("Bool"),
            EntryTarget::memory_admission(mem.term().clone()),
            boolean(true),
            hm.term().clone(),
        ),
    )
    .map_err(|e| format!("initialized prefix trace: {e}"))?;
    let mut states = trace.states;
    let mut steps = Vec::new();
    for (i, step) in trace.steps.into_iter().enumerate() {
        steps.push(asm.convert_endpoints(
            step,
            shape.step(states[i].clone()),
            states[i + 1].clone(),
        )?);
    }
    let initial = asm.convert_endpoints(
        trace.initial.clone(),
        app(
            "ir_clean_tag32_helper_init_v1",
            [
                w.term().clone(),
                shape.context.clone(),
                nat(wrapper.index().into()),
                list(
                    "IRScalar",
                    [
                        app(
                            "IRScalar.ptr_",
                            [app("ir_clean_tag32_encode_v1", [u32_nat(x.term().clone())])],
                        ),
                        app(
                            "IRScalar.ptr_",
                            [app("ir_clean_tag32_encode_v1", [u32_nat(y.term().clone())])],
                        ),
                    ],
                ),
                mem.term().clone(),
                host.term().clone(),
            ],
        ),
        states[0].clone(),
    )?;
    let model = MachineModel::new(
        w.term().clone(),
        source.reflected(),
        app(
            "ir_clean_tag32_helper_provider_v1",
            [
                w.term().clone(),
                nat(shape.unbox.index().into()),
                nat(shape.boxer.index().into()),
            ],
        ),
    );
    let entered = call::enter(
        source,
        &mut asm,
        &mut catalog,
        &model,
        &shape,
        &trace.current,
        &trace.valid,
        [x.term().clone(), y.term().clone()],
    )
    .map_err(|e| format!("actual call70 entry: {e}"))?;
    steps.push(lift::byte(
        &mut asm,
        &shape,
        &model,
        &trace.current,
        entered.step(),
    )?);
    states.push(shape.state(entered.current().running(&model), false, false));
    let body = crate::source_value_operational::contextual::body_after_call(
        source,
        &mut asm,
        &mut catalog,
        &model,
        &entered,
        x.term().clone(),
        y.term().clone(),
    )
    .map_err(|e| format!("actual scalar body: {e}"))?;
    for (i, step) in body.steps().iter().enumerate() {
        steps.push(lift::byte_state(
            &mut asm,
            &shape,
            &model,
            body.states()[i].clone(),
            step,
        )?);
        states.push(shape.state(body.states()[i + 1].clone(), false, false));
    }
    let returned = returning::callee(source, &mut asm, &mut catalog, &model, &body)
        .map_err(|e| format!("actual callee Return: {e}"))?;
    let one = asm.convert_endpoints(
        returned.run().equality().clone(),
        model.step(body.current().running(&model)),
        returned.resumed().running(&model),
    )?;
    steps.push(lift::byte(&mut asm, &shape, &model, body.current(), &one)?);
    states.push(shape.state(returned.resumed().running(&model), false, false));
    let boxed = call::box_result(
        source,
        &mut asm,
        &mut catalog,
        &shape,
        &model,
        returned.resumed(),
        returned.valid(),
        body.result().clone(),
        body.result_bound(),
    )
    .map_err(|e| format!("actual box import: {e}"))?;
    steps.push(lift::byte(
        &mut asm,
        &shape,
        &model,
        returned.resumed(),
        boxed.step(),
    )?);
    states.push(shape.state(boxed.current().running(&model), false, false));
    let root = returning::root(
        source,
        &mut asm,
        &mut catalog,
        &shape,
        &model,
        boxed.current(),
        boxed.valid(),
        body.result().clone(),
        body.result_bound(),
        app("ir_byte_fresh_owner_v1", [mem.term().clone()]),
    )
    .map_err(|e| format!("actual root Return: {e}"))?;
    let root_step = asm.convert_endpoints(
        root.run().equality().clone(),
        model.step(boxed.current().running(&model)),
        root.halted().clone(),
    )?;
    let last = lift::byte(&mut asm, &shape, &model, boxed.current(), &root_step)?;
    let bridge = asm.conversion(
        shape.state_type(),
        last.right().clone(),
        shape.expected_final(
            mem.term().clone(),
            host.term().clone(),
            body.result().clone(),
        ),
    )?;
    let last = asm
        .compose(last, bridge)
        .map_err(|e| format!("final world transport: {e}"))?;
    let eq = body.source_result_equation();
    let reversed = reverse(c("Nat"), eq);
    let mapped = asm.congruence(reversed, shape.state_type(), |v| {
        shape.expected_final(mem.term().clone(), host.term().clone(), v)
    })?;
    // Congruence deliberately retains beta-redex endpoints. Re-present them
    // explicitly, as the shared scalar mapped helper does; strict replay still
    // checks this conversion against the complete independent claim.
    let mapped = asm.convert_endpoints(
        mapped,
        last.right().clone(),
        shape.expected_final(mem.term().clone(), host.term().clone(), eq.left().clone()),
    )?;
    let last = asm
        .compose(last, mapped)
        .map_err(|e| format!("source-result transport: {e}"))?;
    states.push(last.right().clone());
    steps.push(last);
    let count = steps.len();
    if count != 7 + source.instruction_count() || states.len() != count + 1 {
        return Err("actual helper trace count disagrees with source/body".into());
    }
    let mut prefixes = Vec::new();
    for n in 0..count {
        let p = run::interval(
            &mut asm,
            &shape,
            &initial,
            &steps,
            &states,
            n,
            nat(0),
            false,
        )
        .map_err(|e| format!("proper-prefix run interval: {e}"))?;
        prefixes.push((p.proposition(), p.term().clone()));
    }
    let extra = asm.local(c("Nat"))?;
    let p = run::interval(
        &mut asm,
        &shape,
        &initial,
        &steps,
        &states,
        count,
        extra.term().clone(),
        true,
    )
    .map_err(|e| format!("complete run interval: {e}"))?;
    let complete = (extra.pi(p.proposition()), extra.lam(p.term().clone()));
    drop(catalog);
    drop(asm);
    let close = |(claim, proof): (Expr, Expr)| -> Result<(Expr, Expr), String> {
        let claim = globals.iter().rev().fold(claim, |v, b| b.pi(v));
        let proof = globals.iter().rev().fold(proof, |v, b| b.lam(v));
        Ok((
            scope.close(&claim).map_err(|e| e.to_string())?,
            scope.close(&proof).map_err(|e| e.to_string())?,
        ))
    };
    Ok(Candidates {
        steps: count,
        prefixes: prefixes
            .into_iter()
            .map(close)
            .collect::<Result<Vec<_>, _>>()?,
        complete: close(complete)?,
    })
}
