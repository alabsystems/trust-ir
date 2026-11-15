// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Candidates for the SAME initialized full context, universally quantified over
//! canonical tag payloads and framed memory/host. No supplied provider premise.
use super::*;
mod call;
mod release;
mod run;
mod trace;
use crate::core_execution::{
    Assembler, Catalog, Coordinate, Current, EntryTarget, ImportPremises, ImportResult, Limits,
    MachineModel, PendingEquality,
};
use crate::scoped_local::{LocalScope, ScopedLocal};
use release::release;
use run::interval;
pub(crate) use trace::initialized_trace;

pub(super) struct UniversalCandidates {
    pub prefixes: Vec<(Expr, Expr)>,
    pub handoff: (Expr, Expr),
}
struct Shape {
    context: Expr,
    world_type: Expr,
    wrapper: FuncId,
    block: trust_ir::BlockId,
    unbox: FuncId,
    parameters: [ValueId; 2],
}
impl Shape {
    fn state_type(&self) -> Expr {
        app("IRCleanTag32PrefixV1", [self.world_type.clone()])
    }
    fn run_type(&self) -> Expr {
        app("IRCleanTag32RunV1", [self.world_type.clone()])
    }
    fn state(&self, cfg: Expr, left: bool, right: bool) -> Expr {
        app(
            "IRCleanTag32PrefixV1.mk",
            [self.world_type.clone(), cfg, boolean(left), boolean(right)],
        )
    }
    fn arguments(&self) -> Vec<Expr> {
        vec![
            self.world_type.clone(),
            self.context.clone(),
            nat(u64::from(self.wrapper.index())),
            nat(u64::from(self.block.index())),
            nat(u64::from(self.unbox.index())),
            nat(u64::from(self.parameters[0].index())),
            nat(u64::from(self.parameters[1].index())),
        ]
    }
    fn step(&self, state: Expr) -> Expr {
        let mut a = self.arguments();
        a.push(state);
        app("ir_clean_tag32_step_v1", a)
    }
    fn run(&self, fuel: Expr, state: Expr) -> Expr {
        let mut a = self.arguments();
        a.extend([fuel, state]);
        app("ir_clean_tag32_run_v1", a)
    }
    fn result(&self, state: Expr, remaining: Expr) -> Expr {
        app(
            "IRCleanTag32RunV1.mk",
            [self.world_type.clone(), state, remaining],
        )
    }
}
fn refl(ty: Expr, value: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [ty, value],
    )
}
fn equation(ty: Expr, left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [ty, left, right],
    )
}
fn and(left: PendingEquality, right: PendingEquality) -> PendingEquality {
    PendingEquality::candidate(
        c("Bool"),
        app("Bool.and", [left.left().clone(), right.left().clone()]),
        c("Bool.true"),
        app(
            "ir_byte_world_and_intro_v1",
            [
                left.left().clone(),
                right.left().clone(),
                left.term().clone(),
                right.term().clone(),
            ],
        ),
    )
}
fn true_value() -> PendingEquality {
    PendingEquality::reflexive(c("Bool"), c("Bool.true"))
}
fn hypothesis(local: &ScopedLocal) -> PendingEquality {
    let fields = local.ty().get_app_args();
    PendingEquality::candidate(
        c("Bool"),
        fields[1].clone(),
        c("Bool.true"),
        local.term().clone(),
    )
}
// Derive the actual memory-owner check from the PRE-state world validity, not
// an extra provider/poststate premise.
pub(crate) fn memory_owners(
    model: &MachineModel,
    current: &Current,
    before: &PendingEquality,
) -> PendingEquality {
    let world = &current.world;
    let owners = app(
        "ir_byte_world_owners_v1",
        [model.world_type().clone(), world.clone()],
    );
    let next = app(
        "ir_byte_world_next_v1",
        [model.world_type().clone(), world.clone()],
    );
    let memory = app(
        "ir_byte_world_memory_v1",
        [model.world_type().clone(), world.clone()],
    );
    let a = app(
        "ir_nat_eqb",
        [
            app(
                "ir_byte_length_v1",
                [c("IRMemSlot"), current.legacy_memory.clone()],
            ),
            nat(0),
        ],
    );
    let b = app(
        "ir_nat_eqb",
        [
            app(
                "ir_byte_length_v1",
                [c("IRFrame"), app("ir_mach_frames", [current.machine()])],
            ),
            app("ir_byte_length_v1", [c("Nat"), owners.clone()]),
        ],
    );
    let d = app("ir_byte_owners_valid_v1", [owners.clone(), next.clone()]);
    let e = app("ir_byte_memory_owners_v1", [memory, owners, next]);
    let de = app("Bool.and", [d.clone(), e.clone()]);
    let bde = app("Bool.and", [b.clone(), de.clone()]);
    let h1 = app(
        "ir_byte_world_and_right_v1",
        [a, bde, before.term().clone()],
    );
    let h2 = app("ir_byte_world_and_right_v1", [b, de, h1]);
    PendingEquality::candidate(
        c("Bool"),
        e.clone(),
        c("Bool.true"),
        app("ir_byte_world_and_right_v1", [d, e, h2]),
    )
}
fn pointer_fit(shape: &Shape, x: Expr, bound: Expr) -> PendingEquality {
    let word = app("ir_clean_tag32_encode_v1", [x.clone()]);
    let guard = app(
        "ir_byte_value_matches_v1",
        [
            shape.context.clone(),
            c("IRTy.ptr_"),
            app("IRScalar.ptr_", [word]),
        ],
    );
    PendingEquality::candidate(
        c("Bool"),
        guard,
        c("Bool.true"),
        app(
            "ir_clean_tag32_encoded_pointer_v1",
            [shape.context.clone(), x, bound],
        ),
    )
}
pub(super) fn derive(
    source: &CheckedSourceValueOperational<'_>,
    wrapper: FuncId,
    environment: &Environment,
    limits: Limits,
) -> Result<UniversalCandidates, String> {
    let prepared = prepare_tagged_u32_boxed_prefix(source, wrapper).map_err(|e| e.to_string())?;
    let body = &prepared.wrapper().blocks[0];
    let mut scope = LocalScope::new();
    let mut asm = Assembler::new(&mut scope, limits)?;
    let w = asm.local(Expr::sort(Level::succ(Level::zero())))?;
    let mem = asm.local(c("IRByteMemoryV1"))?;
    let host = asm.local(w.term().clone())?;
    let x = asm.local(c("Nat"))?;
    let y = asm.local(c("Nat"))?;
    let bx = asm.local(app("Nat.lt", [x.term().clone(), nat(4294967296)]))?;
    let by = asm.local(app("Nat.lt", [y.term().clone(), nat(4294967296)]))?;
    let hm = asm.local(equation(
        c("Bool"),
        EntryTarget::memory_admission(mem.term().clone()),
        c("Bool.true"),
    ))?;
    let globals = [
        w.clone(),
        mem.clone(),
        host.clone(),
        x.clone(),
        y.clone(),
        bx.clone(),
        by.clone(),
        hm.clone(),
    ];
    let shape = Shape {
        context: source.context().clone(),
        world_type: w.term().clone(),
        wrapper,
        block: body.id,
        unbox: prepared.unbox_id(),
        parameters: [body.params[0].0, body.params[1].0],
    };
    let mut catalog = Catalog::new(environment, source.reflected(), limits)?;
    let trace = initialized_trace(
        source,
        wrapper,
        &mut asm,
        &mut catalog,
        w.term().clone(),
        mem.term().clone(),
        host.term().clone(),
        [x.term().clone(), y.term().clone()],
        [bx.term().clone(), by.term().clone()],
        hypothesis(&hm),
    )?;
    let initial = trace.initial;
    let states = trace.states;
    let steps = trace.steps;
    let mut candidates = vec![];
    for count in 0..4 {
        let proof = interval(&mut asm, &shape, &initial, &steps, &states, count, nat(0))?;
        candidates.push((proof.proposition(), proof.term().clone()));
    }
    let extra = asm.local(c("Nat"))?;
    let handoff = interval(
        &mut asm,
        &shape,
        &initial,
        &steps,
        &states,
        4,
        extra.term().clone(),
    )?;
    let handoff = (
        extra.pi(handoff.proposition()),
        extra.lam(handoff.term().clone()),
    );
    drop(catalog);
    drop(asm);
    let close = |(claim, proof): (Expr, Expr)| -> Result<(Expr, Expr), String> {
        let claim = globals.iter().rev().fold(claim, |b, p| p.pi(b));
        let proof = globals.iter().rev().fold(proof, |b, p| p.lam(b));
        Ok((
            scope.close(&claim).map_err(|e| e.to_string())?,
            scope.close(&proof).map_err(|e| e.to_string())?,
        ))
    };
    let prefixes = candidates
        .into_iter()
        .map(close)
        .collect::<Result<Vec<_>, _>>()?;
    let handoff = close(handoff)?;
    Ok(UniversalCandidates { prefixes, handoff })
}
