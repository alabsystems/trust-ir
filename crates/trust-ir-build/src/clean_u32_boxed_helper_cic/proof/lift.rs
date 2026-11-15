// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Lift actual Byte steps, proving Bool-rec constructor mapping rather than
//! assuming intermediate validity or commuting constructors by defeq.
use super::*;

fn select(ty: Expr, no: Expr, yes: Expr, flag: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Bool.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [
            Expr::lam(BinderInfo::Default, c("Bool"), ty.lift(1)),
            no,
            yes,
            flag,
        ],
    )
}
fn commute(
    asm: &mut Assembler<'_>,
    shape: &Shape,
    model: &MachineModel,
    bad: Expr,
    good: Expr,
    flag: Expr,
) -> Result<PendingEquality, String> {
    let b = asm.local(c("Bool"))?;
    let mapped = |v| shape.state(v, false, false);
    let equation_at = |value: Expr| {
        equation(
            shape.state_type(),
            mapped(select(
                model.config_type(),
                bad.clone(),
                good.clone(),
                value.clone(),
            )),
            select(
                shape.state_type(),
                mapped(bad.clone()),
                mapped(good.clone()),
                value,
            ),
        )
    };
    let motive = b.lam(equation_at(b.term().clone()));
    let proof = Expr::apps(
        Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
        [
            motive,
            refl(shape.state_type(), mapped(bad.clone())),
            refl(shape.state_type(), mapped(good.clone())),
            flag.clone(),
        ],
    );
    Ok(PendingEquality::candidate(
        shape.state_type(),
        mapped(select(
            model.config_type(),
            bad.clone(),
            good.clone(),
            flag.clone(),
        )),
        select(shape.state_type(), mapped(bad), mapped(good), flag),
        proof,
    ))
}
fn known_running(
    asm: &mut Assembler<'_>,
    shape: &Shape,
    model: &MachineModel,
    before: Expr,
    machine: Expr,
    world: Expr,
    step: &PendingEquality,
) -> Result<PendingEquality, String> {
    let bad = app(
        "IRByteConfigV1.halted",
        [
            shape.world_type.clone(),
            app("IROutcome.type_error", [c("IRFault.bad_addr")]),
            world.clone(),
        ],
    );
    let good = app(
        "ir_byte_step_machine_v1",
        [
            shape.world_type.clone(),
            shape.context.clone(),
            model.providers().clone(),
            machine.clone(),
            world.clone(),
        ],
    );
    let flag = app(
        "ir_byte_world_valid_v1",
        [shape.world_type.clone(), machine, world],
    );
    let mapped = commute(asm, shape, model, bad, good, flag)?;
    let first = asm.convert_endpoints(
        reverse(shape.state_type(), &mapped),
        shape.step(shape.state(before.clone(), false, false)),
        shape.state(model.step(before), false, false),
    )?;
    let second = asm.congruence(step.clone(), shape.state_type(), |cfg| {
        shape.state(cfg, false, false)
    })?;
    // The canonical step producer may retain an equivalent frame/world
    // expression rather than our chosen constructor spelling. Transport it
    // explicitly; conversion remains part of the final strict kernel replay.
    let second = asm.convert_endpoints(
        second.clone(),
        first.right().clone(),
        second.right().clone(),
    )?;
    asm.compose(first, second)
        .map_err(|e| format!("complete-step lift: {e}"))
}
pub(super) fn byte(
    asm: &mut Assembler<'_>,
    shape: &Shape,
    model: &MachineModel,
    before: &Current,
    step: &PendingEquality,
) -> Result<PendingEquality, String> {
    known_running(
        asm,
        shape,
        model,
        before.running(model),
        before.machine(),
        before.world.clone(),
        step,
    )
}
pub(super) fn byte_state(
    asm: &mut Assembler<'_>,
    shape: &Shape,
    model: &MachineModel,
    before: Expr,
    step: &PendingEquality,
) -> Result<PendingEquality, String> {
    if !matches!(before.get_app_fn().kind(),clean_kernel::ExprKind::Const(n,_) if n==&Name::from_string("IRByteConfigV1.running"))
    {
        return Err("scalar proper-prefix state is not running".into());
    }
    let fields = before.get_app_args();
    let [_, machine, world] = fields.as_slice() else {
        return Err("running configuration constructor arity".into());
    };
    known_running(
        asm,
        shape,
        model,
        before.clone(),
        (*machine).clone(),
        (*world).clone(),
        step,
    )
}
