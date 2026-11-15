// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
use super::*;
// Only the ACTUAL halted constructor stops this target; Nat induction retains extra fuel.
fn stopped(
    asm: &mut Assembler<'_>,
    shape: &Shape,
    state: Expr,
    fuel: Expr,
) -> Result<PendingEquality, String> {
    let n = asm.local(c("Nat"))?;
    let n_goal = equation(
        shape.run_type(),
        shape.run(n.term().clone(), state.clone()),
        shape.result(state.clone(), n.term().clone()),
    );
    let ih = asm.local(n_goal.clone())?;
    let next = app("Nat.succ", [n.term().clone()]);
    let step = ih.lam(refl(shape.run_type(), shape.result(state.clone(), next)));
    let step = n.lam(step);
    let motive = n.lam(n_goal);
    let proof = Expr::apps(
        Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
        [
            motive,
            refl(shape.run_type(), shape.result(state.clone(), nat(0))),
            step,
            fuel.clone(),
        ],
    );
    Ok(PendingEquality::candidate(
        shape.run_type(),
        shape.run(fuel.clone(), state.clone()),
        shape.result(state, fuel),
        proof,
    ))
}
pub(super) fn interval(
    asm: &mut Assembler<'_>,
    shape: &Shape,
    initial: &PendingEquality,
    steps: &[PendingEquality],
    states: &[Expr],
    count: usize,
    extra: Expr,
    terminal: bool,
) -> Result<PendingEquality, String> {
    let fuel = if count == 0 {
        extra.clone()
    } else {
        app("Nat.add", [extra.clone(), nat(count as u64)])
    };
    let first = asm.congruence(initial.clone(), shape.run_type(), |state| {
        shape.run(fuel.clone(), state)
    })?;
    let mut result = asm.convert_endpoints(
        first,
        shape.run(fuel, initial.left().clone()),
        shape.run(
            if count == 0 {
                extra.clone()
            } else {
                app("Nat.add", [extra.clone(), nat(count as u64)])
            },
            states[0].clone(),
        ),
    )?;
    for i in 0..count {
        let remaining = if count - i - 1 == 0 {
            extra.clone()
        } else {
            app("Nat.add", [extra.clone(), nat((count - i - 1) as u64)])
        };
        let unfolded = asm.conversion(
            shape.run_type(),
            result.right().clone(),
            shape.run(remaining.clone(), steps[i].left().clone()),
        )?;
        result = asm.compose(result, unfolded)?;
        let mapped = asm.congruence(steps[i].clone(), shape.run_type(), |state| {
            shape.run(remaining.clone(), state)
        })?;
        let mapped = asm.convert_endpoints(
            mapped,
            result.right().clone(),
            shape.run(remaining, states[i + 1].clone()),
        )?;
        result = asm.compose(result, mapped)?;
    }
    let tail = if terminal {
        stopped(asm, shape, states[count].clone(), extra)?
    } else {
        asm.conversion(
            shape.run_type(),
            result.right().clone(),
            shape.result(states[count].clone(), nat(0)),
        )?
    };
    asm.compose(result, tail)
}
