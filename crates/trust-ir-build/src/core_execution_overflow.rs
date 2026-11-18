// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Pending fetched transfers for byte-native, two-result checked arithmetic.
//!
//! The result and overflow flag are computed by the shared operational model,
//! never supplied as answers by the caller. A transfer ends at the actual Byte
//! binding operation, which can still refuse bad destinations. It does not
//! assert normal completion, absence of overflow, termination, source meaning,
//! or native authority. Closing and independent whole-claim replay are required.

use super::*;

#[path = "core_execution_overflow_normalization.rs"]
mod normalization;

#[cfg(test)]
#[path = "core_execution_overflow_tests.rs"]
mod tests;

/// Exact input facts for an actual fetched Overflow instruction. These are
/// untrusted candidates; matching Rust metadata does not validate their terms.
pub struct OverflowPremises {
    /// The actual left/right SSA reads equal the supplied canonical bit patterns.
    pub left: PendingEquality,
    pub right: PendingEquality,
    /// Each bit pattern fits the instruction's exact nominal integer type.
    pub left_fits: PendingEquality,
    pub right_fits: PendingEquality,
    /// The actual result catalog is exactly [integer type, Bool], in that order.
    pub result_types: PendingEquality,
    /// Whole-world validity before this instruction, not after it.
    pub before: PendingEquality,
}

/// One pending actual step and its exact one-step run, including both computed
/// result lanes. Binding/fault behavior remains in the reached configuration.
pub struct OverflowTransfer {
    step: PendingEquality,
    run: ExactRun,
    values: [Expr; 2],
}

impl OverflowTransfer {
    pub fn step(&self) -> &PendingEquality {
        &self.step
    }

    pub fn run(&self) -> &ExactRun {
        &self.run
    }

    pub fn values(&self) -> &[Expr; 2] {
        &self.values
    }
}

/// Recognize syntax only. No instruction, operand, lookup or proof is admitted
/// by this extraction; the complete fetched law remains a replay obligation.
struct OverflowShape<'a> {
    op: &'a Expr,
    ty: &'a Expr,
    left: &'a Expr,
    right: &'a Expr,
    width: &'a Expr,
    signed: bool,
}

fn shape(instruction: &Expr) -> Result<OverflowShape<'_>> {
    let [op, ty, left, right] = exact_constructor_fields(instruction, "IRInst.overflow")
        .ok_or("overflow transfer requires an exact IRInst.overflow constructor")?;
    if ![
        "IROverflowOp.addoverflow",
        "IROverflowOp.suboverflow",
        "IROverflowOp.muloverflow",
    ]
    .into_iter()
    .any(|name| exact_constructor_fields::<0>(op, name).is_some())
    {
        return Err("overflow transfer requires Add, Sub or Mul".into());
    }
    let (width, signed) = if let Some([width]) = exact_constructor_fields(ty, "IRTy.uint_") {
        (width, false)
    } else if let Some([width]) = exact_constructor_fields(ty, "IRTy.int_") {
        (width, true)
    } else {
        return Err("overflow transfer requires the nominal int_ or uint_ carrier".into());
    };
    Ok(OverflowShape {
        op,
        ty,
        left,
        right,
        width,
        signed,
    })
}

impl FetchedSite {
    /// Assemble the shared fetched Overflow law from operand/canonicality,
    /// exact catalog and pre-world facts alone. Value and overflow flag are
    /// always derived from the actual opcode, signedness, width and operands.
    ///
    /// A construction operation is charged before every context/shape check;
    /// two ordered lanes also consume the existing per-list construction limit.
    /// No locals, vocabulary, proof cache, budgets or executable state change.
    /// The reached configuration is the actual checked binding, not a promise
    /// that binding succeeded. Assert/panic semantics are a separate obligation.
    pub fn overflow(
        &self,
        assembler: &mut Assembler<'_>,
        model: &MachineModel,
        current: &Current,
        operands: [Expr; 2],
        premises: OverflowPremises,
    ) -> Result<OverflowTransfer> {
        let (step, values) =
            self.assemble_overflow_step(assembler, model, current, operands, premises)?;
        let run = assembler.one_step(model, current.running(model), step.clone())?;
        Ok(OverflowTransfer { step, run, values })
    }

    // Both direct and normalized transfers share the exact fetched law. The
    // latter transports its binding endpoint before assembling one final run,
    // rather than constructing and discarding a second one-step proof.
    fn assemble_overflow_step(
        &self,
        assembler: &mut Assembler<'_>,
        model: &MachineModel,
        current: &Current,
        operands: [Expr; 2],
        premises: OverflowPremises,
    ) -> Result<(PendingEquality, [Expr; 2])> {
        let shared_current = current.shared_machine();
        let current = &shared_current;
        assembler.charge()?;
        assembler.items(2)?;
        require_same(&self.context, model.context(), "overflow fetched context")?;
        let OverflowShape {
            op,
            ty,
            left,
            right,
            width,
            signed,
        } = shape(&self.instruction)?;
        let [a, b] = operands;
        let read = |id: &Expr| app("ir_getd", [current.machine(), id.clone()]);
        let x = app("IRScalar.int_", [a.clone()]);
        let y = app("IRScalar.int_", [b.clone()]);
        premises
            .left
            .endpoints(&constant("IRScalar"), &read(left), &x)?;
        premises
            .right
            .endpoints(&constant("IRScalar"), &read(right), &y)?;
        for (word, fit) in [(&a, &premises.left_fits), (&b, &premises.right_fits)] {
            fit.endpoints(
                &constant("Bool"),
                &app("ir_byte_integer_fits_v1", [ty.clone(), word.clone()]),
                &constant("Bool.true"),
            )?;
        }
        premises.result_types.endpoints(
            &constant("Bool"),
            &app(
                "ir_byte_ty_list_eq_v1",
                [
                    app("ir_byte_site_results_v1", [self.site.clone()]),
                    list("IRTy", &[ty.clone(), constant("IRTy.bool_")]),
                ],
            ),
            &constant("Bool.true"),
        )?;
        premises.before.endpoints(
            &constant("Bool"),
            &current.valid(model),
            &constant("Bool.true"),
        )?;
        let values = [
            app(
                "IRScalar.int_",
                [app(
                    "ir_overflow_value",
                    [op.clone(), width.clone(), a.clone(), b.clone()],
                )],
            ),
            app(
                "IRScalar.bool_",
                [app(
                    "ir_overflow_flag",
                    [
                        op.clone(),
                        constant(if signed { "Bool.true" } else { "Bool.false" }),
                        width.clone(),
                        a.clone(),
                        b.clone(),
                    ],
                )],
            ),
        ];
        let bound = app(
            "ir_byte_bind_values_v1",
            [
                model.world_type().clone(),
                model.context().clone(),
                current.machine(),
                current.world.clone(),
                self.results.clone(),
                app("ir_byte_site_results_v1", [self.site.clone()]),
                list("IRScalar", &values),
            ],
        );
        // The same exact catalog candidates used by FetchedSite::step. Their
        // reflexivity terms are only candidates: actual function/block/PC/site
        // lookup and destination arity must reduce correctly during replay.
        let found = |name, value| refl(&app("IROption", [constant(name)]), some(name, value));
        let term = app(
            if signed {
                "ir_byte_step_overflow_int_v1"
            } else {
                "ir_byte_step_overflow_uint_v1"
            },
            [
                model.world_type().clone(),
                model.context().clone(),
                model.providers().clone(),
                current.frame.clone(),
                current.tail.clone(),
                current.legacy_memory.clone(),
                current.legacy_cursor.clone(),
                current.world.clone(),
                left.clone(),
                right.clone(),
                self.results.clone(),
                self.site.clone(),
                self.function.clone(),
                self.block.clone(),
                op.clone(),
                width.clone(),
                a,
                b,
                premises.left_fits.term,
                premises.right_fits.term,
                premises.result_types.term,
                premises.before.term,
                premises.left.term,
                premises.right.term,
                found("IRFunc", self.function.clone()),
                found("IRBlock", self.block.clone()),
                found("IRNode", self.node.clone()),
                found("IRByteSiteV1", self.site.clone()),
                refl(&constant("Bool"), constant("Bool.true")),
            ],
        );
        let step = PendingEquality::candidate(
            model.config_type(),
            model.step(current.running(model)),
            bound,
            term,
        );
        Ok((step, values))
    }
}
