// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Pending multiplication transport through checked arithmetic agreement.
//! This does not accelerate or replace the operational evaluator. Both result
//! lanes are lifted into its original checked binding, preserving all faults
//! and the complete world. The consumer must carry the actual checked Clean
//! product/total-remainder package and independently replay the closed claim.

use super::*;

impl FetchedSite {
    /// Fetch a nominal checked multiplication and transport its two computed
    /// lanes through the shared all-Nat multiplication/residue proofs.
    ///
    /// There is no output-answer premise. Signed magnitude, sign selection,
    /// result ordering, destination checks and world ownership stay unchanged.
    /// All terms are pending candidates: familiar theorem names grant no
    /// authority without the consumer's actual vocabulary and strict replay.
    pub fn overflow_mul_normalized(
        &self,
        assembler: &mut Assembler<'_>,
        model: &MachineModel,
        current: &Current,
        operands: [Expr; 2],
        premises: OverflowPremises,
    ) -> Result<OverflowTransfer> {
        let shared_current = current.shared_machine();
        let current = &shared_current;
        assembler.charge()?;
        let OverflowShape {
            op, width, signed, ..
        } = shape(&self.instruction)?;
        if exact_constructor_fields::<0>(op, "IROverflowOp.muloverflow").is_none() {
            return Err("normalized overflow transfer requires exact MulOverflow".into());
        }
        let [a, b] = operands.clone();
        let (original_step, original_values) =
            self.assemble_overflow_step(assembler, model, current, operands, premises)?;

        let word = app(
            "ir_nat_rem_total_v1",
            [
                app("Nat.mul", [a.clone(), b.clone()]),
                app("ir_nat_pow2", [width.clone()]),
            ],
        );
        let wrapped = PendingEquality::candidate(
            constant("Nat"),
            app(
                "ir_wrap",
                [width.clone(), app("ir_nat_mul", [a.clone(), b.clone()])],
            ),
            word.clone(),
            app(
                "ir_wrap_mul_total_agrees_v1",
                [width.clone(), a.clone(), b.clone()],
            ),
        );
        let value = app("IRScalar.int_", [word]);
        let value_equality = assembler.congruence(wrapped, constant("IRScalar"), |word| {
            app("IRScalar.int_", [word])
        })?;
        let value_equality = assembler.convert_endpoints(
            value_equality,
            original_values[0].clone(),
            value.clone(),
        )?;

        let magnitude = |operand: &Expr| {
            if signed {
                app("ir_signed_magnitude", [width.clone(), operand.clone()])
            } else {
                operand.clone()
            }
        };
        let ma = magnitude(&a);
        let mb = magnitude(&b);
        let product = PendingEquality::candidate(
            constant("Nat"),
            app("ir_nat_mul", [ma.clone(), mb.clone()]),
            app("Nat.mul", [ma.clone(), mb.clone()]),
            app("ir_nat_mul_canonical_agrees_v1", [ma, mb]),
        );
        let flag = assembler.congruence(product, constant("Bool"), |product| {
            if signed {
                let limit = app("ir_nat_pow2", [app("Nat.pred", [width.clone()])]);
                choose(
                    &constant("Bool"),
                    app(
                        "ir_bool_xor",
                        [
                            app("ir_sign_bit", [width.clone(), a]),
                            app("ir_sign_bit", [width.clone(), b]),
                        ],
                    ),
                    app("ir_nat_ltb", [limit.clone(), product.clone()]),
                    app("ir_nat_leb", [limit, product]),
                )
            } else {
                app("ir_nat_leb", [app("ir_nat_pow2", [width.clone()]), product])
            }
        })?;
        let flag = assembler.congruence(flag, constant("IRScalar"), |flag| {
            app("IRScalar.bool_", [flag])
        })?;
        let flag_value = flag.right().clone();
        let flag_equality =
            assembler.convert_endpoints(flag, original_values[1].clone(), flag_value.clone())?;
        let values = [value, flag_value];

        let bind = |values: [Expr; 2]| {
            app(
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
            )
        };
        // Transport each ordered lane through the unchanged checked binder.
        // In particular, neither congruence assumes binding completed normally.
        let middle = bind([values[0].clone(), original_values[1].clone()]);
        let first = assembler.congruence(value_equality, model.config_type(), |value| {
            bind([value, original_values[1].clone()])
        })?;
        let first =
            assembler.convert_endpoints(first, original_step.right.clone(), middle.clone())?;
        let last = bind(values.clone());
        let second = assembler.congruence(flag_equality, model.config_type(), |flag| {
            bind([values[0].clone(), flag])
        })?;
        let second = assembler.convert_endpoints(second, middle, last)?;
        let step = assembler.compose(original_step, first)?;
        let step = assembler.compose(step, second)?;
        let run = assembler.one_step(model, current.running(model), step.clone())?;
        Ok(OverflowTransfer { step, run, values })
    }
}
