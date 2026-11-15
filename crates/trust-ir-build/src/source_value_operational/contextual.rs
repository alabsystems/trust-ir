// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Contextual scalar-body proof candidates, not a new checked execution receipt.
//!
//! The same actual body phase serves root and internal callers. This phase stops
//! BEFORE Return: the consumer must use its reached state with the actual fetched
//! return rule, then strictly replay an independently reconstructed closed claim.

use super::*;
use crate::core_execution::{ExactRun, InternalCallTransfer, ReturnFrame};

#[cfg(test)]
#[path = "contextual_tests.rs"]
mod tests;

/// Source-bound untrusted candidates for the arithmetic prefix of an entered
/// scalar call. No public constructor, assumed answer, provider premise, or
/// root-return substitution is provided.
#[must_use = "contextual candidates require a closed consumer claim and strict replay"]
pub struct ContextualBodyPrefix<'receipt, 'source> {
    source: &'receipt CheckedSourceValueOperational<'source>,
    states: Vec<Expr>,
    steps: Vec<PendingEquality>,
    run: ExactRun,
    arguments: PendingEquality,
    current: Current,
    valid: PendingEquality,
    result: body::Word,
    source_equation: PendingEquality,
    returning: ReturnFrame,
}

impl<'receipt, 'source> ContextualBodyPrefix<'receipt, 'source> {
    pub fn source(&self) -> &'receipt CheckedSourceValueOperational<'source> {
        self.source
    }
    pub fn states(&self) -> &[Expr] {
        &self.states
    }
    pub fn steps(&self) -> &[PendingEquality] {
        &self.steps
    }
    pub fn run(&self) -> &ExactRun {
        &self.run
    }
    pub fn entered_arguments(&self) -> &PendingEquality {
        &self.arguments
    }
    pub fn current(&self) -> &Current {
        &self.current
    }
    pub fn valid(&self) -> &PendingEquality {
        &self.valid
    }
    /// The actual raw scalar word, not a supplied result.
    pub fn result(&self) -> &Expr {
        &self.result.value
    }
    pub fn result_bound(&self) -> &PendingProof {
        &self.result.bound
    }
    /// Denotation -> actual word, the original shared body invariant.
    pub fn result_equation(&self) -> &PendingEquality {
        &self.result.equation
    }
    /// Original checked source result -> actual returned word. This is an
    /// application of the SAME source equation, not of its root-run theorem.
    pub fn source_result_equation(&self) -> &PendingEquality {
        &self.source_equation
    }
    /// The REACHED callee frame/world. The caller is already advanced by the
    /// original call; return_to_caller must not advance it a second time.
    pub fn return_frame(&self) -> &ReturnFrame {
        &self.returning
    }
}

fn input(profile: ScalarProfile, value: Expr) -> body::Word {
    let n = app(profile.to_nat(), [value.clone()]);
    let fin = app(
        "BitVec.toFin",
        [nat(profile.bits()), app(profile.to_bitvec(), [value])],
    );
    body::Word {
        value: n.clone(),
        bound: PendingProof::candidate(
            profile.bound(n.clone()),
            Expr::proj(Name::from_string("Fin"), 1, fin),
        ),
        denotation: n.clone(),
        equation: pending(c("Nat"), n),
    }
}

/// Assemble the actual U32 arithmetic body AFTER a real internal call transfer.
/// `x` and `y` are UInt32 terms; their canonical bounds are derived here. Every
/// expression/candidate still requires strict whole-claim replay by the caller.
/// No caller-selected environment, arithmetic endpoint or provider equation is
/// accepted. The supplied assembler/catalog are the existing caller instances.
pub fn body_after_call<'receipt, 'source>(
    source: &'receipt CheckedSourceValueOperational<'source>,
    assembler: &mut Assembler<'_>,
    catalog: &mut Catalog<'_, '_>,
    model: &MachineModel,
    entered: &InternalCallTransfer,
    x: Expr,
    y: Expr,
) -> core::result::Result<ContextualBodyPrefix<'receipt, 'source>, SourceValueOperationalError> {
    let derive = || -> Result<ContextualBodyPrefix<'receipt, 'source>> {
        if source.subject.profile != ScalarProfile::U32ConstAddMul {
            return Err("contextual scalar body requires the existing U32 profile".into());
        }
        if model.context() != source.reflected().context_term() {
            return Err("contextual scalar body requires the same checked context".into());
        }
        let a = input(source.subject.profile, x.clone());
        let b = input(source.subject.profile, y.clone());
        let denotation = source.subject.denotation(a.value.clone(), b.value.clone());
        // Derive the exact entered argument projection. A caller cannot attach
        // arbitrary scalar answers to this body candidate.
        let arguments = list("IRScalar", [int(a.value.clone()), int(b.value.clone())]);
        let resolved = assembler.conversion(
            app("IRList", [c("IRScalar")]),
            app(
                "ir_resolve",
                [
                    entered.current().machine(),
                    list(
                        "Nat",
                        source
                            .subject
                            .parameters
                            .map(|id| nat(u64::from(id.index()))),
                    ),
                ],
            ),
            arguments,
        )?;
        let words = BTreeMap::from([
            (source.subject.parameters[0], a),
            (source.subject.parameters[1], b),
        ]);
        let result = body::derive(
            &source.subject,
            assembler,
            catalog,
            model,
            entered.current().clone(),
            entered.valid().clone(),
            words,
        )?;
        let mut returning = entered.return_frame().clone();
        returning.returning = result.current.frame.clone();
        // The shared scalar_value transitions retain the complete world. This
        // assertion is exact data coherence, not an inferred lifetime theorem.
        if returning.current(model).running(model) != result.current.running(model) {
            return Err("contextual body lost its actual reached return state".into());
        }
        if result.result.denotation != denotation {
            return Err("contextual body disagrees with the original scalar denotation".into());
        }
        let original = app(
            "UInt32.toNat",
            [Expr::apps(
                Expr::const_(source.source.source().clone(), vec![]),
                [x.clone(), y.clone()],
            )],
        );
        let original_equation = PendingEquality::candidate(
            c("Nat"),
            original,
            denotation,
            Expr::apps(source.source.proof().clone(), [x, y]),
        );
        let source_equation =
            assembler.compose(original_equation, result.result.equation.clone())?;
        let mut run = assembler.zero(model, result.states[0].clone())?;
        for (state, step) in result.states.iter().zip(&result.steps) {
            let next = assembler.one_step(model, state.clone(), step.clone())?;
            run = assembler.concatenate(run, next)?;
        }
        Ok(ContextualBodyPrefix {
            source,
            states: result.states,
            steps: result.steps,
            run,
            arguments: resolved,
            current: result.current,
            valid: result.valid,
            result: result.result,
            source_equation,
            returning,
        })
    };
    derive().map_err(SourceValueOperationalError)
}
