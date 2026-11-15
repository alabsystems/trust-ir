// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Shared actual scalar body phase. Stops before Return; never initializes or retires a world.
use super::*;

#[derive(Clone)]
pub(super) struct Word {
    pub(super) value: Expr,
    pub(super) bound: PendingProof,
    pub(super) denotation: Expr,
    pub(super) equation: PendingEquality,
}
pub(super) fn fits(
    profile: ScalarProfile,
    assembler: &mut Assembler<'_>,
    model: &MachineModel,
    word: &Word,
) -> Result<PendingEquality> {
    let proof = app(
        "ir_byte_ltb_of_lt_v1",
        [
            word.value.clone(),
            profile.limit(),
            word.bound.term().clone(),
        ],
    );
    let equality = PendingEquality::candidate(
        c("Bool"),
        app("ir_nat_ltb", [word.value.clone(), profile.limit()]),
        c("Bool.true"),
        proof,
    );
    assembler.convert_endpoints(
        equality,
        app(
            "ir_byte_value_matches_v1",
            [
                model.context().clone(),
                profile.scalar_type(),
                int(word.value.clone()),
            ],
        ),
        c("Bool.true"),
    )
}
pub(super) fn both(
    assembler: &mut Assembler<'_>,
    a: PendingEquality,
    b: PendingEquality,
) -> Result<PendingEquality> {
    let first = mapped(assembler, a, c("Bool"), |flag| {
        app("Bool.and", [flag, b.left().clone()])
    })?;
    let second = mapped(assembler, b, c("Bool"), |flag| {
        app("Bool.and", [c("Bool.true"), flag])
    })?;
    let result = assembler.compose(first, second)?;
    assembler.convert_endpoints(result.clone(), result.left().clone(), c("Bool.true"))
}
fn constant_bound(profile: ScalarProfile, value: u64) -> PendingProof {
    PendingProof::candidate(
        profile.bound(nat(value)),
        app(
            "Nat.le_add_right",
            [
                app("Nat.succ", [nat(value)]),
                nat(profile.maximum() - value),
            ],
        ),
    )
}
fn add_word(assembler: &mut Assembler<'_>, a: &Word, b: &Word) -> Result<(Word, PendingEquality)> {
    let (_, evaluated, output_bound) = assembler.byte_add_u64_canonical(
        a.value.clone(),
        b.value.clone(),
        a.bound.clone(),
        b.bound.clone(),
    )?;
    let value = fast(a.value.clone(), b.value.clone());
    let first = mapped(assembler, a.equation.clone(), c("Nat"), |left| {
        den_add(left, b.denotation.clone())
    })?;
    let second = mapped(assembler, b.equation.clone(), c("Nat"), |right| {
        den_add(a.value.clone(), right)
    })?;
    let arguments = [
        nat(64),
        a.value.clone(),
        b.value.clone(),
        app(
            "ir_byte_ltb_of_lt_v1",
            [a.value.clone(), limit(), a.bound.term().clone()],
        ),
        app(
            "ir_byte_ltb_of_lt_v1",
            [b.value.clone(), limit(), b.bound.term().clone()],
        ),
    ];
    let modulus = PendingEquality::candidate(
        c("Nat"),
        den_add(a.value.clone(), b.value.clone()),
        value.clone(),
        app("RustSourceWord64IRV1.modCanonical", arguments),
    );
    let equation = assembler.compose(first, second)?;
    let equation = assembler.compose(equation, modulus)?;
    Ok((
        Word {
            value,
            bound: output_bound,
            denotation: den_add(a.denotation.clone(), b.denotation.clone()),
            equation,
        },
        evaluated,
    ))
}

// U32 retains the original raw operational word; only its denotation uses
// prelude Nat.mod. The helper's raw→mod equality is reversed to preserve the
// common Word invariant denotation→actual value. No input/result answer is
// assumed, and scalar evaluation is checked conversion of the real opcode.
fn u32_word(
    assembler: &mut Assembler<'_>,
    kind: Arithmetic,
    a: &Word,
    b: &Word,
) -> Result<(Word, PendingEquality)> {
    let profile = ScalarProfile::U32ConstAddMul;
    let (raw, modulus, output_bound) = match kind {
        Arithmetic::Add => assembler.byte_add_word32_mod(a.value.clone(), b.value.clone())?,
        Arithmetic::Mul => assembler.byte_mul_word32_mod(a.value.clone(), b.value.clone())?,
    };
    let first = mapped(assembler, a.equation.clone(), c("Nat"), |left| {
        profile.denotation(kind, left, b.denotation.clone())
    })?;
    let second = mapped(assembler, b.equation.clone(), c("Nat"), |right| {
        profile.denotation(kind, a.value.clone(), right)
    })?;
    let equation = assembler.compose(first, second)?;
    let equation = assembler.compose(equation, symm(&modulus))?;
    let evaluated = assembler.conversion(
        c("IRStepResult"),
        app(
            "ir_binop_eval",
            [
                c(match kind {
                    Arithmetic::Add => "IRBinOp.add",
                    Arithmetic::Mul => "IRBinOp.mul",
                }),
                profile.scalar_type(),
                int(a.value.clone()),
                int(b.value.clone()),
            ],
        ),
        app("IRStepResult.value", [int(raw.clone())]),
    )?;
    Ok((
        Word {
            value: raw,
            bound: output_bound,
            denotation: profile.denotation(kind, a.denotation.clone(), b.denotation.clone()),
            equation,
        },
        evaluated,
    ))
}

pub(super) struct BodyPrefix {
    pub(super) states: Vec<Expr>,
    pub(super) steps: Vec<PendingEquality>,
    pub(super) current: Current,
    pub(super) valid: PendingEquality,
    pub(super) result: Word,
}

pub(super) fn derive(
    subject: &Subject<'_>,
    assembler: &mut Assembler<'_>,
    catalog: &mut Catalog<'_, '_>,
    model: &MachineModel,
    mut current: Current,
    mut validity: PendingEquality,
    mut words: BTreeMap<ValueId, Word>,
) -> Result<BodyPrefix> {
    let mut all_states = vec![current.running(model)];
    let mut steps = Vec::new();
    for (pc, operation) in subject.operations.iter().enumerate() {
        let site = catalog.fetch(Coordinate {
            function: subject.source.function().id,
            block: subject.source.function().entry,
            instruction: pc,
        })?;
        let (destination, word, arithmetic_evaluated) = match operation {
            Operation::Constant {
                destination,
                literal,
            } => {
                let bound = constant_bound(subject.profile, *literal);
                let denotation = nat(*literal);
                let equation = pending(c("Nat"), denotation.clone());
                (
                    *destination,
                    Word {
                        value: nat(*literal),
                        bound,
                        denotation,
                        equation,
                    },
                    None,
                )
            }
            Operation::Arithmetic {
                kind,
                destination,
                left,
                right,
            } => {
                let (word, proof) = match subject.profile {
                    ScalarProfile::U64ConstAdd if *kind == Arithmetic::Add => {
                        add_word(assembler, &words[left], &words[right])?
                    }
                    ScalarProfile::U64ConstAdd => {
                        return Err(subject.profile.operation_error().into());
                    }
                    ScalarProfile::U32ConstAddMul => {
                        u32_word(assembler, *kind, &words[left], &words[right])?
                    }
                };
                (*destination, word, Some(proof))
            }
        };
        let checks = site.scalar_checks(model, &current, int(word.value.clone()))?;
        let output_fits = fits(subject.profile, assembler, model, &word)?;
        let result = both(
            assembler,
            output_fits.clone(),
            pending(c("Bool"), c("Bool.true")),
        )?;
        let result = assembler.convert_endpoints(result, checks.result.clone(), c("Bool.true"))?;
        let (evaluated, operands) = match operation {
            Operation::Arithmetic { left, right, .. } => {
                let evaluated = assembler.convert_endpoints(
                    arithmetic_evaluated.unwrap(),
                    checks.evaluation.clone(),
                    app("IRStepResult.value", [int(word.value.clone())]),
                )?;
                let af = fits(subject.profile, assembler, model, &words[left])?;
                let bf = fits(subject.profile, assembler, model, &words[right])?;
                let operands = both(assembler, af, bf)?;
                (
                    evaluated,
                    assembler.convert_endpoints(
                        operands,
                        checks.operands.clone(),
                        c("Bool.true"),
                    )?,
                )
            }
            Operation::Constant { .. } => (
                assembler.conversion(
                    c("IRStepResult"),
                    checks.evaluation.clone(),
                    app("IRStepResult.value", [int(word.value.clone())]),
                )?,
                truth(assembler, checks.operands.clone())?,
            ),
        };
        let transferred = site.scalar_value(
            assembler,
            model,
            &current,
            int(word.value.clone()),
            ScalarPremises {
                evaluated,
                operands,
                result,
                before: validity,
            },
        )?;
        steps.push(transferred.step().clone());
        current = transferred.current().clone();
        validity = transferred.valid().clone();
        words.insert(destination, word);
        all_states.push(current.running(model));
    }
    let result = words
        .get(&subject.returned)
        .ok_or("missing actual scalar return word")?
        .clone();
    Ok(BodyPrefix {
        states: all_states,
        steps,
        current,
        valid: validity,
        result,
    })
}
