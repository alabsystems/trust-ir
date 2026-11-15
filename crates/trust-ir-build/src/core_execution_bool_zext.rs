// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Symbolic candidates for the existing ByteV1 Bool-to-integer ZExt.
//! No vocabulary, instruction, source relation or checked authority is installed.

use super::*;
use clean_kernel::BinderInfo;
use trust_ir::Ty;

/// The exact zero-extended Boolean word and its pending typed candidates.
/// The unchanged fetched scalar adapter must authenticate the actual Cast,
/// SSA operand, destination and whole world separately.
#[derive(Clone)]
pub struct ByteBoolZext {
    /// `Bool.rec Nat 0 1 flag`, not a host-computed Boolean or integer.
    pub word: Expr,
    /// The original integer scalar carrying that word.
    pub value: Expr,
    /// Exact ByteV1 ZExt evaluation from Bool to the requested nominal type.
    pub evaluated: PendingEquality,
    /// Exact destination carrier check for this same context and scalar.
    pub fits: PendingEquality,
}

fn nominal_integer(destination: &Ty) -> Result<Expr> {
    let (constructor, width) = match destination {
        Ty::I8 => ("IRTy.int_", 8),
        Ty::I16 => ("IRTy.int_", 16),
        Ty::I32 => ("IRTy.int_", 32),
        Ty::I64 => ("IRTy.int_", 64),
        Ty::I128 => ("IRTy.int_", 128),
        Ty::U8 => ("IRTy.uint_", 8),
        Ty::U16 => ("IRTy.uint_", 16),
        Ty::U32 => ("IRTy.uint_", 32),
        Ty::U64 => ("IRTy.uint_", 64),
        Ty::U128 => ("IRTy.uint_", 128),
        _ => return Err("Boolean ZExt requires a nominal I/U8..128 destination".into()),
    };
    Ok(app(constructor, [nat(width)]))
}

fn word(flag: Expr) -> Expr {
    choose(&constant("Nat"), flag, nat(1), nat(0))
}

fn value(flag: Expr) -> Expr {
    app("IRScalar.int_", [word(flag)])
}

fn evaluation(context: Expr, destination: Expr, flag: Expr) -> Expr {
    app(
        "ir_byte_cast_eval_v1",
        [
            context,
            constant("IRCastOp.zext"),
            constant("IRTy.bool_"),
            destination,
            app("IRScalar.bool_", [flag]),
        ],
    )
}

fn proof_cases(motive: Expr, on_false: Expr, on_true: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
        [motive, on_false, on_true, Expr::bvar(0)],
    )
}

impl Assembler<'_> {
    /// Derive exact symbolic Bool ZExt and result Fits for nominal I/U8..128.
    ///
    /// One operation is charged BEFORE destination validation; failed work is
    /// not refunded. No output answer/Fits proof, flag case, local, list, cache
    /// entry or new declaration is supplied or allocated. Both proofs perform
    /// checked Boolean elimination under CLOSED neutral context/flag binders;
    /// caller-owned free/de Bruijn expressions are applied outside those two
    /// binders, so they are not captured. Ill-typed inputs remain pending terms
    /// and must be refused by independent strict original/DAG replay.
    ///
    /// This uses the original checked ByteV1 cast semantics. It does not run a
    /// fetched instruction or certify a source/native conversion. In particular
    /// the consumer still needs the actual site's typed scalar transfer and its
    /// original SSA lookup, destination arity/Fits and before-validity premises.
    ///
    /// # Errors
    ///
    /// Returns an error for a non-nominal integer destination or the unchanged
    /// construction operation limit/counter checks. Failed charged work remains
    /// spent; ill-typed semantic inputs still require strict replay refusal.
    pub fn byte_bool_zext(
        &mut self,
        context: Expr,
        destination: &Ty,
        flag: Expr,
    ) -> Result<ByteBoolZext> {
        self.charge()?;
        let destination = nominal_integer(destination)?;
        // Under the context and flag lambdas: context=bvar1, flag=bvar0.
        // Under either recursor's motive lambda, context is lifted to bvar2.
        let evaluated_motive = Expr::lam(
            BinderInfo::Default,
            constant("Bool"),
            eq(
                &constant("IRStepResult"),
                evaluation(Expr::bvar(2), destination.clone(), Expr::bvar(0)),
                app("IRStepResult.value", [value(Expr::bvar(0))]),
            ),
        );
        let fits_motive = Expr::lam(
            BinderInfo::Default,
            constant("Bool"),
            eq(
                &constant("Bool"),
                app(
                    "ir_byte_value_matches_v1",
                    [Expr::bvar(2), destination.clone(), value(Expr::bvar(0))],
                ),
                constant("Bool.true"),
            ),
        );
        let closed = |body| {
            Expr::lam(
                BinderInfo::Default,
                constant("IRByteContextV1"),
                Expr::lam(BinderInfo::Default, constant("Bool"), body),
            )
        };
        let evaluated = closed(proof_cases(
            evaluated_motive,
            refl(
                &constant("IRStepResult"),
                app("IRStepResult.value", [app("IRScalar.int_", [nat(0)])]),
            ),
            refl(
                &constant("IRStepResult"),
                app("IRStepResult.value", [app("IRScalar.int_", [nat(1)])]),
            ),
        ));
        let fits = closed(proof_cases(
            fits_motive,
            refl(&constant("Bool"), constant("Bool.true")),
            refl(&constant("Bool"), constant("Bool.true")),
        ));
        let extended_word = word(flag.clone());
        let result = app("IRScalar.int_", [extended_word.clone()]);
        Ok(ByteBoolZext {
            word: extended_word,
            value: result.clone(),
            evaluated: PendingEquality::candidate(
                constant("IRStepResult"),
                evaluation(context.clone(), destination.clone(), flag.clone()),
                app("IRStepResult.value", [result.clone()]),
                Expr::apps(evaluated, [context.clone(), flag.clone()]),
            ),
            fits: PendingEquality::candidate(
                constant("Bool"),
                app(
                    "ir_byte_value_matches_v1",
                    [context.clone(), destination, result],
                ),
                constant("Bool.true"),
                Expr::apps(fits, [context, flag]),
            ),
        })
    }
}

#[cfg(test)]
#[path = "core_execution_bool_zext_tests.rs"]
mod tests;
