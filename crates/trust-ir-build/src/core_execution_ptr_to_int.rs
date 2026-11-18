// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Pending thin-pointer cast proofs for ordinary Core consumers. Address bits
//! are transported through the existing byte evaluator, without loads, access,
//! allocation, positivity, source semantics or native admission authority.

use super::*;
use clean_kernel::BinderInfo;
use trust_ir::Ty;

/// Candidate result and exact carrier/evaluator equations. The fetched scalar
/// transfer separately checks the real operand, opcode, result lane and World.
#[derive(Clone)]
pub struct BytePtrToInt {
    /// The integer scalar carrying exactly the recovered address word.
    pub value: Expr,
    /// Actual-context matching for this same scalar and nominal destination.
    pub fits: PendingEquality,
    /// The existing ByteV1 PtrToInt evaluator returns this scalar.
    pub evaluated: PendingEquality,
}

fn fit(context: Expr, ty: Expr, value: Expr) -> Expr {
    app("ir_byte_value_matches_v1", [context, ty, value])
}

fn scalar(word: Expr) -> Expr {
    app("IRScalar.int_", [word])
}

fn recovered(operand: Expr, word: Expr) -> Expr {
    eq(
        &app("IROption", [constant("Nat")]),
        app("ir_byte_pointer_address_v1", [operand]),
        some("Nat", word),
    )
}

fn bounded(word: Expr) -> Expr {
    app("Nat.lt", [word, constant("ir_byte_limit_v1")])
}

// All dependent types are written in their original outer context. The body
// has six neutral binders: ctx5, operand4, word3, fit2, recovery1, bound0.
// Actual caller expressions enter only as arguments to this CLOSED template.
fn close_inputs(body: Expr) -> Expr {
    let input = eq(
        &constant("Bool"),
        fit(Expr::bvar(2), constant("IRTy.ptr_"), Expr::bvar(1)),
        constant("Bool.true"),
    );
    let recovery = recovered(Expr::bvar(2), Expr::bvar(1));
    [
        constant("IRByteContextV1"),
        constant("IRScalar"),
        constant("Nat"),
        input,
        recovery,
        bounded(Expr::bvar(2)),
    ]
    .into_iter()
    .rev()
    .fold(body, |body, ty| Expr::lam(BinderInfo::Default, ty, body))
}

fn templates(destination: Expr, fits_theorem: &str) -> (Expr, Expr) {
    let context = Expr::bvar(5);
    let operand = Expr::bvar(4);
    let word = Expr::bvar(3);
    let result = scalar(word.clone());
    let expected = app("IRStepResult.value", [result.clone()]);
    let fault = app(
        "IRStepResult.fault",
        [app("IROutcome.type_error", [constant("IRFault.bad_field")])],
    );
    let canonical = app(
        "ir_byte_ltb_of_lt_v1",
        [word.clone(), app("ir_nat_pow2", [nat(64)]), Expr::bvar(0)],
    );
    let fits = app(fits_theorem, [context.clone(), word.clone(), canonical]);
    let compute = app(
        "ir_byte_cast_compute_v1",
        [
            constant("IRCastOp.ptrtoint"),
            constant("IRTy.ptr_"),
            destination.clone(),
            operand.clone(),
        ],
    );
    let computed = app(
        "ir_byte_case_some_v1",
        [
            constant("Nat"),
            constant("IRStepResult"),
            app("ir_byte_pointer_address_v1", [operand.clone()]),
            word,
            fault.clone(),
            Expr::lam(
                BinderInfo::Default,
                constant("Nat"),
                app("IRStepResult.value", [scalar(Expr::bvar(0))]),
            ),
            expected.clone(),
            Expr::bvar(1),
            refl(&constant("IRStepResult"), expected.clone()),
        ],
    );
    let checked = |value| {
        app(
            "ir_byte_cast_result_v1",
            [context.clone(), destination.clone(), value],
        )
    };
    let mapped = app(
        "ir_eq_cong",
        [
            constant("IRStepResult"),
            constant("IRStepResult"),
            Expr::lam(
                BinderInfo::Default,
                constant("IRStepResult"),
                app(
                    "ir_byte_cast_result_v1",
                    [Expr::bvar(6), destination.clone(), Expr::bvar(0)],
                ),
            ),
            compute.clone(),
            expected.clone(),
            computed,
        ],
    );
    let output_check = app(
        "ir_byte_case_true_v1",
        [
            constant("IRStepResult"),
            fit(context.clone(), destination.clone(), result),
            fault.clone(),
            expected.clone(),
            expected.clone(),
            fits.clone(),
            refl(&constant("IRStepResult"), expected.clone()),
        ],
    );
    let output = trans(
        &constant("IRStepResult"),
        checked(compute.clone()),
        checked(expected.clone()),
        expected.clone(),
        mapped,
        output_check,
    );
    let evaluated = app(
        "ir_byte_case_true_v1",
        [
            constant("IRStepResult"),
            fit(context.clone(), constant("IRTy.ptr_"), operand),
            fault,
            checked(compute),
            expected,
            Expr::bvar(2),
            output,
        ],
    );
    (close_inputs(fits), close_inputs(evaluated))
}

impl Assembler<'_> {
    /// Propose Ptr -> I64/U64 evaluation and destination Fits from the exact
    /// input fit, address recovery and natural bound. Zero is admitted as null;
    /// no memory operation, positive address or accessible object is inferred.
    ///
    /// The first charge precedes validation/construction; the second is the
    /// existing typed endpoint ascription. Both remain spent on later refusal.
    /// No scoped local, list, cache entry or declaration is allocated. Proofs
    /// abstract neutral inputs before applying caller free/outer-bound terms.
    /// Every returned candidate still requires independent strict kernel replay.
    ///
    /// # Errors
    /// Returns an error for another destination, mismatched premise endpoints
    /// or the unchanged construction budget. Failed charged work stays spent;
    /// forged proof terms require independent semantic rejection by the kernel.
    pub fn byte_ptr_to_int(
        &mut self,
        context: Expr,
        destination: &Ty,
        operand: Expr,
        word: Expr,
        input_fit: PendingEquality,
        address_recovery: PendingEquality,
        bounded_word: PendingProof,
    ) -> Result<BytePtrToInt> {
        self.charge()?;
        let (destination, theorem) = match destination {
            Ty::I64 => (app("IRTy.int_", [nat(64)]), "ir_byte_i64_value_fits_v1"),
            Ty::U64 => (app("IRTy.uint_", [nat(64)]), "ir_byte_u64_value_fits_v1"),
            _ => return Err("PtrToInt requires a nominal I64/U64 destination".into()),
        };
        input_fit.endpoints(
            &constant("Bool"),
            &fit(context.clone(), constant("IRTy.ptr_"), operand.clone()),
            &constant("Bool.true"),
        )?;
        require_same(
            &address_recovery.proposition(),
            &recovered(operand.clone(), word.clone()),
            "PtrToInt address recovery",
        )?;
        require_same(
            bounded_word.proposition(),
            &bounded(word.clone()),
            "PtrToInt word bound",
        )?;
        let (fits_template, evaluated_template) = templates(destination.clone(), theorem);
        let arguments = [
            context.clone(),
            operand.clone(),
            word.clone(),
            input_fit.term,
            address_recovery.term,
            bounded_word.term,
        ];
        let value = scalar(word);
        let left = app(
            "ir_byte_cast_eval_v1",
            [
                context.clone(),
                constant("IRCastOp.ptrtoint"),
                constant("IRTy.ptr_"),
                destination.clone(),
                operand,
            ],
        );
        let right = app("IRStepResult.value", [value.clone()]);
        let evaluated = PendingEquality::candidate(
            constant("IRStepResult"),
            left.clone(),
            right.clone(),
            Expr::apps(evaluated_template, arguments.iter().cloned()),
        );
        let evaluated = self.ascribe_endpoints(evaluated, left, right)?;
        Ok(BytePtrToInt {
            fits: PendingEquality::candidate(
                constant("Bool"),
                fit(context, destination, value.clone()),
                constant("Bool.true"),
                Expr::apps(fits_template, arguments),
            ),
            value,
            evaluated,
        })
    }
}
