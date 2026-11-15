// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pure canonical thin-pointer evidence, including null. These are untrusted
//! proof candidates for existing byte semantics, not casts, allocations or
//! memory transfers. No positivity, access, lifetime or owner fact is inferred.

use super::*;

#[cfg(test)]
#[path = "core_execution_pointer_tests.rs"]
mod tests;

fn word_guard(word: Expr) -> Expr {
    app("ir_nat_ltb", [word, app("ir_nat_pow2", [nat(64)])])
}

fn pointer_value(word: Expr) -> Expr {
    app("ir_byte_pointer_value_v1", [word])
}

fn pointer_address(value: Expr) -> Expr {
    app("ir_byte_pointer_address_v1", [value])
}

fn pointer_fits(context: Expr, value: Expr) -> Expr {
    app(
        "ir_byte_value_matches_v1",
        [context, constant("IRTy.ptr_"), value],
    )
}

fn claims(context: Expr, word: Expr) -> [Expr; 2] {
    let value = pointer_value(word.clone());
    [
        eq(
            &app("IROption", [constant("Nat")]),
            pointer_address(value.clone()),
            some("Nat", word),
        ),
        eq(
            &constant("Bool"),
            pointer_fits(context, value),
            constant("Bool.true"),
        ),
    ]
}

fn paired(context: Expr, word: Expr, address: Expr, fits: Expr) -> Expr {
    let [address_claim, fits_claim] = claims(context, word);
    app("And.intro", [address_claim, fits_claim, address, fits])
}

/// Candidate data for the exact canonical pointer value. Address recovery at
/// zero returns `some 0`, while the value remains `nullptr_`, never `ptr_ 0`.
/// These equations say nothing about whether that address may be accessed.
#[derive(Clone)]
pub struct BytePointerWord {
    pub value: Expr,
    /// Eq (IROption Nat) (pointer_address value) (some word).
    pub address: PendingEquality,
    /// Eq Bool (value_matches actual_context Ptr value) true.
    pub fits: PendingEquality,
}

impl Assembler<'_> {
    /// Derive address recovery and actual-context Ptr matching from the exact
    /// unsigned 64-bit word guard. Canonical evidence is not trusted by this
    /// Rust wrapper: the consumer must close and independently replay both
    /// claims and their terms. This does not execute an IntToPtr instruction.
    pub fn byte_pointer_word(
        &mut self,
        context: Expr,
        word: Expr,
        canonical: PendingEquality,
    ) -> Result<BytePointerWord> {
        self.charge()?;
        canonical.endpoints(
            &constant("Bool"),
            &word_guard(word.clone()),
            &constant("Bool.true"),
        )?;
        let helper = self.byte_pointer_word_helper()?;
        let [address_claim, fits_claim] = claims(context.clone(), word.clone());
        let proof = Expr::apps(helper, [context.clone(), word.clone(), canonical.term]);
        let value = pointer_value(word.clone());
        Ok(BytePointerWord {
            address: PendingEquality::candidate(
                app("IROption", [constant("Nat")]),
                pointer_address(value.clone()),
                some("Nat", word),
                app(
                    "And.left",
                    [address_claim.clone(), fits_claim.clone(), proof.clone()],
                ),
            ),
            fits: PendingEquality::candidate(
                constant("Bool"),
                pointer_fits(context, value.clone()),
                constant("Bool.true"),
                app("And.right", [address_claim, fits_claim, proof]),
            ),
            value,
        })
    }

    /// One closed zero/successor template. Actual context, word and evidence
    /// are application arguments, never recaptured under the helper's binders.
    /// Every template local uses the existing shared allocator and budgets.
    fn byte_pointer_word_helper(&mut self) -> Result<Expr> {
        if let Some(candidate) = &self.byte_pointer_word_candidate {
            return Ok(candidate.clone());
        }
        let context = self.local(constant("IRByteContextV1"))?;
        let word = self.local(constant("Nat"))?;
        let bound = |value| eq(&constant("Bool"), word_guard(value), constant("Bool.true"));
        let canonical = self.local(bound(word.term().clone()))?;

        let value = self.local(constant("Nat"))?;
        let value_bound = self.local(bound(value.term().clone()))?;
        let [address_claim, fits_claim] = claims(context.term().clone(), value.term().clone());
        let motive = value.lam(value_bound.pi(app("And", [address_claim, fits_claim])));

        let zero_bound = self.local(bound(nat(0)))?;
        let zero = zero_bound.lam(paired(
            context.term().clone(),
            nat(0),
            refl(&app("IROption", [constant("Nat")]), some("Nat", nat(0))),
            refl(&constant("Bool"), constant("Bool.true")),
        ));

        let predecessor = self.local(constant("Nat"))?;
        let induction = self.local(Expr::app(motive.clone(), predecessor.term().clone()))?;
        let successor = app("Nat.succ", [predecessor.term().clone()]);
        let successor_bound = self.local(bound(successor.clone()))?;
        let address = app(
            "ir_byte_case_true_v1",
            [
                app("IROption", [constant("Nat")]),
                word_guard(successor.clone()),
                app("IROption.none", [constant("Nat")]),
                some("Nat", successor.clone()),
                some("Nat", successor.clone()),
                successor_bound.term().clone(),
                refl(
                    &app("IROption", [constant("Nat")]),
                    some("Nat", successor.clone()),
                ),
            ],
        );
        // pointer_value (succ n) reduces to ptr_ (succ n); positivity reduces
        // to true. The only remaining fit/address guard is this exact bound.
        let step = predecessor.lam(induction.lam(successor_bound.lam(paired(
            context.term().clone(),
            successor,
            address,
            successor_bound.term().clone(),
        ))));
        let body = Expr::apps(
            Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            [
                motive,
                zero,
                step,
                word.term().clone(),
                canonical.term().clone(),
            ],
        );
        let template = context.lam(word.lam(canonical.lam(body)));
        let closed = self
            .scope
            .close(&template)
            .map_err(|error| error.to_string())?;
        self.byte_pointer_word_candidate = Some(closed.clone());
        Ok(closed)
    }
}
