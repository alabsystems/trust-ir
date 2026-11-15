// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Layout/pointer/arithmetic candidates for an already selected nominal index.
//! The fetched-site bridge separately authenticates the original operand
//! catalog, machine and ordered IDs. These candidates authorize no access,
//! source lowering, native execution or checked verdict.

use super::*;

#[cfg(test)]
#[path = "core_execution_byte_gep_typed_tests.rs"]
mod tests;

/// Actual operands of `ir_byte_gep_typed_v1` at `Some index`. No erased list or
/// source-decoder proof is carried: that proof belongs to the fetched site.
#[derive(Clone)]
pub struct ByteGepTyped {
    pub pointee: Expr,
    pub layout: Expr,
    pub stride: Expr,
    pub pointer: Expr,
    pub base: Expr,
    pub index: Expr,
    pub memory: Expr,
}

/// Exact expected claims, not proofs or permission to access the result.
#[derive(Clone)]
pub struct ByteGepTypedChecks {
    pub layout: (Expr, Expr, Expr),
    pub layout_size: (Expr, Expr, Expr),
    pub pointer: (Expr, Expr, Expr),
    pub base_positive: Expr,
    pub stride_positive: Expr,
    pub stride_bound: Expr,
    pub delta_bound: Expr,
    pub result_bound: Expr,
    pub inbounds_membership: (Expr, Expr, Expr),
}

#[derive(Clone)]
pub struct ByteGepTypedPremises {
    pub layout: PendingEquality,
    pub layout_size: PendingEquality,
    pub pointer: PendingEquality,
    pub base_positive: PendingProof,
    pub stride_positive: PendingProof,
    pub stride_bound: PendingProof,
    /// Unbounded `stride * index < 2^64`, not a wrapped-word assertion.
    pub delta_bound: PendingProof,
    /// Unbounded `base + stride * index < 2^64`.
    pub result_bound: PendingProof,
}

/// The existing result carrier is independent of how the index was decoded.
pub type ByteGepTypedResult = ByteGepSingletonResult;

impl ByteGepTyped {
    #[must_use]
    pub fn checks(&self, context: &Expr) -> ByteGepTypedChecks {
        let [layout, layout_size, pointer] = self.equalities(context);
        let [
            base_positive,
            stride_positive,
            stride_bound,
            delta_bound,
            result_bound,
        ] = self.propositions();
        ByteGepTypedChecks {
            layout,
            layout_size,
            pointer,
            base_positive,
            stride_positive,
            stride_bound,
            delta_bound,
            result_bound,
            inbounds_membership: (
                constant("Bool"),
                self.resolved().membership(),
                constant("Bool.true"),
            ),
        }
    }

    fn resolved(&self) -> GepResolved {
        GepResolved {
            layout: self.layout.clone(),
            stride: self.stride.clone(),
            pointer: self.pointer.clone(),
            base: self.base.clone(),
            index: self.index.clone(),
            memory: self.memory.clone(),
        }
    }

    fn evaluation(&self, context: Expr, flag: Expr) -> Expr {
        app(
            "ir_byte_gep_typed_v1",
            [
                context,
                self.pointee.clone(),
                self.pointer.clone(),
                some("Nat", self.index.clone()),
                flag,
                self.memory.clone(),
            ],
        )
    }

    fn equalities(&self, context: &Expr) -> [(Expr, Expr, Expr); 3] {
        [
            (
                option("IRByteLayoutV1"),
                app("ir_byte_layout_v1", [context.clone(), self.pointee.clone()]),
                some("IRByteLayoutV1", self.layout.clone()),
            ),
            (
                constant("Nat"),
                app("ir_byte_layout_size_v1", [self.layout.clone()]),
                self.stride.clone(),
            ),
            (
                option("Nat"),
                pointer_address(self.pointer.clone()),
                some("Nat", self.base.clone()),
            ),
        ]
    }

    fn propositions(&self) -> [Expr; 5] {
        let input = self.resolved();
        [
            app("Nat.lt", [nat(0), self.base.clone()]),
            app("Nat.lt", [nat(0), self.stride.clone()]),
            app("Nat.lt", [self.stride.clone(), limit()]),
            app("Nat.lt", [input.delta(), limit()]),
            app("Nat.lt", [input.address(), limit()]),
        ]
    }
}

impl Assembler<'_> {
    /// Selected-index GEP with exact layout and nonwrapping arithmetic. There
    /// is no legacy `<2^63` index premise and no inferred allocation membership.
    pub fn byte_gep_typed_noninbounds(
        &mut self,
        context: Expr,
        input: ByteGepTyped,
        premises: ByteGepTypedPremises,
    ) -> Result<ByteGepTypedResult> {
        self.byte_gep_typed(context, input, premises, None)
    }

    /// Same-allocation (including one-past) must name this exact original
    /// memory and the unbounded scaled address. It grants no load/store right.
    pub fn byte_gep_typed_inbounds(
        &mut self,
        context: Expr,
        input: ByteGepTyped,
        premises: ByteGepTypedPremises,
        same_allocation: PendingEquality,
    ) -> Result<ByteGepTypedResult> {
        same_allocation.endpoints(
            &constant("Bool"),
            &input.resolved().membership(),
            &constant("Bool.true"),
        )?;
        self.byte_gep_typed(context, input, premises, Some(same_allocation))
    }

    fn byte_gep_typed(
        &mut self,
        context: Expr,
        input: ByteGepTyped,
        premises: ByteGepTypedPremises,
        membership: Option<PendingEquality>,
    ) -> Result<ByteGepTypedResult> {
        // No singleton list is constructed, so no list-item charge is added.
        // All ordinary helper construction charges and failures stay spent.
        self.charge()?;
        for (proof, (ty, left, right)) in
            [&premises.layout, &premises.layout_size, &premises.pointer]
                .into_iter()
                .zip(input.equalities(&context))
        {
            proof.endpoints(&ty, &left, &right)?;
        }
        for (proof, expected) in [
            &premises.base_positive,
            &premises.stride_positive,
            &premises.stride_bound,
            &premises.delta_bound,
            &premises.result_bound,
        ]
        .into_iter()
        .zip(input.propositions())
        {
            require_same(
                proof.proposition(),
                &expected,
                "typed GEP arithmetic premise",
            )?;
        }
        let flag = constant(if membership.is_some() {
            "Bool.true"
        } else {
            "Bool.false"
        });
        let helper = self.byte_gep_typed_helper(membership.is_some())?;
        let resolved = input.resolved();
        let address = resolved.address();
        let positive = app(
            "Nat.le_trans",
            [
                nat(1),
                input.base.clone(),
                address.clone(),
                premises.base_positive.term.clone(),
                app("Nat.le_add_right", [input.base.clone(), resolved.delta()]),
            ],
        );
        let result = MemoryResult {
            value: app("IRScalar.ptr_", [address.clone()]),
            memory: input.memory.clone(),
        };
        let evaluated = PendingEquality::candidate(
            constant("IRByteMemoryResultV1"),
            input.evaluation(context.clone(), flag),
            result.result(),
            Expr::apps(
                helper,
                [
                    context.clone(),
                    input.pointee,
                    input.layout,
                    input.stride,
                    input.pointer,
                    input.base,
                    input.index,
                    input.memory.clone(),
                    premises.layout.term,
                    premises.layout_size.term,
                    premises.pointer.term,
                    premises.base_positive.term,
                    premises.stride_positive.term,
                    premises.stride_bound.term,
                    premises.delta_bound.term,
                    premises.result_bound.term.clone(),
                ]
                .into_iter()
                .chain(membership.map(|proof| proof.term)),
            ),
        );
        Ok(ByteGepTypedResult {
            result_fits: bool_fact(
                app(
                    "ir_byte_value_matches_v1",
                    [context.clone(), constant("IRTy.ptr_"), result.value.clone()],
                ),
                app(
                    "ir_byte_allocated_pointer_matches_v1",
                    [context, address, positive, premises.result_bound.term],
                ),
            ),
            allocations: PendingEquality::reflexive(
                app("IRList", [constant("IRByteAllocationV1")]),
                allocs(input.memory),
            ),
            result,
            evaluated,
        })
    }

    fn byte_gep_typed_helper(&mut self, inbounds: bool) -> Result<Expr> {
        let key = usize::from(inbounds);
        if let Some(candidate) = &self.byte_gep_typed_candidates[key] {
            return Ok(candidate.clone());
        }
        // Preserve the original mandatory/optional telescope charges, but
        // instantiate no caller locals. All three congruences and eliminators
        // remain paid; typed ascription replaces only the redundant Refl/trans
        // presentation bridges inside each neutral congruence.
        let depth = if inbounds { 17 } else { 16 };
        for _ in 0..depth {
            self.charge()?;
        }
        let (context, input) = neutral_selected(depth);
        let equality = |position: usize| {
            let (ty, left, right) = input.equalities(&context)[position].clone();
            PendingEquality::candidate(
                ty,
                left,
                right,
                Expr::bvar(depth - (8 + position as u32) - 1),
            )
        };
        let proposition = |position: usize| {
            PendingProof::candidate(
                input.propositions()[position].clone(),
                Expr::bvar(depth - (11 + position as u32) - 1),
            )
        };
        let proof = self.byte_gep_resolved_term_with_binders(
            input.resolved(),
            GepResolvedPremises {
                layout: equality(0),
                layout_size: equality(1),
                pointer: equality(2),
                base_positive: proposition(0),
                stride_positive: proposition(1),
                stride_bound: proposition(2),
                delta_bound: proposition(3),
                result_bound: proposition(4),
            },
            PendingEquality::reflexive(option("Nat"), some("Nat", input.index.clone())),
            input.evaluation(
                context,
                constant(if inbounds { "Bool.true" } else { "Bool.false" }),
            ),
            inbounds.then(|| Expr::bvar(0)),
            "typed GEP derived result",
            GepProofBinders::Neutral,
        )?;
        let term = close_selected_body(inbounds, proof.term);
        // Closing is still a structural scope check, not kernel admission.
        // No candidate is cached if any paid construction/closing step fails.
        let closed = self.scope.close(&term).map_err(|error| error.to_string())?;
        self.byte_gep_typed_candidates[key] = Some(closed.clone());
        Ok(closed)
    }
}

// The sixteen mandatory parameters are context, pointee, layout, stride,
// pointer, base, index, memory, three equality proofs and five arithmetic
// proofs. Inbounds adds its exact current-memory membership equality last.
// This is a fixed neutral telescope, never an invented caller-Scope.
fn neutral_selected(depth: u32) -> (Expr, ByteGepTyped) {
    let parameter = |position| Expr::bvar(depth - position - 1);
    (
        parameter(0),
        ByteGepTyped {
            pointee: parameter(1),
            layout: parameter(2),
            stride: parameter(3),
            pointer: parameter(4),
            base: parameter(5),
            index: parameter(6),
            memory: parameter(7),
        },
    )
}

fn closed_selected_parameter_types(inbounds: bool) -> Vec<Expr> {
    let mut types = vec![
        constant("IRByteContextV1"),
        constant("IRTy"),
        constant("IRByteLayoutV1"),
        constant("Nat"),
        constant("IRScalar"),
        constant("Nat"),
        constant("Nat"),
        constant("IRByteMemoryV1"),
    ];
    for position in 0..3 {
        let (context, input) = neutral_selected(8 + position as u32);
        let (ty, left, right) = input.equalities(&context)[position].clone();
        types.push(eq(&ty, left, right));
    }
    for position in 0..5 {
        let (_, input) = neutral_selected(11 + position as u32);
        types.push(input.propositions()[position].clone());
    }
    if inbounds {
        let (_, input) = neutral_selected(16);
        types.push(eq(
            &constant("Bool"),
            input.resolved().membership(),
            constant("Bool.true"),
        ));
    }
    types
}

fn close_selected_body(inbounds: bool, body: Expr) -> Expr {
    closed_selected_parameter_types(inbounds)
        .into_iter()
        .rev()
        .fold(body, |body, ty| {
            Expr::lam(clean_kernel::BinderInfo::Default, ty, body)
        })
}
