// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact nominal singleton-GEP candidates for the existing ByteV1 denotation.
//! The layout, ordered SSA read, arithmetic bounds and actual current memory
//! remain proof inputs. The bounded I64/U64 reflection profile authenticates
//! source types separately: ByteV1 still requires each runtime index below
//! 2^63 and does not read GEP operand catalogs. No source type is relabeled,
//! no index is truncated, and no allocation or native authority is inferred.

use super::*;

#[cfg(test)]
#[path = "core_execution_typed_gep_tests.rs"]
mod tests;

#[path = "core_execution_byte_gep_typed.rs"]
mod selected;
pub use selected::{ByteGepTyped, ByteGepTypedChecks, ByteGepTypedPremises, ByteGepTypedResult};

/// Actual singleton operands and exact reflected pointee layout. `indices`
/// is the original resolved list, not a replacement instruction or SSA graph.
#[derive(Clone)]
pub struct ByteGepSingleton {
    pub pointee: Expr,
    pub layout: Expr,
    pub stride: Expr,
    pub pointer: Expr,
    pub indices: Expr,
    pub base: Expr,
    pub index: Expr,
    pub memory: Expr,
}

/// Expected claims only: every equality is `(type, left, right)`. No field
/// contains a proof, checked verdict, source type theorem or access permission.
/// A consumer supplies independently replayed candidates for these endpoints.
#[derive(Clone)]
pub struct ByteGepSingletonChecks {
    pub layout: (Expr, Expr, Expr),
    pub layout_size: (Expr, Expr, Expr),
    pub pointer: (Expr, Expr, Expr),
    pub indices: (Expr, Expr, Expr),
    pub base_positive: Expr,
    pub index_bound: Expr,
    pub stride_positive: Expr,
    pub stride_bound: Expr,
    pub delta_bound: Expr,
    pub result_bound: Expr,
    /// Required only by the inbounds entrypoint. Merely constructing this
    /// claim establishes neither membership nor permission to read or write.
    pub inbounds_membership: (Expr, Expr, Expr),
}

#[derive(Clone)]
pub struct ByteGepSingletonPremises {
    /// layout(actual context, actual nominal pointee) = some actual layout.
    pub layout: PendingEquality,
    /// size(actual layout) = actual stride; no invented scalar layout.
    pub layout_size: PendingEquality,
    pub pointer: PendingEquality,
    /// Actual ordered resolved operands = [IRScalar.int_ index].
    pub indices: PendingEquality,
    pub base_positive: PendingProof,
    /// ByteV1's actual guard: index < 2^63, even for nominal U64 operands.
    pub index_bound: PendingProof,
    pub stride_positive: PendingProof,
    pub stride_bound: PendingProof,
    /// stride * index < 2^64, with unbounded arithmetic, before any truncation.
    pub delta_bound: PendingProof,
    /// base + stride * index < 2^64.
    pub result_bound: PendingProof,
}

pub struct ByteGepSingletonResult {
    pub result: MemoryResult,
    pub evaluated: PendingEquality,
    pub allocations: PendingEquality,
    pub result_fits: PendingEquality,
}

impl ByteGepSingleton {
    /// Return the shared exact expected claims without evaluating, checking or
    /// changing anything. This avoids a consumer duplicating ByteV1 predicates.
    #[must_use]
    pub fn checks(&self, context: &Expr) -> ByteGepSingletonChecks {
        let [layout, layout_size, pointer, indices] = self.equalities(context);
        let [
            base_positive,
            index_bound,
            stride_positive,
            stride_bound,
            delta_bound,
            result_bound,
        ] = self.propositions();
        ByteGepSingletonChecks {
            layout,
            layout_size,
            pointer,
            indices,
            base_positive,
            index_bound,
            stride_positive,
            stride_bound,
            delta_bound,
            result_bound,
            inbounds_membership: (constant("Bool"), self.membership(), constant("Bool.true")),
        }
    }

    fn delta(&self) -> Expr {
        app("Nat.mul", [self.stride.clone(), self.index.clone()])
    }

    fn address(&self) -> Expr {
        app("Nat.add", [self.base.clone(), self.delta()])
    }

    fn evaluation(&self, context: Expr, flag: Expr) -> Expr {
        app(
            "ir_byte_gep_v1",
            [
                context,
                self.pointee.clone(),
                self.pointer.clone(),
                self.indices.clone(),
                flag,
                self.memory.clone(),
            ],
        )
    }

    fn equalities(&self, context: &Expr) -> [(Expr, Expr, Expr); 4] {
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
            (
                app("IRList", [constant("IRScalar")]),
                self.indices.clone(),
                list("IRScalar", &[scalar(self.index.clone())]),
            ),
        ]
    }

    fn propositions(&self) -> [Expr; 6] {
        [
            app("Nat.lt", [nat(0), self.base.clone()]),
            app("Nat.lt", [self.index.clone(), nat(1_u64 << 63)]),
            app("Nat.lt", [nat(0), self.stride.clone()]),
            app("Nat.lt", [self.stride.clone(), limit()]),
            app("Nat.lt", [self.delta(), limit()]),
            app("Nat.lt", [self.address(), limit()]),
        ]
    }

    fn membership(&self) -> Expr {
        app(
            "ir_byte_same_allocation_v1",
            [
                allocs(self.memory.clone()),
                self.base.clone(),
                self.address(),
            ],
        )
    }
}

/// Build the actual nested eliminator functions once inside the universal
/// helper. Reuse their exact success functions in the corresponding case
/// proofs instead of rebuilding and rebinding the same recursors. The three
/// locals still use the ordinary allocator; all actual input operands remain
/// parameters of the enclosing closed GEP candidate.
struct GepEliminators {
    pointer_success: Expr,
    pointer: Expr,
    indices: Expr,
    layout: Expr,
}

/// The shared layout/pointer/arithmetic suffix consumes an already selected
/// option. The legacy list decoder and the fetched nominal decoder remain
/// separate; neither is given authority by this private representation.
struct GepResolved {
    layout: Expr,
    stride: Expr,
    pointer: Expr,
    base: Expr,
    index: Expr,
    memory: Expr,
}

impl GepResolved {
    fn delta(&self) -> Expr {
        app("Nat.mul", [self.stride.clone(), self.index.clone()])
    }

    fn address(&self) -> Expr {
        app("Nat.add", [self.base.clone(), self.delta()])
    }

    fn membership(&self) -> Expr {
        app(
            "ir_byte_same_allocation_v1",
            [
                allocs(self.memory.clone()),
                self.base.clone(),
                self.address(),
            ],
        )
    }
}

struct GepResolvedPremises {
    layout: PendingEquality,
    layout_size: PendingEquality,
    pointer: PendingEquality,
    base_positive: PendingProof,
    stride_positive: PendingProof,
    stride_bound: PendingProof,
    delta_bound: PendingProof,
    result_bound: PendingProof,
}

impl GepEliminators {
    fn new(
        assembler: &mut Assembler<'_>,
        input: &GepResolved,
        decoded: Expr,
        flag: Expr,
    ) -> Result<Self> {
        let shape = assembler.local(constant("IRByteLayoutV1"))?;
        let index = assembler.local(constant("Nat"))?;
        let address = assembler.local(constant("Nat"))?;
        let success = address.lam(gep_at(
            shape.term().clone(),
            address.term().clone(),
            index.term().clone(),
            input.memory.clone(),
            flag,
        ));
        let motive = Expr::lam(
            clean_kernel::BinderInfo::Default,
            option("Nat"),
            constant("IRByteMemoryResultV1"),
        );
        let pointer = option_rec([
            constant("Nat"),
            motive.clone(),
            fault("type_error", "not_ptr", input.memory.clone()),
            success.clone(),
            pointer_address(input.pointer.clone()),
        ]);
        let indices = option_rec([
            constant("Nat"),
            motive,
            fault("unmodelled", "width_bounded", input.memory.clone()),
            index.lam(pointer.clone()),
            decoded,
        ]);
        let layout = choose(
            &constant("IRByteMemoryResultV1"),
            size_guard(app("ir_byte_layout_size_v1", [shape.term().clone()])),
            indices.clone(),
            fault("unmodelled", "width_bounded", input.memory.clone()),
        );
        Ok(Self {
            pointer_success: shape.lam(index.lam(success)),
            pointer: shape.lam(index.lam(pointer)),
            indices: shape.lam(indices),
            layout: shape.lam(layout),
        })
    }
}

// The scoped route remains the legacy singleton proof's original allocator.
// Only a proof under the selected helper's fixed neutral telescope uses the
// closed route. Its typed presentation retains both old/new equalities while
// omitting the scoped route's four actual Refl/trans bridge constructions.
#[derive(Clone, Copy)]
enum GepProofBinders {
    Scoped,
    Neutral,
}

impl GepProofBinders {
    fn mapped(
        self,
        assembler: &mut Assembler<'_>,
        equality: PendingEquality,
        ty: Expr,
        map: impl Fn(Expr) -> Expr,
        closed_function: impl FnOnce() -> Expr,
    ) -> Result<PendingEquality> {
        if matches!(self, Self::Scoped) {
            return mapped(assembler, equality, ty, map);
        }
        let left = map(equality.left.clone());
        let right = map(equality.right.clone());
        // This paid API replaces precisely the original paid scoped local.
        let proof = assembler.congruence_function(equality, ty, closed_function())?;
        assembler.ascribe_preserving_endpoints(proof, left, right)
    }

    fn eliminators(
        self,
        assembler: &mut Assembler<'_>,
        input: &GepResolved,
        decoded: Expr,
        flag: Expr,
    ) -> Result<GepEliminators> {
        if matches!(self, Self::Scoped) {
            return GepEliminators::new(assembler, input, decoded, flag);
        }
        // Preserve shape, index, address construction charges in that order.
        for _ in 0..3 {
            assembler.charge()?;
        }
        let binder = clean_kernel::BinderInfo::Default;
        let result_ty = constant("IRByteMemoryResultV1");
        let motive = Expr::lam(binder, option("Nat"), result_ty.clone());
        // Every enclosing neutral field is lifted past ONLY these binders.
        let pointer_success = Expr::lam(
            binder,
            constant("IRByteLayoutV1"),
            Expr::lam(
                binder,
                constant("Nat"),
                Expr::lam(
                    binder,
                    constant("Nat"),
                    gep_at(
                        Expr::bvar(2),
                        Expr::bvar(0),
                        Expr::bvar(1),
                        input.memory.lift(3),
                        flag.lift(3),
                    ),
                ),
            ),
        );
        let pointer = Expr::lam(
            binder,
            constant("IRByteLayoutV1"),
            Expr::lam(
                binder,
                constant("Nat"),
                option_rec([
                    constant("Nat"),
                    motive.clone(),
                    fault("type_error", "not_ptr", input.memory.lift(2)),
                    Expr::apps(pointer_success.lift(2), [Expr::bvar(1), Expr::bvar(0)]),
                    pointer_address(input.pointer.lift(2)),
                ]),
            ),
        );
        let indices = Expr::lam(
            binder,
            constant("IRByteLayoutV1"),
            option_rec([
                constant("Nat"),
                motive,
                fault("unmodelled", "width_bounded", input.memory.lift(1)),
                Expr::app(pointer.lift(1), Expr::bvar(0)),
                decoded.lift(1),
            ]),
        );
        let layout = Expr::lam(
            binder,
            constant("IRByteLayoutV1"),
            choose(
                &result_ty,
                size_guard(app("ir_byte_layout_size_v1", [Expr::bvar(0)])),
                Expr::app(indices.lift(1), Expr::bvar(0)),
                fault("unmodelled", "width_bounded", input.memory.lift(1)),
            ),
        );
        Ok(GepEliminators {
            pointer_success,
            pointer,
            indices,
            layout,
        })
    }
}

fn size_guard(size: Expr) -> Expr {
    app(
        "Bool.and",
        [
            app("ir_nat_pos", [size.clone()]),
            app("ir_nat_ltb", [size, limit()]),
        ],
    )
}

impl Assembler<'_> {
    /// Ordinary singleton GEP. Positivity and nonwrapping arithmetic do not
    /// establish that either pointer belongs to any allocation.
    pub fn byte_gep_singleton_noninbounds(
        &mut self,
        context: Expr,
        input: ByteGepSingleton,
        premises: ByteGepSingletonPremises,
    ) -> Result<ByteGepSingletonResult> {
        self.byte_gep_singleton(context, input, premises, None)
    }

    /// Inbounds singleton GEP. Membership must name the exact current memory
    /// and full scaled result. One-past is allowed but authorizes no access.
    pub fn byte_gep_singleton_inbounds(
        &mut self,
        context: Expr,
        input: ByteGepSingleton,
        premises: ByteGepSingletonPremises,
        same_allocation: PendingEquality,
    ) -> Result<ByteGepSingletonResult> {
        same_allocation.endpoints(
            &constant("Bool"),
            &input.membership(),
            &constant("Bool.true"),
        )?;
        self.byte_gep_singleton(context, input, premises, Some(same_allocation))
    }

    fn byte_gep_singleton(
        &mut self,
        context: Expr,
        input: ByteGepSingleton,
        premises: ByteGepSingletonPremises,
        membership: Option<PendingEquality>,
    ) -> Result<ByteGepSingletonResult> {
        self.charge()?;
        self.items(1)?;
        for (proof, (ty, left, right)) in [
            &premises.layout,
            &premises.layout_size,
            &premises.pointer,
            &premises.indices,
        ]
        .into_iter()
        .zip(input.equalities(&context))
        {
            proof.endpoints(&ty, &left, &right)?;
        }
        for (proof, expected) in [
            &premises.base_positive,
            &premises.index_bound,
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
                "singleton GEP arithmetic premise",
            )?;
        }
        let inbounds = membership.is_some();
        let flag = constant(if inbounds { "Bool.true" } else { "Bool.false" });
        let helper = self.byte_gep_singleton_helper(inbounds)?;
        let address = input.address();
        let positive = app(
            "Nat.le_trans",
            [
                nat(1),
                input.base.clone(),
                address.clone(),
                premises.base_positive.term.clone(),
                app("Nat.le_add_right", [input.base.clone(), input.delta()]),
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
                    input.indices,
                    input.base,
                    input.index,
                    input.memory.clone(),
                    premises.layout.term,
                    premises.layout_size.term,
                    premises.pointer.term,
                    premises.indices.term,
                    premises.base_positive.term,
                    premises.index_bound.term,
                    premises.stride_positive.term,
                    premises.stride_bound.term,
                    premises.delta_bound.term,
                    premises.result_bound.term.clone(),
                ]
                .into_iter()
                .chain(membership.map(|proof| proof.term)),
            ),
        );
        Ok(ByteGepSingletonResult {
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

    // Close one universal helper per actual flag; changed source expressions
    // are application arguments, not traversed beneath fresh helper binders.
    fn byte_gep_singleton_helper(&mut self, inbounds: bool) -> Result<Expr> {
        let key = usize::from(inbounds);
        if let Some(candidate) = &self.byte_gep_singleton_candidates[key] {
            return Ok(candidate.clone());
        }
        let context = self.local(constant("IRByteContextV1"))?;
        let pointee = self.local(constant("IRTy"))?;
        let shape = self.local(constant("IRByteLayoutV1"))?;
        let stride = self.local(constant("Nat"))?;
        let pointer = self.local(constant("IRScalar"))?;
        let indices = self.local(app("IRList", [constant("IRScalar")]))?;
        let base = self.local(constant("Nat"))?;
        let index = self.local(constant("Nat"))?;
        let memory = self.local(constant("IRByteMemoryV1"))?;
        let input = ByteGepSingleton {
            pointee: pointee.term().clone(),
            layout: shape.term().clone(),
            stride: stride.term().clone(),
            pointer: pointer.term().clone(),
            indices: indices.term().clone(),
            base: base.term().clone(),
            index: index.term().clone(),
            memory: memory.term().clone(),
        };
        let mut parameters = vec![
            context.clone(),
            pointee,
            shape,
            stride,
            pointer,
            indices,
            base,
            index,
            memory,
        ];
        let mut equalities = Vec::with_capacity(4);
        for (ty, left, right) in input.equalities(context.term()) {
            let local = self.local(eq(&ty, left.clone(), right.clone()))?;
            equalities.push(PendingEquality::candidate(
                ty,
                left,
                right,
                local.term().clone(),
            ));
            parameters.push(local);
        }
        let mut proofs = Vec::with_capacity(6);
        for proposition in input.propositions() {
            let local = self.local(proposition.clone())?;
            proofs.push(PendingProof::candidate(proposition, local.term().clone()));
            parameters.push(local);
        }
        let membership = if inbounds {
            let local = self.local(eq(
                &constant("Bool"),
                input.membership(),
                constant("Bool.true"),
            ))?;
            let term = local.term().clone();
            parameters.push(local);
            Some(term)
        } else {
            None
        };
        let proof = self.byte_gep_singleton_term(
            context.term().clone(),
            input,
            ByteGepSingletonPremises {
                layout: equalities[0].clone(),
                layout_size: equalities[1].clone(),
                pointer: equalities[2].clone(),
                indices: equalities[3].clone(),
                base_positive: proofs[0].clone(),
                index_bound: proofs[1].clone(),
                stride_positive: proofs[2].clone(),
                stride_bound: proofs[3].clone(),
                delta_bound: proofs[4].clone(),
                result_bound: proofs[5].clone(),
            },
            membership,
        )?;
        let term = parameters
            .iter()
            .rev()
            .fold(proof.term, |body, local| local.lam(body));
        let closed = self.scope.close(&term).map_err(|error| error.to_string())?;
        self.byte_gep_singleton_candidates[key] = Some(closed.clone());
        Ok(closed)
    }

    fn byte_gep_singleton_term(
        &mut self,
        context: Expr,
        input: ByteGepSingleton,
        premises: ByteGepSingletonPremises,
        membership: Option<Expr>,
    ) -> Result<PendingEquality> {
        let flag = constant(if membership.is_some() {
            "Bool.true"
        } else {
            "Bool.false"
        });
        let option_nat = option("Nat");
        let none = app("IROption.none", [constant("Nat")]);
        let index = input.index.clone();
        let index_word_bound = app(
            "Nat.le_trans",
            [
                app("Nat.succ", [index.clone()]),
                nat(1_u64 << 63),
                limit(),
                premises.index_bound.term.clone(),
                app("Nat.le_add_right", [nat(1_u64 << 63), nat(1_u64 << 63)]),
            ],
        );
        let decoded_index = true_case(
            option_nat.clone(),
            app("ir_byte_gep_index_v1", [scalar(index.clone())]),
            none.clone(),
            some("Nat", index.clone()),
            ltb(index.clone(), nat(1_u64 << 63), premises.index_bound.term),
            PendingEquality::reflexive(option_nat.clone(), some("Nat", index.clone())),
        );
        let sum_case = |sum: Expr| {
            choose(
                &option_nat,
                app("ir_nat_ltb", [sum.clone(), limit()]),
                some("Nat", sum),
                none.clone(),
            )
        };
        let add_zero = PendingEquality::candidate(
            constant("Nat"),
            app("Nat.add", [index.clone(), nat(0)]),
            index.clone(),
            app("Nat.add_zero", [index.clone()]),
        );
        let sum = mapped(self, add_zero, option_nat.clone(), sum_case)?;
        let bounded_sum = true_case(
            option_nat.clone(),
            sum_case(index.clone()),
            none.clone(),
            some("Nat", index.clone()),
            ltb(index.clone(), limit(), index_word_bound),
            PendingEquality::reflexive(option_nat.clone(), some("Nat", index.clone())),
        );
        let sum = self.compose(sum, bounded_sum)?;
        let singleton = some_case(
            self,
            "Nat",
            option_nat.clone(),
            app(
                "ir_byte_gep_indices_v1",
                [list("IRScalar", &[scalar(index.clone())])],
            ),
            none.clone(),
            decoded_index,
            index.clone(),
            |_, value| Ok(sum_case(app("Nat.add", [value, nat(0)]))),
            sum,
        )?;
        let indices = self.congruence_function(
            premises.indices,
            option_nat,
            constant("ir_byte_gep_indices_v1"),
        )?;
        let indices = self.compose(indices, singleton)?;

        let source = input.evaluation(context, flag);
        self.byte_gep_resolved_term(
            GepResolved {
                layout: input.layout,
                stride: input.stride,
                pointer: input.pointer,
                base: input.base,
                index: input.index,
                memory: input.memory,
            },
            GepResolvedPremises {
                layout: premises.layout,
                layout_size: premises.layout_size,
                pointer: premises.pointer,
                base_positive: premises.base_positive,
                stride_positive: premises.stride_positive,
                stride_bound: premises.stride_bound,
                delta_bound: premises.delta_bound,
                result_bound: premises.result_bound,
            },
            indices,
            source,
            membership,
            "singleton GEP derived result",
        )
    }

    fn byte_gep_resolved_term(
        &mut self,
        input: GepResolved,
        premises: GepResolvedPremises,
        indices: PendingEquality,
        source: Expr,
        membership: Option<Expr>,
        derived_result_label: &str,
    ) -> Result<PendingEquality> {
        self.byte_gep_resolved_term_with_binders(
            input,
            premises,
            indices,
            source,
            membership,
            derived_result_label,
            GepProofBinders::Scoped,
        )
    }

    fn byte_gep_resolved_term_with_binders(
        &mut self,
        input: GepResolved,
        premises: GepResolvedPremises,
        indices: PendingEquality,
        source: Expr,
        membership: Option<Expr>,
        derived_result_label: &str,
        binders: GepProofBinders,
    ) -> Result<PendingEquality> {
        let flag = constant(if membership.is_some() {
            "Bool.true"
        } else {
            "Bool.false"
        });
        let result_ty = constant("IRByteMemoryResultV1");
        let index = input.index.clone();
        let base = input.base.clone();
        let delta = input.delta();
        let address = input.address();
        let memory = input.memory.clone();
        let expected = MemoryResult {
            value: app("IRScalar.ptr_", [address.clone()]),
            memory: memory.clone(),
        }
        .result();

        let arithmetic = join(
            bool_fact(
                app("ir_nat_pos", [base.clone()]),
                app(
                    "ir_byte_allocation_pos_v1",
                    [base.clone(), premises.base_positive.term.clone()],
                ),
            ),
            join(
                ltb(delta.clone(), limit(), premises.delta_bound.term),
                join(
                    ltb(address.clone(), limit(), premises.result_bound.term),
                    bool_fact(
                        app(
                            "Bool.or",
                            [app("Bool.not", [flag.clone()]), input.membership()],
                        ),
                        membership
                            .unwrap_or_else(|| refl(&constant("Bool"), constant("Bool.true"))),
                    ),
                ),
            ),
        );
        let positive = app(
            "Nat.le_trans",
            [
                nat(1),
                base.clone(),
                address.clone(),
                premises.base_positive.term,
                app("Nat.le_add_right", [base.clone(), delta]),
            ],
        );
        let pointer_value = PendingEquality::candidate(
            constant("IRScalar"),
            app("ir_byte_pointer_value_v1", [address.clone()]),
            app("IRScalar.ptr_", [address.clone()]),
            app(
                "ir_byte_allocation_pointer_value_v1",
                [address.clone(), positive],
            ),
        );
        let result_value = binders.mapped(
            self,
            pointer_value,
            result_ty.clone(),
            |value| {
                MemoryResult {
                    value,
                    memory: memory.clone(),
                }
                .result()
            },
            || {
                Expr::lam(
                    clean_kernel::BinderInfo::Default,
                    constant("IRScalar"),
                    MemoryResult {
                        value: Expr::bvar(0),
                        memory: memory.lift(1),
                    }
                    .result(),
                )
            },
        )?;
        let arithmetic = true_case(
            result_ty.clone(),
            app(
                "ir_byte_gep_at_v1",
                [
                    base.clone(),
                    input.stride.clone(),
                    index.clone(),
                    flag.clone(),
                    memory.clone(),
                ],
            ),
            fault("ub", "bad_addr", memory.clone()),
            result_value.left.clone(),
            arithmetic,
            result_value,
        );
        let shape_at = binders.mapped(
            self,
            premises.layout_size.clone(),
            result_ty.clone(),
            |stride| {
                app(
                    "ir_byte_gep_at_v1",
                    [
                        base.clone(),
                        stride,
                        index.clone(),
                        flag.clone(),
                        memory.clone(),
                    ],
                )
            },
            || {
                Expr::lam(
                    clean_kernel::BinderInfo::Default,
                    constant("Nat"),
                    app(
                        "ir_byte_gep_at_v1",
                        [
                            base.lift(1),
                            Expr::bvar(0),
                            index.lift(1),
                            flag.lift(1),
                            memory.lift(1),
                        ],
                    ),
                )
            },
        )?;
        let at = self.compose(shape_at, arithmetic)?;
        let eliminators = binders.eliminators(self, &input, indices.left.clone(), flag.clone())?;
        let pointer_source = Expr::apps(
            eliminators.pointer.clone(),
            [input.layout.clone(), index.clone()],
        );
        let pointer = some_case_function(
            "Nat",
            result_ty.clone(),
            pointer_source,
            fault("type_error", "not_ptr", memory.clone()),
            premises.pointer,
            base,
            Expr::apps(
                eliminators.pointer_success,
                [input.layout.clone(), index.clone()],
            ),
            at,
        );
        let indices_source = Expr::app(eliminators.indices, input.layout.clone());
        let indices = some_case_function(
            "Nat",
            result_ty.clone(),
            indices_source,
            fault("unmodelled", "width_bounded", memory.clone()),
            indices,
            index,
            Expr::app(eliminators.pointer, input.layout.clone()),
            pointer,
        );
        let stride_guard = join(
            bool_fact(
                app("ir_nat_pos", [input.stride.clone()]),
                app(
                    "ir_byte_allocation_pos_v1",
                    [input.stride.clone(), premises.stride_positive.term],
                ),
            ),
            ltb(input.stride.clone(), limit(), premises.stride_bound.term),
        );
        let actual_guard = binders.mapped(
            self,
            premises.layout_size,
            constant("Bool"),
            size_guard,
            || {
                Expr::lam(
                    clean_kernel::BinderInfo::Default,
                    constant("Nat"),
                    size_guard(Expr::bvar(0)),
                )
            },
        )?;
        let actual_guard = self.compose(actual_guard, stride_guard)?;
        let layout_source = Expr::app(eliminators.layout.clone(), input.layout.clone());
        let admitted = true_case(
            result_ty.clone(),
            layout_source,
            fault("unmodelled", "width_bounded", memory.clone()),
            indices.left.clone(),
            actual_guard,
            indices,
        );
        let proof = some_case_function(
            "IRByteLayoutV1",
            result_ty,
            source,
            fault("unmodelled", "width_bounded", memory),
            premises.layout,
            input.layout.clone(),
            eliminators.layout,
            admitted,
        );
        require_same(&proof.right, &expected, derived_result_label)?;
        Ok(proof)
    }
}
