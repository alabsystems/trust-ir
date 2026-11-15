// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Untrusted pointwise proof builders for the existing byte-memory laws.
//!
//! Ordinary I8 GEP needs bounded arithmetic, not a fresh allocation. Eight-byte
//! stores need the actual accessibility predicate, not a high-water invariant.
//! Independent typed loads additionally require initialization at that exact
//! memory, with explicit codec and pointer identity. They never execute a node.
//! Returned memory is constructed here from the real write operation; raw and
//! typed readback both observe that same memory. None of these candidates is
//! execution or native authority. `FetchedSite::memory_value` remains the only
//! memory transfer gate, and the consumer must replay its complete closed claim.

use super::*;

#[path = "core_execution_typed_gep.rs"]
pub(super) mod typed_gep;

#[cfg(test)]
#[path = "core_execution_pointer_codec_tests.rs"]
mod pointer_codec_tests;

fn option(ty: &str) -> Expr {
    app("IROption", [constant(ty)])
}
fn limit() -> Expr {
    constant("ir_byte_limit_v1")
}
fn scalar(value: Expr) -> Expr {
    app("IRScalar.int_", [value])
}
fn i8_ty() -> Expr {
    app("IRTy.int_", [nat(8)])
}
fn allocs(memory: Expr) -> Expr {
    app("ir_byte_mem_allocs_v1", [memory])
}
fn bytes(memory: Expr) -> Expr {
    app("ir_byte_mem_bytes_v1", [memory])
}
fn cursor(memory: Expr) -> Expr {
    app("ir_byte_mem_next_v1", [memory])
}
fn layout(ty: Expr, size: u64) -> Expr {
    app(
        "IRByteLayoutV1.mk",
        [
            ty,
            nat(size),
            nat(size),
            list("IRTy", &[]),
            list("Nat", &[]),
        ],
    )
}
fn layout_guard(layout: Expr) -> Expr {
    app(
        "Bool.and",
        [
            app(
                "ir_nat_eqb",
                [nat(8), app("ir_byte_layout_size_v1", [layout.clone()])],
            ),
            app(
                "ir_byte_alignment_v1",
                [app("ir_byte_layout_align_v1", [layout])],
            ),
        ],
    )
}
fn pointer_address(pointer: Expr) -> Expr {
    app("ir_byte_pointer_address_v1", [pointer])
}
fn option_rec(arguments: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("IROption.rec"),
            vec![Level::succ(Level::zero())],
        ),
        arguments,
    )
}
fn fault(kind: &str, code: &str, memory: Expr) -> Expr {
    app(
        "IRByteMemoryResultV1.fault",
        [
            app(
                &format!("IROutcome.{kind}"),
                [constant(&format!("IRFault.{code}"))],
            ),
            memory,
        ],
    )
}
fn bool_fact(left: Expr, term: Expr) -> PendingEquality {
    PendingEquality::candidate(constant("Bool"), left, constant("Bool.true"), term)
}
fn ltb(left: Expr, right: Expr, term: Expr) -> PendingEquality {
    bool_fact(
        app("ir_nat_ltb", [left.clone(), right.clone()]),
        app("ir_byte_ltb_of_lt_v1", [left, right, term]),
    )
}
fn mapped(
    assembler: &mut Assembler<'_>,
    equality: PendingEquality,
    ty: Expr,
    map: impl Fn(Expr) -> Expr,
) -> Result<PendingEquality> {
    let left = map(equality.left.clone());
    let right = map(equality.right.clone());
    let proof = assembler.congruence(equality, ty.clone(), map)?;
    let start = assembler.conversion(ty.clone(), left, proof.left.clone())?;
    let end = assembler.conversion(ty, proof.right.clone(), right)?;
    let proof = assembler.compose(start, proof)?;
    assembler.compose(proof, end)
}
fn join(left: PendingEquality, right: PendingEquality) -> PendingEquality {
    bool_fact(
        app("Bool.and", [left.left.clone(), right.left.clone()]),
        app(
            "ir_byte_world_and_intro_v1",
            [left.left, right.left, left.term, right.term],
        ),
    )
}
fn true_case(
    ty: Expr,
    source: Expr,
    failure: Expr,
    success: Expr,
    guard: PendingEquality,
    step: PendingEquality,
) -> PendingEquality {
    PendingEquality::candidate(
        ty.clone(),
        source,
        step.right.clone(),
        app(
            "ir_byte_case_true_v1",
            [
                ty, guard.left, failure, success, step.right, guard.term, step.term,
            ],
        ),
    )
}
#[allow(clippy::too_many_arguments)]
fn some_case(
    assembler: &mut Assembler<'_>,
    input_ty: &str,
    ty: Expr,
    source: Expr,
    failure: Expr,
    found: PendingEquality,
    value: Expr,
    success: impl FnOnce(&mut Assembler<'_>, Expr) -> Result<Expr>,
    step: PendingEquality,
) -> Result<PendingEquality> {
    let local = assembler.local(constant(input_ty))?;
    let body = success(assembler, local.term().clone())?;
    let function = local.lam(body);
    Ok(some_case_function(
        input_ty, ty, source, failure, found, value, function, step,
    ))
}

/// Use an already-constructed actual option-success function. This changes
/// neither case-law premises nor equality endpoints and allocates no locals.
#[allow(clippy::too_many_arguments)]
fn some_case_function(
    input_ty: &str,
    ty: Expr,
    source: Expr,
    failure: Expr,
    found: PendingEquality,
    value: Expr,
    function: Expr,
    step: PendingEquality,
) -> PendingEquality {
    PendingEquality::candidate(
        ty.clone(),
        source,
        step.right.clone(),
        app(
            "ir_byte_case_some_v1",
            [
                constant(input_ty),
                ty,
                found.left,
                value,
                failure,
                function,
                step.right,
                found.term,
                step.term,
            ],
        ),
    )
}

fn gep_at(shape: Expr, address: Expr, index: Expr, memory: Expr, flag: Expr) -> Expr {
    app(
        "ir_byte_gep_at_v1",
        [
            address,
            app("ir_byte_layout_size_v1", [shape]),
            index,
            flag,
            memory,
        ],
    )
}
fn gep_pointer_option(
    assembler: &mut Assembler<'_>,
    shape: Expr,
    index: Expr,
    input: &ByteGepI8,
    flag: Expr,
) -> Result<Expr> {
    let address = assembler.local(constant("Nat"))?;
    let body = gep_at(
        shape,
        address.term().clone(),
        index,
        input.memory.clone(),
        flag,
    );
    Ok(option_rec([
        constant("Nat"),
        Expr::lam(
            clean_kernel::BinderInfo::Default,
            option("Nat"),
            constant("IRByteMemoryResultV1"),
        ),
        fault("type_error", "not_ptr", input.memory.clone()),
        address.lam(body),
        pointer_address(input.pointer.clone()),
    ]))
}
fn gep_indices_option(
    assembler: &mut Assembler<'_>,
    shape: Expr,
    input: &ByteGepI8,
    flag: Expr,
) -> Result<Expr> {
    let index = assembler.local(constant("Nat"))?;
    let body = gep_pointer_option(assembler, shape, index.term().clone(), input, flag)?;
    Ok(option_rec([
        constant("Nat"),
        Expr::lam(
            clean_kernel::BinderInfo::Default,
            option("Nat"),
            constant("IRByteMemoryResultV1"),
        ),
        fault("unmodelled", "width_bounded", input.memory.clone()),
        index.lam(body),
        app("ir_byte_gep_indices_v1", [input.indices.clone()]),
    ]))
}
fn gep_layout_body(
    assembler: &mut Assembler<'_>,
    shape: Expr,
    input: &ByteGepI8,
    flag: Expr,
) -> Result<Expr> {
    let admitted = gep_indices_option(assembler, shape.clone(), input, flag)?;
    Ok(choose(
        &constant("IRByteMemoryResultV1"),
        app(
            "Bool.and",
            [
                app(
                    "ir_nat_pos",
                    [app("ir_byte_layout_size_v1", [shape.clone()])],
                ),
                app(
                    "ir_nat_ltb",
                    [app("ir_byte_layout_size_v1", [shape]), limit()],
                ),
            ],
        ),
        admitted,
        fault("unmodelled", "width_bounded", input.memory.clone()),
    ))
}

/// Exact operands of the singleton, non-inbounds I8 profile. The reflected
/// fetched instruction must separately establish signed-I64 index identity.
#[derive(Clone)]
pub struct ByteGepI8 {
    pub pointer: Expr,
    pub indices: Expr,
    pub base: Expr,
    pub offset: Expr,
    pub memory: Expr,
}

#[derive(Clone)]
pub struct ByteGepI8Premises {
    /// layout(actual context, I8) = some (mk I8 1 1 [] []).
    pub layout: PendingEquality,
    /// pointer_address(actual operand) = some base.
    pub pointer: PendingEquality,
    /// Actual ordered operand list = [int offset].
    pub indices: PendingEquality,
    pub positive: PendingProof,
    /// Nat.lt offset 2^63, not unsigned-64 or a negative-index encoding.
    pub index_bound: PendingProof,
    /// Nat.lt (Nat.add base offset) 2^64; arithmetic never wraps.
    pub result_bound: PendingProof,
}

pub struct ByteGepI8Result {
    pub result: MemoryResult,
    pub evaluated: PendingEquality,
    pub allocations: PendingEquality,
    pub result_fits: PendingEquality,
}

impl ByteGepI8 {
    fn address(&self) -> Expr {
        app("Nat.add", [self.base.clone(), self.offset.clone()])
    }
    fn evaluation(&self, context: Expr) -> Expr {
        self.evaluation_with_flag(context, constant("Bool.false"))
    }
    fn evaluation_with_flag(&self, context: Expr, flag: Expr) -> Expr {
        app(
            "ir_byte_gep_v1",
            [
                context,
                i8_ty(),
                self.pointer.clone(),
                self.indices.clone(),
                flag,
                self.memory.clone(),
            ],
        )
    }
    fn premise_equalities(&self, context: &Expr) -> [(Expr, Expr, Expr); 3] {
        [
            (
                option("IRByteLayoutV1"),
                app("ir_byte_layout_v1", [context.clone(), i8_ty()]),
                some("IRByteLayoutV1", layout(i8_ty(), 1)),
            ),
            (
                option("Nat"),
                pointer_address(self.pointer.clone()),
                some("Nat", self.base.clone()),
            ),
            (
                app("IRList", [constant("IRScalar")]),
                self.indices.clone(),
                list("IRScalar", &[scalar(self.offset.clone())]),
            ),
        ]
    }
    fn premise_propositions(&self) -> [Expr; 3] {
        [
            app("Nat.lt", [nat(0), self.base.clone()]),
            app("Nat.lt", [self.offset.clone(), nat(1_u64 << 63)]),
            app("Nat.lt", [self.address(), limit()]),
        ]
    }
}

impl Assembler<'_> {
    /// Bounded, nonnegative singleton I8 GEP. No allocation, ownership,
    /// accessibility or freshness premise is accepted or inferred here.
    pub fn byte_gep_i8_noninbounds(
        &mut self,
        context: Expr,
        input: ByteGepI8,
        premises: ByteGepI8Premises,
    ) -> Result<ByteGepI8Result> {
        self.byte_gep_i8(context, input, premises, None)
    }

    fn byte_gep_i8(
        &mut self,
        context: Expr,
        input: ByteGepI8,
        premises: ByteGepI8Premises,
        membership: Option<PendingEquality>,
    ) -> Result<ByteGepI8Result> {
        self.charge()?;
        self.items(1)?;
        for (proof, (ty, left, right)) in [&premises.layout, &premises.pointer, &premises.indices]
            .into_iter()
            .zip(input.premise_equalities(&context))
        {
            proof.endpoints(&ty, &left, &right)?;
        }
        for (proof, proposition) in [
            &premises.positive,
            &premises.index_bound,
            &premises.result_bound,
        ]
        .into_iter()
        .zip(input.premise_propositions())
        {
            require_same(
                proof.proposition(),
                &proposition,
                "I8 GEP arithmetic premise",
            )?;
        }
        let inbounds = membership.is_some();
        let helper = if inbounds {
            self.byte_gep_i8_helper_for(true)?
        } else {
            self.byte_gep_i8_helper()?
        };
        let address = input.address();
        let positive = app(
            "Nat.le_trans",
            [
                nat(1),
                input.base.clone(),
                address.clone(),
                premises.positive.term.clone(),
                app(
                    "Nat.le_add_right",
                    [input.base.clone(), input.offset.clone()],
                ),
            ],
        );
        let result = MemoryResult {
            value: app("IRScalar.ptr_", [address.clone()]),
            memory: input.memory.clone(),
        };
        let evaluation = if inbounds {
            input.evaluation_with_flag(context.clone(), constant("Bool.true"))
        } else {
            input.evaluation(context.clone())
        };
        let arguments = [
            context.clone(),
            input.pointer,
            input.indices,
            input.base,
            input.offset,
            input.memory.clone(),
            premises.layout.term,
            premises.pointer.term,
            premises.indices.term,
            premises.positive.term,
            premises.index_bound.term,
            premises.result_bound.term.clone(),
        ];
        let evaluated = PendingEquality::candidate(
            constant("IRByteMemoryResultV1"),
            evaluation,
            result.result(),
            Expr::apps(
                helper,
                arguments
                    .into_iter()
                    .chain(membership.map(|proof| proof.term)),
            ),
        );
        let result_fits = bool_fact(
            app(
                "ir_byte_value_matches_v1",
                [context.clone(), constant("IRTy.ptr_"), result.value.clone()],
            ),
            app(
                "ir_byte_allocated_pointer_matches_v1",
                [context, address, positive, premises.result_bound.term],
            ),
        );
        Ok(ByteGepI8Result {
            allocations: PendingEquality::reflexive(
                app("IRList", [constant("IRByteAllocationV1")]),
                allocs(input.memory),
            ),
            result,
            evaluated,
            result_fits,
        })
    }

    /// Inbounds singleton I8 GEP. Membership names the exact current memory,
    /// base and result (including one-past); it is not a dereference permission.
    /// Candidates require independent kernel replay, as on the noninbounds path.
    pub fn byte_gep_i8_inbounds(
        &mut self,
        context: Expr,
        input: ByteGepI8,
        premises: ByteGepI8Premises,
        same_allocation: PendingEquality,
    ) -> Result<ByteGepI8Result> {
        same_allocation.endpoints(
            &constant("Bool"),
            &app(
                "ir_byte_same_allocation_v1",
                [
                    allocs(input.memory.clone()),
                    input.base.clone(),
                    input.address(),
                ],
            ),
            &constant("Bool.true"),
        )?;
        self.byte_gep_i8(context, input, premises, Some(same_allocation))
    }

    /// Cache a closed polymorphic candidate. Actual memory histories, context
    /// catalogs and operand expressions are application arguments, never copied
    /// underneath the helper's fresh binders on each successive GEP.
    fn byte_gep_i8_helper(&mut self) -> Result<Expr> {
        self.byte_gep_i8_helper_for(false)
    }

    fn byte_gep_i8_helper_for(&mut self, inbounds: bool) -> Result<Expr> {
        if let Some(candidate) = if inbounds {
            &self.byte_gep_i8_inbounds_candidate
        } else {
            &self.byte_gep_i8_candidate
        } {
            return Ok(candidate.clone());
        }
        let context = self.local(constant("IRByteContextV1"))?;
        let pointer = self.local(constant("IRScalar"))?;
        let indices = self.local(app("IRList", [constant("IRScalar")]))?;
        let base = self.local(constant("Nat"))?;
        let offset = self.local(constant("Nat"))?;
        let memory = self.local(constant("IRByteMemoryV1"))?;
        let input = ByteGepI8 {
            pointer: pointer.term().clone(),
            indices: indices.term().clone(),
            base: base.term().clone(),
            offset: offset.term().clone(),
            memory: memory.term().clone(),
        };
        let mut parameters = vec![context.clone(), pointer, indices, base, offset, memory];
        let mut equalities = Vec::new();
        for (ty, left, right) in input.premise_equalities(context.term()) {
            let proof = self.local(eq(&ty, left.clone(), right.clone()))?;
            equalities.push(PendingEquality::candidate(
                ty,
                left,
                right,
                proof.term().clone(),
            ));
            parameters.push(proof);
        }
        let mut proofs = Vec::new();
        for proposition in input.premise_propositions() {
            let proof = self.local(proposition.clone())?;
            proofs.push(PendingProof::candidate(proposition, proof.term().clone()));
            parameters.push(proof);
        }
        let membership = if inbounds {
            let proposition = eq(
                &constant("Bool"),
                app(
                    "ir_byte_same_allocation_v1",
                    [
                        allocs(input.memory.clone()),
                        input.base.clone(),
                        input.address(),
                    ],
                ),
                constant("Bool.true"),
            );
            let proof = self.local(proposition)?;
            let term = proof.term().clone();
            parameters.push(proof);
            Some(term)
        } else {
            None
        };
        let candidate = self.byte_gep_i8_term(
            context.term().clone(),
            input,
            ByteGepI8Premises {
                layout: equalities[0].clone(),
                pointer: equalities[1].clone(),
                indices: equalities[2].clone(),
                positive: proofs[0].clone(),
                index_bound: proofs[1].clone(),
                result_bound: proofs[2].clone(),
            },
            membership,
        )?;
        let term = parameters
            .iter()
            .rev()
            .fold(candidate.term, |body, local| local.lam(body));
        let closed = self.scope.close(&term).map_err(|e| e.to_string())?;
        if inbounds {
            self.byte_gep_i8_inbounds_candidate = Some(closed.clone());
        } else {
            self.byte_gep_i8_candidate = Some(closed.clone());
        }
        Ok(closed)
    }

    fn byte_gep_i8_term(
        &mut self,
        context: Expr,
        input: ByteGepI8,
        premises: ByteGepI8Premises,
        membership: Option<Expr>,
    ) -> Result<PendingEquality> {
        let flag = constant(if membership.is_some() {
            "Bool.true"
        } else {
            "Bool.false"
        });
        let result_ty = constant("IRByteMemoryResultV1");
        let option_nat = option("Nat");
        let none = app("IROption.none", [constant("Nat")]);
        let offset = input.offset.clone();
        let base = input.base.clone();
        let address = input.address();
        let memory = input.memory.clone();
        let expected = MemoryResult {
            value: app("IRScalar.ptr_", [address.clone()]),
            memory: memory.clone(),
        }
        .result();
        let offset_bound = app(
            "Nat.le_trans",
            [
                app("Nat.succ", [offset.clone()]),
                nat(1_u64 << 63),
                limit(),
                premises.index_bound.term.clone(),
                app("Nat.le_add_right", [nat(1_u64 << 63), nat(1_u64 << 63)]),
            ],
        );
        let index = true_case(
            option_nat.clone(),
            app("ir_byte_gep_index_v1", [scalar(offset.clone())]),
            none.clone(),
            some("Nat", offset.clone()),
            ltb(offset.clone(), nat(1_u64 << 63), premises.index_bound.term),
            PendingEquality::reflexive(option_nat.clone(), some("Nat", offset.clone())),
        );
        let summed = |sum: Expr| {
            choose(
                &option_nat,
                app("ir_nat_ltb", [sum.clone(), limit()]),
                some("Nat", sum),
                none.clone(),
            )
        };
        let sum_zero = PendingEquality::candidate(
            constant("Nat"),
            app("Nat.add", [offset.clone(), nat(0)]),
            offset.clone(),
            app("Nat.add_zero", [offset.clone()]),
        );
        let sum = mapped(self, sum_zero, option_nat.clone(), summed)?;
        let bounded_sum = true_case(
            option_nat.clone(),
            summed(offset.clone()),
            none.clone(),
            some("Nat", offset.clone()),
            ltb(offset.clone(), limit(), offset_bound.clone()),
            PendingEquality::reflexive(option_nat.clone(), some("Nat", offset.clone())),
        );
        let sum = self.compose(sum, bounded_sum)?;
        let singleton = some_case(
            self,
            "Nat",
            option_nat.clone(),
            app(
                "ir_byte_gep_indices_v1",
                [list("IRScalar", &[scalar(offset.clone())])],
            ),
            none.clone(),
            index,
            offset.clone(),
            |_, index| Ok(summed(app("Nat.add", [index, nat(0)]))),
            sum,
        )?;
        let indices = mapped(self, premises.indices, option_nat.clone(), |xs| {
            app("ir_byte_gep_indices_v1", [xs])
        })?;
        let indices = self.compose(indices, singleton)?;

        let delta_guard = |delta: Expr| {
            app(
                "Bool.and",
                [
                    app("ir_nat_pos", [base.clone()]),
                    app(
                        "Bool.and",
                        [
                            app("ir_nat_ltb", [delta.clone(), limit()]),
                            app(
                                "Bool.and",
                                [
                                    app(
                                        "ir_nat_ltb",
                                        [app("Nat.add", [base.clone(), delta.clone()]), limit()],
                                    ),
                                    app(
                                        "Bool.or",
                                        [
                                            app("Bool.not", [flag.clone()]),
                                            app(
                                                "ir_byte_same_allocation_v1",
                                                [
                                                    allocs(memory.clone()),
                                                    base.clone(),
                                                    app("Nat.add", [base.clone(), delta]),
                                                ],
                                            ),
                                        ],
                                    ),
                                ],
                            ),
                        ],
                    ),
                ],
            )
        };
        let delta_case = |delta: Expr| {
            choose(
                &result_ty,
                delta_guard(delta.clone()),
                MemoryResult {
                    value: app(
                        "ir_byte_pointer_value_v1",
                        [app("Nat.add", [base.clone(), delta])],
                    ),
                    memory: memory.clone(),
                }
                .result(),
                fault("ub", "bad_addr", memory.clone()),
            )
        };
        let one_mul = PendingEquality::candidate(
            constant("Nat"),
            app("Nat.mul", [nat(1), offset.clone()]),
            offset.clone(),
            app("Nat.one_mul", [offset.clone()]),
        );
        let scaled = mapped(self, one_mul, result_ty.clone(), delta_case)?;
        let arithmetic = join(
            bool_fact(
                app("ir_nat_pos", [base.clone()]),
                app(
                    "ir_byte_allocation_pos_v1",
                    [base.clone(), premises.positive.term.clone()],
                ),
            ),
            join(
                ltb(offset.clone(), limit(), offset_bound),
                join(
                    ltb(address.clone(), limit(), premises.result_bound.term),
                    bool_fact(
                        app(
                            "Bool.or",
                            [
                                app("Bool.not", [flag.clone()]),
                                app(
                                    "ir_byte_same_allocation_v1",
                                    [allocs(memory.clone()), base.clone(), address.clone()],
                                ),
                            ],
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
                premises.positive.term,
                app("Nat.le_add_right", [base.clone(), offset.clone()]),
            ],
        );
        let pointer_value = PendingEquality::candidate(
            constant("IRScalar"),
            app("ir_byte_pointer_value_v1", [address.clone()]),
            app("IRScalar.ptr_", [address.clone()]),
            app("ir_byte_allocation_pointer_value_v1", [address, positive]),
        );
        let result_value = mapped(self, pointer_value, result_ty.clone(), |value| {
            MemoryResult {
                value,
                memory: memory.clone(),
            }
            .result()
        })?;
        let arithmetic = true_case(
            result_ty.clone(),
            delta_case(offset.clone()),
            fault("ub", "bad_addr", memory.clone()),
            result_value.left.clone(),
            arithmetic,
            result_value,
        );
        let scaled = self.compose(scaled, arithmetic)?;
        let at = app(
            "ir_byte_gep_at_v1",
            [
                base.clone(),
                nat(1),
                offset.clone(),
                flag.clone(),
                memory.clone(),
            ],
        );
        let start = self.conversion(result_ty.clone(), at, scaled.left.clone())?;
        let at = self.compose(start, scaled)?;
        let canonical_layout = layout(i8_ty(), 1);
        let pointer_source = gep_pointer_option(
            self,
            canonical_layout.clone(),
            offset.clone(),
            &input,
            flag.clone(),
        )?;
        let pointer = some_case(
            self,
            "Nat",
            result_ty.clone(),
            pointer_source,
            fault("type_error", "not_ptr", memory.clone()),
            premises.pointer,
            base,
            |_, location| {
                Ok(gep_at(
                    canonical_layout.clone(),
                    location,
                    offset.clone(),
                    memory.clone(),
                    flag.clone(),
                ))
            },
            at,
        )?;
        let indices_source =
            gep_indices_option(self, canonical_layout.clone(), &input, flag.clone())?;
        let indices = some_case(
            self,
            "Nat",
            result_ty.clone(),
            indices_source,
            fault("unmodelled", "width_bounded", memory.clone()),
            indices,
            offset,
            |assembler, index| {
                gep_pointer_option(
                    assembler,
                    canonical_layout.clone(),
                    index,
                    &input,
                    flag.clone(),
                )
            },
            pointer,
        )?;
        let layout_source = gep_layout_body(self, canonical_layout.clone(), &input, flag.clone())?;
        let admitted = self.conversion(result_ty.clone(), layout_source, indices.left.clone())?;
        let admitted = self.compose(admitted, indices)?;
        let proof = some_case(
            self,
            "IRByteLayoutV1",
            result_ty,
            input.evaluation_with_flag(context, flag.clone()),
            fault("unmodelled", "width_bounded", memory),
            premises.layout,
            canonical_layout,
            |assembler, shape| gep_layout_body(assembler, shape, &input, flag.clone()),
            admitted,
        )?;
        require_same(&proof.right, &expected, "I8 GEP derived result")?;
        Ok(proof)
    }
}

/// An exact eight-byte codec candidate. Keeping actual type/context/layout and
/// both codec directions explicit prevents pointer/catalog identities from
/// being replaced by an arbitrary integer lane. Fields are not checked facts.
#[derive(Clone)]
pub struct ByteEightCodec {
    pub context: Expr,
    pub ty: Expr,
    pub value: Expr,
    pub word: Expr,
    pub layout: Expr,
    pub lane: PendingEquality,
    pub layout_found: PendingEquality,
    pub valid_layout: PendingEquality,
    pub fits: PendingEquality,
    pub encoded: PendingEquality,
    pub decoded: PendingEquality,
    pub bounded: PendingProof,
}

#[derive(Clone)]
pub struct ByteLoadEight {
    pub pointer: Expr,
    pub address: Expr,
    pub requested_align: Expr,
    pub memory: Expr,
}

/// Exact endpoint candidates, not trusted facts. Kernel replay is required.
#[derive(Clone)]
pub struct ByteLoadEightPremises {
    pub pointer: PendingEquality,
    /// Complete live unique range at effective alignment in the input memory.
    pub accessible: PendingEquality,
    /// read_word(bytes(input.memory), 8, input.address) = some(codec.word).
    pub initialized: PendingEquality,
}

#[derive(Clone)]
pub struct ByteStoreEight {
    pub pointer: Expr,
    pub address: Expr,
    pub requested_align: Expr,
    pub memory: Expr,
}

#[derive(Clone)]
pub struct ByteStoreEightPremises {
    pub pointer: PendingEquality,
    /// The real complete-live-unique-range/alignment check on incoming memory.
    /// Alignment is effective_align(requested_align, layout_align(codec.layout)).
    pub accessible: PendingEquality,
}

pub struct ByteStoreEightResult {
    pub result: MemoryResult,
    pub evaluated: PendingEquality,
    pub allocations: PendingEquality,
    pub cursor: PendingEquality,
    /// read_word(bytes(FINAL memory), 8, address) = some encoded word.
    pub raw_read: PendingEquality,
    /// Actual nonvolatile typed load from FINAL memory, not an executed node.
    pub typed_readback: PendingEquality,
}

impl ByteEightCodec {
    fn validate(&self) -> Result<()> {
        self.lane.endpoints(
            &option("Nat"),
            &app("ir_byte_lane_size_v1", [self.ty.clone()]),
            &some("Nat", nat(8)),
        )?;
        self.layout_found.endpoints(
            &option("IRByteLayoutV1"),
            &app("ir_byte_layout_v1", [self.context.clone(), self.ty.clone()]),
            &some("IRByteLayoutV1", self.layout.clone()),
        )?;
        self.valid_layout.endpoints(
            &constant("Bool"),
            &layout_guard(self.layout.clone()),
            &constant("Bool.true"),
        )?;
        self.fits.endpoints(
            &constant("Bool"),
            &app(
                "ir_byte_value_matches_v1",
                [self.context.clone(), self.ty.clone(), self.value.clone()],
            ),
            &constant("Bool.true"),
        )?;
        self.encoded.endpoints(
            &option("Nat"),
            &app(
                "ir_byte_scalar_word_v1",
                [self.context.clone(), self.value.clone()],
            ),
            &some("Nat", self.word.clone()),
        )?;
        self.decoded.endpoints(
            &option("IRScalar"),
            &app(
                "ir_byte_decode_word_v1",
                [self.context.clone(), self.ty.clone(), self.word.clone()],
            ),
            &some("IRScalar", self.value.clone()),
        )?;
        require_same(
            self.bounded.proposition(),
            &app("Nat.lt", [self.word.clone(), limit()]),
            "eight-byte canonical word bound",
        )
    }
}

fn byte_ptr_codec_claims(context: Expr, word: Expr) -> [Expr; 2] {
    let value = app("ir_byte_pointer_value_v1", [word.clone()]);
    [
        eq(
            &option("Nat"),
            app("ir_byte_scalar_word_v1", [context.clone(), value.clone()]),
            some("Nat", word),
        ),
        eq(
            &constant("Bool"),
            app(
                "ir_byte_value_matches_v1",
                [context, constant("IRTy.ptr_"), value],
            ),
            constant("Bool.true"),
        ),
    ]
}

fn byte_ptr_codec_pair(context: Expr, word: Expr, encoded: Expr, fits: Expr) -> Expr {
    let [encoded_claim, fits_claim] = byte_ptr_codec_claims(context, word);
    app("And.intro", [encoded_claim, fits_claim, encoded, fits])
}

impl Assembler<'_> {
    /// Canonical nominal thin-pointer transport, including null and the full
    /// unsigned 64-bit range. Layout comes from the actual context. Neither
    /// representability nor this codec supplies live storage or permission to
    /// access the pointer's referent. Consumers must replay every candidate.
    pub fn byte_ptr_codec(
        &mut self,
        context: Expr,
        word: Expr,
        layout_found: PendingEquality,
        bounded: PendingProof,
    ) -> Result<ByteEightCodec> {
        self.charge()?;
        require_same(
            bounded.proposition(),
            &app("Nat.lt", [word.clone(), limit()]),
            "pointer canonical word bound",
        )?;
        let ty = constant("IRTy.ptr_");
        let layout = layout(ty.clone(), 8);
        layout_found.endpoints(
            &option("IRByteLayoutV1"),
            &app("ir_byte_layout_v1", [context.clone(), ty.clone()]),
            &some("IRByteLayoutV1", layout.clone()),
        )?;
        let value = app("ir_byte_pointer_value_v1", [word.clone()]);
        let [encoded_claim, fits_claim] = byte_ptr_codec_claims(context.clone(), word.clone());
        let encoded_helper = self.byte_ptr_encoded_helper()?;
        let paired = Expr::apps(
            encoded_helper,
            [context.clone(), word.clone(), bounded.term().clone()],
        );
        let codec = ByteEightCodec {
            context: context.clone(),
            ty: ty.clone(),
            value: value.clone(),
            word: word.clone(),
            layout: layout.clone(),
            lane: PendingEquality::candidate(
                option("Nat"),
                app("ir_byte_lane_size_v1", [ty.clone()]),
                some("Nat", nat(8)),
                constant("ir_byte_ptr_lane_eight_v1"),
            ),
            layout_found,
            valid_layout: bool_fact(
                layout_guard(layout),
                app("ir_byte_canonical_layout_eight_v1", [ty.clone()]),
            ),
            fits: PendingEquality::candidate(
                constant("Bool"),
                app(
                    "ir_byte_value_matches_v1",
                    [context.clone(), ty.clone(), value.clone()],
                ),
                constant("Bool.true"),
                app(
                    "And.right",
                    [encoded_claim.clone(), fits_claim.clone(), paired.clone()],
                ),
            ),
            encoded: PendingEquality::candidate(
                option("Nat"),
                app("ir_byte_scalar_word_v1", [context.clone(), value.clone()]),
                some("Nat", word.clone()),
                app("And.left", [encoded_claim, fits_claim, paired]),
            ),
            decoded: PendingEquality::candidate(
                option("IRScalar"),
                app("ir_byte_decode_word_v1", [context, ty, word]),
                some("IRScalar", value.clone()),
                refl(&option("IRScalar"), some("IRScalar", value)),
            ),
            bounded,
        };
        codec.validate()?;
        Ok(codec)
    }

    /// One closed combined encoding/type-fit candidate. The independent
    /// address-recovery helper is not built for a codec that does not use it.
    /// Actual context, word and bound stay application arguments. The original
    /// positive-pointer law and exact bound handle successors; null is zero.
    fn byte_ptr_encoded_helper(&mut self) -> Result<Expr> {
        if let Some(candidate) = &self.byte_ptr_encoded_candidate {
            return Ok(candidate.clone());
        }
        let context = self.local(constant("IRByteContextV1"))?;
        let word = self.local(constant("Nat"))?;
        let bound = |word: Expr| app("Nat.lt", [word, limit()]);
        let bounded = self.local(bound(word.term().clone()))?;
        let claim = |word: Expr| {
            let [encoded, fits] = byte_ptr_codec_claims(context.term().clone(), word);
            app("And", [encoded, fits])
        };
        let value = self.local(constant("Nat"))?;
        let value_bound = self.local(bound(value.term().clone()))?;
        let motive = value.lam(value_bound.pi(claim(value.term().clone())));
        let zero_bound = self.local(bound(nat(0)))?;
        let zero = zero_bound.lam(byte_ptr_codec_pair(
            context.term().clone(),
            nat(0),
            refl(&option("Nat"), some("Nat", nat(0))),
            refl(&constant("Bool"), constant("Bool.true")),
        ));
        let predecessor = self.local(constant("Nat"))?;
        let induction = self.local(Expr::app(motive.clone(), predecessor.term().clone()))?;
        let successor = app("Nat.succ", [predecessor.term().clone()]);
        let successor_bound = self.local(bound(successor.clone()))?;
        let encoded = app(
            "ir_byte_pointer_scalar_word_v1",
            [
                context.term().clone(),
                predecessor.term().clone(),
                successor_bound.term().clone(),
            ],
        );
        let fits = ltb(
            successor.clone(),
            app("ir_nat_pow2", [nat(64)]),
            successor_bound.term().clone(),
        );
        let step = predecessor.lam(induction.lam(successor_bound.lam(byte_ptr_codec_pair(
            context.term().clone(),
            successor,
            encoded,
            fits.term,
        ))));
        let body = Expr::apps(
            Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            [
                motive,
                zero,
                step,
                word.term().clone(),
                bounded.term().clone(),
            ],
        );
        let template = context.lam(word.lam(bounded.lam(body)));
        let closed = self
            .scope
            .close(&template)
            .map_err(|error| error.to_string())?;
        self.byte_ptr_encoded_candidate = Some(closed.clone());
        Ok(closed)
    }

    /// All canonical 64-bit I64 carriers, including the high-bit half. The
    /// actual context layout remains an independent premise, not a host guess.
    pub fn byte_i64_codec(
        &mut self,
        context: Expr,
        word: Expr,
        layout_found: PendingEquality,
        bounded: PendingProof,
    ) -> Result<ByteEightCodec> {
        self.byte_integer64_codec(context, word, layout_found, bounded, false)
    }

    /// All canonical U64 carriers, including zero and the high-bit half. The
    /// nominal unsigned type remains exact even though ByteV1 represents both
    /// integer signednesses with `IRScalar.int_` bit patterns. The actual
    /// context's layout and the full `< 2^64` bound are independent premises;
    /// none of these candidates grants access to memory or executes a node.
    pub fn byte_u64_codec(
        &mut self,
        context: Expr,
        word: Expr,
        layout_found: PendingEquality,
        bounded: PendingProof,
    ) -> Result<ByteEightCodec> {
        self.byte_integer64_codec(context, word, layout_found, bounded, true)
    }

    fn byte_integer64_codec(
        &mut self,
        context: Expr,
        word: Expr,
        layout_found: PendingEquality,
        bounded: PendingProof,
        unsigned: bool,
    ) -> Result<ByteEightCodec> {
        self.charge()?;
        let ty = app(if unsigned { "IRTy.uint_" } else { "IRTy.int_" }, [nat(64)]);
        let value = scalar(word.clone());
        let layout = layout(ty.clone(), 8);
        let codec = ByteEightCodec {
            context: context.clone(),
            ty: ty.clone(),
            value: value.clone(),
            word: word.clone(),
            layout: layout.clone(),
            lane: PendingEquality::candidate(
                option("Nat"),
                app("ir_byte_lane_size_v1", [ty.clone()]),
                some("Nat", nat(8)),
                if unsigned {
                    constant("ir_byte_u64_lane_eight_v1")
                } else {
                    constant("ir_byte_i64_lane_eight_v1")
                },
            ),
            layout_found,
            valid_layout: bool_fact(
                layout_guard(layout),
                app("ir_byte_canonical_layout_eight_v1", [ty.clone()]),
            ),
            fits: bool_fact(
                app(
                    "ir_byte_value_matches_v1",
                    [context.clone(), ty.clone(), value.clone()],
                ),
                app(
                    if unsigned {
                        "ir_byte_u64_value_fits_v1"
                    } else {
                        "ir_byte_i64_value_fits_v1"
                    },
                    [
                        context.clone(),
                        word.clone(),
                        app(
                            "ir_byte_ltb_of_lt_v1",
                            [
                                word.clone(),
                                app("ir_nat_pow2", [nat(64)]),
                                bounded.term.clone(),
                            ],
                        ),
                    ],
                ),
            ),
            encoded: PendingEquality::candidate(
                option("Nat"),
                app("ir_byte_scalar_word_v1", [context.clone(), value.clone()]),
                some("Nat", word.clone()),
                refl(&option("Nat"), some("Nat", word.clone())),
            ),
            decoded: PendingEquality::candidate(
                option("IRScalar"),
                app("ir_byte_decode_word_v1", [context, ty, word]),
                some("IRScalar", value.clone()),
                refl(&option("IRScalar"), some("IRScalar", value)),
            ),
            bounded,
        };
        codec.validate()?;
        Ok(codec)
    }

    /// Construct a nonvolatile typed-load candidate at the exact supplied
    /// memory. No instruction is executed and no proof authority is minted.
    /// Pointer/function identities are fixed by the checked codec endpoints.
    pub fn byte_load_eight(
        &mut self,
        codec: &ByteEightCodec,
        input: ByteLoadEight,
        premises: ByteLoadEightPremises,
    ) -> Result<PendingEquality> {
        self.charge()?;
        codec.validate()?;
        premises.pointer.endpoints(
            &option("Nat"),
            &pointer_address(input.pointer.clone()),
            &some("Nat", input.address.clone()),
        )?;
        let align = app(
            "ir_byte_effective_align_v1",
            [
                input.requested_align.clone(),
                app("ir_byte_layout_align_v1", [codec.layout.clone()]),
            ],
        );
        premises.accessible.endpoints(
            &constant("Bool"),
            &app(
                "ir_byte_accessible_v1",
                [
                    allocs(input.memory.clone()),
                    input.address.clone(),
                    nat(8),
                    align.clone(),
                ],
            ),
            &constant("Bool.true"),
        )?;
        premises.initialized.endpoints(
            &option("Nat"),
            &app(
                "ir_byte_read_word_v1",
                [bytes(input.memory.clone()), nat(8), input.address.clone()],
            ),
            &some("Nat", codec.word.clone()),
        )?;
        self.byte_load_eight_candidate(
            codec,
            input,
            align,
            premises.pointer.term,
            premises.accessible.term,
            premises.initialized.term,
        )
    }

    // Shared term construction only. The public load checks exact endpoints;
    // Store has already checked its input and preserves allocation rows by
    // reduction. Do not insert transports/charges here: existing Store proof
    // bytes and its operation budget must remain unchanged.
    fn byte_load_eight_candidate(
        &mut self,
        codec: &ByteEightCodec,
        input: ByteLoadEight,
        align: Expr,
        pointer: Expr,
        accessible: Expr,
        initialized: Expr,
    ) -> Result<PendingEquality> {
        let loaded = MemoryResult {
            value: codec.value.clone(),
            memory: input.memory.clone(),
        }
        .result();
        let load_at = app(
            "ir_byte_load_at_v1",
            [
                codec.context.clone(),
                codec.ty.clone(),
                input.address.clone(),
                nat(8),
                align.clone(),
                input.memory.clone(),
            ],
        );
        let dispatch = PendingEquality::candidate(
            constant("IRByteMemoryResultV1"),
            app(
                "ir_byte_load_v1",
                [
                    codec.context.clone(),
                    codec.ty.clone(),
                    input.pointer.clone(),
                    input.requested_align.clone(),
                    constant("Bool.false"),
                    input.memory.clone(),
                ],
            ),
            load_at.clone(),
            app(
                "ir_byte_load_dispatch_eight_v1",
                [
                    codec.context.clone(),
                    codec.ty.clone(),
                    input.pointer,
                    input.requested_align,
                    input.memory.clone(),
                    codec.layout.clone(),
                    input.address.clone(),
                    codec.lane.term.clone(),
                    codec.layout_found.term.clone(),
                    codec.valid_layout.term.clone(),
                    pointer,
                ],
            ),
        );
        let readback = PendingEquality::candidate(
            constant("IRByteMemoryResultV1"),
            load_at,
            loaded,
            app(
                "ir_byte_load_at_rule_v1",
                [
                    codec.context.clone(),
                    codec.ty.clone(),
                    input.address,
                    nat(8),
                    align,
                    input.memory.clone(),
                    codec.word.clone(),
                    codec.value.clone(),
                    accessible,
                    initialized,
                    codec.decoded.term.clone(),
                    codec.fits.term.clone(),
                ],
            ),
        );
        self.compose(dispatch, readback)
    }

    /// Store to arbitrary accessible incoming memory; derive raw AND typed
    /// readback from the final write. This neither allocates nor changes owners.
    pub fn byte_store_eight(
        &mut self,
        codec: &ByteEightCodec,
        input: ByteStoreEight,
        premises: ByteStoreEightPremises,
    ) -> Result<ByteStoreEightResult> {
        self.charge()?;
        codec.validate()?;
        premises.pointer.endpoints(
            &option("Nat"),
            &pointer_address(input.pointer.clone()),
            &some("Nat", input.address.clone()),
        )?;
        let align = app(
            "ir_byte_effective_align_v1",
            [
                input.requested_align.clone(),
                app("ir_byte_layout_align_v1", [codec.layout.clone()]),
            ],
        );
        premises.accessible.endpoints(
            &constant("Bool"),
            &app(
                "ir_byte_accessible_v1",
                [
                    allocs(input.memory.clone()),
                    input.address.clone(),
                    nat(8),
                    align.clone(),
                ],
            ),
            &constant("Bool.true"),
        )?;
        let next = app(
            "IRByteMemoryV1.mk",
            [
                allocs(input.memory.clone()),
                app(
                    "ir_byte_write_word_v1",
                    [
                        bytes(input.memory.clone()),
                        input.address.clone(),
                        nat(8),
                        codec.word.clone(),
                    ],
                ),
                cursor(input.memory.clone()),
            ],
        );
        let result = MemoryResult {
            value: constant("IRScalar.unit_"),
            memory: next.clone(),
        };
        let store = app(
            "ir_byte_store_v1",
            [
                codec.context.clone(),
                codec.ty.clone(),
                input.pointer.clone(),
                codec.value.clone(),
                input.requested_align.clone(),
                constant("Bool.false"),
                input.memory.clone(),
            ],
        );
        let store_at = app(
            "ir_byte_store_at_v1",
            [
                codec.context.clone(),
                codec.ty.clone(),
                input.address.clone(),
                codec.value.clone(),
                nat(8),
                align.clone(),
                input.memory.clone(),
            ],
        );
        let dispatch = PendingEquality::candidate(
            constant("IRByteMemoryResultV1"),
            store,
            store_at.clone(),
            app(
                "ir_byte_store_dispatch_eight_v1",
                [
                    codec.context.clone(),
                    codec.ty.clone(),
                    input.pointer.clone(),
                    codec.value.clone(),
                    input.requested_align.clone(),
                    input.memory.clone(),
                    codec.layout.clone(),
                    input.address.clone(),
                    codec.lane.term.clone(),
                    codec.layout_found.term.clone(),
                    codec.valid_layout.term.clone(),
                    premises.pointer.term.clone(),
                ],
            ),
        );
        let stored = PendingEquality::candidate(
            constant("IRByteMemoryResultV1"),
            store_at,
            result.result(),
            app(
                "ir_byte_store_at_eight_rule_v1",
                [
                    codec.context.clone(),
                    codec.ty.clone(),
                    input.address.clone(),
                    codec.value.clone(),
                    align.clone(),
                    input.memory.clone(),
                    codec.word.clone(),
                    premises.accessible.term.clone(),
                    codec.fits.term.clone(),
                    codec.encoded.term.clone(),
                    codec.bounded.term.clone(),
                ],
            ),
        );
        let evaluated = self.compose(dispatch, stored)?;
        let raw_read = PendingEquality::candidate(
            option("Nat"),
            app(
                "ir_byte_read_word_v1",
                [bytes(next.clone()), nat(8), input.address.clone()],
            ),
            some("Nat", codec.word.clone()),
            app(
                "ir_byte_read_write_eight_v1",
                [
                    bytes(input.memory.clone()),
                    input.address.clone(),
                    codec.word.clone(),
                    codec.bounded.term.clone(),
                ],
            ),
        );
        let typed_readback = self.byte_load_eight_candidate(
            codec,
            ByteLoadEight {
                pointer: input.pointer,
                address: input.address,
                requested_align: input.requested_align,
                memory: next.clone(),
            },
            align,
            premises.pointer.term,
            premises.accessible.term,
            raw_read.term.clone(),
        )?;
        let allocations = self.conversion(
            app("IRList", [constant("IRByteAllocationV1")]),
            allocs(next.clone()),
            allocs(input.memory.clone()),
        )?;
        let cursor = self.conversion(constant("Nat"), cursor(next), cursor(input.memory))?;
        Ok(ByteStoreEightResult {
            result,
            evaluated,
            allocations,
            cursor,
            raw_read,
            typed_readback,
        })
    }
}

#[path = "core_execution_memory_four.rs"]
mod four;
pub use four::{
    ByteFourCodec, ByteLoadFour, ByteLoadFourPremises, ByteLoadWord, ByteLoadWordPremises,
    ByteStoreFour, ByteStoreFourPremises, ByteStoreFourResult, ByteStoreWord,
    ByteStoreWordPremises, ByteStoreWordResult, ByteWordCodec,
};

#[cfg(test)]
#[path = "core_execution_memory_access_tests.rs"]
mod tests;
