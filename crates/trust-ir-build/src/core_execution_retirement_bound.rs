// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Pending allocation-history identity from the original MemoryOwners bound.
//! No activation, actual Return, frame, access or whole-world authority.

use super::*;
use clean_kernel::BinderInfo;

#[cfg(test)]
#[path = "core_execution_retirement_bound_tests.rs"]
mod tests;

fn allocations_type() -> Expr {
    app("IRList", [constant("IRByteAllocationV1")])
}
fn allocations(memory: Expr) -> Expr {
    app("ir_byte_mem_allocs_v1", [memory])
}
fn retired(owner: Expr, rows: Expr) -> Expr {
    app("ir_byte_retire_allocs_v1", [owner, rows])
}
fn cons(row: Expr, tail: Expr) -> Expr {
    app("IRList.cons", [constant("IRByteAllocationV1"), row, tail])
}
fn yes(flag: Expr) -> Expr {
    eq(&constant("Bool"), flag, constant("Bool.true"))
}
fn no(flag: Expr) -> Expr {
    eq(&constant("Bool"), flag, constant("Bool.false"))
}
fn ltb(left: Expr, right: Expr) -> Expr {
    app("ir_nat_ltb", [left, right])
}
fn eqb(left: Expr, right: Expr) -> Expr {
    app("ir_nat_eqb", [left, right])
}
fn le(left: Expr, right: Expr) -> Expr {
    app("Nat.le", [left, right])
}
fn lam(ty: Expr, body: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, ty, body)
}
fn close<const N: usize>(types: [Expr; N], body: Expr, proposition: bool) -> Expr {
    types.into_iter().rev().fold(body, |body, ty| {
        if proposition {
            Expr::pi(BinderInfo::Default, ty, body)
        } else {
            lam(ty, body)
        }
    })
}
fn recursor(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string(name), vec![Level::zero()]),
        args,
    )
}
fn symm(ty: &Expr, left: Expr, right: Expr, proof: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.symm"),
            vec![Level::succ(Level::zero())],
        ),
        [ty.clone(), left, right, proof],
    )
}

// Exact reversed endpoint of the existing TY paired-Nat proof. The installed
// ir_byte_world_lt_ne_v1 has the FORWARD eqb endpoint, not this one. Preserve
// the old induction rather than replacing it with an unproved commutativity.
fn reversed_walk_relation(a: Expr, b: Expr) -> Expr {
    Expr::arrow(
        yes(app("ir_nat_ltb_walk", [a.clone(), b.clone()])),
        // `arrow` constructs a Pi verbatim: its proof argument is a new
        // binder, so shift this fixed neutral codomain past that binder.
        no(app("ir_nat_eqb_walk", [b, a])).lift(1),
    )
}
fn closed_reverse_less() -> Expr {
    let n = constant("Nat");
    let boolean = constant("Bool");
    let motive = lam(
        n.clone(),
        // For each x, the motive is the proposition `forall y, relation`;
        // a second lambda would return a predicate instead of a proposition.
        Expr::pi(
            BinderInfo::Default,
            n.clone(),
            reversed_walk_relation(Expr::bvar(1), Expr::bvar(0)),
        ),
    );
    let absurd = recursor(
        "False.elim",
        [
            no(constant("Bool.true")),
            app("ir_byte_world_false_true_v1", [Expr::bvar(0)]),
        ],
    );
    let zero_case = lam(
        n.clone(),
        recursor(
            "Nat.rec",
            [
                lam(n.clone(), reversed_walk_relation(nat(0), Expr::bvar(0))),
                lam(yes(constant("Bool.false")), absurd),
                lam(
                    n.clone(),
                    lam(
                        reversed_walk_relation(nat(0), Expr::bvar(0)),
                        lam(
                            yes(constant("Bool.true")),
                            refl(&boolean, constant("Bool.false")),
                        ),
                    ),
                ),
                Expr::bvar(0),
            ],
        ),
    );
    let ih_type = Expr::pi(
        BinderInfo::Default,
        n.clone(),
        reversed_walk_relation(Expr::bvar(1), Expr::bvar(0)),
    );
    // Under x, ih, y the nested Nat.rec handles z; the branch also retains
    // its unused recursive hypothesis as a genuine, typed constructor input.
    let successor_case = lam(
        n.clone(),
        lam(
            ih_type,
            lam(
                n.clone(),
                recursor(
                    "Nat.rec",
                    [
                        lam(
                            n.clone(),
                            reversed_walk_relation(app("Nat.succ", [Expr::bvar(3)]), Expr::bvar(0)),
                        ),
                        lam(
                            yes(constant("Bool.false")),
                            refl(&boolean, constant("Bool.false")),
                        ),
                        lam(
                            n.clone(),
                            lam(
                                reversed_walk_relation(
                                    app("Nat.succ", [Expr::bvar(3)]),
                                    Expr::bvar(0),
                                ),
                                lam(
                                    yes(app("ir_nat_ltb_walk", [Expr::bvar(4), Expr::bvar(1)])),
                                    Expr::apps(Expr::bvar(4), [Expr::bvar(2), Expr::bvar(0)]),
                                ),
                            ),
                        ),
                        Expr::bvar(0),
                    ],
                ),
            ),
        ),
    );
    // Under the closed a, b, less telescope.
    let a = Expr::bvar(2);
    let b = Expr::bvar(1);
    let fast_less = ltb(a.clone(), b.clone());
    let walk_less = app("ir_nat_ltb_walk", [a.clone(), b.clone()]);
    let less = trans(
        &boolean,
        walk_less.clone(),
        fast_less.clone(),
        constant("Bool.true"),
        symm(
            &boolean,
            fast_less,
            walk_less,
            app("ir_nat_ltb_walk_eq", [a.clone(), b.clone()]),
        ),
        Expr::bvar(0),
    );
    let different = Expr::apps(
        recursor("Nat.rec", [motive, zero_case, successor_case, a.clone()]),
        [b.clone(), less],
    );
    let result = trans(
        &boolean,
        eqb(b.clone(), a.clone()),
        app("ir_nat_eqb_walk", [b.clone(), a.clone()]),
        constant("Bool.false"),
        app("ir_nat_eqb_walk_eq", [b, a]),
        different,
    );
    close(
        [n.clone(), n, yes(ltb(Expr::bvar(1), Expr::bvar(0)))],
        result,
        false,
    )
}

// row_owner, next, retiring, row_below, next_le_retiring. Nat.le's recursor
// remains Prop-only (NO universe parameters), exactly as the original proof.
fn closed_raise_bound() -> Expr {
    let n = constant("Nat");
    let motive = lam(
        n.clone(),
        lam(
            le(Expr::bvar(4), Expr::bvar(0)),
            yes(ltb(Expr::bvar(6), Expr::bvar(1))),
        ),
    );
    let step = lam(
        n.clone(),
        lam(
            le(Expr::bvar(4), Expr::bvar(0)),
            lam(
                yes(ltb(Expr::bvar(6), Expr::bvar(1))),
                app(
                    "ir_byte_world_lt_raise_v1",
                    [Expr::bvar(7), Expr::bvar(2), Expr::bvar(0)],
                ),
            ),
        ),
    );
    let body = app(
        "Nat.le.rec",
        [
            Expr::bvar(3),
            motive,
            Expr::bvar(1),
            step,
            Expr::bvar(2),
            Expr::bvar(0),
        ],
    );
    close(
        [
            n.clone(),
            n.clone(),
            n,
            yes(ltb(Expr::bvar(2), Expr::bvar(1))),
            le(Expr::bvar(2), Expr::bvar(1)),
        ],
        body,
        false,
    )
}

// Fixed neutral parameter slots ONLY. All calls are in this closed recipe,
// whose first four slots are memory, owners, next and retiring. Caller-sized
// expressions/proofs are never substituted, lifted or captured beneath it.
fn parameter(depth: u32, slot: u32) -> Expr {
    Expr::bvar(depth - slot - 1)
}
fn owner_guard(memory: Expr, owners: Expr, next: Expr) -> Expr {
    app("ir_byte_memory_owners_v1", [memory, owners, next])
}
fn guard(depth: u32, rows: Expr) -> Expr {
    let memory = parameter(depth, 0);
    owner_guard(
        app(
            "IRByteMemoryV1.mk",
            [
                rows,
                app("ir_byte_mem_bytes_v1", [memory.clone()]),
                app("ir_byte_mem_next_v1", [memory]),
            ],
        ),
        parameter(depth, 1),
        parameter(depth, 2),
    )
}
fn identity(depth: u32, rows: Expr) -> Expr {
    eq(
        &allocations_type(),
        retired(parameter(depth, 3), rows.clone()),
        rows,
    )
}
fn relation(depth: u32, rows: Expr) -> Expr {
    Expr::arrow(
        yes(guard(depth, rows.clone())),
        identity(depth, rows).lift(1),
    )
}
fn concrete(depth: u32) -> Expr {
    app(
        "IRByteAllocationV1.mk",
        [
            parameter(depth, 9),
            parameter(depth, 10),
            parameter(depth, 11),
            parameter(depth, 12),
        ],
    )
}
fn family_domains() -> [Expr; 6] {
    [
        constant("IRByteMemoryV1"),
        app("IRList", [constant("Nat")]),
        constant("Nat"),
        constant("Nat"),
        yes(owner_guard(Expr::bvar(3), Expr::bvar(2), Expr::bvar(1))),
        le(Expr::bvar(2), Expr::bvar(1)),
    ]
}
fn closed_retirement_family() -> Expr {
    let rows_ty = allocations_type();
    let nil = list("IRByteAllocationV1", &[]);
    let nil_case = lam(yes(guard(6, nil.clone())), refl(&rows_ty, nil));
    // Under six outer parameters, then row, tail and its IH, and finally
    // base, size, row_owner, live and ready (14 slots in the constructor).
    let row = concrete(14);
    let tail = parameter(14, 7);
    let whole = cons(row.clone(), tail.clone());
    let support = app(
        "Bool.or",
        [
            app("Bool.not", [parameter(14, 12)]),
            app(
                "Bool.or",
                [
                    eqb(parameter(14, 11), nat(0)),
                    app(
                        "ir_byte_owner_member_v1",
                        [parameter(14, 11), parameter(14, 1)],
                    ),
                ],
            ),
        ],
    );
    let bound = ltb(parameter(14, 11), parameter(14, 2));
    let valid = app("ir_byte_alloc_valid_v1", [row.clone()]);
    let rest = app("Bool.and", [bound.clone(), support.clone()]);
    let row_guard = app("Bool.and", [valid.clone(), rest.clone()]);
    let tail_guard = guard(14, tail.clone());
    let row_proof = app(
        "ir_byte_world_and_right_v1",
        [tail_guard.clone(), row_guard.clone(), parameter(14, 13)],
    );
    let rest_proof = app("ir_byte_world_and_right_v1", [valid, rest, row_proof]);
    let bound_proof = app("ir_byte_world_and_left_v1", [bound, support, rest_proof]);
    let widened = Expr::apps(
        closed_raise_bound(),
        [
            parameter(14, 11),
            parameter(14, 2),
            parameter(14, 3),
            bound_proof,
            parameter(14, 5),
        ],
    );
    let unequal = Expr::apps(
        closed_reverse_less(),
        [parameter(14, 11), parameter(14, 3), widened],
    );
    let rewritten = app(
        "ir_byte_retire_cons_other_v1",
        [
            parameter(14, 3),
            parameter(14, 9),
            parameter(14, 10),
            parameter(14, 11),
            parameter(14, 12),
            tail.clone(),
            unequal,
        ],
    );
    let tail_ready = app(
        "ir_byte_world_and_left_v1",
        [tail_guard, row_guard, parameter(14, 13)],
    );
    let tail_equal = Expr::app(parameter(14, 8), tail_ready);
    let mapped = app(
        "ir_eq_cong",
        [
            rows_ty.clone(),
            rows_ty.clone(),
            lam(rows_ty.clone(), cons(row.lift(1), Expr::bvar(0))),
            retired(parameter(14, 3), tail.clone()),
            tail.clone(),
            tail_equal,
        ],
    );
    let result = trans(
        &rows_ty,
        retired(parameter(14, 3), whole.clone()),
        cons(row, retired(parameter(14, 3), tail)),
        whole,
        rewritten,
        mapped,
    );
    let constructor = close(
        [
            constant("Nat"),
            constant("Nat"),
            constant("Nat"),
            constant("Bool"),
            yes(guard(13, cons(concrete(13), parameter(13, 7)))),
        ],
        result,
        false,
    );
    let row_case = recursor(
        "IRByteAllocationV1.rec",
        [
            lam(
                constant("IRByteAllocationV1"),
                relation(10, cons(Expr::bvar(0), parameter(10, 7))),
            ),
            constructor,
            parameter(9, 6),
        ],
    );
    let step = close(
        [
            constant("IRByteAllocationV1"),
            rows_ty.clone(),
            relation(8, parameter(8, 7)),
        ],
        row_case,
        false,
    );
    let induction = recursor(
        "IRList.rec",
        [
            constant("IRByteAllocationV1"),
            lam(rows_ty, relation(7, Expr::bvar(0))),
            nil_case,
            step,
            allocations(parameter(6, 0)),
        ],
    );
    close(
        family_domains(),
        Expr::app(induction, parameter(6, 4)),
        false,
    )
}

fn owner_rule_domains() -> [Expr; 4] {
    [
        constant("IRByteMemoryV1"),
        app("IRList", [constant("Nat")]),
        constant("Nat"),
        yes(owner_guard(Expr::bvar(2), Expr::bvar(1), Expr::bvar(0))),
    ]
}
fn owner_rule_goal() -> Expr {
    let rows = allocations(Expr::bvar(3));
    eq(
        &allocations_type(),
        retired(Expr::bvar(1), rows.clone()),
        rows,
    )
}

impl Assembler<'_> {
    /// Candidate identity for the allocation history in exactly `memory`.
    /// The original MemoryOwners guard and Nat.le premise are not answers.
    /// This does not retire a frame, prove accessibility or execute Return.
    ///
    /// # Errors
    /// Existing charged-operation refusal and exact premise-metadata mismatch.
    /// Every successful/failed attempt retains its spent charges; no locals,
    /// list-input quota or candidate cache are allocated or published.
    pub fn byte_retire_beyond_bound(
        &mut self,
        memory: Expr,
        owners: Expr,
        next: Expr,
        retiring: Expr,
        memory_owners: PendingEquality,
        at_or_above: PendingProof,
    ) -> Result<PendingEquality> {
        // Historical candidate local calls: reversed decision18, list/row12,
        // Nat.le weakening3. Each slot keeps its original one operation.
        for _ in 0..33 {
            self.charge()?;
        }
        memory_owners.endpoints(
            &constant("Bool"),
            &owner_guard(memory.clone(), owners.clone(), next.clone()),
            &constant("Bool.true"),
        )?;
        require_same(
            at_or_above.proposition(),
            &le(next.clone(), retiring.clone()),
            "retirement bound premise",
        )?;
        let rows = allocations(memory.clone());
        let term = Expr::apps(
            closed_retirement_family(),
            [
                memory,
                owners,
                next,
                retiring.clone(),
                memory_owners.term,
                at_or_above.term,
            ],
        );
        Ok(PendingEquality::candidate(
            allocations_type(),
            retired(retiring, rows.clone()),
            rows,
            term,
        ))
    }

    /// Universally quantified pending owner-bound rule, for one consumer-owned
    /// LET at an activation's original memory. No checked fact is published.
    ///
    /// # Errors
    /// Existing operation-budget/counter refusal. The four old rule-parameter
    /// slots plus all33 induction slots remain charged before construction.
    /// The consumer's actual retained LET remains separately paid/owned.
    pub fn byte_retirement_owner_rule(&mut self) -> Result<PendingProof> {
        for _ in 0..37 {
            self.charge()?;
        }
        let term = close(
            owner_rule_domains(),
            Expr::apps(
                closed_retirement_family(),
                [
                    Expr::bvar(3),
                    Expr::bvar(2),
                    Expr::bvar(1),
                    Expr::bvar(1),
                    Expr::bvar(0),
                    app("Nat.le_refl", [Expr::bvar(1)]),
                ],
            ),
            false,
        );
        Ok(PendingProof::candidate(
            close(owner_rule_domains(), owner_rule_goal(), true),
            term,
        ))
    }
}
