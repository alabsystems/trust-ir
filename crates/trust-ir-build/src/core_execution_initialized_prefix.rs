// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared candidates for an ordered, adjacent prefix of initialized raw words.
//!
//! The collector calls the EXISTING byte reader. It is not a Store/Load
//! evaluator or accessibility proof. FetchedSite memory transfers still prove
//! actual execution. A changed memory needs an explicit equality; valid owners
//! do not preserve bytes. Retirement may preserve bytes while revoking access.
//! All helpers are closed candidates, not declarations or kernel admission.

use super::*;

#[cfg(test)]
#[path = "core_execution_initialized_prefix_tests.rs"]
mod tests;

fn nat_list() -> Expr {
    app("IRList", [constant("Nat")])
}
fn option_nat() -> Expr {
    app("IROption", [constant("Nat")])
}
fn option_list() -> Expr {
    app("IROption", [nat_list()])
}
fn nil() -> Expr {
    app("IRList.nil", [constant("Nat")])
}
fn cons(head: Expr, tail: Expr) -> Expr {
    app("IRList.cons", [constant("Nat"), head, tail])
}
fn some_list(value: Expr) -> Expr {
    app("IROption.some", [nat_list(), value])
}
fn none_list() -> Expr {
    app("IROption.none", [nat_list()])
}
fn bytes(memory: Expr) -> Expr {
    app("ir_byte_mem_bytes_v1", [memory])
}
fn bytes_type() -> Expr {
    Expr::pi(
        clean_kernel::BinderInfo::Default,
        constant("Nat"),
        option_nat(),
    )
}
fn address(base: Expr, count: Expr) -> Expr {
    app("Nat.add", [base, app("Nat.mul", [nat(8), count])])
}
fn write_bytes(before: Expr, at: Expr, word: Expr) -> Expr {
    app("ir_byte_write_word_v1", [before, at, nat(8), word])
}
fn written(before: Expr, at: Expr, word: Expr) -> Expr {
    app(
        "IRByteMemoryV1.mk",
        [
            app("ir_byte_mem_allocs_v1", [before.clone()]),
            write_bytes(bytes(before.clone()), at, word),
            app("ir_byte_mem_next_v1", [before]),
        ],
    )
}
fn extent(base: Expr, count: Expr) -> Expr {
    app(
        "Nat.le",
        [address(base, count), constant("ir_byte_limit_v1")],
    )
}
fn read_word(input: Expr, at: Expr) -> Expr {
    app("ir_byte_read_word_v1", [input, nat(8), at])
}
fn rec(name: &str, proposition: bool, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string(name),
            vec![if proposition {
                Level::zero()
            } else {
                Level::succ(Level::zero())
            }],
        ),
        args,
    )
}
fn close(assembler: &Assembler<'_>, parameters: &[Local], body: Expr) -> Result<Expr> {
    let term = parameters
        .iter()
        .rev()
        .fold(body, |body, local| local.lam(body));
    assembler.scope.close(&term).map_err(|e| e.to_string())
}
fn mapped(
    assembler: &mut Assembler<'_>,
    equality: PendingEquality,
    ty: Expr,
    map: impl Fn(Expr) -> Expr,
) -> Result<PendingEquality> {
    let left = map(equality.left.clone());
    let right = map(equality.right.clone());
    let mapped = assembler.congruence(equality, ty.clone(), map)?;
    let start = assembler.conversion(ty.clone(), left, mapped.left.clone())?;
    let end = assembler.conversion(ty, mapped.right.clone(), right)?;
    let mapped = assembler.compose(start, mapped)?;
    assembler.compose(mapped, end)
}

/// Only constructors below can change count/order. Sharing this Rust value is
/// not scope authority: as elsewhere in this API, use the SAME owning Scope.
pub struct InitializedEightPrefix {
    memory: Expr,
    base: Expr,
    count: usize,
    words_rev: Expr,
    readback: PendingEquality,
    extent: Option<PendingProof>,
}

impl InitializedEightPrefix {
    pub fn memory(&self) -> &Expr {
        &self.memory
    }
    pub fn base(&self) -> &Expr {
        &self.base
    }
    pub fn count(&self) -> usize {
        self.count
    }
    pub fn words_reverse(&self) -> &Expr {
        &self.words_rev
    }
    /// Reverse-order raw reads only; this equality alone is not boundedness.
    pub fn readback(&self) -> &PendingEquality {
        &self.readback
    }
    /// Empty prefixes make no extent or accessibility claim.
    pub fn extent(&self) -> Option<&PendingProof> {
        self.extent.as_ref()
    }
}

pub struct InitializedEightAppendPremises {
    /// actual address = base + 8 * old count.
    pub adjacent: PendingEquality,
    /// Actual after-memory = the exact write to this prefix's before-memory.
    pub written: PendingEquality,
    pub bounded_word: PendingProof,
    /// base + 8 * new count <= 2^64; not positivity, GEP or accessibility.
    pub extent: PendingProof,
}

pub struct InitializedEightRead {
    memory: Expr,
    base: Expr,
    count: usize,
    ordered_words: Expr,
    readback: PendingEquality,
    extent: Option<PendingProof>,
}

impl InitializedEightRead {
    pub fn memory(&self) -> &Expr {
        &self.memory
    }
    pub fn base(&self) -> &Expr {
        &self.base
    }
    pub fn count(&self) -> usize {
        self.count
    }
    pub fn ordered_words(&self) -> &Expr {
        &self.ordered_words
    }
    /// Forward raw reads only. Missing bytes remain none, never an empty list.
    pub fn readback(&self) -> &PendingEquality {
        &self.readback
    }
    pub fn extent(&self) -> Option<&PendingProof> {
        self.extent.as_ref()
    }
    /// Consumer candidate retaining BOTH the nonempty extent and actual reads.
    /// A forged extent must be rejected when replaying this conjunction.
    pub fn bounded_readback(&self) -> Option<PendingProof> {
        let bound = self.extent.as_ref()?;
        let read = self.readback.proposition();
        Some(PendingProof::candidate(
            app("And", [bound.proposition.clone(), read.clone()]),
            app(
                "And.intro",
                [
                    bound.proposition.clone(),
                    read,
                    bound.term.clone(),
                    self.readback.term.clone(),
                ],
            ),
        ))
    }
}

#[derive(Clone)]
pub(super) struct InitializedEightHelpers {
    reader: Expr,
    reverse: Expr,
    option_reverse: Expr,
    append: Expr,
    transport: Expr,
}

impl InitializedEightHelpers {
    fn read(&self, memory: Expr, base: Expr, count: Expr) -> Expr {
        Expr::apps(self.reader.clone(), [bytes(memory), base, count])
    }
    fn forward(&self, memory: Expr, base: Expr, count: Expr) -> Expr {
        Expr::app(self.option_reverse.clone(), self.read(memory, base, count))
    }
}

fn join_equalities(
    assembler: &mut Assembler<'_>,
    join: &Expr,
    head: PendingEquality,
    tail: PendingEquality,
) -> Result<PendingEquality> {
    let right_head = head.right.clone();
    let head = mapped(assembler, head, option_list(), |value| {
        Expr::apps(join.clone(), [value, tail.left.clone()])
    })?;
    let tail = mapped(assembler, tail, option_list(), |value| {
        Expr::apps(join.clone(), [right_head.clone(), value])
    })?;
    assembler.compose(head, tail)
}

impl Assembler<'_> {
    /// Fixed list combinators only. Actual memory/history terms are never
    /// captured under these binders and are not traversed when a prefix grows.
    fn initialized_eight_combinators(&mut self) -> Result<(Expr, Expr, Expr, Expr)> {
        let head = self.local(option_nat())?;
        let tail = self.local(option_list())?;
        let word = self.local(constant("Nat"))?;
        let words = self.local(nat_list())?;
        let option_motive = Expr::lam(
            clean_kernel::BinderInfo::Default,
            option_list(),
            option_list(),
        );
        let tail_case = rec(
            "IROption.rec",
            false,
            [
                nat_list(),
                option_motive.clone(),
                none_list(),
                words.lam(some_list(cons(word.term().clone(), words.term().clone()))),
                tail.term().clone(),
            ],
        );
        let join = close(
            self,
            &[head.clone(), tail],
            rec(
                "IROption.rec",
                false,
                [
                    constant("Nat"),
                    Expr::lam(
                        clean_kernel::BinderInfo::Default,
                        option_nat(),
                        option_list(),
                    ),
                    none_list(),
                    word.lam(tail_case),
                    head.term().clone(),
                ],
            ),
        )?;

        let input = self.local(bytes_type())?;
        let base = self.local(constant("Nat"))?;
        let count = self.local(constant("Nat"))?;
        let index = self.local(constant("Nat"))?;
        let previous = self.local(option_list())?;
        let step = index.lam(previous.lam(Expr::apps(
            join.clone(),
            [
                read_word(
                    input.term().clone(),
                    address(base.term().clone(), index.term().clone()),
                ),
                previous.term().clone(),
            ],
        )));
        let reader = close(
            self,
            &[input, base, count.clone()],
            rec(
                "Nat.rec",
                false,
                [
                    Expr::lam(
                        clean_kernel::BinderInfo::Default,
                        constant("Nat"),
                        option_list(),
                    ),
                    some_list(nil()),
                    step,
                    count.term().clone(),
                ],
            ),
        )?;

        // Tail-accumulating reverse: the induction result is a function from
        // the accumulator, never repeated list append or repeated nth lookup.
        let source = self.local(nat_list())?;
        let empty_acc = self.local(nat_list())?;
        let item = self.local(constant("Nat"))?;
        let rest = self.local(nat_list())?;
        let list_function = Expr::pi(clean_kernel::BinderInfo::Default, nat_list(), nat_list());
        let reverse_rest = self.local(list_function.clone())?;
        let accumulator = self.local(nat_list())?;
        let step = item.lam(rest.lam(reverse_rest.lam(accumulator.lam(Expr::app(
            reverse_rest.term().clone(),
            cons(item.term().clone(), accumulator.term().clone()),
        )))));
        let reverse = close(
            self,
            std::slice::from_ref(&source),
            Expr::app(
                rec(
                    "IRList.rec",
                    false,
                    [
                        constant("Nat"),
                        Expr::lam(clean_kernel::BinderInfo::Default, nat_list(), list_function),
                        empty_acc.lam(empty_acc.term().clone()),
                        step,
                        source.term().clone(),
                    ],
                ),
                nil(),
            ),
        )?;
        let input = self.local(option_list())?;
        let words = self.local(nat_list())?;
        let option_reverse = close(
            self,
            std::slice::from_ref(&input),
            rec(
                "IROption.rec",
                false,
                [
                    nat_list(),
                    option_motive,
                    none_list(),
                    words.lam(some_list(Expr::app(reverse.clone(), words.term().clone()))),
                    input.term().clone(),
                ],
            ),
        )?;
        Ok((join, reader, reverse, option_reverse))
    }

    /// forall count <= writeIndex, an adjacent later write preserves the
    /// complete raw read collector, including none from uninitialized bytes.
    /// Nat.rec lives in ONE closed generic helper; append does not enumerate
    /// prior slots in Rust or build one readback proof per old word.
    fn initialized_eight_frame_helper(&mut self, join: &Expr, reader: &Expr) -> Result<Expr> {
        let input = self.local(bytes_type())?;
        let base = self.local(constant("Nat"))?;
        let write_index = self.local(constant("Nat"))?;
        let word = self.local(constant("Nat"))?;
        let count = self.local(constant("Nat"))?;
        let write_at = address(base.term().clone(), write_index.term().clone());
        let new_bytes = write_bytes(input.term().clone(), write_at.clone(), word.term().clone());
        let read =
            |input: Expr, n: Expr| Expr::apps(reader.clone(), [input, base.term().clone(), n]);
        let bound_type = |n: Expr| app("Nat.le", [n, write_index.term().clone()]);
        let result_type = |n: Expr| {
            eq(
                &option_list(),
                read(new_bytes.clone(), n.clone()),
                read(input.term().clone(), n),
            )
        };
        let index = self.local(constant("Nat"))?;
        let bound = self.local(bound_type(index.term().clone()))?;
        let motive = index.lam(bound.pi(result_type(index.term().clone())));
        let zero_bound = self.local(bound_type(nat(0)))?;
        let zero = zero_bound.lam(refl(&option_list(), some_list(nil())));
        let k = self.local(constant("Nat"))?;
        let ih = self.local(Expr::app(motive.clone(), k.term().clone()))?;
        let successor = app("Nat.succ", [k.term().clone()]);
        let upper = self.local(bound_type(successor.clone()))?;
        let read_at = address(base.term().clone(), k.term().clone());
        let read_end = app("Nat.add", [read_at.clone(), nat(8)]);
        let next_at = address(base.term().clone(), successor.clone());
        // In the pinned Nat definitions, 8*(succ k) reduces to (8*k)+8.
        // add_assoc proves (base+8*k)+8 = base+8*(succ k); do not assume the
        // differently oriented public mul_succ statement is this equation.
        let end_eq = app(
            "Nat.add_assoc",
            [
                base.term().clone(),
                app("Nat.mul", [nat(8), k.term().clone()]),
                nat(8),
            ],
        );
        let mul_bound = app(
            "Nat.mul_le_mul_left",
            [
                successor.clone(),
                write_index.term().clone(),
                nat(8),
                upper.term().clone(),
            ],
        );
        let canonical_bound = app(
            "Nat.add_le_add_left",
            [
                app("Nat.mul", [nat(8), successor.clone()]),
                app("Nat.mul", [nat(8), write_index.term().clone()]),
                mul_bound,
                base.term().clone(),
            ],
        );
        let endpoint = self.local(constant("Nat"))?;
        let before = rec(
            "Eq.subst",
            false,
            [
                constant("Nat"),
                endpoint.lam(app("Nat.le", [endpoint.term().clone(), write_at.clone()])),
                next_at.clone(),
                read_end.clone(),
                rec(
                    "Eq.symm",
                    false,
                    [constant("Nat"), read_end.clone(), next_at, end_eq],
                ),
                canonical_bound,
            ],
        );
        let before_type = app("Nat.le", [read_end, write_at.clone()]);
        let after_type = app(
            "Nat.le",
            [app("Nat.add", [write_at.clone(), nat(8)]), read_at.clone()],
        );
        let apart = app("Or.inl", [before_type, after_type, before]);
        let head = PendingEquality::candidate(
            option_nat(),
            read_word(new_bytes.clone(), read_at.clone()),
            read_word(input.term().clone(), read_at.clone()),
            app(
                "ir_byte_read_write_disjoint_v1",
                [
                    input.term().clone(),
                    read_at,
                    nat(8),
                    write_at,
                    nat(8),
                    word.term().clone(),
                    apart,
                ],
            ),
        );
        let tail_bound = app(
            "Nat.le_trans",
            [
                k.term().clone(),
                successor.clone(),
                write_index.term().clone(),
                app("Nat.le_add_right", [k.term().clone(), nat(1)]),
                upper.term().clone(),
            ],
        );
        let tail = PendingEquality::candidate(
            option_list(),
            read(new_bytes.clone(), k.term().clone()),
            read(input.term().clone(), k.term().clone()),
            Expr::app(ih.term().clone(), tail_bound),
        );
        let joined = join_equalities(self, join, head, tail)?;
        let left = self.conversion(
            option_list(),
            read(new_bytes, successor.clone()),
            joined.left.clone(),
        )?;
        let right = self.conversion(
            option_list(),
            joined.right.clone(),
            read(input.term().clone(), successor),
        )?;
        let joined = self.compose(left, joined)?;
        let joined = self.compose(joined, right)?;
        let step = k.lam(ih.lam(upper.lam(joined.term)));
        let final_bound = self.local(bound_type(count.term().clone()))?;
        let body = Expr::app(
            rec("Nat.rec", true, [motive, zero, step, count.term().clone()]),
            final_bound.term().clone(),
        );
        close(
            self,
            &[input, base, write_index, word, count, final_bound],
            body,
        )
    }

    fn initialized_eight_append_helper(
        &mut self,
        join: &Expr,
        reader: &Expr,
        frame: &Expr,
    ) -> Result<Expr> {
        let before = self.local(constant("IRByteMemoryV1"))?;
        let after = self.local(constant("IRByteMemoryV1"))?;
        let base = self.local(constant("Nat"))?;
        let count = self.local(constant("Nat"))?;
        let words = self.local(nat_list())?;
        let at = self.local(constant("Nat"))?;
        let word = self.local(constant("Nat"))?;
        let canonical_at = address(base.term().clone(), count.term().clone());
        let adjacent = self.local(eq(
            &constant("Nat"),
            at.term().clone(),
            canonical_at.clone(),
        ))?;
        let written_at = written(
            before.term().clone(),
            at.term().clone(),
            word.term().clone(),
        );
        let written_proof = self.local(eq(
            &constant("IRByteMemoryV1"),
            after.term().clone(),
            written_at.clone(),
        ))?;
        let bounded = self.local(app(
            "Nat.lt",
            [word.term().clone(), constant("ir_byte_limit_v1")],
        ))?;
        let read = |memory: Expr, n: Expr| {
            Expr::apps(reader.clone(), [bytes(memory), base.term().clone(), n])
        };
        let old_left = read(before.term().clone(), count.term().clone());
        let old = self.local(eq(
            &option_list(),
            old_left.clone(),
            some_list(words.term().clone()),
        ))?;
        let canonical_memory = written(
            before.term().clone(),
            canonical_at.clone(),
            word.term().clone(),
        );
        let adjacent_map = mapped(
            self,
            PendingEquality::candidate(
                constant("Nat"),
                at.term().clone(),
                canonical_at.clone(),
                adjacent.term().clone(),
            ),
            constant("IRByteMemoryV1"),
            |value| written(before.term().clone(), value, word.term().clone()),
        )?;
        let memory_eq = self.compose(
            PendingEquality::candidate(
                constant("IRByteMemoryV1"),
                after.term().clone(),
                written_at,
                written_proof.term().clone(),
            ),
            adjacent_map,
        )?;
        let next_count = app("Nat.succ", [count.term().clone()]);
        let leading = mapped(self, memory_eq, option_list(), |memory| {
            read(memory, next_count.clone())
        })?;
        let framed = PendingEquality::candidate(
            option_list(),
            read(canonical_memory.clone(), count.term().clone()),
            old_left.clone(),
            Expr::apps(
                frame.clone(),
                [
                    bytes(before.term().clone()),
                    base.term().clone(),
                    count.term().clone(),
                    word.term().clone(),
                    count.term().clone(),
                    app("Nat.le_refl", [count.term().clone()]),
                ],
            ),
        );
        let tail = self.compose(
            framed,
            PendingEquality::candidate(
                option_list(),
                old_left,
                some_list(words.term().clone()),
                old.term().clone(),
            ),
        )?;
        let head = PendingEquality::candidate(
            option_nat(),
            read_word(bytes(canonical_memory.clone()), canonical_at.clone()),
            some("Nat", word.term().clone()),
            app(
                "ir_byte_read_write_eight_v1",
                [
                    bytes(before.term().clone()),
                    canonical_at,
                    word.term().clone(),
                    bounded.term().clone(),
                ],
            ),
        );
        let joined = join_equalities(self, join, head, tail)?;
        let start = self.conversion(
            option_list(),
            read(canonical_memory, next_count),
            joined.left.clone(),
        )?;
        let end = self.conversion(
            option_list(),
            joined.right.clone(),
            some_list(cons(word.term().clone(), words.term().clone())),
        )?;
        let proof = self.compose(leading, start)?;
        let proof = self.compose(proof, joined)?;
        let proof = self.compose(proof, end)?;
        close(
            self,
            &[
                before,
                after,
                base,
                count,
                words,
                at,
                word,
                adjacent,
                written_proof,
                bounded,
                old,
            ],
            proof.term,
        )
    }

    fn initialized_eight_transport_helper(&mut self, reader: &Expr) -> Result<Expr> {
        let before = self.local(constant("IRByteMemoryV1"))?;
        let after = self.local(constant("IRByteMemoryV1"))?;
        let base = self.local(constant("Nat"))?;
        let count = self.local(constant("Nat"))?;
        let words = self.local(nat_list())?;
        let same = self.local(eq(
            &bytes_type(),
            bytes(after.term().clone()),
            bytes(before.term().clone()),
        ))?;
        let read = |input: Expr| {
            Expr::apps(
                reader.clone(),
                [input, base.term().clone(), count.term().clone()],
            )
        };
        let old_left = read(bytes(before.term().clone()));
        let old = self.local(eq(
            &option_list(),
            old_left.clone(),
            some_list(words.term().clone()),
        ))?;
        let mapped = mapped(
            self,
            PendingEquality::candidate(
                bytes_type(),
                bytes(after.term().clone()),
                bytes(before.term().clone()),
                same.term().clone(),
            ),
            option_list(),
            read,
        )?;
        let proof = self.compose(
            mapped,
            PendingEquality::candidate(
                option_list(),
                old_left,
                some_list(words.term().clone()),
                old.term().clone(),
            ),
        )?;
        close(
            self,
            &[before, after, base, count, words, same, old],
            proof.term,
        )
    }

    fn initialized_eight_helpers(&mut self) -> Result<InitializedEightHelpers> {
        if let Some(helpers) = &self.initialized_eight_helpers {
            return Ok(helpers.clone());
        }
        let (join, reader, reverse, option_reverse) = self.initialized_eight_combinators()?;
        let frame = self.initialized_eight_frame_helper(&join, &reader)?;
        let append = self.initialized_eight_append_helper(&join, &reader, &frame)?;
        let transport = self.initialized_eight_transport_helper(&reader)?;
        let helpers = InitializedEightHelpers {
            reader,
            reverse,
            option_reverse,
            append,
            transport,
        };
        #[cfg(test)]
        {
            self.initialized_eight_helper_builds += 1;
        }
        self.initialized_eight_helpers = Some(helpers.clone());
        Ok(helpers)
    }
}

impl Assembler<'_> {
    /// Independently construct the forward reader from actual memory/base/count.
    /// Expected words are NOT an input to this expression.
    pub fn byte_initialized_eight_read(
        &mut self,
        memory: Expr,
        base: Expr,
        count: &NatTerm,
    ) -> Result<Expr> {
        self.charge()?;
        let helpers = self.initialized_eight_helpers()?;
        Ok(helpers.forward(memory, base, count.0.clone()))
    }

    pub fn byte_initialized_eight_empty(
        &mut self,
        memory: Expr,
        base: Expr,
    ) -> Result<InitializedEightPrefix> {
        self.charge()?;
        self.items(0)?;
        let helpers = self.initialized_eight_helpers()?;
        let words_rev = nil();
        Ok(InitializedEightPrefix {
            readback: PendingEquality::candidate(
                option_list(),
                helpers.read(memory.clone(), base.clone(), nat(0)),
                some_list(words_rev.clone()),
                refl(&option_list(), some_list(words_rev.clone())),
            ),
            memory,
            base,
            count: 0,
            words_rev,
            extent: None,
        })
    }

    pub fn byte_initialized_eight_append(
        &mut self,
        prefix: InitializedEightPrefix,
        at: Expr,
        word: Expr,
        after_memory: Expr,
        premises: InitializedEightAppendPremises,
    ) -> Result<InitializedEightPrefix> {
        self.charge()?;
        let count = prefix
            .count
            .checked_add(1)
            .ok_or("initialized prefix count overflow")?;
        self.items(count)?;
        let old_count =
            u64::try_from(prefix.count).map_err(|_| "initialized prefix count does not fit u64")?;
        let new_count =
            u64::try_from(count).map_err(|_| "initialized prefix count does not fit u64")?;
        new_count
            .checked_mul(8)
            .ok_or("initialized prefix byte offset overflow")?;
        let helpers = self.initialized_eight_helpers()?;
        prefix.readback.endpoints(
            &option_list(),
            &helpers.read(prefix.memory.clone(), prefix.base.clone(), nat(old_count)),
            &some_list(prefix.words_rev.clone()),
        )?;
        premises.adjacent.endpoints(
            &constant("Nat"),
            &at,
            &address(prefix.base.clone(), nat(old_count)),
        )?;
        premises.written.endpoints(
            &constant("IRByteMemoryV1"),
            &after_memory,
            &written(prefix.memory.clone(), at.clone(), word.clone()),
        )?;
        require_same(
            premises.bounded_word.proposition(),
            &app("Nat.lt", [word.clone(), constant("ir_byte_limit_v1")]),
            "initialized prefix word bound",
        )?;
        require_same(
            premises.extent.proposition(),
            &extent(prefix.base.clone(), nat(new_count)),
            "initialized prefix extent",
        )?;
        let words_rev = cons(word.clone(), prefix.words_rev.clone());
        let proof = Expr::apps(
            helpers.append.clone(),
            [
                prefix.memory,
                after_memory.clone(),
                prefix.base.clone(),
                nat(old_count),
                prefix.words_rev,
                at,
                word,
                premises.adjacent.term,
                premises.written.term,
                premises.bounded_word.term,
                prefix.readback.term,
            ],
        );
        #[cfg(test)]
        {
            self.initialized_eight_appends += 1;
        }
        Ok(InitializedEightPrefix {
            readback: PendingEquality::candidate(
                option_list(),
                helpers.read(after_memory.clone(), prefix.base.clone(), nat(new_count)),
                some_list(words_rev.clone()),
                proof,
            ),
            memory: after_memory,
            base: prefix.base,
            count,
            words_rev,
            extent: Some(premises.extent),
        })
    }

    /// Explicit raw-byte equality, not owner-only or accessibility framing.
    pub fn byte_initialized_eight_transport(
        &mut self,
        prefix: InitializedEightPrefix,
        after_memory: Expr,
        same_bytes: PendingEquality,
    ) -> Result<InitializedEightPrefix> {
        self.charge()?;
        self.items(prefix.count)?;
        let count =
            nat(u64::try_from(prefix.count)
                .map_err(|_| "initialized prefix count does not fit u64")?);
        let helpers = self.initialized_eight_helpers()?;
        prefix.readback.endpoints(
            &option_list(),
            &helpers.read(prefix.memory.clone(), prefix.base.clone(), count.clone()),
            &some_list(prefix.words_rev.clone()),
        )?;
        same_bytes.endpoints(
            &bytes_type(),
            &bytes(after_memory.clone()),
            &bytes(prefix.memory.clone()),
        )?;
        let term = Expr::apps(
            helpers.transport.clone(),
            [
                prefix.memory,
                after_memory.clone(),
                prefix.base.clone(),
                count.clone(),
                prefix.words_rev.clone(),
                same_bytes.term,
                prefix.readback.term,
            ],
        );
        Ok(InitializedEightPrefix {
            readback: PendingEquality::candidate(
                option_list(),
                helpers.read(after_memory.clone(), prefix.base.clone(), count),
                some_list(prefix.words_rev.clone()),
                term,
            ),
            memory: after_memory,
            base: prefix.base,
            count: prefix.count,
            words_rev: prefix.words_rev,
            extent: prefix.extent,
        })
    }

    pub fn byte_initialized_eight_finish(
        &mut self,
        prefix: InitializedEightPrefix,
    ) -> Result<InitializedEightRead> {
        self.charge()?;
        self.items(prefix.count)?;
        let count =
            nat(u64::try_from(prefix.count)
                .map_err(|_| "initialized prefix count does not fit u64")?);
        let helpers = self.initialized_eight_helpers()?;
        prefix.readback.endpoints(
            &option_list(),
            &helpers.read(prefix.memory.clone(), prefix.base.clone(), count.clone()),
            &some_list(prefix.words_rev.clone()),
        )?;
        let ordered_words = Expr::app(helpers.reverse.clone(), prefix.words_rev);
        let term = app(
            "ir_eq_cong",
            [
                option_list(),
                option_list(),
                helpers.option_reverse.clone(),
                prefix.readback.left,
                prefix.readback.right,
                prefix.readback.term,
            ],
        );
        Ok(InitializedEightRead {
            readback: PendingEquality::candidate(
                option_list(),
                helpers.forward(prefix.memory.clone(), prefix.base.clone(), count),
                some_list(ordered_words.clone()),
                term,
            ),
            memory: prefix.memory,
            base: prefix.base,
            count: prefix.count,
            ordered_words,
            extent: prefix.extent,
        })
    }
}
