// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pending small integer compositions of the existing ByteV1 evaluator and laws.
//!
//! I/U8, I/U16 and I/U32 retain their actual nominal type and bit pattern.
//! These helpers do not execute a source node, grant access, install a theorem,
//! or mint proof authority. The complete closed claim still needs independent
//! kernel replay, and actual instruction transfer uses `FetchedSite::memory_value`.
//! The existing eight-byte proof construction and serialized terms are unchanged.

use super::*;

#[derive(Clone, Copy)]
enum WordDomain {
    FourOnly,
    Small,
}

fn integer_byte_count(ty: &Expr, domain: WordDomain) -> Result<u64> {
    // Keep the old API's charged refusal, including its exact diagnostic.
    if matches!(domain, WordDomain::FourOnly) {
        integer32(ty)?;
        return Ok(4);
    }
    for (bits, count) in [(8, 1), (16, 2), (32, 4)] {
        if ty == &app("IRTy.int_", [nat(bits)]) || ty == &app("IRTy.uint_", [nat(bits)]) {
            return Ok(count);
        }
    }
    Err("small integer codec requires the actual I/U8, I/U16 or I/U32 type".into())
}

fn integer_word_limit(count: u64) -> Expr {
    app("ir_nat_pow2", [nat(8 * count)])
}

fn bound_label(domain: WordDomain) -> &'static str {
    match domain {
        WordDomain::FourOnly => "four-byte canonical word bound",
        WordDomain::Small => "small integer canonical word bound",
    }
}

#[cfg(test)]
fn word_limit() -> Expr {
    integer_word_limit(4)
}

fn integer32(ty: &Expr) -> Result<()> {
    if ty == &app("IRTy.int_", [nat(32)]) || ty == &app("IRTy.uint_", [nat(32)]) {
        Ok(())
    } else {
        Err("four-byte codec requires the actual I32 or U32 type".into())
    }
}

fn word_layout_guard(shape: Expr, count: u64) -> Expr {
    word_layout_condition(shape, nat(count))
}

/// Exact integer codec endpoints are candidates, not checked facts. The
/// historical name remains source-compatible; Four APIs still require32 bits.
#[derive(Clone)]
pub struct ByteFourCodec {
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
pub struct ByteLoadFour {
    pub pointer: Expr,
    pub address: Expr,
    pub requested_align: Expr,
    pub memory: Expr,
}

#[derive(Clone)]
pub struct ByteLoadFourPremises {
    pub pointer: PendingEquality,
    /// Complete live unique nominal-width extent at the effective alignment.
    pub accessible: PendingEquality,
    /// Initialized read_word(bytes(input.memory), nominal width, input.address).
    pub initialized: PendingEquality,
}

#[derive(Clone)]
pub struct ByteStoreFour {
    pub pointer: Expr,
    pub address: Expr,
    pub requested_align: Expr,
    pub memory: Expr,
}

#[derive(Clone)]
pub struct ByteStoreFourPremises {
    pub pointer: PendingEquality,
    /// Complete live unique nominal-width extent in the actual incoming memory.
    pub accessible: PendingEquality,
}

pub struct ByteStoreFourResult {
    pub result: MemoryResult,
    pub evaluated: PendingEquality,
    pub allocations: PendingEquality,
    pub cursor: PendingEquality,
    /// Readback from final memory, not entry memory.
    pub raw_read: PendingEquality,
    /// Actual nonvolatile typed load from that same final memory.
    pub typed_readback: PendingEquality,
}

/// Small integer codec, with width derived only from its exact nominal type.
pub type ByteWordCodec = ByteFourCodec;
pub type ByteLoadWord = ByteLoadFour;
pub type ByteLoadWordPremises = ByteLoadFourPremises;
pub type ByteStoreWord = ByteStoreFour;
pub type ByteStoreWordPremises = ByteStoreFourPremises;
pub type ByteStoreWordResult = ByteStoreFourResult;

struct WordLoadEvidence {
    align: Expr,
    pointer: PendingEquality,
    accessible: Expr,
    initialized: Expr,
}

impl ByteFourCodec {
    /// Return only nominal width metadata, never proof or access authority.
    /// Forged or unsupported nominal types refuse rather than choosing a width.
    pub fn byte_count(&self) -> Result<u64> {
        integer_byte_count(&self.ty, WordDomain::Small)
    }

    fn validate(&self, domain: WordDomain) -> Result<u64> {
        let count = integer_byte_count(&self.ty, domain)?;
        self.lane.endpoints(
            &option("Nat"),
            &app("ir_byte_lane_size_v1", [self.ty.clone()]),
            &some("Nat", nat(count)),
        )?;
        self.layout_found.endpoints(
            &option("IRByteLayoutV1"),
            &app("ir_byte_layout_v1", [self.context.clone(), self.ty.clone()]),
            &some("IRByteLayoutV1", self.layout.clone()),
        )?;
        self.valid_layout.endpoints(
            &constant("Bool"),
            &word_layout_guard(self.layout.clone(), count),
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
            &app("Nat.lt", [self.word.clone(), integer_word_limit(count)]),
            bound_label(domain),
        )?;
        Ok(count)
    }
}

// These terms are the case branches of the existing checked public dispatch,
// not an additional memory evaluator. Arbitrary operands remain in its claim.
fn access_at(
    codec: &ByteFourCodec,
    input: &ByteLoadFour,
    shape: Expr,
    size: Expr,
    address: Expr,
    store: bool,
) -> Expr {
    WordDispatchInput::actual(codec, input).at(shape, size, address, store)
}

// Fixed template inputs: context, nominal type, scalar value, pointer,
// requested alignment and complete memory. Caller terms are ONLY arguments
// outside the six closed binders; no traversal/substitution of caller data.
struct WordDispatchInput {
    context: Expr,
    ty: Expr,
    value: Expr,
    pointer: Expr,
    requested_align: Expr,
    memory: Expr,
}

impl WordDispatchInput {
    fn actual(codec: &ByteFourCodec, input: &ByteLoadFour) -> Self {
        Self {
            context: codec.context.clone(),
            ty: codec.ty.clone(),
            value: codec.value.clone(),
            pointer: input.pointer.clone(),
            requested_align: input.requested_align.clone(),
            memory: input.memory.clone(),
        }
    }

    fn neutral(depth: u32) -> Self {
        let parameter = |position| Expr::bvar(depth - position - 1);
        Self {
            context: parameter(0),
            ty: parameter(1),
            value: parameter(2),
            pointer: parameter(3),
            requested_align: parameter(4),
            memory: parameter(5),
        }
    }

    fn arguments(self) -> [Expr; 6] {
        [
            self.context,
            self.ty,
            self.value,
            self.pointer,
            self.requested_align,
            self.memory,
        ]
    }

    fn at(&self, shape: Expr, size: Expr, address: Expr, store: bool) -> Expr {
        let align = app(
            "ir_byte_effective_align_v1",
            [
                self.requested_align.clone(),
                app("ir_byte_layout_align_v1", [shape]),
            ],
        );
        if store {
            app(
                "ir_byte_store_at_v1",
                [
                    self.context.clone(),
                    self.ty.clone(),
                    address,
                    self.value.clone(),
                    size,
                    align,
                    self.memory.clone(),
                ],
            )
        } else {
            app(
                "ir_byte_load_at_v1",
                [
                    self.context.clone(),
                    self.ty.clone(),
                    address,
                    size,
                    align,
                    self.memory.clone(),
                ],
            )
        }
    }
}

// One actual option-success tree, with the same size/layout/address binders
// reused by the checked case laws. These are fixed closed candidate templates,
// not a cache, assumption or evaluator. Former local charges are retained.
struct WordDispatchFunctions {
    pointer: Expr,
    layout: Expr,
    size: Expr,
}

fn word_layout_condition(shape: Expr, size: Expr) -> Expr {
    app(
        "Bool.and",
        [
            app(
                "ir_nat_eqb",
                [size, app("ir_byte_layout_size_v1", [shape.clone()])],
            ),
            app(
                "ir_byte_alignment_v1",
                [app("ir_byte_layout_align_v1", [shape])],
            ),
        ],
    )
}

fn option_branch(input_ty: &str, failure: Expr, success: Expr, scrutinee: Expr) -> Expr {
    option_rec([
        constant(input_ty),
        Expr::lam(
            clean_kernel::BinderInfo::Default,
            option(input_ty),
            constant("IRByteMemoryResultV1"),
        ),
        failure,
        success,
        scrutinee,
    ])
}

fn word_dispatch_functions(
    assembler: &mut Assembler<'_>,
    codec: &ByteFourCodec,
    input: &ByteLoadFour,
    store: bool,
) -> Result<WordDispatchFunctions> {
    // Preserve address/shape/size's original three construction charges, in
    // that order. Only their allocations in the caller Scope disappear.
    for _ in 0..3 {
        assembler.charge()?;
    }
    let functions = closed_word_dispatch_functions(store);
    let arguments = WordDispatchInput::actual(codec, input).arguments();
    Ok(WordDispatchFunctions {
        pointer: Expr::apps(functions.pointer, arguments.clone()),
        layout: Expr::apps(functions.layout, arguments.clone()),
        size: Expr::apps(functions.size, arguments),
    })
}

fn close_word_dispatch(body: Expr) -> Expr {
    [
        "IRByteContextV1",
        "IRTy",
        "IRScalar",
        "IRScalar",
        "Nat",
        "IRByteMemoryV1",
    ]
    .into_iter()
    .rev()
    .fold(body, |body, ty| {
        Expr::lam(clean_kernel::BinderInfo::Default, constant(ty), body)
    })
}

fn closed_word_dispatch_functions(store: bool) -> WordDispatchFunctions {
    // The common neutral inputs are followed by size, shape and address.
    let pointer_success = Expr::lam(
        clean_kernel::BinderInfo::Default,
        constant("Nat"),
        WordDispatchInput::neutral(9).at(Expr::bvar(1), Expr::bvar(2), Expr::bvar(0), store),
    );
    let layout_data = WordDispatchInput::neutral(8);
    let pointer = option_branch(
        "Nat",
        fault("type_error", "not_ptr", layout_data.memory.clone()),
        pointer_success.clone(),
        pointer_address(layout_data.pointer.clone()),
    );
    let layout_success = Expr::lam(
        clean_kernel::BinderInfo::Default,
        constant("IRByteLayoutV1"),
        choose(
            &constant("IRByteMemoryResultV1"),
            word_layout_condition(Expr::bvar(0), Expr::bvar(1)),
            pointer,
            fault("type_error", "width_bounded", layout_data.memory),
        ),
    );
    let size_data = WordDispatchInput::neutral(7);
    let layout = option_branch(
        "IRByteLayoutV1",
        fault("unmodelled", "width_bounded", size_data.memory),
        layout_success.clone(),
        app("ir_byte_layout_v1", [size_data.context, size_data.ty]),
    );
    let size_lam = |body| Expr::lam(clean_kernel::BinderInfo::Default, constant("Nat"), body);
    WordDispatchFunctions {
        pointer: close_word_dispatch(size_lam(Expr::lam(
            clean_kernel::BinderInfo::Default,
            constant("IRByteLayoutV1"),
            pointer_success,
        ))),
        layout: close_word_dispatch(size_lam(layout_success)),
        size: close_word_dispatch(size_lam(layout)),
    }
}

fn dispatch_word(
    assembler: &mut Assembler<'_>,
    codec: &ByteFourCodec,
    input: &ByteLoadFour,
    count: u64,
    pointer: PendingEquality,
    store: bool,
) -> Result<PendingEquality> {
    let functions = word_dispatch_functions(assembler, codec, input, store)?;
    let ty = constant("IRByteMemoryResultV1");
    let expected = access_at(
        codec,
        input,
        codec.layout.clone(),
        nat(count),
        input.address.clone(),
        store,
    );
    let step = PendingEquality::reflexive(ty.clone(), expected);
    let pointer_function = Expr::apps(functions.pointer, [nat(count), codec.layout.clone()]);
    let source = option_branch(
        "Nat",
        fault("type_error", "not_ptr", input.memory.clone()),
        pointer_function.clone(),
        pointer_address(input.pointer.clone()),
    );
    let pointer = some_case_function(
        "Nat",
        ty.clone(),
        source,
        fault("type_error", "not_ptr", input.memory.clone()),
        pointer,
        input.address.clone(),
        pointer_function,
        step,
    );
    let source = choose(
        &ty,
        word_layout_condition(codec.layout.clone(), nat(count)),
        pointer.left.clone(),
        fault("type_error", "width_bounded", input.memory.clone()),
    );
    let layout = true_case(
        ty.clone(),
        source,
        fault("type_error", "width_bounded", input.memory.clone()),
        pointer.left.clone(),
        codec.valid_layout.clone(),
        pointer,
    );
    let layout_function = Expr::app(functions.layout, nat(count));
    let source = option_branch(
        "IRByteLayoutV1",
        fault("unmodelled", "width_bounded", input.memory.clone()),
        layout_function.clone(),
        app(
            "ir_byte_layout_v1",
            [codec.context.clone(), codec.ty.clone()],
        ),
    );
    let layout = some_case_function(
        "IRByteLayoutV1",
        ty.clone(),
        source,
        fault("unmodelled", "width_bounded", input.memory.clone()),
        codec.layout_found.clone(),
        codec.layout.clone(),
        layout_function,
        layout,
    );
    let source = if store {
        app(
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
        )
    } else {
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
        )
    };
    Ok(some_case_function(
        "Nat",
        ty,
        source,
        fault("unmodelled", "width_bounded", input.memory.clone()),
        codec.lane.clone(),
        nat(count),
        functions.size,
        layout,
    ))
}

fn store_word_branch(input: &ByteLoadFour, word: Expr, count: u64) -> Expr {
    store_word_branch_at(input.memory.clone(), input.address.clone(), word, count)
}

fn store_word_branch_at(memory: Expr, address: Expr, word: Expr, count: u64) -> Expr {
    let next = written_word(memory.clone(), address, count, word.clone());
    choose(
        &constant("IRByteMemoryResultV1"),
        app(
            "ir_nat_ltb",
            [
                word,
                app("ir_nat_pow2", [app("Nat.mul", [nat(8), nat(count)])]),
            ],
        ),
        MemoryResult {
            value: constant("IRScalar.unit_"),
            memory: next,
        }
        .result(),
        fault("type_error", "width_bounded", memory),
    )
}

fn store_option_branch(
    assembler: &mut Assembler<'_>,
    codec: &ByteFourCodec,
    input: &ByteLoadFour,
    count: u64,
) -> Result<(Expr, Expr)> {
    // Keep the former word-local operation at its original position.
    assembler.charge()?;
    let success = Expr::apps(
        closed_store_word_function(count),
        [input.memory.clone(), input.address.clone()],
    );
    let source = option_branch(
        "Nat",
        fault("type_error", "width_bounded", input.memory.clone()),
        success.clone(),
        app(
            "ir_byte_scalar_word_v1",
            [codec.context.clone(), codec.value.clone()],
        ),
    );
    Ok((source, success))
}

fn closed_store_word_function(count: u64) -> Expr {
    // memory, address, then word. Width is still the validated nominal count.
    let body = store_word_branch_at(Expr::bvar(2), Expr::bvar(1), Expr::bvar(0), count);
    ["IRByteMemoryV1", "Nat", "Nat"]
        .into_iter()
        .rev()
        .fold(body, |body, ty| {
            Expr::lam(clean_kernel::BinderInfo::Default, constant(ty), body)
        })
}

fn written_word(memory: Expr, address: Expr, count: u64, word: Expr) -> Expr {
    app(
        "IRByteMemoryV1.mk",
        [
            allocs(memory.clone()),
            app(
                "ir_byte_write_word_v1",
                [bytes(memory.clone()), address, nat(count), word],
            ),
            cursor(memory),
        ],
    )
}

fn some_function() -> Expr {
    Expr::lam(
        clean_kernel::BinderInfo::Default,
        constant("Nat"),
        some("Nat", Expr::bvar(0)),
    )
}

fn option_congruence(left: Expr, right: Expr, proof: Expr) -> Expr {
    app(
        "ir_eq_cong",
        [
            constant("Nat"),
            option("Nat"),
            some_function(),
            left,
            right,
            proof,
        ],
    )
}

fn symmetric_nat(left: Expr, right: Expr, proof: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.symm"),
            vec![Level::succ(Level::zero())],
        ),
        [constant("Nat"), left, right, proof],
    )
}

// A bounded nominal-width proof of the actual byte writer/reader for every old
// byte map, address and canonical word. No finite-value lookup or new axiom.
fn raw_read_word(
    assembler: &mut Assembler<'_>,
    old_bytes: Expr,
    address: Expr,
    word: Expr,
    count: u64,
    bounded: Expr,
) -> Result<PendingEquality> {
    assembler.charge()?;
    let ty = option("Nat");
    // count comes only from integer_byte_count (1, 2 or 4), so these host
    // divisors are representable. Do not extend this algorithm to8 or16 bytes.
    let limit = 1_u64 << (8 * count);
    let modulus = nat(limit);
    let written = app(
        "ir_byte_write_word_v1",
        [old_bytes.clone(), address.clone(), nat(count), word.clone()],
    );
    let quotient = app("Nat.div", [word.clone(), modulus.clone()]);
    let final_address = app("Nat.add", [address.clone(), nat(count)]);
    let below = app(
        "ir_byte_div_below_v1",
        [
            word.clone(),
            modulus,
            app("Nat.zero_lt_succ", [nat(limit - 1)]),
            bounded,
        ],
    );
    let mut tail = trans(
        &ty,
        app(
            "ir_byte_read_word_v1",
            [written.clone(), nat(0), final_address.clone()],
        ),
        some("Nat", nat(0)),
        some("Nat", quotient.clone()),
        app("ir_byte_read_zero_v1", [written.clone(), final_address]),
        option_congruence(
            nat(0),
            quotient.clone(),
            symmetric_nat(quotient, nat(0), below),
        ),
    );
    for i in (0_u64..count).rev() {
        assembler.charge()?;
        let divisor = 1_u64 << (8 * i);
        let quotient = app("Nat.div", [word.clone(), nat(divisor)]);
        let next = app("Nat.div", [word.clone(), nat(divisor * 256)]);
        let byte = app("Nat.mod", [quotient.clone(), nat(256)]);
        let at = app("Nat.add", [address.clone(), nat(i)]);
        let combined = app(
            "Nat.add",
            [byte.clone(), app("Nat.mul", [nat(256), next.clone()])],
        );
        let mut offset_bound = app("Nat.zero_le", [nat(count - 1 - i)]);
        for k in 0..=i {
            offset_bound = app(
                "Nat.succ_le_succ",
                [nat(k), nat(count - 1 - i + k), offset_bound],
            );
        }
        let digit = app(
            "ir_byte_write_digit_v1",
            [
                old_bytes.clone(),
                address.clone(),
                nat(count),
                word.clone(),
                nat(i),
                offset_bound,
            ],
        );
        let byte_bound = app(
            "ir_byte_ltb_of_lt_v1",
            [
                byte.clone(),
                nat(256),
                app(
                    "Nat.mod_lt",
                    [
                        quotient.clone(),
                        nat(256),
                        app("Nat.zero_lt_succ", [nat(255)]),
                    ],
                ),
            ],
        );
        let read = app(
            "ir_byte_read_success_v1",
            [
                written.clone(),
                nat(count - 1 - i),
                at.clone(),
                byte,
                next,
                digit,
                byte_bound,
                tail,
            ],
        );
        let radix = app(
            "ir_byte_radix_step_v1",
            [
                word.clone(),
                nat(divisor),
                app("Nat.zero_lt_succ", [nat(divisor - 1)]),
            ],
        );
        tail = trans(
            &ty,
            app(
                "ir_byte_read_word_v1",
                [written.clone(), nat(count - i), at],
            ),
            some("Nat", combined.clone()),
            some("Nat", quotient.clone()),
            read,
            option_congruence(combined, quotient, radix),
        );
    }
    let source = app("ir_byte_read_word_v1", [written, nat(count), address]);
    let quotient = app("Nat.div", [word.clone(), nat(1)]);
    let term = trans(
        &ty,
        source.clone(),
        some("Nat", quotient.clone()),
        some("Nat", word.clone()),
        tail,
        option_congruence(
            quotient,
            word.clone(),
            app("ir_byte_div_one_v1", [word.clone()]),
        ),
    );
    Ok(PendingEquality::candidate(
        ty,
        source,
        some("Nat", word),
        term,
    ))
}

impl Assembler<'_> {
    /// Candidate codec for the exact I/U8, I/U16 or I/U32 nominal type.
    /// Width is derived from that type; all terms still require kernel replay.
    pub fn byte_integer_word_codec(
        &mut self,
        context: Expr,
        ty: Expr,
        word: Expr,
        layout_found: PendingEquality,
        bounded: PendingProof,
    ) -> Result<ByteWordCodec> {
        self.integer_word_codec(context, ty, word, layout_found, bounded, WordDomain::Small)
    }

    /// Preserve the actual nominal I32/U32 type and all canonical 32-bit
    /// patterns. The reflected context's layout remains an exact premise.
    pub fn byte_integer32_codec(
        &mut self,
        context: Expr,
        ty: Expr,
        word: Expr,
        layout_found: PendingEquality,
        bounded: PendingProof,
    ) -> Result<ByteFourCodec> {
        self.integer_word_codec(
            context,
            ty,
            word,
            layout_found,
            bounded,
            WordDomain::FourOnly,
        )
    }

    fn integer_word_codec(
        &mut self,
        context: Expr,
        ty: Expr,
        word: Expr,
        layout_found: PendingEquality,
        bounded: PendingProof,
        domain: WordDomain,
    ) -> Result<ByteWordCodec> {
        self.charge()?;
        let count = integer_byte_count(&ty, domain)?;
        require_same(
            bounded.proposition(),
            &app("Nat.lt", [word.clone(), integer_word_limit(count)]),
            bound_label(domain),
        )?;
        let value = scalar(word.clone());
        let shape = layout(ty.clone(), count);
        let fits = app(
            "ir_byte_value_matches_v1",
            [context.clone(), ty.clone(), value.clone()],
        );
        let fits_shape = self.conversion(
            constant("Bool"),
            fits,
            app("ir_nat_ltb", [word.clone(), integer_word_limit(count)]),
        )?;
        let fits = self.compose(
            fits_shape,
            ltb(
                word.clone(),
                integer_word_limit(count),
                bounded.term.clone(),
            ),
        )?;
        let codec = ByteFourCodec {
            context: context.clone(),
            ty: ty.clone(),
            value: value.clone(),
            word: word.clone(),
            layout: shape.clone(),
            lane: PendingEquality::candidate(
                option("Nat"),
                app("ir_byte_lane_size_v1", [ty.clone()]),
                some("Nat", nat(count)),
                refl(&option("Nat"), some("Nat", nat(count))),
            ),
            layout_found,
            valid_layout: bool_fact(
                word_layout_guard(shape, count),
                refl(&constant("Bool"), constant("Bool.true")),
            ),
            fits,
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
        codec.validate(domain)?;
        Ok(codec)
    }

    pub fn byte_load_word(
        &mut self,
        codec: &ByteWordCodec,
        input: ByteLoadWord,
        premises: ByteLoadWordPremises,
    ) -> Result<PendingEquality> {
        self.load_word(codec, input, premises, WordDomain::Small)
    }

    pub fn byte_load_four(
        &mut self,
        codec: &ByteFourCodec,
        input: ByteLoadFour,
        premises: ByteLoadFourPremises,
    ) -> Result<PendingEquality> {
        self.load_word(codec, input, premises, WordDomain::FourOnly)
    }

    fn load_word(
        &mut self,
        codec: &ByteWordCodec,
        input: ByteLoadWord,
        premises: ByteLoadWordPremises,
        domain: WordDomain,
    ) -> Result<PendingEquality> {
        self.charge()?;
        let count = codec.validate(domain)?;
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
                    nat(count),
                    align.clone(),
                ],
            ),
            &constant("Bool.true"),
        )?;
        premises.initialized.endpoints(
            &option("Nat"),
            &app(
                "ir_byte_read_word_v1",
                [
                    bytes(input.memory.clone()),
                    nat(count),
                    input.address.clone(),
                ],
            ),
            &some("Nat", codec.word.clone()),
        )?;
        self.byte_load_word_candidate(
            codec,
            input,
            count,
            WordLoadEvidence {
                align,
                pointer: premises.pointer,
                accessible: premises.accessible.term,
                initialized: premises.initialized.term,
            },
        )
    }

    fn byte_load_word_candidate(
        &mut self,
        codec: &ByteFourCodec,
        input: ByteLoadFour,
        count: u64,
        evidence: WordLoadEvidence,
    ) -> Result<PendingEquality> {
        let WordLoadEvidence {
            align,
            pointer,
            accessible,
            initialized,
        } = evidence;
        let dispatch = dispatch_word(self, codec, &input, count, pointer, false)?;
        let loaded = MemoryResult {
            value: codec.value.clone(),
            memory: input.memory.clone(),
        };
        let readback = PendingEquality::candidate(
            constant("IRByteMemoryResultV1"),
            dispatch.right.clone(),
            loaded.result(),
            app(
                "ir_byte_load_at_rule_v1",
                [
                    codec.context.clone(),
                    codec.ty.clone(),
                    input.address,
                    nat(count),
                    align,
                    input.memory,
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

    /// Actual nominal-width typed store, allocation/cursor framing and raw/typed
    /// readback for I/U8, I/U16 or I/U32. Exact width comes from the codec's
    /// nominal type, never an independent caller-supplied byte count.
    pub fn byte_store_word(
        &mut self,
        codec: &ByteWordCodec,
        input: ByteStoreWord,
        premises: ByteStoreWordPremises,
    ) -> Result<ByteStoreWordResult> {
        self.store_word(codec, input, premises, WordDomain::Small)
    }

    /// Actual four-byte typed store, allocation/cursor framing and raw/typed
    /// readback. All accesses observe the same returned memory; no no-alias
    /// premise or uniform-byte-map premise is introduced.
    pub fn byte_store_four(
        &mut self,
        codec: &ByteFourCodec,
        input: ByteStoreFour,
        premises: ByteStoreFourPremises,
    ) -> Result<ByteStoreFourResult> {
        self.store_word(codec, input, premises, WordDomain::FourOnly)
    }

    fn store_word(
        &mut self,
        codec: &ByteWordCodec,
        input: ByteStoreWord,
        premises: ByteStoreWordPremises,
        domain: WordDomain,
    ) -> Result<ByteStoreWordResult> {
        self.charge()?;
        let count = codec.validate(domain)?;
        premises.pointer.endpoints(
            &option("Nat"),
            &pointer_address(input.pointer.clone()),
            &some("Nat", input.address.clone()),
        )?;
        let input = ByteLoadFour {
            pointer: input.pointer,
            address: input.address,
            requested_align: input.requested_align,
            memory: input.memory,
        };
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
                    nat(count),
                    align.clone(),
                ],
            ),
            &constant("Bool.true"),
        )?;
        let next = written_word(
            input.memory.clone(),
            input.address.clone(),
            count,
            codec.word.clone(),
        );
        let result = MemoryResult {
            value: constant("IRScalar.unit_"),
            memory: next.clone(),
        };
        let dispatch = dispatch_word(self, codec, &input, count, premises.pointer.clone(), true)?;
        let word_guard = bool_fact(
            app(
                "ir_nat_ltb",
                [
                    codec.word.clone(),
                    app("ir_nat_pow2", [app("Nat.mul", [nat(8), nat(count)])]),
                ],
            ),
            app(
                "ir_byte_ltb_of_lt_v1",
                [
                    codec.word.clone(),
                    integer_word_limit(count),
                    codec.bounded.term.clone(),
                ],
            ),
        );
        let canonical = true_case(
            constant("IRByteMemoryResultV1"),
            store_word_branch(&input, codec.word.clone(), count),
            fault("type_error", "width_bounded", input.memory.clone()),
            result.result(),
            word_guard,
            PendingEquality::reflexive(constant("IRByteMemoryResultV1"), result.result()),
        );
        let (option_branch, encoded_function) = store_option_branch(self, codec, &input, count)?;
        let encoded = some_case_function(
            "Nat",
            constant("IRByteMemoryResultV1"),
            option_branch.clone(),
            fault("type_error", "width_bounded", input.memory.clone()),
            codec.encoded.clone(),
            codec.word.clone(),
            encoded_function,
            canonical,
        );
        let fits_branch = choose(
            &constant("IRByteMemoryResultV1"),
            codec.fits.left.clone(),
            option_branch.clone(),
            fault("type_error", "width_bounded", input.memory.clone()),
        );
        let fits = true_case(
            constant("IRByteMemoryResultV1"),
            fits_branch.clone(),
            fault("type_error", "width_bounded", input.memory.clone()),
            option_branch,
            codec.fits.clone(),
            encoded,
        );
        let stored = true_case(
            constant("IRByteMemoryResultV1"),
            dispatch.right.clone(),
            fault("ub", "bad_addr", input.memory.clone()),
            fits_branch,
            premises.accessible.clone(),
            fits,
        );
        let evaluated = self.compose(dispatch, stored)?;
        let raw_read = raw_read_word(
            self,
            bytes(input.memory.clone()),
            input.address.clone(),
            codec.word.clone(),
            count,
            codec.bounded.term.clone(),
        )?;
        let typed_readback = self.byte_load_word_candidate(
            codec,
            ByteLoadFour {
                memory: next.clone(),
                ..input.clone()
            },
            count,
            WordLoadEvidence {
                align,
                pointer: premises.pointer,
                accessible: premises.accessible.term,
                initialized: raw_read.term.clone(),
            },
        )?;
        let allocations = self.conversion(
            app("IRList", [constant("IRByteAllocationV1")]),
            allocs(next.clone()),
            allocs(input.memory.clone()),
        )?;
        let cursor = self.conversion(constant("Nat"), cursor(next), cursor(input.memory))?;
        Ok(ByteStoreFourResult {
            result,
            evaluated,
            allocations,
            cursor,
            raw_read,
            typed_readback,
        })
    }
}

#[cfg(test)]
#[path = "core_execution_memory_four_tests.rs"]
mod tests;
