// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Independent small-word controls for the existing fetched ByteV1 evaluator.
//! These are kernel/DAG tests, not native execution or caller-memory authority.

use super::*;
use trust_ir::Inst;

fn replay_word(scope: &Scope, proof: &PendingEquality, accepted: bool) {
    let term = scope.close(proof.term()).unwrap();
    let claim = scope.close(&proof.proposition()).unwrap();
    assert!(!term.has_fvar_quick() && !claim.has_fvar_quick());
    assert!(!term.has_loose_bvars() && !claim.has_loose_bvars());
    let decoded = trust_ir::proof::decode_clean_expr_dag_v2(
        &trust_ir::proof::encode_clean_expr_dag_v2(&term).unwrap(),
    )
    .unwrap();
    assert_eq!(decoded, term);
    for candidate in [&term, &decoded] {
        let checker = checker();
        checker
            .check_type(&claim, &Expr::sort(Level::zero()))
            .unwrap();
        let result = checker.check_type(candidate, &claim);
        assert!(
            !checker.heartbeat_spent(),
            "a resource stop is not a verdict"
        );
        assert!(!clean_kernel::tc::declaration_budget_exhausted());
        if accepted {
            result.unwrap();
            assert!(
                environment()
                    .audit_certification(&claim, candidate)
                    .is_certified()
            );
        } else {
            assert!(
                matches!(result, Err(KernelTypeError::TypeMismatch { .. })),
                "{result:?}"
            );
        }
    }
}

fn small_codec(
    assembler: &mut Assembler<'_>,
    model: &MachineModel,
    bits: u32,
    signed: bool,
    word: u32,
) -> ByteWordCodec {
    codec_for(
        assembler,
        model,
        app(
            if signed { "IRTy.int_" } else { "IRTy.uint_" },
            [nat(u64::from(bits))],
        ),
        bits,
        word,
        TestApi::Word,
    )
}

fn small_store(
    assembler: &mut Assembler<'_>,
    codec: &ByteWordCodec,
    memory: Expr,
) -> ByteStoreWordResult {
    store_for(
        assembler,
        codec,
        load_input_word(
            app("IRScalar.ptr_", [nat(80)]),
            80,
            memory,
            codec.byte_count().unwrap(),
        ),
        TestApi::Word,
    )
}

fn initialized(input: &ByteLoadWord, count: u64, word: Expr) -> PendingEquality {
    conversion(
        option("Nat"),
        app(
            "ir_byte_read_word_v1",
            [
                bytes(input.memory.clone()),
                nat(count),
                input.address.clone(),
            ],
        ),
        some("Nat", word),
    )
}

fn load_candidate(
    assembler: &mut Assembler<'_>,
    codec: &ByteWordCodec,
    input: ByteLoadWord,
    initialized: PendingEquality,
) -> Result<PendingEquality> {
    let premises = ByteLoadWordPremises {
        pointer: conversion(
            option("Nat"),
            pointer_address(input.pointer.clone()),
            some("Nat", input.address.clone()),
        ),
        accessible: accessible(codec, &input),
        initialized,
    };
    assembler.byte_load_word(codec, input, premises)
}

// The old four-byte fixture's short extent and missing byte are not faults
// for narrower reads. These rows target the actual small-word extent instead.
fn fault_memory(kind: usize, count: u64) -> Expr {
    let allocation = |base, size, live| {
        app(
            "IRByteAllocationV1.mk",
            [
                nat(base),
                nat(size),
                nat(0),
                constant(if live { "Bool.true" } else { "Bool.false" }),
            ],
        )
    };
    // Reconstruct the retained root-owned row and one exact caller allocation.
    let mut allocations = vec![app(
        "IRByteAllocationV1.mk",
        [nat(16), nat(16), nat(8), constant("Bool.true")],
    )];
    if kind == 2 {
        allocations.push(if count == 1 {
            allocation(81, 8, true)
        } else {
            allocation(80, count - 1, true)
        });
    } else {
        allocations.push(allocation(80, 8, kind != 1));
    }
    if kind == 3 {
        allocations.push(allocation(80, 8, true));
    }
    let rows = list("IRByteAllocationV1", &allocations);
    let map = if matches!(kind, 4 | 5) {
        Expr::lam(
            BinderInfo::Default,
            constant("Nat"),
            choose(
                &option("Nat"),
                app("ir_nat_eqb", [Expr::bvar(0), nat(80 + count - 1)]),
                if kind == 4 {
                    app("IROption.none", [constant("Nat")])
                } else {
                    some("Nat", nat(256))
                },
                some("Nat", nat(173)),
            ),
        )
    } else {
        Expr::lam(BinderInfo::Default, constant("Nat"), some("Nat", nat(173)))
    };
    app("IRByteMemoryV1.mk", [rows, map, nat(1)])
}

#[test]
fn small_word_fetched_unsigned_store_load_zero_extend_return_replays_full_world() {
    for bits in [8, 16] {
        for word in [0, 1, 1 << (bits - 1), (1 << bits) - 1] {
            fetched_sequence_word(bits, false, false, word, TestApi::Word);
        }
    }
    // The generalized API also executes its four-byte arm, not only metadata.
    fetched_sequence_word(32, false, false, 0x0102_0304, TestApi::Word);
}

#[test]
fn small_word_fetched_signed_high_bits_distinguish_sign_and_zero_extension() {
    for bits in [8, 16] {
        for word in [1 << (bits - 1), (1 << bits) - 1] {
            fetched_sequence_word(bits, true, true, word, TestApi::Word);
            fetched_sequence_word(bits, true, false, word, TestApi::Word);
        }
    }
    fetched_sequence_word(32, true, true, u32::MAX, TestApi::Word);
}

#[test]
fn small_word_store_replays_universal_word_and_arbitrary_prior_bytes() {
    for bits in [8, 16, 32] {
        for signed in [false, true] {
            universal_prior_bytes(bits, signed, TestApi::Word);
        }
    }
}

#[test]
fn small_word_last_store_preserves_neighbors_and_remaining_wide_slot_bytes() {
    let mut f = fixture(false, false);
    // All three store widths belong to this same reflected source context.
    f.module.types.extend([Ty::U8, Ty::U16]);
    assert!(crate::validate_module(&f.module).is_empty());
    let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    for (bits, first_word, last_word) in [(8, 0xa5, 0x5a), (16, 0xbeef, 0x1234)] {
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let wide_codec = codec(&mut assembler, &model, f.ty.clone(), 0x0102_0304);
        let wide = store(
            &mut assembler,
            &wide_codec,
            load_input(app("IRScalar.ptr_", [nat(80)]), 80, memory(0)),
        );
        let first_codec = small_codec(&mut assembler, &model, bits, false, first_word);
        let first = small_store(&mut assembler, &first_codec, wide.result.memory.clone());
        let last_codec = small_codec(&mut assembler, &model, bits, false, last_word);
        let last = small_store(&mut assembler, &last_codec, first.result.memory.clone());
        let count = last_codec.byte_count().unwrap();
        let input = load_input_word(
            app("IRScalar.ptr_", [nat(80)]),
            80,
            last.result.memory.clone(),
            count,
        );
        let error = load_candidate(
            &mut assembler,
            &last_codec,
            input.clone(),
            first.raw_read.clone(),
        )
        .err()
        .unwrap();
        assert_eq!(
            error,
            "equality left endpoint: different candidate terms; supply an explicit equality transport"
        );
        let loaded = load_candidate(
            &mut assembler,
            &last_codec,
            input.clone(),
            initialized(&input, count, nat(u64::from(last_word))),
        )
        .unwrap();
        let wide_word = (0x0102_0304_u64 & !((1_u64 << bits) - 1)) | u64::from(last_word);
        let wide_read = initialized(&input, 4, nat(wide_word));
        let stale_wide = initialized(&input, 4, nat(0x0102_0304));
        let stale_small = initialized(&input, count, nat(u64::from(first_word)));
        let digits = (79..=84)
            .map(|at| {
                let byte = if !(80..84).contains(&at) {
                    173
                } else {
                    (wide_word >> (8 * (at - 80))) & 255
                };
                conversion(
                    option("Nat"),
                    Expr::app(bytes(last.result.memory.clone()), nat(at)),
                    some("Nat", nat(byte)),
                )
            })
            .collect::<Vec<_>>();
        drop(assembler);
        for proof in [
            &wide.evaluated,
            &first.evaluated,
            &last.evaluated,
            &last.raw_read,
            &last.typed_readback,
            &last.allocations,
            &last.cursor,
            &loaded,
            &wide_read,
        ] {
            replay_word(&scope, proof, true);
        }
        for digit in digits {
            replay_word(&scope, &digit, true);
        }
        replay_word(&scope, &stale_wide, false);
        replay_word(&scope, &stale_small, false);
    }
}

#[test]
fn small_word_codec_nominal_width_bound_layout_and_forged_proofs_fail_closed() {
    for bits in [8, 16] {
        let f = fixture_word(bits, false, false);
        let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
        let model = MachineModel::new(constant("Nat"), &reflected, providers());
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let found = conversion(
            option("IRByteLayoutV1"),
            app("ir_byte_layout_v1", [model.context().clone(), f.ty.clone()]),
            some("IRByteLayoutV1", layout(f.ty.clone(), f.bytes)),
        );
        let wrong_bound = PendingProof::candidate(
            app("Nat.lt", [nat(7), word_limit()]),
            constant("True.intro"),
        );
        let error = assembler
            .byte_integer_word_codec(
                model.context().clone(),
                f.ty.clone(),
                nat(7),
                found.clone(),
                wrong_bound,
            )
            .err()
            .unwrap();
        assert_eq!(
            error,
            "small integer canonical word bound: different candidate terms; supply an explicit equality transport"
        );
        let out_of_range = 1_u64 << bits;
        let bad = assembler
            .byte_integer_word_codec(
                model.context().clone(),
                f.ty.clone(),
                nat(out_of_range),
                found,
                PendingProof::candidate(
                    app("Nat.lt", [nat(out_of_range), integer_word_limit(f.bytes)]),
                    app("Nat.zero_le", [nat(0)]),
                ),
            )
            .unwrap();
        let noncanonical = small_store(&mut assembler, &bad, memory(0));
        let mut valid = small_codec(&mut assembler, &model, bits, false, 7);
        valid.layout_found.term = constant("True.intro");
        let forged_layout = small_store(&mut assembler, &valid, memory(0));
        let mut wrong_layout = small_codec(&mut assembler, &model, bits, false, 7);
        wrong_layout.layout = layout(f.ty.clone(), if bits == 8 { 2 } else { 1 });
        wrong_layout.layout_found = conversion(
            option("IRByteLayoutV1"),
            app("ir_byte_layout_v1", [model.context().clone(), f.ty.clone()]),
            some("IRByteLayoutV1", wrong_layout.layout.clone()),
        );
        wrong_layout.valid_layout = truth(word_layout_guard(wrong_layout.layout.clone(), f.bytes));
        let wrong_layout_store = small_store(&mut assembler, &wrong_layout, memory(0));
        let mut wrong_width = small_codec(&mut assembler, &model, bits, false, 7);
        wrong_width.ty = app("IRTy.uint_", [nat(if bits == 8 { 16 } else { 8 })]);
        let input = load_input_word(app("IRScalar.ptr_", [nat(80)]), 80, memory(0), f.bytes);
        let error = assembler
            .byte_store_word(
                &wrong_width,
                ByteStoreWord {
                    pointer: input.pointer.clone(),
                    address: input.address.clone(),
                    requested_align: input.requested_align.clone(),
                    memory: input.memory.clone(),
                },
                ByteStoreWordPremises {
                    pointer: conversion(
                        option("Nat"),
                        pointer_address(input.pointer.clone()),
                        some("Nat", input.address.clone()),
                    ),
                    accessible: accessible(&wrong_width, &input),
                },
            )
            .err()
            .unwrap();
        assert_eq!(
            error,
            "equality left endpoint: different candidate terms; supply an explicit equality transport"
        );
        drop(assembler);
        replay_word(&scope, &noncanonical.evaluated, false);
        replay_word(&scope, &forged_layout.evaluated, false);
        replay_word(&scope, &wrong_layout_store.evaluated, false);
    }
}

#[test]
fn small_word_store_requires_live_unique_complete_and_aligned_extent() {
    for bits in [8, 16] {
        for kind in [1, 2, 3, 6] {
            let mut f = fixture_word(bits, false, false);
            let address = if kind == 6 { 81 } else { 80 };
            if kind == 6 {
                let Inst::Store { align, .. } = &mut f.module.functions
                    [f.function.index() as usize]
                    .blocks[f.block.index() as usize]
                    .body[0]
                    .inst
                else {
                    unreachable!()
                };
                *align = Some(2);
            }
            let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
            let model = MachineModel::new(constant("Nat"), &reflected, providers());
            let site = Catalog::new(environment(), &reflected, limits())
                .unwrap()
                .fetch(f.coordinate(0))
                .unwrap();
            let before = f.current(
                address,
                7,
                if kind == 6 {
                    memory(0)
                } else {
                    fault_memory(kind, f.bytes)
                },
            );
            let mut scope = Scope::new();
            let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
            let codec = small_codec(&mut assembler, &model, bits, false, 7);
            let input = load_input_word(
                app(
                    "ir_getd",
                    [before.machine(), nat(u64::from(f.pointer.index()))],
                ),
                address,
                current_memory(&before),
                if kind == 6 { 2 } else { f.bytes },
            );
            let denied = conversion(
                constant("Bool"),
                accessible(&codec, &input).left().clone(),
                constant("Bool.false"),
            );
            let stored = store_for(&mut assembler, &codec, input, TestApi::Word);
            let step = transfer(
                &mut assembler,
                &model,
                &site,
                &before,
                stored.result,
                stored.evaluated,
                stored.allocations,
            );
            drop(assembler);
            replay_word(&scope, &denied, true);
            replay_word(&scope, step.step(), false);
        }
    }
}

#[test]
fn small_word_load_requires_every_initialized_byte_and_exact_claimed_word() {
    for bits in [8, 16] {
        let f = fixture_word(bits, false, false);
        let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
        let model = MachineModel::new(constant("Nat"), &reflected, providers());
        for kind in [0, 4, 5] {
            let mut scope = Scope::new();
            let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
            let codec = small_codec(&mut assembler, &model, bits, false, 7);
            let input = load_input_word(
                app("IRScalar.ptr_", [nat(80)]),
                80,
                if kind == 0 {
                    memory(0)
                } else {
                    fault_memory(kind, f.bytes)
                },
                f.bytes,
            );
            let loaded = load_candidate(
                &mut assembler,
                &codec,
                input.clone(),
                initialized(&input, f.bytes, nat(7)),
            )
            .unwrap();
            let actual = conversion(
                option("Nat"),
                initialized(&input, f.bytes, nat(7)).left().clone(),
                if kind == 0 {
                    some("Nat", nat(if bits == 8 { 0xad } else { 0xadad }))
                } else {
                    app("IROption.none", [constant("Nat")])
                },
            );
            drop(assembler);
            replay_word(&scope, &actual, true);
            replay_word(&scope, &loaded, false);
        }
    }
}

#[test]
fn small_word_fetched_volatile_ssa_and_result_substitutions_are_not_authority() {
    for bits in [8, 16] {
        for mutation in 0..4 {
            let mut f = fixture_word(bits, false, false);
            if mutation == 0 {
                let Inst::Store { volatile, .. } = &mut f.module.functions
                    [f.function.index() as usize]
                    .blocks[f.block.index() as usize]
                    .body[0]
                    .inst
                else {
                    unreachable!()
                };
                *volatile = true;
                let error = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap_err();
                assert_eq!(
                    error.to_string(),
                    "volatile memory operations have no Core byte profile semantics"
                );
                continue;
            }
            let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
            let model = MachineModel::new(constant("Nat"), &reflected, providers());
            let mut site = Catalog::new(environment(), &reflected, limits())
                .unwrap()
                .fetch(f.coordinate(0))
                .unwrap();
            if mutation == 3 {
                site.results = list("Nat", &[nat(u64::from(f.loaded.index()))]);
            }
            let before = f.current(
                if mutation == 2 { 16 } else { 80 },
                if mutation == 1 { 11 } else { 7 },
                memory(0),
            );
            let mut scope = Scope::new();
            let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
            let codec = small_codec(&mut assembler, &model, bits, false, 7);
            let stored = store_for(
                &mut assembler,
                &codec,
                load_input_word(
                    app(
                        "ir_getd",
                        [before.machine(), nat(u64::from(f.pointer.index()))],
                    ),
                    80,
                    current_memory(&before),
                    f.bytes,
                ),
                TestApi::Word,
            );
            let step = transfer(
                &mut assembler,
                &model,
                &site,
                &before,
                stored.result,
                stored.evaluated,
                stored.allocations,
            );
            drop(assembler);
            replay_word(&scope, step.step(), false);
        }
        let mut invalid = fixture_word(bits, false, false);
        invalid.module.functions[invalid.function.index() as usize].blocks
            [invalid.block.index() as usize]
            .body[0]
            .results
            .push(invalid.loaded);
        assert!(crate::validate_module(&invalid.module).iter().any(|error| matches!(error,
            crate::ValidationError::InstrResultArityMismatch { op, expected: 0, actual: 1, .. } if op == "store")));
        let error =
            reflect_core_module_v1(&invalid.module, &[(invalid.function, 4096)]).unwrap_err();
        assert!(
            error.to_string().contains("invalid actual Core module:"),
            "{error}"
        );
    }
}

#[test]
fn legacy_four_refuses_small_word_aliases_after_charge_and_retains_four_terms() {
    let f = fixture(false, false);
    let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    for bits in [8, 16] {
        for signed in [false, true] {
            let codec = small_codec(&mut assembler, &model, bits, signed, 7);
            assert_eq!(codec.byte_count().unwrap(), u64::from(bits / 8));
            let before = assembler.operations();
            let error = assembler
                .byte_integer32_codec(
                    model.context().clone(),
                    codec.ty.clone(),
                    codec.word.clone(),
                    codec.layout_found.clone(),
                    codec.bounded.clone(),
                )
                .err()
                .unwrap();
            assert_eq!(error, "four-byte codec requires the actual I32 or U32 type");
            assert_eq!(assembler.operations(), before + 1);
            let input = load_input_word(
                app("IRScalar.ptr_", [nat(80)]),
                80,
                memory(0),
                codec.byte_count().unwrap(),
            );
            let pointer = conversion(
                option("Nat"),
                pointer_address(input.pointer.clone()),
                some("Nat", input.address.clone()),
            );
            let access = accessible(&codec, &input);
            let before = assembler.operations();
            let error = assembler
                .byte_load_four(
                    &codec,
                    input.clone(),
                    ByteLoadWordPremises {
                        pointer: pointer.clone(),
                        accessible: access.clone(),
                        initialized: initialized(&input, codec.byte_count().unwrap(), nat(7)),
                    },
                )
                .err()
                .unwrap();
            assert_eq!(error, "four-byte codec requires the actual I32 or U32 type");
            assert_eq!(assembler.operations(), before + 1);
            let before = assembler.operations();
            let error = assembler
                .byte_store_four(
                    &codec,
                    ByteStoreWord {
                        pointer: input.pointer,
                        address: input.address,
                        requested_align: input.requested_align,
                        memory: input.memory,
                    },
                    ByteStoreWordPremises {
                        pointer,
                        accessible: access,
                    },
                )
                .err()
                .unwrap();
            assert_eq!(error, "four-byte codec requires the actual I32 or U32 type");
            assert_eq!(assembler.operations(), before + 1);
        }
    }
    for ty in [
        constant("IRTy.ptr_"),
        constant("IRTy.bool_"),
        app("IRTy.int_", [nat(64)]),
    ] {
        let found = conversion(
            option("IRByteLayoutV1"),
            app("ir_byte_layout_v1", [model.context().clone(), ty.clone()]),
            some("IRByteLayoutV1", layout(ty.clone(), 1)),
        );
        let before = assembler.operations();
        let error = assembler
            .byte_integer_word_codec(
                model.context().clone(),
                ty,
                nat(7),
                found,
                bounded_word(8, nat(7), 7),
            )
            .err()
            .unwrap();
        assert_eq!(
            error,
            "small integer codec requires the actual I/U8, I/U16 or I/U32 type"
        );
        assert_eq!(assembler.operations(), before + 1);
    }
    let before = assembler.operations();
    let old = codec(&mut assembler, &model, f.ty.clone(), 7);
    let old_codec_ops = assembler.operations() - before;
    let before = assembler.operations();
    let generic = codec_for(&mut assembler, &model, f.ty.clone(), 32, 7, TestApi::Word);
    assert_eq!(assembler.operations() - before, old_codec_ops);
    assert_eq!(old.byte_count().unwrap(), 4);
    assert_eq!(old.bounded.proposition(), generic.bounded.proposition());
    assert_eq!(old.bounded.term(), generic.bounded.term());
    for (old, generic) in [
        (&old.lane, &generic.lane),
        (&old.layout_found, &generic.layout_found),
        (&old.valid_layout, &generic.valid_layout),
        (&old.fits, &generic.fits),
        (&old.encoded, &generic.encoded),
        (&old.decoded, &generic.decoded),
    ] {
        assert_eq!(old.proposition(), generic.proposition());
        assert_eq!(old.term(), generic.term());
    }
    let input = load_input(app("IRScalar.ptr_", [nat(80)]), 80, memory(0));
    let before = assembler.operations();
    let old_store = store(&mut assembler, &old, input.clone());
    let old_store_ops = assembler.operations() - before;
    let before = assembler.operations();
    let generic_store = store_for(&mut assembler, &generic, input, TestApi::Word);
    assert_eq!(assembler.operations() - before, old_store_ops);
    let input = load_input(
        app("IRScalar.ptr_", [nat(80)]),
        80,
        old_store.result.memory.clone(),
    );
    let read = initialized(&input, 4, nat(7));
    let premises = ByteLoadWordPremises {
        pointer: conversion(
            option("Nat"),
            pointer_address(input.pointer.clone()),
            some("Nat", input.address.clone()),
        ),
        accessible: accessible(&old, &input),
        initialized: read,
    };
    let before = assembler.operations();
    let old_load = load_for(
        &mut assembler,
        &old,
        input.clone(),
        premises.clone(),
        TestApi::LegacyFour,
    )
    .unwrap();
    let old_load_ops = assembler.operations() - before;
    let before = assembler.operations();
    let generic_load = load_for(&mut assembler, &generic, input, premises, TestApi::Word).unwrap();
    assert_eq!(assembler.operations() - before, old_load_ops);
    drop(assembler);
    for (old, generic) in [
        (&old_store.evaluated, &generic_store.evaluated),
        (&old_store.raw_read, &generic_store.raw_read),
        (&old_store.typed_readback, &generic_store.typed_readback),
        (&old_load, &generic_load),
    ] {
        assert_eq!(old.proposition(), generic.proposition());
        assert_eq!(
            scope.close(old.term()).unwrap(),
            scope.close(generic.term()).unwrap()
        );
        replay_word(&scope, old, true);
        replay_word(&scope, generic, true);
    }
}

fn word_public_door(
    assembler: &mut Assembler<'_>,
    codec: &ByteWordCodec,
    input: &ByteLoadWord,
    door: usize,
) -> Result<()> {
    let pointer = conversion(
        option("Nat"),
        pointer_address(input.pointer.clone()),
        some("Nat", input.address.clone()),
    );
    let access = accessible(codec, input);
    match door {
        0 => assembler
            .byte_integer_word_codec(
                codec.context.clone(),
                codec.ty.clone(),
                codec.word.clone(),
                codec.layout_found.clone(),
                codec.bounded.clone(),
            )
            .map(|_| ()),
        1 => assembler
            .byte_load_word(
                codec,
                input.clone(),
                ByteLoadWordPremises {
                    pointer,
                    accessible: access,
                    initialized: initialized(
                        input,
                        codec.byte_count().unwrap(),
                        codec.word.clone(),
                    ),
                },
            )
            .map(|_| ()),
        2 => assembler
            .byte_store_word(
                codec,
                ByteStoreWord {
                    pointer: input.pointer.clone(),
                    address: input.address.clone(),
                    requested_align: input.requested_align.clone(),
                    memory: input.memory.clone(),
                },
                ByteStoreWordPremises {
                    pointer,
                    accessible: access,
                },
            )
            .map(|_| ()),
        _ => unreachable!(),
    }
}

#[test]
fn small_word_partial_failure_and_operation_counter_overflow_never_refund_or_wrap() {
    for bits in [8, 16] {
        let f = fixture_word(bits, false, false);
        let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
        let model = MachineModel::new(constant("Nat"), &reflected, providers());
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let codec = small_codec(&mut assembler, &model, bits, false, 7);
        let stored = small_store(&mut assembler, &codec, memory(0));
        let input = load_input_word(
            app("IRScalar.ptr_", [nat(80)]),
            80,
            stored.result.memory.clone(),
            f.bytes,
        );
        drop(assembler);
        // These are genuine closed prerequisites, not malformed inputs whose
        // semantic refusal could accidentally stand in for the resource gate.
        replay_word(&scope, &codec.fits, true);
        replay_word(&scope, &stored.evaluated, true);
        replay_word(&scope, &stored.raw_read, true);
        let mut partial_limits = limits();
        partial_limits.max_operations = 1;
        let mut partial = Assembler::new(&mut scope, partial_limits).unwrap();
        let error = word_public_door(&mut partial, &codec, &input, 2).unwrap_err();
        assert_eq!(error, "execution construction operation budget exceeded");
        assert_eq!(
            partial.operations(),
            1,
            "retain the successfully charged prefix"
        );
        for door in 0..3 {
            let error = word_public_door(&mut partial, &codec, &input, door).unwrap_err();
            assert_eq!(error, "execution construction operation budget exceeded");
            assert_eq!(partial.operations(), 1);
        }
        drop(partial);
        let mut overflowing = Assembler::new(&mut scope, limits()).unwrap();
        // The ordinary limit is unchanged: checked_add must fail before its
        // comparison against max_operations, without publishing a candidate.
        overflowing.operations = usize::MAX;
        for door in 0..3 {
            let error = word_public_door(&mut overflowing, &codec, &input, door).unwrap_err();
            assert_eq!(error, "operation counter overflow");
            assert_eq!(overflowing.operations(), usize::MAX);
            assert_eq!(codec.byte_count().unwrap(), f.bytes);
        }
    }
}
