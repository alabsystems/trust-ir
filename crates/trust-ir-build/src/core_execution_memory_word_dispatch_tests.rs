// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Ordinary-consumer controls for call-local reuse of actual option functions.
//! The old dispatch is a test-only construction oracle, never an evaluator or
//! production fallback. Charged construction savings are not runtime claims.

use super::*;

#[path = "core_execution_closed_word_dispatch_tests.rs"]
mod closed_templates;

fn old_pointer_branch(
    assembler: &mut Assembler<'_>,
    codec: &ByteFourCodec,
    input: &ByteLoadFour,
    shape: Expr,
    size: Expr,
    store: bool,
) -> Result<Expr> {
    let address = assembler.local(constant("Nat"))?;
    let success = address.lam(access_at(
        codec,
        input,
        shape,
        size,
        address.term().clone(),
        store,
    ));
    Ok(option_rec([
        constant("Nat"),
        Expr::lam(
            clean_kernel::BinderInfo::Default,
            option("Nat"),
            constant("IRByteMemoryResultV1"),
        ),
        fault("type_error", "not_ptr", input.memory.clone()),
        success,
        pointer_address(input.pointer.clone()),
    ]))
}

fn old_layout_branch(
    assembler: &mut Assembler<'_>,
    codec: &ByteFourCodec,
    input: &ByteLoadFour,
    shape: Expr,
    size: Expr,
    store: bool,
) -> Result<Expr> {
    let guard = app(
        "Bool.and",
        [
            app(
                "ir_nat_eqb",
                [size.clone(), app("ir_byte_layout_size_v1", [shape.clone()])],
            ),
            app(
                "ir_byte_alignment_v1",
                [app("ir_byte_layout_align_v1", [shape.clone()])],
            ),
        ],
    );
    let success = old_pointer_branch(assembler, codec, input, shape, size, store)?;
    Ok(choose(
        &constant("IRByteMemoryResultV1"),
        guard,
        success,
        fault("type_error", "width_bounded", input.memory.clone()),
    ))
}

fn old_layout_option_branch(
    assembler: &mut Assembler<'_>,
    codec: &ByteFourCodec,
    input: &ByteLoadFour,
    size: Expr,
    store: bool,
) -> Result<Expr> {
    let shape = assembler.local(constant("IRByteLayoutV1"))?;
    let body = old_layout_branch(assembler, codec, input, shape.term().clone(), size, store)?;
    Ok(option_rec([
        constant("IRByteLayoutV1"),
        Expr::lam(
            clean_kernel::BinderInfo::Default,
            option("IRByteLayoutV1"),
            constant("IRByteMemoryResultV1"),
        ),
        fault("unmodelled", "width_bounded", input.memory.clone()),
        shape.lam(body),
        app(
            "ir_byte_layout_v1",
            [codec.context.clone(), codec.ty.clone()],
        ),
    ]))
}

fn old_dispatch_word(
    assembler: &mut Assembler<'_>,
    codec: &ByteFourCodec,
    input: &ByteLoadFour,
    count: u64,
    pointer: PendingEquality,
    store: bool,
) -> Result<PendingEquality> {
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
    let source = old_pointer_branch(
        assembler,
        codec,
        input,
        codec.layout.clone(),
        nat(count),
        store,
    )?;
    let pointer = some_case(
        assembler,
        "Nat",
        ty.clone(),
        source,
        fault("type_error", "not_ptr", input.memory.clone()),
        pointer,
        input.address.clone(),
        |_, address| {
            Ok(access_at(
                codec,
                input,
                codec.layout.clone(),
                nat(count),
                address,
                store,
            ))
        },
        step,
    )?;
    let source = old_layout_branch(
        assembler,
        codec,
        input,
        codec.layout.clone(),
        nat(count),
        store,
    )?;
    let layout = true_case(
        ty.clone(),
        source,
        fault("type_error", "width_bounded", input.memory.clone()),
        pointer.left.clone(),
        codec.valid_layout.clone(),
        pointer,
    );
    let source = old_layout_option_branch(assembler, codec, input, nat(count), store)?;
    let layout = some_case(
        assembler,
        "IRByteLayoutV1",
        ty.clone(),
        source,
        fault("unmodelled", "width_bounded", input.memory.clone()),
        codec.layout_found.clone(),
        codec.layout.clone(),
        |assembler, shape| old_layout_branch(assembler, codec, input, shape, nat(count), store),
        layout,
    )?;
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
    some_case(
        assembler,
        "Nat",
        ty,
        source,
        fault("unmodelled", "width_bounded", input.memory.clone()),
        codec.lane.clone(),
        nat(count),
        |assembler, size| old_layout_option_branch(assembler, codec, input, size, store),
        layout,
    )
}

fn replay_both(scope: &Scope, proof: &PendingEquality, accepted: bool) {
    let term = scope.close(proof.term()).unwrap();
    let claim = scope.close(&proof.proposition()).unwrap();
    assert!(!term.has_fvar_quick() && !claim.has_fvar_quick());
    assert!(!term.has_loose_bvars() && !claim.has_loose_bvars());
    let decoded = trust_ir::proof::decode_clean_expr_dag_v2(
        &trust_ir::proof::encode_clean_expr_dag_v2(&term).unwrap(),
    )
    .unwrap();
    for candidate in [&term, &decoded] {
        let checker = checker();
        checker
            .check_type(&claim, &Expr::sort(Level::zero()))
            .unwrap();
        let checked = checker.check_type(candidate, &claim);
        assert!(
            !checker.heartbeat_spent(),
            "resource stops are not verdicts"
        );
        assert!(!clean_kernel::tc::declaration_budget_exhausted());
        if accepted {
            checked.unwrap();
            let audit = environment().audit_certification(&claim, candidate);
            assert!(audit.is_certified());
            for dependency in &audit.dependencies {
                assert!(environment().axiom_deps(dependency).unwrap().is_empty());
                assert!(
                    environment()
                        .foundational_axiom_deps(dependency)
                        .unwrap()
                        .is_empty()
                );
                assert!(
                    environment()
                        .trust_marker_deps(dependency)
                        .unwrap()
                        .is_empty()
                );
            }
        } else {
            assert!(
                matches!(checked, Err(KernelTypeError::TypeMismatch { .. })),
                "{checked:?}"
            );
        }
    }
}

fn pointer(input: &ByteLoadWord) -> PendingEquality {
    conversion(
        option("Nat"),
        pointer_address(input.pointer.clone()),
        some("Nat", input.address.clone()),
    )
}

fn public_store(
    assembler: &mut Assembler<'_>,
    codec: &ByteWordCodec,
    input: &ByteLoadWord,
    premises: ByteStoreWordPremises,
) -> Result<ByteStoreWordResult> {
    assembler.byte_store_word(
        codec,
        ByteStoreWord {
            pointer: input.pointer.clone(),
            address: input.address.clone(),
            requested_align: input.requested_align.clone(),
            memory: input.memory.clone(),
        },
        premises,
    )
}

#[test]
fn shared_word_dispatch_matches_old_ordered_case_oracle_with_zero_helper_locals() {
    for bits in [8, 16, 32] {
        for signed in [false, true] {
            let f = fixture_word(bits, signed, false);
            let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
            let model = MachineModel::new(constant("Nat"), &reflected, providers());
            let mut scope = Scope::new();
            let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
            let codec = codec_for(&mut assembler, &model, f.ty, bits, 7, TestApi::Word);
            let input = load_input_word(app("IRScalar.ptr_", [nat(80)]), 80, memory(0), f.bytes);
            let mut proofs = Vec::new();
            for store in [false, true] {
                let before = (assembler.operations(), assembler.locals);
                let old = old_dispatch_word(
                    &mut assembler,
                    &codec,
                    &input,
                    f.bytes,
                    pointer(&input),
                    store,
                )
                .unwrap();
                assert_eq!(
                    (
                        assembler.operations() - before.0,
                        assembler.locals - before.1
                    ),
                    (10, 10)
                );
                let before = (assembler.operations(), assembler.locals);
                let shared = dispatch_word(
                    &mut assembler,
                    &codec,
                    &input,
                    f.bytes,
                    pointer(&input),
                    store,
                )
                .unwrap();
                assert_eq!(
                    (
                        assembler.operations() - before.0,
                        assembler.locals - before.1
                    ),
                    (3, 0)
                );
                assert_eq!(old.proposition(), shared.proposition());
                proofs.extend([old, shared]);
            }
            drop(assembler);
            for proof in proofs {
                replay_both(&scope, &proof, true);
            }
        }
    }
}

#[test]
fn shared_word_store_keeps_all_readback_and_frame_proofs_without_helper_locals() {
    for (bits, signed, api) in [
        (8, false, TestApi::Word),
        (8, true, TestApi::Word),
        (16, false, TestApi::Word),
        (16, true, TestApi::Word),
        (32, false, TestApi::Word),
        (32, true, TestApi::Word),
        (32, false, TestApi::LegacyFour),
        (32, true, TestApi::LegacyFour),
    ] {
        let f = fixture_word(bits, signed, false);
        let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
        let model = MachineModel::new(constant("Nat"), &reflected, providers());
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let codec = codec_for(&mut assembler, &model, f.ty, bits, 7, api);
        let before = (assembler.operations(), assembler.locals);
        let stored = store_for(
            &mut assembler,
            &codec,
            load_input_word(app("IRScalar.ptr_", [nat(80)]), 80, memory(0), f.bytes),
            api,
        );
        assert_eq!(assembler.locals - before.1, 0);
        assert_eq!(assembler.operations() - before.0, 13 + f.bytes as usize);
        let input = load_input_word(
            app("IRScalar.ptr_", [nat(80)]),
            80,
            stored.result.memory.clone(),
            f.bytes,
        );
        // Public Load checks its exact returned-memory projection. Store's
        // raw readback uses the written byte map, so retain the same charged
        // conversion/compose bridge as the fetched-sequence controls.
        let before_bridge = (assembler.operations(), assembler.locals);
        let initialized_bridge = assembler
            .conversion(
                option("Nat"),
                app(
                    "ir_byte_read_word_v1",
                    [bytes(input.memory.clone()), nat(f.bytes), nat(80)],
                ),
                stored.raw_read.left().clone(),
            )
            .unwrap();
        let initialized = assembler
            .compose(initialized_bridge.clone(), stored.raw_read.clone())
            .unwrap();
        assert_eq!(
            (
                assembler.operations() - before_bridge.0,
                assembler.locals - before_bridge.1
            ),
            (2, 0)
        );
        let before = (assembler.operations(), assembler.locals);
        let loaded = load_for(
            &mut assembler,
            &codec,
            input.clone(),
            ByteLoadWordPremises {
                pointer: pointer(&input),
                accessible: accessible(&codec, &input),
                initialized: initialized.clone(),
            },
            api,
        )
        .unwrap();
        assert_eq!(
            (
                assembler.operations() - before.0,
                assembler.locals - before.1
            ),
            (5, 0)
        );
        assert_eq!(loaded.proposition(), stored.typed_readback.proposition());
        drop(assembler);
        for proof in [
            &stored.evaluated,
            &stored.allocations,
            &stored.cursor,
            &stored.raw_read,
            &stored.typed_readback,
            &initialized_bridge,
            &initialized,
            &loaded,
        ] {
            replay_both(&scope, proof, true);
        }
    }
}

#[test]
fn shared_word_store_tight_caps_charge_real_work_and_never_refund_failures() {
    for bits in [8, 16, 32] {
        let f = fixture_word(bits, false, false);
        let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
        let model = MachineModel::new(constant("Nat"), &reflected, providers());
        let mut scope = Scope::new();
        let mut setup = Assembler::new(&mut scope, limits()).unwrap();
        let codec = codec_for(&mut setup, &model, f.ty, bits, 7, TestApi::Word);
        drop(setup);
        let input = load_input_word(app("IRScalar.ptr_", [nat(80)]), 80, memory(0), f.bytes);
        let premises = ByteStoreWordPremises {
            pointer: pointer(&input),
            accessible: accessible(&codec, &input),
        };
        let operations = 13 + f.bytes as usize;
        let mut tight = limits();
        tight.max_locals = 1;
        tight.max_operations = operations;
        let mut assembler = Assembler::new(&mut scope, tight).unwrap();
        let stored = public_store(&mut assembler, &codec, &input, premises.clone()).unwrap();
        assert_eq!((assembler.operations(), assembler.locals), (operations, 0));
        drop(assembler);
        replay_both(&scope, &stored.evaluated, true);
        replay_both(&scope, &stored.typed_readback, true);
        // The deliberately removed helper footprint makes exhausted caller
        // locals a success for Store, not permission to allocate another local.
        let mut local_limit = limits();
        local_limit.max_locals = 1;
        let mut assembler = Assembler::new(&mut scope, local_limit).unwrap();
        let caller = assembler.local(constant("Nat")).unwrap();
        let before = (assembler.operations(), assembler.locals);
        let allocated_before = assembler.local_scope().allocated();
        let stored = public_store(&mut assembler, &codec, &input, premises.clone()).unwrap();
        assert_eq!(
            (assembler.operations(), assembler.locals),
            (before.0 + operations, 1)
        );
        let spent = assembler.operations();
        assert_eq!(
            assembler.local(constant("Nat")).err().unwrap(),
            "execution construction local budget exceeded"
        );
        assert_eq!((assembler.operations(), assembler.locals), (spent + 1, 1));
        assert_eq!(assembler.local_scope().allocated(), allocated_before);
        drop(caller);
        drop(assembler);
        replay_both(&scope, &stored.evaluated, true);
        replay_both(&scope, &stored.typed_readback, true);
        let mut tight = limits();
        tight.max_operations = operations - 1;
        let mut assembler = Assembler::new(&mut scope, tight).unwrap();
        assert_eq!(
            public_store(&mut assembler, &codec, &input, premises.clone())
                .err()
                .unwrap(),
            "execution construction operation budget exceeded"
        );
        assert_eq!(
            (assembler.operations(), assembler.locals),
            (operations - 1, 0)
        );
        let before = (assembler.operations(), assembler.locals);
        assert!(public_store(&mut assembler, &codec, &input, premises.clone()).is_err());
        assert_eq!((assembler.operations(), assembler.locals), before);
    }
}

#[test]
fn shared_word_store_endpoint_refusals_precede_dispatch_allocation() {
    let f = fixture_word(8, false, false);
    let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let codec = codec_for(&mut assembler, &model, f.ty, 8, 7, TestApi::Word);
    let input = load_input_word(app("IRScalar.ptr_", [nat(80)]), 80, memory(0), 1);
    for mutation in 0..8 {
        let mut codec = codec.clone();
        let mut premises = ByteStoreWordPremises {
            pointer: pointer(&input),
            accessible: accessible(&codec, &input),
        };
        match mutation {
            0 => codec.lane.right = some("Nat", nat(2)),
            1 => codec.layout_found.right = some("IRByteLayoutV1", layout(codec.ty.clone(), 2)),
            2 => premises.pointer.right = some("Nat", nat(81)),
            3 => codec.encoded.right = some("Nat", nat(8)),
            4 => codec.fits.right = constant("Bool.false"),
            5 => premises.accessible.right = constant("Bool.false"),
            6 => codec.decoded.right = some("IRScalar", scalar(nat(8))),
            7 => {
                codec.bounded = PendingProof::candidate(
                    app("Nat.lt", [nat(7), nat(256)]),
                    codec.bounded.term().clone(),
                )
            }
            _ => unreachable!(),
        }
        let before = (assembler.operations(), assembler.locals);
        assert!(public_store(&mut assembler, &codec, &input, premises).is_err());
        assert_eq!(
            (
                assembler.operations() - before.0,
                assembler.locals - before.1
            ),
            (1, 0)
        );
    }
}

#[test]
fn shared_word_store_forged_case_evidence_and_stale_readback_fail_semantically() {
    let f = fixture_word(8, false, false);
    let reflected = reflect_core_module_v1(&f.module, &[(f.function, 4096)]).unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let codec = codec_for(&mut assembler, &model, f.ty, 8, 7, TestApi::Word);
    let input = load_input_word(app("IRScalar.ptr_", [nat(80)]), 80, memory(0), 1);
    let mut negatives = Vec::new();
    for mutation in 0..7 {
        let mut codec = codec.clone();
        let mut premises = ByteStoreWordPremises {
            pointer: pointer(&input),
            accessible: accessible(&codec, &input),
        };
        let evidence = match mutation {
            0 => &mut codec.lane,
            1 => &mut codec.layout_found,
            2 => &mut premises.pointer,
            3 => &mut codec.encoded,
            4 => &mut codec.fits,
            5 => &mut premises.accessible,
            6 => &mut codec.decoded,
            _ => unreachable!(),
        };
        let wrong = if evidence.ty == constant("Bool") {
            constant("Bool.false")
        } else if evidence.ty == option("IRByteLayoutV1") {
            app("IROption.none", [constant("IRByteLayoutV1")])
        } else if evidence.ty == option("IRScalar") {
            app("IROption.none", [constant("IRScalar")])
        } else {
            app("IROption.none", [constant("Nat")])
        };
        evidence.term = refl(&evidence.ty, wrong);
        let stored = public_store(&mut assembler, &codec, &input, premises).unwrap();
        negatives.push(if mutation == 6 {
            stored.typed_readback
        } else {
            stored.evaluated
        });
    }
    let stored = public_store(
        &mut assembler,
        &codec,
        &input,
        ByteStoreWordPremises {
            pointer: pointer(&input),
            accessible: accessible(&codec, &input),
        },
    )
    .unwrap();
    let stale = PendingEquality::candidate(
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
        MemoryResult {
            value: codec.value.clone(),
            memory: input.memory.clone(),
        }
        .result(),
        stored.typed_readback.term().clone(),
    );
    drop(assembler);
    replay_both(&scope, &stored.evaluated, true);
    replay_both(&scope, &stored.typed_readback, true);
    negatives.push(stale);
    for proof in negatives {
        replay_both(&scope, &proof, false);
    }
}
