// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Independent ByteV1 model replay, not native/caller or whole-source credit.
//! A canonical pointer's bits and its referent's accessibility are separate.

use super::*;
use crate::{ModuleBuilder, core_reflection::reflect_core_module_v1};
use clean_kernel::{BinderInfo, ExprKind, KernelTypeError};
use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};
use trust_ir::{Endianness, StructPassingPolicy, TargetInfo, Ty};

fn environment() -> &'static Environment {
    shared_specification_with_stack(EvalIrVocabulary::ByteV1)
        .unwrap()
        .env()
}

fn checker() -> TypeChecker<'static> {
    let mut checker = TypeChecker::new(environment());
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    checker.set_heartbeat_limit(5_000_000);
    checker.set_max_cache_entries(100_000);
    checker
}

fn limits() -> Limits {
    Limits {
        max_operations: 1_000,
        max_locals: 100,
        max_list_items: 100,
        max_lookup_candidates: 32,
        lookup_heartbeats: 5_000_000,
        lookup_cache_entries: 100_000,
    }
}

fn closed(scope: &Scope, parameters: &[Local], term: &Expr, claim: &Expr) -> (Expr, Expr) {
    let term = parameters
        .iter()
        .rev()
        .fold(term.clone(), |body, local| local.lam(body));
    let claim = parameters
        .iter()
        .rev()
        .fold(claim.clone(), |body, local| local.pi(body));
    (scope.close(&term).unwrap(), scope.close(&claim).unwrap())
}

fn replay(scope: &Scope, parameters: &[Local], proof: &PendingEquality, accepted: bool) {
    let (term, claim) = closed(scope, parameters, proof.term(), &proof.proposition());
    assert!(!term.has_fvar_quick() && !claim.has_fvar_quick());
    let checker = checker();
    checker
        .check_type(&claim, &Expr::sort(Level::zero()))
        .expect("a real, well-typed model proposition");
    if accepted {
        checker.check_type(&term, &claim).unwrap();
        assert!(
            environment()
                .audit_certification(&claim, &term)
                .is_certified()
        );
        let encoded = trust_ir::proof::encode_clean_expr_dag_v2(&term).unwrap();
        let decoded = trust_ir::proof::decode_clean_expr_dag_v2(&encoded).unwrap();
        assert_eq!(decoded, term, "retain the complete closed proof graph");
        checker.check_type(&decoded, &claim).unwrap();
        assert!(
            environment()
                .audit_certification(&claim, &decoded)
                .is_certified()
        );
    } else {
        let error = checker.check_type(&term, &claim).unwrap_err();
        assert!(
            matches!(error, KernelTypeError::TypeMismatch { .. }),
            "a genuine kernel mismatch, not a resource stop: {error:?}"
        );
    }
}

fn replay_codec(scope: &Scope, parameters: &[Local], codec: &ByteEightCodec) {
    assert_eq!(codec.ty, constant("IRTy.ptr_"));
    assert_eq!(
        codec.value,
        app("ir_byte_pointer_value_v1", [codec.word.clone()])
    );
    for proof in [
        &codec.lane,
        &codec.layout_found,
        &codec.valid_layout,
        &codec.fits,
        &codec.encoded,
        &codec.decoded,
    ] {
        replay(scope, parameters, proof, true);
    }
    let (term, claim) = closed(
        scope,
        parameters,
        codec.bounded.term(),
        codec.bounded.proposition(),
    );
    checker().check_type(&term, &claim).unwrap();
}

fn conversion(ty: Expr, left: Expr, right: Expr) -> PendingEquality {
    PendingEquality::candidate(ty.clone(), left, right.clone(), refl(&ty, right))
}

fn truth(left: Expr) -> PendingEquality {
    conversion(constant("Bool"), left, constant("Bool.true"))
}

fn bounded(word: Expr, literal: u64) -> PendingProof {
    PendingProof::candidate(
        app("Nat.lt", [word.clone(), limit()]),
        app(
            "Nat.le_add_right",
            [app("Nat.succ", [word]), nat(u64::MAX - literal)],
        ),
    )
}

fn context(address: u64, extra_type: Ty) -> Expr {
    let mut builder = ModuleBuilder::new_with_target_info(
        "ordinary_pointer_codec_consumer",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: StructPassingPolicy::NativeC,
        },
    );
    let signature = builder.add_func_type(vec![Ty::Ptr, extra_type.clone()], vec![Ty::Ptr]);
    let function = builder.declare_function("pointer_transport", signature);
    let mut body = builder.define_function(function).unwrap();
    let block = body.create_block();
    let value = body.add_block_param(block, Ty::Ptr);
    body.add_block_param(block, extra_type);
    body.switch_to_block(block);
    body.ret(vec![value]);
    body.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    assert!(crate::validate_module(&module).is_empty());
    reflect_core_module_v1(&module, &[(function, address)])
        .unwrap()
        .context_term()
        .clone()
}

fn found(context: Expr) -> PendingEquality {
    conversion(
        option("IRByteLayoutV1"),
        app("ir_byte_layout_v1", [context, constant("IRTy.ptr_")]),
        some("IRByteLayoutV1", layout(constant("IRTy.ptr_"), 8)),
    )
}

fn codec(assembler: &mut Assembler<'_>, context: Expr, word: u64) -> ByteEightCodec {
    assembler
        .byte_ptr_codec(
            context.clone(),
            nat(word),
            found(context),
            bounded(nat(word), word),
        )
        .unwrap()
}

fn memory(live: bool, size: u64, duplicate: bool, initialized: bool) -> Expr {
    let allocation = || {
        app(
            "IRByteAllocationV1.mk",
            [
                nat(80),
                nat(size),
                nat(0),
                constant(if live { "Bool.true" } else { "Bool.false" }),
            ],
        )
    };
    let rows = if duplicate {
        vec![allocation(), allocation()]
    } else {
        vec![allocation()]
    };
    memory_with_bytes(
        list("IRByteAllocationV1", &rows),
        Expr::lam(
            BinderInfo::Default,
            constant("Nat"),
            if initialized {
                some("Nat", nat(173))
            } else {
                app("IROption.none", [constant("Nat")])
            },
        ),
    )
}

fn memory_with_bytes(rows: Expr, byte_map: Expr) -> Expr {
    app("IRByteMemoryV1.mk", [rows, byte_map, nat(1)])
}

fn input(memory: Expr) -> ByteLoadEight {
    ByteLoadEight {
        pointer: app("IRScalar.ptr_", [nat(80)]),
        address: nat(80),
        requested_align: nat(8),
        memory,
    }
}

fn pointer(input: &ByteLoadEight) -> PendingEquality {
    conversion(
        option("Nat"),
        pointer_address(input.pointer.clone()),
        some("Nat", input.address.clone()),
    )
}

fn accessible(codec: &ByteEightCodec, input: &ByteLoadEight) -> PendingEquality {
    truth(app(
        "ir_byte_accessible_v1",
        [
            allocs(input.memory.clone()),
            input.address.clone(),
            nat(8),
            app(
                "ir_byte_effective_align_v1",
                [
                    input.requested_align.clone(),
                    app("ir_byte_layout_align_v1", [codec.layout.clone()]),
                ],
            ),
        ],
    ))
}

fn store(
    assembler: &mut Assembler<'_>,
    codec: &ByteEightCodec,
    input: &ByteLoadEight,
) -> ByteStoreEightResult {
    assembler
        .byte_store_eight(
            codec,
            ByteStoreEight {
                pointer: input.pointer.clone(),
                address: input.address.clone(),
                requested_align: input.requested_align.clone(),
                memory: input.memory.clone(),
            },
            ByteStoreEightPremises {
                pointer: pointer(input),
                accessible: accessible(codec, input),
            },
        )
        .unwrap()
}

fn load(
    assembler: &mut Assembler<'_>,
    codec: &ByteEightCodec,
    input: &ByteLoadEight,
    initialized: PendingEquality,
) -> Result<PendingEquality> {
    assembler.byte_load_eight(
        codec,
        input.clone(),
        ByteLoadEightPremises {
            pointer: pointer(input),
            accessible: accessible(codec, input),
            initialized,
        },
    )
}

#[test]
fn pointer_codec_canonical_null_one_high_half_and_max_replay_kernel_dag_v2() {
    let context = context(4096, Ty::I64);
    for word in [0, 1, 1 << 63, u64::MAX] {
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let codec = codec(&mut assembler, context.clone(), word);
        let canonical = assembler
            .conversion(
                constant("IRScalar"),
                codec.value.clone(),
                if word == 0 {
                    constant("IRScalar.nullptr_")
                } else {
                    app("IRScalar.ptr_", [nat(word)])
                },
            )
            .unwrap();
        drop(assembler);
        replay_codec(&scope, &[], &codec);
        replay(&scope, &[], &canonical, true);
    }
}

#[test]
fn pointer_codec_symbolic_context_and_word_use_exact_independent_premises() {
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let unrelated = assembler.local(constant("Nat")).unwrap();
    let context = assembler.local(constant("IRByteContextV1")).unwrap();
    let word = assembler.local(constant("Nat")).unwrap();
    let layout_claim = found(context.term().clone());
    let layout_local = assembler.local(layout_claim.proposition()).unwrap();
    let bound_local = assembler
        .local(app("Nat.lt", [word.term().clone(), limit()]))
        .unwrap();
    let codec = assembler
        .byte_ptr_codec(
            context.term().clone(),
            word.term().clone(),
            PendingEquality::candidate(
                option("IRByteLayoutV1"),
                layout_claim.left().clone(),
                layout_claim.right().clone(),
                layout_local.term().clone(),
            ),
            PendingProof::candidate(bound_local.ty().clone(), bound_local.term().clone()),
        )
        .unwrap();
    assert!(
        !assembler
            .byte_ptr_encoded_candidate
            .as_ref()
            .unwrap()
            .has_fvar_quick(),
        "no caller locals captured in the combined codec cache"
    );
    assert!(
        assembler.byte_pointer_word_candidate.is_none(),
        "the codec does not construct unused address-recovery evidence"
    );
    drop(assembler);
    replay_codec(
        &scope,
        &[unrelated, context, word, layout_local, bound_local],
        &codec,
    );
}

#[test]
fn pointer_codec_closed_combined_cache_reuses_changed_context_word_and_layout_catalog() {
    let contexts = [context(4096, Ty::I64), context(8192, Ty::U32)];
    assert_ne!(contexts[0], contexts[1]);
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let unrelated = assembler.local(constant("Nat")).unwrap();
    let first = codec(&mut assembler, contexts[0].clone(), 0);
    let cached = assembler.byte_ptr_encoded_candidate.clone().unwrap();
    let locals = assembler.locals;
    let operations = assembler.operations;
    assert_eq!(locals, 10, "one caller local plus one nine-local factory");
    assert!(assembler.byte_pointer_word_candidate.is_none());
    let second = codec(&mut assembler, contexts[1].clone(), u64::MAX);
    assert_eq!(
        assembler.locals, locals,
        "cache hits allocate no new locals"
    );
    assert_eq!(assembler.operations, operations + 1);
    assert!(assembler.byte_pointer_word_candidate.is_none());
    let actual = assembler.byte_ptr_encoded_candidate.as_ref().unwrap();
    assert_eq!(actual, &cached);
    let (ExprKind::Lam(_, actual_ty, actual_body), ExprKind::Lam(_, saved_ty, saved_body)) =
        (actual.kind(), cached.kind())
    else {
        panic!("a closed reusable lambda, not a consumer-specific result");
    };
    assert!(std::sync::Arc::ptr_eq(actual_ty, saved_ty));
    assert!(std::sync::Arc::ptr_eq(actual_body, saved_body));
    assert!(!actual.has_fvar_quick());
    drop(assembler);
    replay_codec(&scope, std::slice::from_ref(&unrelated), &first);
    replay_codec(&scope, &[unrelated], &second);
}

#[test]
fn pointer_codec_combined_factory_fits_actual_local_budget_without_unused_address() {
    let context = context(4096, Ty::I64);
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    for _ in 0..91 {
        assembler.local(constant("Nat")).unwrap();
    }
    let first = codec(&mut assembler, context.clone(), 0);
    assert_eq!(assembler.locals, 100, "one combined nine-local factory");
    assert_eq!(
        assembler.limits.max_locals, 100,
        "the actual limit is unchanged"
    );
    assert!(assembler.byte_pointer_word_candidate.is_none());
    let cached = assembler.byte_ptr_encoded_candidate.clone().unwrap();
    let operations = assembler.operations;
    let second = codec(&mut assembler, context, u64::MAX);
    assert_eq!(assembler.locals, 100, "no caller local budget reset");
    assert_eq!(assembler.operations, operations + 1);
    assert!(assembler.byte_pointer_word_candidate.is_none());
    assert_eq!(assembler.byte_ptr_encoded_candidate.as_ref(), Some(&cached));
    drop(assembler);
    // The caller's 91 unrelated locals are not captured by either candidate.
    replay_codec(&scope, &[], &first);
    replay_codec(&scope, &[], &second);
}

#[test]
fn pointer_codec_store_load_current_memory_and_both_neighbor_bytes_replay() {
    let context = context(4096, Ty::I64);
    for word in [0, 1 << 63] {
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let prior_bytes = assembler
            .local(Expr::pi(
                BinderInfo::Default,
                constant("Nat"),
                option("Nat"),
            ))
            .unwrap();
        let codec = codec(&mut assembler, context.clone(), word);
        let before = input(memory_with_bytes(
            allocs(memory(true, 8, false, true)),
            prior_bytes.term().clone(),
        ));
        let stored = store(&mut assembler, &codec, &before);
        let after = input(stored.result.memory.clone());
        let loaded = load(&mut assembler, &codec, &after, stored.raw_read.clone()).unwrap();
        assert_eq!(
            loaded.right(),
            &MemoryResult {
                value: codec.value.clone(),
                memory: after.memory.clone()
            }
            .result()
        );
        let framed = [79, 88].map(|neighbor| {
            PendingEquality::candidate(
                option("Nat"),
                Expr::app(bytes(after.memory.clone()), nat(neighbor)),
                Expr::app(bytes(before.memory.clone()), nat(neighbor)),
                app(
                    "ir_byte_write_outside_v1",
                    [
                        bytes(before.memory.clone()),
                        nat(80),
                        nat(8),
                        nat(word),
                        nat(neighbor),
                        refl(&constant("Bool"), constant("Bool.false")),
                    ],
                ),
            )
        });
        drop(assembler);
        let parameters = std::slice::from_ref(&prior_bytes);
        for proof in [
            &stored.evaluated,
            &stored.raw_read,
            &stored.typed_readback,
            &stored.allocations,
            &stored.cursor,
            &loaded,
            &framed[0],
            &framed[1],
        ] {
            replay(&scope, parameters, proof, true);
        }
    }
}

#[test]
fn pointer_codec_foreign_endpoints_refuse_and_false_matching_proofs_kernel_reject() {
    let context = context(4096, Ty::I64);
    for mutation in 0..4 {
        let mut layout_found = found(context.clone());
        let mut bound = bounded(nat(7), 7);
        match mutation {
            0 => {
                layout_found.left = app(
                    "ir_byte_layout_v1",
                    [context.clone(), app("IRTy.int_", [nat(64)])],
                )
            }
            1 => layout_found.right = some("IRByteLayoutV1", layout(constant("IRTy.ptr_"), 4)),
            2 => bound.proposition = app("Nat.lt", [nat(8), limit()]),
            3 => bound.proposition = app("Nat.lt", [nat(7), nat(1 << 63)]),
            _ => unreachable!(),
        }
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        assert!(
            assembler
                .byte_ptr_codec(context.clone(), nat(7), layout_found, bound)
                .is_err()
        );
        assert!(assembler.byte_ptr_encoded_candidate.is_none());
        assert!(assembler.byte_pointer_word_candidate.is_none());
    }
    for bad_layout in [false, true] {
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let mut layout_found = found(context.clone());
        let mut bound = bounded(nat(7), 7);
        if bad_layout {
            layout_found.term = refl(
                &option("IRByteLayoutV1"),
                some("IRByteLayoutV1", layout(constant("IRTy.ptr_"), 4)),
            );
        } else {
            bound.term = refl(&constant("Bool"), constant("Bool.true"));
        }
        let codec = assembler
            .byte_ptr_codec(context.clone(), nat(7), layout_found, bound)
            .unwrap();
        let before = input(memory(true, 8, false, true));
        let stored = store(&mut assembler, &codec, &before);
        drop(assembler);
        replay(&scope, &[], &stored.evaluated, false);
    }
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let noncanonical = assembler
        .byte_ptr_codec(
            context.clone(),
            limit(),
            found(context),
            PendingProof::candidate(
                app("Nat.lt", [limit(), limit()]),
                bounded(nat(7), 7).term().clone(),
            ),
        )
        .unwrap();
    drop(assembler);
    replay(&scope, &[], &noncanonical.fits, false);
    replay(&scope, &[], &noncanonical.encoded, false);
}

#[test]
fn pointer_codec_null_is_not_ptr_zero_and_integer_retyping_does_not_validate() {
    let context = context(4096, Ty::I64);
    for (word, bad_value) in [(0, app("IRScalar.ptr_", [nat(0)])), (7, scalar(nat(7)))] {
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let mut codec = codec(&mut assembler, context.clone(), word);
        codec.value = bad_value.clone();
        codec.fits.left = app(
            "ir_byte_value_matches_v1",
            [context.clone(), codec.ty.clone(), bad_value.clone()],
        );
        codec.encoded.left = app(
            "ir_byte_scalar_word_v1",
            [context.clone(), bad_value.clone()],
        );
        codec.decoded.right = some("IRScalar", bad_value);
        codec.validate().unwrap(); // Matching wrappers alone are not proof.
        let before = input(memory(true, 8, false, true));
        let stored = store(&mut assembler, &codec, &before);
        drop(assembler);
        replay(&scope, &[], &stored.evaluated, false);
    }
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let mut codec = codec(&mut assembler, context, 7);
    codec.ty = app("IRTy.int_", [nat(64)]);
    assert!(codec.validate().is_err(), "nominal Ptr is not an I64 codec");
}

#[test]
fn pointer_codec_requires_current_memory_initialization_and_separate_permissions() {
    let context = context(4096, Ty::I64);
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let codec = codec(&mut assembler, context, 7);
    let before = input(memory(true, 8, false, true));
    let stored = store(&mut assembler, &codec, &before);
    let after = input(stored.result.memory.clone());
    let positive = load(&mut assembler, &codec, &after, stored.raw_read.clone()).unwrap();
    assert!(
        load(&mut assembler, &codec, &before, stored.raw_read.clone()).is_err(),
        "a final-memory witness cannot name the old memory"
    );
    let mut stale = stored.raw_read.clone();
    stale.left = app(
        "ir_byte_read_word_v1",
        [bytes(before.memory.clone()), nat(8), nat(80)],
    );
    let stale_load = load(&mut assembler, &codec, &before, stale).unwrap();
    let mut negatives = vec![stale_load];
    let mut valid_initializations = Vec::new();
    for kind in 0..5 {
        let mut inaccessible = input(memory(
            kind != 0,
            if kind == 1 { 7 } else { 8 },
            kind == 2,
            kind != 3,
        ));
        if kind == 4 {
            inaccessible.requested_align = nat(32); // 80 is not aligned32.
        }
        if kind != 3 {
            // Change only allocation rows/alignment, retaining genuinely
            // initialized bytes. Each access refusal must stand on its own.
            inaccessible.memory = memory_with_bytes(
                allocs(inaccessible.memory.clone()),
                bytes(after.memory.clone()),
            );
        }
        let read = app(
            "ir_byte_read_word_v1",
            [bytes(inaccessible.memory.clone()), nat(8), nat(80)],
        );
        let initialized = if kind == 3 {
            conversion(option("Nat"), read, some("Nat", nat(7)))
        } else {
            let bridge = assembler
                .conversion(option("Nat"), read, stored.raw_read.left().clone())
                .unwrap();
            let initialized = assembler.compose(bridge, stored.raw_read.clone()).unwrap();
            valid_initializations.push(initialized.clone());
            initialized
        };
        negatives.push(load(&mut assembler, &codec, &inaccessible, initialized).unwrap());
    }
    // Representability does not make the stored value7 an accessible address.
    let mut referent = after;
    referent.pointer = codec.value.clone();
    referent.address = nat(7);
    let old_bytes = bytes(referent.memory.clone());
    referent.memory = memory_with_bytes(
        allocs(referent.memory.clone()),
        app(
            "ir_byte_write_word_v1",
            [old_bytes.clone(), nat(7), nat(8), nat(7)],
        ),
    );
    let initialized = PendingEquality::candidate(
        option("Nat"),
        app(
            "ir_byte_read_word_v1",
            [bytes(referent.memory.clone()), nat(8), nat(7)],
        ),
        some("Nat", nat(7)),
        app(
            "ir_byte_read_write_eight_v1",
            [old_bytes, nat(7), nat(7), codec.bounded.term().clone()],
        ),
    );
    valid_initializations.push(initialized.clone());
    negatives.push(load(&mut assembler, &codec, &referent, initialized).unwrap());
    drop(assembler);
    replay(&scope, &[], &stored.evaluated, true);
    replay(&scope, &[], &positive, true);
    for initialization in valid_initializations {
        replay(&scope, &[], &initialization, true);
    }
    for negative in negatives {
        replay(&scope, &[], &negative, false);
    }
}

#[test]
fn pointer_codec_existing_operation_and_local_caps_remain_fail_closed() {
    let context = context(4096, Ty::I64);
    for local_cap in [false, true] {
        let mut cap = limits();
        if local_cap {
            cap.max_locals = 1;
        } else {
            cap.max_operations = 1;
        }
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, cap).unwrap();
        let error = assembler
            .byte_ptr_codec(
                context.clone(),
                nat(7),
                found(context.clone()),
                bounded(nat(7), 7),
            )
            .err()
            .expect("unchanged construction limits must refuse");
        assert_eq!(
            error.to_string(),
            if local_cap {
                "execution construction local budget exceeded"
            } else {
                "execution construction operation budget exceeded"
            }
        );
        assert!(assembler.byte_ptr_encoded_candidate.is_none());
    }
}
