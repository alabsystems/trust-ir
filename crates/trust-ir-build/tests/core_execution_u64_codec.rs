// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! An ordinary Trust consumer of full-width U64 byte-memory candidates.
//!
//! The exact unsigned type lives in the reflected context, while ByteV1's
//! scalar stores signed and unsigned integer bits in the same constructor.
//! Every candidate is independently kernel-replayed, including a universally
//! quantified load from arbitrary incoming memory. These are pointwise model
//! laws, not native execution, caller admission, or a whole-program proof.

use clean_kernel::{BinderInfo, Environment, Expr, KernelTypeError, Level, Name, TypeChecker};
use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};
use trust_ir::{Endianness, StructPassingPolicy, TargetInfo, Ty};
use trust_ir_build::{
    ModuleBuilder,
    core_execution::{
        Assembler, ByteEightCodec, ByteLoadEight, ByteLoadEightPremises, Limits, PendingEquality,
        PendingProof,
    },
    core_reflection::reflect_core_module_v1,
    scoped_local::{LocalScope, ScopedLocal},
};

fn c(name: &str) -> Expr {
    Expr::const_str(name)
}

fn app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(name), args)
}

fn nat(value: u64) -> Expr {
    Expr::nat_lit(value)
}

fn option(ty: &str) -> Expr {
    app("IROption", [c(ty)])
}

fn some(ty: &str, value: Expr) -> Expr {
    app("IROption.some", [c(ty), value])
}

fn list(ty: &str, values: &[Expr]) -> Expr {
    values
        .iter()
        .rev()
        .fold(app("IRList.nil", [c(ty)]), |tail, value| {
            app("IRList.cons", [c(ty), value.clone(), tail])
        })
}

fn refl(ty: Expr, value: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [ty, value],
    )
}

fn conversion(ty: Expr, left: Expr, right: Expr) -> PendingEquality {
    PendingEquality::candidate(ty.clone(), left, right.clone(), refl(ty, right))
}

fn truth(left: Expr) -> PendingEquality {
    conversion(c("Bool"), left, c("Bool.true"))
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

fn environment() -> &'static Environment {
    shared_specification_with_stack(EvalIrVocabulary::ByteV1)
        .unwrap()
        .env()
}

fn checker() -> TypeChecker<'static> {
    let mut checker = TypeChecker::new(environment());
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    checker.set_heartbeat_limit(limits().lookup_heartbeats);
    checker.set_max_cache_entries(limits().lookup_cache_entries);
    checker
}

fn close(
    scope: &LocalScope,
    parameters: &[ScopedLocal],
    term: &Expr,
    claim: &Expr,
) -> (Expr, Expr) {
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

fn replay(scope: &LocalScope, parameters: &[ScopedLocal], proof: &PendingEquality, accepted: bool) {
    let (term, claim) = close(scope, parameters, proof.term(), &proof.proposition());
    assert!(!term.has_fvar_quick() && !claim.has_fvar_quick());
    let checker = checker();
    checker
        .check_type(&claim, &Expr::sort(Level::zero()))
        .unwrap();
    if accepted {
        checker.check_type(&term, &claim).unwrap();
        assert!(
            environment()
                .audit_certification(&claim, &term)
                .is_certified()
        );
        let encoded = trust_ir::proof::encode_clean_expr_dag_v2(&term).unwrap();
        let decoded = trust_ir::proof::decode_clean_expr_dag_v2(&encoded).unwrap();
        assert_eq!(decoded, term, "retain the whole candidate graph");
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
            "a real type mismatch, never a resource refusal: {error:?}"
        );
    }
}

fn replay_codec(scope: &LocalScope, parameters: &[ScopedLocal], codec: &ByteEightCodec) {
    assert_eq!(codec.ty, app("IRTy.uint_", [nat(64)]));
    assert_eq!(codec.value, app("IRScalar.int_", [codec.word.clone()]));
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
    let (term, claim) = close(
        scope,
        parameters,
        codec.bounded.term(),
        codec.bounded.proposition(),
    );
    checker().check_type(&term, &claim).unwrap();
    assert!(
        environment()
            .audit_certification(&claim, &term)
            .is_certified()
    );
}

fn layout(ty: Expr) -> Expr {
    app(
        "IRByteLayoutV1.mk",
        [ty, nat(8), nat(8), list("IRTy", &[]), list("Nat", &[])],
    )
}

fn found(context: Expr, ty: Expr) -> PendingEquality {
    conversion(
        option("IRByteLayoutV1"),
        app("ir_byte_layout_v1", [context, ty.clone()]),
        some("IRByteLayoutV1", layout(ty)),
    )
}

fn bound(word: Expr) -> Expr {
    app("Nat.lt", [word, c("ir_byte_limit_v1")])
}

fn bounded(word: u64) -> PendingProof {
    PendingProof::candidate(
        bound(nat(word)),
        app(
            "Nat.le_add_right",
            [app("Nat.succ", [nat(word)]), nat(u64::MAX - word)],
        ),
    )
}

fn context() -> Expr {
    let mut builder = ModuleBuilder::new_with_target_info(
        "ordinary_u64_codec_consumer",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: StructPassingPolicy::NativeC,
        },
    );
    let signature = builder.add_func_type(vec![Ty::U64, Ty::I64, Ty::Ptr], vec![Ty::U64]);
    let function = builder.declare_function("unsigned_transport", signature);
    let mut body = builder.define_function(function).unwrap();
    let block = body.create_block();
    let value = body.add_block_param(block, Ty::U64);
    body.add_block_param(block, Ty::I64);
    body.add_block_param(block, Ty::Ptr);
    body.switch_to_block(block);
    body.ret(vec![value]);
    body.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    assert!(trust_ir_build::validate_module(&module).is_empty());
    reflect_core_module_v1(&module, &[(function, 4096)])
        .unwrap()
        .context_term()
        .clone()
}

fn literal_codec(assembler: &mut Assembler<'_>, context: Expr, word: u64) -> ByteEightCodec {
    assembler
        .byte_u64_codec(
            context.clone(),
            nat(word),
            found(context, app("IRTy.uint_", [nat(64)])),
            bounded(word),
        )
        .unwrap()
}

fn memory(word: u64) -> Expr {
    // Independently authored concrete bytes, not a store/readback receipt.
    // Outside this one live cell the byte map is genuinely uninitialized.
    let bytes = word.to_le_bytes().iter().enumerate().rev().fold(
        app("IROption.none", [c("Nat")]),
        |tail, (offset, byte)| {
            Expr::apps(
                Expr::const_(
                    Name::from_string("Bool.rec"),
                    vec![Level::succ(Level::zero())],
                ),
                [
                    Expr::lam(BinderInfo::Default, c("Bool"), option("Nat")),
                    tail,
                    some("Nat", nat(u64::from(*byte))),
                    app(
                        "ir_nat_eqb",
                        [Expr::bvar(0), nat(80 + u64::try_from(offset).unwrap())],
                    ),
                ],
            )
        },
    );
    app(
        "IRByteMemoryV1.mk",
        [
            list(
                "IRByteAllocationV1",
                &[app(
                    "IRByteAllocationV1.mk",
                    [nat(80), nat(8), nat(0), c("Bool.true")],
                )],
            ),
            Expr::lam(BinderInfo::Default, c("Nat"), bytes),
            nat(128),
        ],
    )
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
        app("ir_byte_pointer_address_v1", [input.pointer.clone()]),
        some("Nat", input.address.clone()),
    )
}

fn accessible(codec: &ByteEightCodec, input: &ByteLoadEight) -> PendingEquality {
    truth(app(
        "ir_byte_accessible_v1",
        [
            app("ir_byte_mem_allocs_v1", [input.memory.clone()]),
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

fn initialized(input: &ByteLoadEight, word: Expr) -> PendingEquality {
    conversion(
        option("Nat"),
        app(
            "ir_byte_read_word_v1",
            [
                app("ir_byte_mem_bytes_v1", [input.memory.clone()]),
                nat(8),
                input.address.clone(),
            ],
        ),
        some("Nat", word),
    )
}

#[test]
fn unsigned_codec_replays_arbitrary_context_and_all_bounded_word_bits() {
    let mut scope = LocalScope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let context = assembler.local(c("IRByteContextV1")).unwrap();
    let word = assembler.local(c("Nat")).unwrap();
    let layout = found(context.term().clone(), app("IRTy.uint_", [nat(64)]));
    let layout_local = assembler.local(layout.proposition()).unwrap();
    let bound_local = assembler.local(bound(word.term().clone())).unwrap();
    let codec = assembler
        .byte_u64_codec(
            context.term().clone(),
            word.term().clone(),
            PendingEquality::candidate(
                option("IRByteLayoutV1"),
                layout.left().clone(),
                layout.right().clone(),
                layout_local.term().clone(),
            ),
            PendingProof::candidate(bound_local.ty().clone(), bound_local.term().clone()),
        )
        .unwrap();
    assert_eq!(
        assembler.operations(),
        5,
        "one codec charge, no local allocation or hidden budget reset"
    );
    drop(assembler);
    replay_codec(&scope, &[context, word, layout_local, bound_local], &codec);
    for name in [
        "ir_byte_u64_lane_eight_v1",
        "ir_byte_u64_value_fits_v1",
        "ir_byte_ltb_of_lt_v1",
    ] {
        let name = Name::from_string(name);
        assert!(environment().axiom_deps(&name).unwrap().is_empty());
        assert!(environment().trust_marker_deps(&name).unwrap().is_empty());
    }
}

#[test]
fn unsigned_codec_loads_actual_eight_bytes_including_high_bit_and_maximum() {
    let context = context();
    for word in [0, 1, 1 << 63, u64::MAX - 6, u64::MAX] {
        let mut scope = LocalScope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let codec = literal_codec(&mut assembler, context.clone(), word);
        let input = input(memory(word));
        let initialized = initialized(&input, nat(word));
        let loaded = assembler
            .byte_load_eight(
                &codec,
                input.clone(),
                ByteLoadEightPremises {
                    pointer: pointer(&input),
                    accessible: accessible(&codec, &input),
                    initialized: initialized.clone(),
                },
            )
            .unwrap();
        assert_eq!(
            loaded.right(),
            &app(
                "IRByteMemoryResultV1.value",
                [app("IRScalar.int_", [nat(word)]), input.memory.clone()]
            )
        );
        drop(assembler);
        replay_codec(&scope, &[], &codec);
        replay(&scope, &[], &initialized, true);
        replay(&scope, &[], &loaded, true);
    }
}

#[test]
fn unsigned_load_replays_universally_from_the_exact_arbitrary_incoming_memory() {
    let mut scope = LocalScope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let context = assembler.local(c("IRByteContextV1")).unwrap();
    let word = assembler.local(c("Nat")).unwrap();
    let layout = found(context.term().clone(), app("IRTy.uint_", [nat(64)]));
    let layout_local = assembler.local(layout.proposition()).unwrap();
    let bound_local = assembler.local(bound(word.term().clone())).unwrap();
    let codec = assembler
        .byte_u64_codec(
            context.term().clone(),
            word.term().clone(),
            PendingEquality::candidate(
                option("IRByteLayoutV1"),
                layout.left().clone(),
                layout.right().clone(),
                layout_local.term().clone(),
            ),
            PendingProof::candidate(bound_local.ty().clone(), bound_local.term().clone()),
        )
        .unwrap();
    let memory = assembler.local(c("IRByteMemoryV1")).unwrap();
    let input = input(memory.term().clone());
    let accessible = accessible(&codec, &input);
    let access_local = assembler.local(accessible.proposition()).unwrap();
    let initialized = initialized(&input, word.term().clone());
    let initialized_local = assembler.local(initialized.proposition()).unwrap();
    let loaded = assembler
        .byte_load_eight(
            &codec,
            input.clone(),
            ByteLoadEightPremises {
                pointer: pointer(&input),
                accessible: PendingEquality::candidate(
                    c("Bool"),
                    accessible.left().clone(),
                    accessible.right().clone(),
                    access_local.term().clone(),
                ),
                initialized: PendingEquality::candidate(
                    option("Nat"),
                    initialized.left().clone(),
                    initialized.right().clone(),
                    initialized_local.term().clone(),
                ),
            },
        )
        .unwrap();
    // The hypothesis is the input cell representation, not the desired typed
    // load/evaluator answer. The output retains that same entire memory.
    assert_eq!(
        loaded.right(),
        &app(
            "IRByteMemoryResultV1.value",
            [
                app("IRScalar.int_", [word.term().clone()]),
                memory.term().clone()
            ]
        )
    );
    assert!(assembler.operations() < limits().max_operations);
    drop(assembler);
    replay(
        &scope,
        &[
            context,
            word,
            layout_local,
            bound_local,
            memory,
            access_local,
            initialized_local,
        ],
        &loaded,
        true,
    );
}

#[test]
fn unsigned_codec_refuses_wrong_bounds_and_foreign_nominal_layout_endpoints() {
    let context = context();
    for ty in [
        app("IRTy.int_", [nat(64)]),
        c("IRTy.ptr_"),
        app("IRTy.uint_", [nat(32)]),
    ] {
        let mut scope = LocalScope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        assert!(
            assembler
                .byte_u64_codec(
                    context.clone(),
                    nat(7),
                    found(context.clone(), ty),
                    bounded(7)
                )
                .is_err()
        );
    }
    for wrong_bound in [bound(nat(8)), app("Nat.lt", [nat(7), nat(1 << 63)])] {
        let mut scope = LocalScope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        assert!(
            assembler
                .byte_u64_codec(
                    context.clone(),
                    nat(7),
                    found(context.clone(), app("IRTy.uint_", [nat(64)])),
                    PendingProof::candidate(wrong_bound, bounded(7).term().clone())
                )
                .is_err()
        );
    }
    for foreign in [app("IRTy.int_", [nat(64)]), c("IRTy.ptr_")] {
        let mut scope = LocalScope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let codec = literal_codec(&mut assembler, context.clone(), u64::MAX);
        let mut changed = codec.clone();
        changed.ty = foreign.clone();
        let foreign = PendingEquality::candidate(
            option("IRByteLayoutV1"),
            codec.layout_found.left().clone(),
            codec.layout_found.right().clone(),
            found(context.clone(), foreign).term().clone(),
        );
        let input = input(memory(u64::MAX));
        assert!(
            assembler
                .byte_load_eight(
                    &changed,
                    input.clone(),
                    ByteLoadEightPremises {
                        pointer: pointer(&input),
                        accessible: accessible(&codec, &input),
                        initialized: initialized(&input, nat(u64::MAX)),
                    }
                )
                .is_err(),
            "mutating a carrier type cannot reuse the candidate endpoints"
        );
        drop(assembler);
        replay(&scope, &[], &foreign, false);
    }
}

#[test]
fn matching_candidate_shapes_do_not_establish_false_bounds_or_initialization() {
    let context = context();
    let mut scope = LocalScope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let mut codec = literal_codec(&mut assembler, context.clone(), u64::MAX);
    // The Rust wrapper matches the exact required goal; only kernel replay
    // detects that the supplied bound term instead ends at 2^64 + 1.
    codec.bounded = PendingProof::candidate(
        bound(nat(u64::MAX)),
        app(
            "Nat.le_add_right",
            [app("Nat.succ", [nat(u64::MAX)]), nat(1)],
        ),
    );
    let bad_bound = assembler
        .byte_u64_codec(
            context,
            nat(u64::MAX),
            codec.layout_found.clone(),
            codec.bounded.clone(),
        )
        .unwrap();
    let good_codec = literal_codec(&mut assembler, bad_bound.context.clone(), u64::MAX);
    let input = input(memory(u64::MAX - 1));
    let false_initialized = initialized(&input, nat(u64::MAX));
    let loaded = assembler
        .byte_load_eight(
            &good_codec,
            input.clone(),
            ByteLoadEightPremises {
                pointer: pointer(&input),
                accessible: accessible(&good_codec, &input),
                initialized: false_initialized.clone(),
            },
        )
        .unwrap();
    drop(assembler);
    replay(&scope, &[], &bad_bound.fits, false);
    replay(&scope, &[], &false_initialized, false);
    replay(&scope, &[], &loaded, false);
}

#[test]
fn unsigned_codec_obeys_the_existing_operation_budget() {
    let context = context();
    let mut scope = LocalScope::new();
    let mut limits = limits();
    limits.max_operations = 1;
    let mut assembler = Assembler::new(&mut scope, limits).unwrap();
    let codec = literal_codec(&mut assembler, context.clone(), u64::MAX);
    assert_eq!(assembler.operations(), 1);
    assert!(
        assembler
            .byte_u64_codec(
                context.clone(),
                nat(0),
                found(context, app("IRTy.uint_", [nat(64)])),
                bounded(0)
            )
            .is_err()
    );
    drop(assembler);
    replay_codec(&scope, &[], &codec);
}
